local Blitbuffer = require("ffi/blitbuffer")
local ButtonTable = require("ui/widget/buttontable")
local CenterContainer = require("ui/widget/container/centercontainer")
local Device = require("device")
local Event = require("ui/event")
local Font = require("ui/font")
local FrameContainer = require("ui/widget/container/framecontainer")
local Geom = require("ui/geometry")
local GestureRange = require("ui/gesturerange")
local HorizontalGroup = require("ui/widget/horizontalgroup")
local HorizontalSpan = require("ui/widget/horizontalspan")
local ImageWidget = require("ui/widget/imagewidget")
local InputContainer = require("ui/widget/container/inputcontainer")
local JSON = require("json")
local NetworkMgr = require("ui/network/manager")
local DataStorage = require("datastorage")
local InfoMessage = require("ui/widget/infomessage")
local LuaSettings = require("luasettings")
local socket = require("socket")
local TextBoxWidget = require("ui/widget/textboxwidget")
local TextWidget = require("ui/widget/textwidget")
local UIManager = require("ui/uimanager")
local VerticalGroup = require("ui/widget/verticalgroup")
local VerticalSpan = require("ui/widget/verticalspan")
local Widget = require("ui/widget/widget")
local WidgetContainer = require("ui/widget/container/widgetcontainer")
local http = require("socket.http")
local ltn12 = require("ltn12")
local Screen = Device.screen

---------------------------------------------------------------- config ----
local BASE_OVERRIDE = ""           -- "" = find the PC automatically; or a fixed address like "http://192.168.1.50:8000"
local PORT = 8000                  -- the port server.py listens on
local SCAN_NETWORK = true          -- look for servers on the Wi-Fi network the Kindle is on
local HOSTS = {}                   -- extra addresses to check, e.g. over Tailscale: { "100.101.102.103:8000" }
local AUTO_CONNECT_SINGLE = true   -- exactly one server found -> connect without asking
local POLL_SECS = 5                -- how often to check the PC (screen only redraws on change)
local LANDSCAPE = true             -- try to rotate to landscape while open
local LANDSCAPE_MODE = 1           -- 1 or 3; swap if it comes up upside down
local ART_PATH = "/tmp/dash_art.png"
local POSTER_PATH = "/tmp/dash_poster.png"
local KEEP_AWAKE = true            -- never sleep while the dashboard is open and the PC is reachable (the offline sleep below still applies)
local KEEP_AWAKE_SECS = 30         -- how often to tell KOReader "someone is here"
local OFFLINE_SLEEP_SECS = 300     -- PC unreachable this long -> sleep (0 = never).
local OFFLINE_ACTION = "suspend"   -- "suspend", or "close" (close dashboard, let KOReader's own autosuspend take over)
local IDLE_SLEEP_SECS = 0          -- PC reachable but nothing playing this long -> sleep (0 = never; the idle clock is used instead)
local OFFLINE_POLL_SECS = 15       -- slower retries while the PC is unreachable
local IDLE_CLOCK_SECS = 300        -- nothing playing this long on the Music page -> clock (0 = off)
local LYRICS_RESYNC_SECS = 10      -- lyrics page: how often to re-read the song position from the PC
local LYRICS_OFFSET_SECS = 1.0     -- show each lyric line this much early (e-ink refresh lag)
local LIKED_LAYOUT = "inline"      -- "inline": "Title  -  Artist"   |  "stacked": title above artist
local BLINK_SECS = 2               -- the Inbox badge (top left) blinks this often while there are new notifications (0 = no blinking)
local LIKED_FETCH = 10             -- how many songs to ask for per page (as many as fit are shown)
------------------------------------------------------------------------------

local BASE = (BASE_OVERRIDE ~= "") and BASE_OVERRIDE or nil
local current = nil   -- the server we're connected to: { url, id, name }

---------------------------------------------------------- discovery ----
-- Finds dashboard servers: scans the Kindle's own /24 network for an open
-- PORT, then asks each hit "who are you?" (/hello) so random web servers
-- are ignored. HOSTS lets you add addresses a scan can't reach (Tailscale).

-- The Kindle's own IP on the network it's connected to (nothing is sent).
local function localIP()
    for _, target in ipairs({ "8.8.8.8", "192.168.1.1", "10.0.0.1" }) do
        local ok, ip = pcall(function()
            local u = socket.udp()
            u:setpeername(target, 9)
            local a = u:getsockname()
            u:close()
            return a
        end)
        if ok and ip and ip ~= "0.0.0.0" then return ip end
    end
    return nil
end

-- Hosts prefix.1 .. prefix.254 with PORT open. Non-blocking connects, 100 at a
-- time, so a whole network takes about 3 seconds instead of minutes.
local function scanPort(prefix, port, skip, wait)
    local hits = {}
    local i = 1
    while i <= 254 do
        local batch, ip_of = {}, {}
        while i <= 254 and #batch < 100 do
            local ip = prefix .. "." .. i
            i = i + 1
            if ip ~= skip then
                local c = socket.tcp()
                c:settimeout(0)
                local ok, err = c:connect(ip, port)
                if ok then
                    table.insert(hits, ip)
                    c:close()
                elseif err == "timeout" then  -- non-blocking: connection in progress
                    table.insert(batch, c)
                    ip_of[c] = ip
                else
                    c:close()
                end
            end
        end
        local deadline = socket.gettime() + wait
        local waiting = batch
        while #waiting > 0 do
            local left = deadline - socket.gettime()
            if left <= 0 then break end
            local _, ready = socket.select(nil, waiting, left)
            if not ready or #ready == 0 then break end
            local isready, still = {}, {}
            for _, c in ipairs(ready) do isready[c] = true end
            for _, c in ipairs(waiting) do
                if isready[c] then
                    -- a second connect() reports how the first one ended
                    local ok, err = c:connect(ip_of[c], port)
                    if ok == 1 or err == "already connected" then table.insert(hits, ip_of[c]) end
                    c:close()
                else
                    table.insert(still, c)
                end
            end
            waiting = still
        end
        for _, c in ipairs(waiting) do c:close() end
    end
    return hits
end

-- Ask url/hello who it is. Returns { url, id, name } or nil.
local function probe(url, wait)
    local t = {}
    http.TIMEOUT = wait or 2
    local ok, code = http.request{ url = url .. "/hello", sink = ltn12.sink.table(t) }
    if not ok or code ~= 200 then return nil end
    local ok2, d = pcall(JSON.decode, table.concat(t))
    if ok2 and type(d) == "table" and d.app == "kindle-dash" then
        return { url = url, id = d.id or url, name = d.name or url }
    end
    return nil
end

local function discover()
    local found, seen_url, seen_id = {}, {}, {}
    local function add(url)
        if seen_url[url] then return end
        seen_url[url] = true
        local sv = probe(url, 2)
        if sv and not seen_id[sv.id] then  -- same PC reachable twice (LAN + Tailscale): keep the first
            seen_id[sv.id] = true
            table.insert(found, sv)
        end
    end
    if SCAN_NETWORK then
        local ip = localIP()
        local prefix = ip and ip:match("^(%d+%.%d+%.%d+)%.")
        if prefix then
            for _, host in ipairs(scanPort(prefix, PORT, ip, 1.0)) do
                add("http://" .. host .. ":" .. PORT)
            end
        end
    end
    for _, h in ipairs(HOSTS) do
        add("http://" .. (h:find(":", 1, true) and h or (h .. ":" .. PORT)))
    end
    table.sort(found, function(a, b) return (a.name or "") < (b.name or "") end)
    return found
end

local SETTINGS_FILE = DataStorage:getSettingsDir() .. "/pc_dashboard.lua"

local function lastServer()
    local ok, v = pcall(function()
        return LuaSettings:open(SETTINGS_FILE):readSetting("last_server")
    end)
    if ok and type(v) == "table" and v.url then return v end
    return nil
end

local function setServer(sv)
    BASE, current = sv.url, sv
    pcall(function()
        local st = LuaSettings:open(SETTINGS_FILE)
        st:saveSetting("last_server", { url = sv.url, id = sv.id, name = sv.name })
        st:flush()
    end)
end
-------------------------------------------------------------------------

local function request(path, method, timeout)
    if not BASE then return nil end
    local t = {}
    http.TIMEOUT = timeout or 5
    local ok, code = http.request{
        url = BASE .. path, method = method or "GET",
        headers = { ["Content-Length"] = "0" },
        sink = ltn12.sink.table(t),
    }
    if not ok or code ~= 200 then return nil end
    return table.concat(t)
end

local function getJSON(path, timeout)
    local body = request(path, "GET", timeout)
    if not body then return nil end
    local ok, data = pcall(JSON.decode, body)
    if ok and type(data) == "table" then return data end
    return nil
end

-- Shorten to n characters (UTF-8 aware) so absurdly long names can't eat the page.
local function truncate(s, n)
    local count = 0
    for pos in s:gmatch("()[%z\1-\127\194-\244][\128-\191]*") do
        count = count + 1
        if count > n then return s:sub(1, pos - 1) .. "..." end
    end
    return s
end

local function postJSON(path, timeout)
    local body = request(path, "POST", timeout)
    if not body then return nil end
    local ok, data = pcall(JSON.decode, body)
    if ok and type(data) == "table" then return data end
    return nil
end

local function text(str, size, bold, maxw)
    return TextWidget:new{
        text = str or "",
        face = Font:getFace(bold and "tfont" or "cfont", size),
        max_width = maxw,
    }
end

local function chunk(list, n)
    local rows, r = {}, {}
    for _, b in ipairs(list) do
        table.insert(r, b)
        if #r == n then table.insert(rows, r) r = {} end
    end
    if #r > 0 then table.insert(rows, r) end
    return rows
end

-- Kindle's own battery, e.g. "83%" or "83%+" while charging.
local function batteryText()
    local ok, txt = pcall(function()
        if not Device:hasBattery() then return nil end
        local pd = Device:getPowerDevice()
        local cap = pd:getCapacity()
        if not cap then return nil end
        return string.format("%d%%%s", cap, pd:isCharging() and "+" or "")
    end)
    if ok then return txt end
    return nil
end

-- Kindle frontlight state, or nil if there isn't one / the API differs.
local function frontlight()
    local ok, res = pcall(function()
        if not Device:hasFrontlight() then return nil end
        local pd = Device:getPowerDevice()
        return {
            pd = pd, min = pd.fl_min or 0, max = pd.fl_max or 24,
            cur = pd:frontlightIntensity(), on = pd:isFrontlightOn(),
        }
    end)
    if ok then return res end
    return nil
end

-- Changes only when something worth redrawing changes.
local function signature(data, extra)
    local bat = batteryText() or ""
    if not data then return "offline|" .. bat end
    local np = data.np or {}
    local wx = data.weather or {}
    return table.concat({
        np.state or "", np.title or "", np.artist or "", np.art_id or "",
        np.shuffle or "", np.loop or "",
        tostring(wx.temp), wx.desc or "", os.date("%H:%M"), bat,
        tostring(data.inbox), tostring(data.inbox_seq), extra or "",
    }, "|")
end

-- A horizontal progress bar (used on the Console page).
local BarWidget = Widget:extend{ width = 300, height = 24, pct = 0 }

function BarWidget:init()
    self.dimen = Geom:new{ w = self.width, h = self.height }
end

function BarWidget:getSize()
    return self.dimen
end

function BarWidget:paintTo(bb, x, y)
    self.dimen.x, self.dimen.y = x, y
    local b = Screen:scaleBySize(2)
    bb:paintRect(x, y, self.width, self.height, Blitbuffer.COLOR_BLACK)
    bb:paintRect(x + b, y + b, self.width - 2 * b, self.height - 2 * b, Blitbuffer.COLOR_WHITE)
    local fill = math.floor((self.width - 4 * b) * math.max(0, math.min(100, self.pct)) / 100)
    if fill > 0 then
        bb:paintRect(x + 2 * b, y + 2 * b, fill, self.height - 4 * b, Blitbuffer.COLOR_BLACK)
    end
end

-- The Inbox badge in the top left corner. Inverted = the "on" half of the blink.
local InboxBadge = Widget:extend{ width = 150, height = 70, count = 0, on = false }

function InboxBadge:init()
    self.dimen = Geom:new{ w = self.width, h = self.height }
end

function InboxBadge:getSize()
    return self.dimen
end

function InboxBadge:paintTo(bb, x, y)
    self.dimen.x, self.dimen.y = x, y
    local black, white = Blitbuffer.COLOR_BLACK, Blitbuffer.COLOR_WHITE
    local b = Screen:scaleBySize(3)
    local bg, fg = white, black
    if self.on then bg, fg = black, white end
    bb:paintRect(x, y, self.width, self.height, black)
    bb:paintRect(x + b, y + b, self.width - 2 * b, self.height - 2 * b, bg)
    local label = (self.count > 0) and ("Inbox  " .. self.count) or "Inbox"
    local t = TextWidget:new{
        text = label, face = Font:getFace(self.count > 0 and "tfont" or "cfont", 26),
        fgcolor = fg, max_width = self.width - 2 * b - Screen:scaleBySize(8),
    }
    local sz = t:getSize()
    t:paintTo(bb, x + math.floor((self.width - sz.w) / 2), y + math.floor((self.height - sz.h) / 2))
    t:free()
end

---------------------------------------------------------------------------
local DashScreen = InputContainer:extend{
    modal = true,
    covers_fullscreen = true,
    page = "music",       -- music | lyrics | queue | weather | deck | controls | liked | poster | clock | devices
    servers = {},
    deck_page = 1,
    lyrics_mode = "synced",
    plain_page = 1,
    liked_offset = 0,
    redraws = 0,
}

function DashScreen:init()
    if self.start_page then self.page = self.start_page end
    self.saved_rotation = Screen:getRotationMode()
    if LANDSCAPE and Screen:getWidth() < Screen:getHeight() then
        pcall(function()
            UIManager:broadcastEvent(Event:new("SetRotationMode", LANDSCAPE_MODE))
        end)
    end
    self.dimen = Geom:new{ w = Screen:getWidth(), h = Screen:getHeight() }
    self.tiles = {}
    self.ges_events = {
        TapDeck = { GestureRange:new{ ges = "tap", range = self.dimen } },
    }
    if Device:hasKeys() then
        self.key_events = { Close = { { Device.input.group.Back } } }
    end
    self.last_ok = os.time()
    self.tick_fn = function()
        if self.page == "clock" then
            self:clockTick()
        elseif self.page == "lyrics" then
            self:lyricsTick()
        else
            self:poll()
        end
        if not self.sleeping and not self.done then
            UIManager:unschedule(self.tick_fn)  -- never leave two timers running
            UIManager:scheduleIn(self:nextDelay(), self.tick_fn)
        end
    end
    self.poll_fn = function() self:poll() end
    self.blink_fn = function()
        if self.done or self.sleeping then return end
        local b = self.badge
        local want = false
        if b and (self.inbox_unread or 0) > 0 and self.page ~= "clock" and self.page ~= "poster" then
            want = not self.blink_on
        end
        if want ~= (self.blink_on or false) then
            self.blink_on = want
            if b then
                b.on = want
                UIManager:setDirty(self, "fast", b.dimen)
            end
        end
        UIManager:scheduleIn(BLINK_SECS, self.blink_fn)
    end
    self:blockStandby()
    self:poll(true)
    self:startTick()
    self:startBlink()
end

function DashScreen:startBlink()
    if BLINK_SECS <= 0 or self.done then return end
    UIManager:unschedule(self.blink_fn)
    UIManager:scheduleIn(BLINK_SECS, self.blink_fn)
end

function DashScreen:startTick()
    if self.sleeping or self.done then return end
    UIManager:unschedule(self.tick_fn)
    UIManager:scheduleIn(self:nextDelay(), self.tick_fn)
end

function DashScreen:nextDelay()
    if self.page == "clock" then
        local to_minute = 61 - (tonumber(os.date("%S")) or 0)  -- just after the next minute starts
        if self.auto_clock then return math.min(15, to_minute) end  -- also watch for music resuming
        return to_minute
    end
    if self.page == "lyrics" and self.pos_state == "Playing" and self:lyricsView() == "synced" then
        local lines = self.lyrics.synced
        local pos = self:lyricsPos()
        local nxt = lines[(self:lyricsIndex() or 0) + 1]
        local d = LYRICS_RESYNC_SECS
        if nxt and pos then d = math.min(d, math.max(1.5, nxt[1] - pos)) end
        return d
    end
    return self.data and POLL_SECS or OFFLINE_POLL_SECS
end

function DashScreen:blockStandby()
    if not self.standby_blocked then
        UIManager:preventStandby()
        self.standby_blocked = true
    end
    self:startKeepAwake()
end

function DashScreen:releaseStandby()
    if self.standby_blocked then
        UIManager:allowStandby()
        self.standby_blocked = false
    end
    self:stopKeepAwake()
end

-- Keep the Kindle from sleeping while the dashboard is open: KOReader's
-- auto-suspend timer is reset every KEEP_AWAKE_SECS (a fake "input" event),
-- and the Kindle's own screensaver is told to stay off.
function DashScreen:startKeepAwake()
    if not KEEP_AWAKE or self.awake_fn then return end
    pcall(os.execute, "lipc-set-prop com.lab126.powerd preventScreenSaver 1 >/dev/null 2>&1")
    self.awake_fn = function()
        if self.done or self.sleeping then
            self.awake_fn = nil
            return
        end
        pcall(function() UIManager:broadcastEvent(Event:new("InputEvent")) end)
        UIManager:scheduleIn(KEEP_AWAKE_SECS, self.awake_fn)
    end
    self.awake_fn()
end

function DashScreen:stopKeepAwake()
    if self.awake_fn then
        UIManager:unschedule(self.awake_fn)
        self.awake_fn = nil
    end
    if KEEP_AWAKE then
        pcall(os.execute, "lipc-set-prop com.lab126.powerd preventScreenSaver 0 >/dev/null 2>&1")
    end
end

-- PC unreachable for too long: leave a message, then suspend the device.
function DashScreen:goToSleep()
    if OFFLINE_ACTION == "close" then
        self.done = true
        UIManager:close(self)
        return
    end
    self.sleeping = true
    if self.sleep_reason ~= "idle" then self.sleep_reason = "offline" end
    self.page = "music"
    self.data = nil
    UIManager:unschedule(self.tick_fn)
    UIManager:unschedule(self.poll_fn)
    self:render(true)  -- leave an explanation on screen
    self:releaseStandby()
    UIManager:scheduleIn(2, function()  -- let the e-ink finish drawing first
        if not self.sleeping then return end
        if UIManager.suspend then
            pcall(UIManager.suspend, UIManager)
        else
            UIManager:broadcastEvent(Event:new("RequestSuspend"))
        end
    end)
end

-- Back from sleep (power button -> Resume event, or a tap as a fallback).
function DashScreen:wake()
    if not self.sleeping then return end
    self.sleeping = false
    self.sleep_reason = nil
    self.quiet_since = nil
    self.last_ok = os.time()  -- fresh grace period
    self:blockStandby()
    self:startBlink()
    NetworkMgr:runWhenOnline(function()
        if self.done then return end
        self:poll(true)
        self:startTick()
    end)
end

function DashScreen:onResume()
    self:wake()
    return false  -- let other widgets see Resume too
end

function DashScreen:onClose()
    UIManager:close(self)
    return true
end

function DashScreen:onCloseWidget()
    UIManager:unschedule(self.tick_fn)
    UIManager:unschedule(self.poll_fn)
    UIManager:unschedule(self.blink_fn)
    self.done = true
    self:releaseStandby()
    if self.saved_rotation ~= nil and Screen:getRotationMode() ~= self.saved_rotation then
        pcall(function()
            UIManager:broadcastEvent(Event:new("SetRotationMode", self.saved_rotation))
        end)
    end
    UIManager:setDirty(nil, "full")
end

function DashScreen:act(cmd)
    self.idle_since = nil
    request("/ctl/" .. cmd, "POST")
    UIManager:scheduleIn(1, self.poll_fn)  -- give the player a moment to update
end

function DashScreen:setPage(p, auto)
    local was_clock = (self.page == "clock")
    local was_full = was_clock or self.page == "poster"  -- full-screen modes; a tap leaves them
    if (p == "clock" or p == "poster") and not was_full then self.prev_page = self.page end
    self.page = p
    self.auto_clock = (p == "clock") and auto or false
    self.idle_since = nil
    if p == "deck" then
        self.deck = getJSON("/deck")   -- re-read so server.py edits show up
        self.deck_page = 1
    elseif p == "controls" then
        self.audio = getJSON("/audio")
    elseif p == "liked" then
        self.liked_offset = 0
        self.liked_stack = {}
        self.liked_msg = nil
        self:loadLiked()
    elseif p == "queue" then
        self:loadQueue()
    elseif p == "console" then
        self.sys = getJSON("/sys")
    elseif p == "inbox" then
        self:loadInbox()
    elseif p == "devices" then
        self.dev_msg = "Scanning the network..."
        UIManager:scheduleIn(0.3, function()  -- let the message show first; the scan blocks for a few seconds
            if self.page == "devices" and not self.done then self:scan() end
        end)
    elseif p == "lyrics" then
        if not self.lyrics then self.lyrics_track = nil end  -- retry a failed lookup
    end
    if p == "clock" then
        self.clock_inbox_seq = self.inbox_seq or 0
        self.clock_wx_t = os.time()
        UIManager:unschedule(self.tick_fn)
        self:render(true)
    elseif was_clock or p == "lyrics" or p == "poster" then
        if was_clock then self.last_ok = os.time() end  -- PC wasn't polled; not "offline"
        self:poll(true)
    else
        self:render(false)
    end
    self:startTick()
end

-- Taps that no button handled: wake from sleep, leave clock mode, or hit a tile.
function DashScreen:onTapDeck(arg, ges)
    if self.sleeping then
        self:wake()
        return true
    end
    if self.page == "clock" or self.page == "poster" then
        self:setPage(self.prev_page or "music")
        return true
    end
    local b = self.badge
    if b and b.dimen and b.dimen:contains(ges.pos) then  -- the Inbox badge, top left
        self:setPage(self.page == "inbox" and "music" or "inbox")
        return true
    end
    if self.page ~= "deck" and self.page ~= "controls" and self.page ~= "liked"
        and self.page ~= "devices" and self.page ~= "inbox" then return false end
    for _, t in ipairs(self.tiles or {}) do
        local d = t.frame.dimen
        if d and d:contains(ges.pos) then
            self:pressTile(t)
            return true
        end
    end
    return false
end

function DashScreen:pressTile(t)
    if t.kind == "notif" then
        local it = self.inbox and self.inbox.items and self.inbox.items[t.idx]
        if it then
            request("/inbox/dismiss/" .. tostring(it.id), "POST")
            self:loadInbox()
            self:render(false)
        end
        return
    end
    if t.kind == "server" then
        self:switchServer(self.servers and self.servers[t.idx])
        return
    end
    if t.kind == "liked" then
        self.pressed = "liked:" .. t.idx
        self.liked_msg = "Starting..."
        self:render(false)  -- inverted tile = feedback
        UIManager:scheduleIn(0.3, function()
            local d = postJSON(string.format("/liked/play/%d/%d", self.liked_offset or 0, t.idx - 1), 20)
            self.pressed = nil
            self:likedResult(d)
        end)
        return
    end
    if t.kind == "audio" then
        request(string.format("/audio/%d", t.idx - 1), "POST")
        self.audio = getJSON("/audio")   -- selected output shows inverted
        self:render(false)
        return
    end
    self.pressed = t.page .. ":" .. t.idx
    self:render(false)  -- inverted tile = feedback
    UIManager:scheduleIn(0.3, function()
        request(string.format("/deck/%d/%d", t.page - 1, t.idx - 1), "POST")
        self.pressed = nil
        self:render(false)
    end)
end

function DashScreen:adjustLight(dir)
    pcall(function()
        local fl = frontlight()
        if not fl then return end
        local step = math.max(1, math.floor((fl.max - fl.min) / 8))
        local target = math.max(fl.min, math.min(fl.max, (fl.cur or fl.min) + dir * step))
        if dir > 0 and not fl.on then fl.pd:turnOnFrontlight() end
        fl.pd:setIntensity(target)
        UIManager:broadcastEvent(Event:new("FrontlightStateChanged"))
    end)
    self:render(false)
end

function DashScreen:toggleLight()
    pcall(function()
        local fl = frontlight()
        if fl then
            fl.pd:toggleFrontlight()
            UIManager:broadcastEvent(Event:new("FrontlightStateChanged"))
        end
    end)
    self:render(false)
end

---------------------------------------------------- idle clock / clock ----
-- Called on every poll. Returns true if it switched to the clock.
-- Nothing has been playing for IDLE_SLEEP_SECS: go to sleep.
function DashScreen:quietCheck(playing)
    if playing then
        self.quiet_since = nil
        return false
    end
    self.quiet_since = self.quiet_since or os.time()
    if IDLE_SLEEP_SECS > 0 and os.time() - self.quiet_since >= IDLE_SLEEP_SECS then
        self.sleep_reason = "idle"
        self:goToSleep()
        return true
    end
    return false
end

function DashScreen:idleTrack(np)
    if self:quietCheck(np.state == "Playing") then return true end
    if np.state == "Playing" then
        self.idle_since = nil
        return false
    end
    self.idle_since = self.idle_since or os.time()
    local idle_page = (self.page == "music" or self.page == "liked" or self.page == "queue")
    if IDLE_CLOCK_SECS > 0 and idle_page
        and os.time() - self.idle_since >= IDLE_CLOCK_SECS then
        self:setPage("clock", true)
        return true
    end
    return false
end

function DashScreen:clockTick()
    local data
    local checked = false
    if self.auto_clock then  -- idle clock: also watches for music starting again
        data = getJSON("/status")
        checked = true
    elseif os.time() - (self.clock_wx_t or 0) >= 50 then  -- manual clock: check in every minute
        self.clock_wx_t = os.time()
        data = getJSON("/status")
        checked = true
    end
    if checked then
        if data then
            self.last_ok = os.time()
        elseif OFFLINE_SLEEP_SECS > 0 and os.time() - (self.last_ok or os.time()) >= OFFLINE_SLEEP_SECS then
            self:goToSleep()  -- PC unreachable while showing the clock
            return
        end
        if data and not self.auto_clock then
            local playing = data.np and data.np.state == "Playing"
            if self:quietCheck(playing and true or false) then return end  -- nothing playing for a long while
        end
    end
    if self.auto_clock and data then
        self.inbox_unread, self.inbox_seq = data.inbox or 0, data.inbox_seq or 0
        if self.inbox_unread > 0 and self.inbox_seq > (self.clock_inbox_seq or 0) then
            self:setPage(self.prev_page or "music")  -- something new arrived: show the badge
            return
        end
    end
    if self.auto_clock and data and data.np and data.np.state == "Playing" then
        self.quiet_since = nil
        self:setPage(self.prev_page or "music")
        return
    end
    if self.auto_clock and data and self:quietCheck(false) then return end
    if data and data.weather then
        local old = self.data and self.data.weather
        if not old or old.temp ~= data.weather.temp or old.desc ~= data.weather.desc then
            self.clock_min = nil  -- weather changed: redraw at this tick
        end
        self.data = data
    end
    local m = os.date("%H:%M")
    if m ~= self.clock_min then
        self.clock_min = m
        self:render(false)
    end
end

----------------------------------------------------------------- lyrics ----
-- Estimated current song position (seconds), nudged ahead for e-ink lag.
function DashScreen:lyricsPos()
    if not self.pos then return nil end
    local pos = self.pos
    if self.pos_state == "Playing" and self.pos_time then
        pos = pos + (os.time() - self.pos_time)
    end
    return pos + LYRICS_OFFSET_SECS
end

-- "synced" | "plain" | "none" (what we can actually show right now).
function DashScreen:lyricsView()
    local ly = self.lyrics
    if not ly or not ly.found then return "none" end
    local has_sync = ly.synced and #ly.synced > 0
    local has_plain = ly.plain and ly.plain ~= ""
    if self.lyrics_mode == "synced" and has_sync then return "synced" end
    if has_plain then return "plain" end
    if has_sync then return "synced" end
    return "none"
end

-- Index of the line being sung (0 = before the first line).
function DashScreen:lyricsIndex()
    local pos = self:lyricsPos()
    if not pos or self:lyricsView() ~= "synced" then return nil end
    local idx = 0
    for i, l in ipairs(self.lyrics.synced) do
        if l[1] <= pos then idx = i else break end
    end
    return idx
end

function DashScreen:fetchLyrics(track_id)
    self.lyrics_track = track_id
    self.lyrics = nil
    self.lyric_idx = nil
    self.plain_page = 1
    local data = getJSON("/lyrics", 15)  -- the PC may need a few seconds to look it up
    if data and data.key == track_id then
        self.lyrics = data
    elseif data then
        self.lyrics_track = nil  -- track changed mid-lookup; try again next poll
    end
end

function DashScreen:lyricsTick()
    if os.time() - (self.last_poll or 0) >= LYRICS_RESYNC_SECS or self.pos_state ~= "Playing" then
        self:poll()
    end
    if self.page == "lyrics" and self.lyrics_mode == "synced" then
        local idx = self:lyricsIndex()
        if idx ~= nil and idx ~= self.lyric_idx then self:render(false) end
    end
end

----------------------------------------------------------------- polling ----
function DashScreen:poll(force)
    if self.sleeping or self.done or self.page == "clock" then return end
    local data = getJSON("/status")
    if data then
        self.last_ok = os.time()
        self.last_poll = os.time()
        self.fail_count = 0
        local np = data.np or {}
        self.pos, self.pos_time, self.pos_state = np.position, os.time(), np.state
        self.inbox_unread, self.inbox_seq = data.inbox or 0, data.inbox_seq or 0
        if self.page == "console" then self.sys = getJSON("/sys") end
        if self.page == "inbox" and self.inbox_seq ~= self.inbox_loaded_seq then self:loadInbox() end
        if self:idleTrack(np) then return end
        if self.page == "lyrics" and np.track_id and np.track_id ~= self.lyrics_track then
            self:fetchLyrics(np.track_id)
            force = true
        end
    elseif self:maybeRediscover() then
        return  -- same PC found at a new address; polling again in a second
    elseif OFFLINE_SLEEP_SECS > 0 and os.time() - self.last_ok >= OFFLINE_SLEEP_SECS then
        self:goToSleep()
        return
    end
    local sig = signature(data, self:extraSig())
    if not force and sig == self.sig then return end
    self.sig = sig
    self.data = data
    if self.page == "queue" then self:loadQueue() end
    local before, pbefore = self.art_id, self.poster_art_id
    self:fetchArt()
    self:render(force or self.art_id ~= before or self.poster_art_id ~= pbefore)
end

-- Page-specific values that should trigger a redraw when they change.
function DashScreen:extraSig()
    if self.page == "console" and self.sys then
        local s = self.sys
        local parts = { math.floor((s.cpu or 0) / 5), s.mem and s.mem.pct, s.uptime and math.floor(s.uptime / 60) }
        for _, d in ipairs(s.disks or {}) do table.insert(parts, d.pct) end
        for k, v in pairs(s.temps or {}) do table.insert(parts, k .. math.floor(v / 2)) end
        if s.net then
            table.insert(parts, math.floor((s.net.down or 0) / 20000))
            table.insert(parts, math.floor((s.net.up or 0) / 20000))
        end
        for _, v in ipairs(s.services or {}) do table.insert(parts, v.ok and "u" or "d") end
        return table.concat(parts, ",")
    end
    return ""
end

function DashScreen:loadInbox()
    local d = getJSON("/inbox")
    self.inbox = d
    self.inbox_loaded_seq = self.inbox_seq
    if d then
        postJSON("/inbox/read")
        self.inbox_unread = 0
    end
end

function DashScreen:render(full)
    self:build()
    self.redraws = self.redraws + 1
    if self.redraws % 20 == 0 then full = true end  -- periodic flash vs. ghosting
    UIManager:setDirty(self, full and "full" or "ui")
end

function DashScreen:fetchArt()
    local np = self.data and self.data.np or {}
    local id = np.art_id
    if self.page == "poster" then self:fetchPoster(id) end
    if not id or id == "" then self.art_id = nil return end
    if id == self.art_id then return end
    local body = request("/art.png")
    if body then
        local f = io.open(ART_PATH, "wb")
        if f then f:write(body) f:close() self.art_id = id end
    end
end

-- Scan for servers (blocks a few seconds) and show them on the Devices page.
function DashScreen:scan()
    self.servers = discover()
    self.dev_msg = nil
    self:render(false)
end

function DashScreen:switchServer(sv)
    if not sv then return end
    setServer(sv)
    self.data, self.sig = nil, nil
    self.art_id, self.poster_art_id = nil, nil
    self.lyrics, self.lyrics_track = nil, nil
    self.deck, self.audio, self.liked, self.queue = nil, nil, nil, nil
    self.last_ok, self.fail_count = os.time(), 0
    self.page = "music"
    self:poll(true)
    self:startTick()
end

-- The PC stopped answering. Its address may have changed (DHCP, other Wi-Fi), so
-- after a few failures look for the SAME server (matching id) and follow it.
-- It never jumps to a different PC by itself; that's what the Devices page is for.
function DashScreen:maybeRediscover()
    if BASE_OVERRIDE ~= "" or not current or not current.id then return false end
    self.fail_count = (self.fail_count or 0) + 1
    if self.fail_count < 3 or os.time() - (self.last_scan or 0) < 60 then return false end
    self.last_scan = os.time()
    local list = discover()
    self.servers = list
    for _, sv in ipairs(list) do
        if sv.id == current.id and sv.url ~= current.url then
            setServer(sv)
            self.fail_count = 0
            UIManager:scheduleIn(1, self.poll_fn)
            return true
        end
    end
    return false
end

function DashScreen:posterSize()
    local w, h = Screen:getWidth(), Screen:getHeight()
    local pad = Screen:scaleBySize(20)
    return (w > h) and (h - 2 * pad) or (w - 2 * pad)
end

-- Poster mode wants the cover much bigger than the normal Music page does.
function DashScreen:fetchPoster(id)
    if not id or id == "" then self.poster_art_id = nil return end
    if id == self.poster_art_id then return end
    local body = request("/art.png?size=" .. self:posterSize(), "GET", 10)
    if body then
        local f = io.open(POSTER_PATH, "wb")
        if f then f:write(body) f:close() self.poster_art_id = id end
    end
end

function DashScreen:loadQueue()
    self.queue = getJSON("/queue", 10)
end

---------------------------------------------------------------- layout ----
function DashScreen:build()
    local w, h = Screen:getWidth(), Screen:getHeight()
    local landscape = w > h
    local pad = Screen:scaleBySize(20)
    local inner = w - 2 * pad
    self.tiles = {}
    self.badge = nil

    if self.page == "clock" then
        self.clock_min = os.date("%H:%M")
        self:buildClock(w, h, pad)
        return
    end
    if self.page == "poster" then
        self:buildPoster(w, h, pad)
        return
    end

    local wx = self.data and self.data.weather
    local np = self.data and self.data.np or {}
    local group = VerticalGroup:new{ align = "left" }

    -- top row: clock, plus a small info block (weather on music page, battery)
    local top = HorizontalGroup:new{ align = "center" }
    self.badge = InboxBadge:new{
        width = Screen:scaleBySize(150), height = Screen:scaleBySize(62),
        count = self.inbox_unread or 0,
        on = ((self.inbox_unread or 0) > 0) and (self.blink_on or false) or false,
    }
    table.insert(top, self.badge)
    table.insert(top, HorizontalSpan:new{ width = pad })
    local clock = text(os.date("%H:%M"), 72, true, inner)
    table.insert(top, clock)
    local info = VerticalGroup:new{ align = "left" }
    local has_info = false
    local infow = inner - self.badge:getSize().w - pad - clock:getSize().w - 2 * pad
    if self.page == "music" and wx then
        table.insert(info, text(string.format("%d°  %s", wx.temp, wx.desc), 36, false, infow))
        has_info = true
    end
    local bat = batteryText()
    if bat then
        table.insert(info, text("Battery " .. bat, 28, false, infow))
        has_info = true
    end
    if has_info then
        table.insert(top, HorizontalSpan:new{ width = 2 * pad })
        table.insert(top, info)
    end

    -- bottom bar
    local function btn(label, fn) return { text = label, callback = fn } end
    local navlist = {}
    for _, p in ipairs({ { "music", "Music" }, { "lyrics", "Lyrics" }, { "queue", "Up next" },
                         { "weather", "Weather" }, { "deck", "Deck" }, { "controls", "Controls" },
                         { "liked", "Liked" }, { "poster", "Poster" }, { "clock", "Clock" },
                         { "console", "Console" }, { "devices", "Devices" } }) do
        if p[1] ~= self.page then
            table.insert(navlist, btn(p[2], function() self:setPage(p[1]) end))
        end
    end
    table.insert(navlist, btn("Close", function() UIManager:close(self) end))

    local rows = {}
    if self.page == "deck" then
        local dp = self.deck and self.deck.pages or {}
        if #dp > 1 then
            local r = {}
            for i, p in ipairs(dp) do
                local label = (i == self.deck_page) and ("[" .. p.name .. "]") or p.name
                table.insert(r, btn(label, function()
                    self.deck_page = i
                    self:render(false)
                end))
            end
            table.insert(rows, r)
        end
    elseif self.page == "lyrics" then
        local view = self:lyricsView()
        local r = {
            btn(self.lyrics_mode == "synced" and "[Synced]" or "Synced", function()
                self.lyrics_mode = "synced"
                self:render(false)
                self:startTick()
            end),
            btn(self.lyrics_mode == "plain" and "[Full text]" or "Full text", function()
                self.lyrics_mode = "plain"
                self.plain_page = 1
                self:render(false)
                self:startTick()
            end),
        }
        if view == "plain" then
            table.insert(r, btn("Page -", function()
                self.plain_page = (self.plain_page or 1) - 1
                self:render(false)
            end))
            table.insert(r, btn("Page +", function()
                self.plain_page = (self.plain_page or 1) + 1
                self:render(false)
            end))
        end
        table.insert(r, btn("Retry", function()
            self.lyrics, self.lyrics_track = nil, nil
            self:poll(true)
        end))
        table.insert(rows, r)
    elseif self.page == "liked" then
        table.insert(rows, {
            btn("< Prev", function() self:likedMove(-1) end),
            btn("Next >", function() self:likedMove(1) end),
            btn("Shuffle all", function() self:likedShuffle() end),
            btn("Refresh", function()
                self.liked_msg = nil
                self:loadLiked()
                self:render(false)
            end),
        })
    elseif self.page == "devices" then
        table.insert(rows, { btn("Rescan", function() self:setPage("devices") end) })
    elseif self.page == "inbox" then
        table.insert(rows, {
            btn("Clear all", function()
                request("/inbox/clear", "POST")
                self:loadInbox()
                self:render(false)
            end),
            btn("Refresh", function()
                self:loadInbox()
                self:render(false)
            end),
            btn("Back", function() self:setPage("music") end),
        })
    elseif self.page == "queue" then
        table.insert(rows, {
            btn("Play/Pause", function() self:act("play-pause") end),
            btn(">>", function() self:act("next") end),
            btn("Refresh", function()
                self:loadQueue()
                self:render(false)
            end),
        })
    elseif self.page == "music" then
        local prev = btn("<<", function() self:act("previous") end)
        local pp = btn("Play/Pause", function() self:act("play-pause") end)
        local nxt = btn(">>", function() self:act("next") end)
        local vdn = btn("Vol -", function() self:act("vol-down") end)
        local vup = btn("Vol +", function() self:act("vol-up") end)
        local shuf_label = "Shuffle"
        if np.shuffle == "On" then shuf_label = "Shuffle: On"
        elseif np.shuffle == "Off" then shuf_label = "Shuffle: Off" end
        local loop_names = { None = "Repeat: Off", Playlist = "Repeat: All", Track = "Repeat: One" }
        local shuf = btn(shuf_label, function() self:act("shuffle") end)
        local rep = btn(loop_names[np.loop or ""] or "Repeat", function() self:act("repeat") end)
        if landscape then
            table.insert(rows, { prev, pp, nxt, vdn, vup, shuf, rep })
        else
            table.insert(rows, { prev, pp, nxt })
            table.insert(rows, { vdn, vup, shuf, rep })
        end
    end
    for _, r in ipairs(chunk(navlist, landscape and 5 or 4)) do table.insert(rows, r) end
    local bottom = ButtonTable:new{ width = inner, show_parent = self, buttons = rows }

    -- body
    table.insert(group, top)
    table.insert(group, VerticalSpan:new{ width = pad })
    local avail = h - 2 * pad - top:getSize().h - bottom:getSize().h - 2 * pad
    if self.page == "deck" then
        self:buildDeck(group, w, pad, avail)
    elseif self.page == "controls" then
        self:buildControls(group, w, pad, avail)
    elseif self.page == "liked" then
        self:buildLiked(group, w, pad, avail)
    elseif self.page == "queue" then
        self:buildQueue(group, w, pad, avail)
    elseif self.page == "devices" then
        self:buildDevices(group, w, pad, avail)
    elseif self.page == "console" then
        self:buildConsole(group, w, pad, avail, landscape)
    elseif self.page == "inbox" then
        self:buildInbox(group, w, pad, avail)
    elseif not self.data then
        local msg = "Can't reach PC"
        if self.sleeping then
            if self.sleep_reason == "idle" then
                msg = "Nothing playing - sleeping.\nPress power or tap to wake."
            else
                msg = "PC unreachable - sleeping.\nPress power or tap to wake."
            end
        end
        table.insert(group, TextBoxWidget:new{
            text = msg, face = Font:getFace("cfont", 36), width = inner,
        })
    elseif self.page == "music" then
        self:buildMusic(group, w, h, pad, landscape)
    elseif self.page == "lyrics" then
        self:buildLyrics(group, w, pad, avail)
    else
        self:buildWeather(group, w, pad, landscape)
    end
    table.insert(group, VerticalSpan:new{ width = pad })
    table.insert(group, bottom)

    self[1] = FrameContainer:new{
        background = Blitbuffer.COLOR_WHITE,
        bordersize = 0, padding = pad,
        width = w, height = h,
        group,
    }
end

-- Clock-only mode: big time, date, nothing else. Tap anywhere to leave.
function DashScreen:buildClock(w, h, pad)
    local inner = w - 2 * pad
    local str = os.date("%H:%M")
    local size = 260
    local clock
    repeat
        clock = text(str, size, true)
        size = size - 20
    until clock:getSize().w <= inner or size < 60
    local group = VerticalGroup:new{ align = "center" }
    table.insert(group, clock)
    table.insert(group, VerticalSpan:new{ width = pad })
    table.insert(group, text(os.date("%A, %B %d"), 48, false, inner))
    local wx = self.data and self.data.weather
    if wx then
        table.insert(group, VerticalSpan:new{ width = pad })
        table.insert(group, text(string.format("%d°  %s", wx.temp, wx.desc), 56, true, inner))
        local today = wx.forecast and wx.forecast[1]
        if today then
            table.insert(group, text(string.format("High %d°    Low %d°", today.hi, today.lo), 40, false, inner))
        end
    end
    local bat = batteryText()
    if bat then
        table.insert(group, VerticalSpan:new{ width = pad })
        table.insert(group, text("Battery " .. bat, 28, false, inner))
    end
    self[1] = FrameContainer:new{
        background = Blitbuffer.COLOR_WHITE,
        bordersize = 0, padding = 0,
        width = w, height = h,
        CenterContainer:new{ dimen = Geom:new{ w = w, h = h }, group },
    }
end

-- Poster mode: the cover as big as it fits, title and artist, nothing else.
-- Redraws only when the track changes. Tap anywhere to leave.
function DashScreen:buildPoster(w, h, pad)
    local np = self.data and self.data.np or {}
    local landscape = w > h
    local size = self:posterSize()
    local group
    if not self.data then
        group = text("Can't reach PC", 40, false, w - 2 * pad)
    elseif not np.title then
        group = text("Nothing playing", 48, false, w - 2 * pad)
    else
        local art
        if self.poster_art_id then
            art = ImageWidget:new{
                file = POSTER_PATH, width = size, height = size,
                scale_factor = 0, file_do_cache = false,
            }
        end
        local textw = landscape and (w - size - 4 * pad) or (w - 2 * pad)
        local align = landscape and "left" or "center"
        local info = VerticalGroup:new{ align = landscape and "left" or "center" }
        table.insert(info, TextBoxWidget:new{
            text = truncate(np.title, 70), face = Font:getFace("tfont", 44),
            width = textw, alignment = align })
        table.insert(info, VerticalSpan:new{ width = math.floor(pad / 2) })
        table.insert(info, TextBoxWidget:new{
            text = truncate(np.artist or "", 60), face = Font:getFace("cfont", 32),
            width = textw, alignment = align })
        if landscape then
            group = HorizontalGroup:new{ align = "center" }
            if art then
                table.insert(group, art)
                table.insert(group, HorizontalSpan:new{ width = 2 * pad })
            end
            table.insert(group, info)
        else
            group = VerticalGroup:new{ align = "center" }
            if art then
                table.insert(group, art)
                table.insert(group, VerticalSpan:new{ width = pad })
            end
            table.insert(group, info)
        end
    end
    self[1] = FrameContainer:new{
        background = Blitbuffer.COLOR_WHITE,
        bordersize = 0, padding = 0,
        width = w, height = h,
        CenterContainer:new{ dimen = Geom:new{ w = w, h = h }, group },
    }
end

-- Devices: every dashboard server found on this network. The current one is
-- inverted; tap another to switch to it.
-- Console: how the PC is doing (CPU, memory, temperatures, drives, network, services).
local function fmtBytes(n)
    n = n or 0
    if n >= 1024 ^ 4 then return string.format("%.1f TB", n / 1024 ^ 4) end
    if n >= 1024 ^ 3 then return string.format("%.1f GB", n / 1024 ^ 3) end
    return string.format("%d MB", math.floor(n / 1024 ^ 2))
end

local function fmtRate(n)
    n = n or 0
    if n >= 1024 * 1024 then return string.format("%.1f MB/s", n / 1024 / 1024) end
    return string.format("%d KB/s", math.floor(n / 1024))
end

local function fmtUptime(s)
    s = s or 0
    local d, h = math.floor(s / 86400), math.floor((s % 86400) / 3600)
    if d > 0 then return d .. "d " .. h .. "h" end
    return h .. "h " .. math.floor((s % 3600) / 60) .. "m"
end

function DashScreen:buildConsole(group, w, pad, avail_h, landscape)
    local inner = w - 2 * pad
    local s = self.sys
    if not s then
        table.insert(group, text("Can't reach PC", 36, false, inner))
        return
    end
    local gap = math.floor(pad / 3)
    local colw = landscape and math.floor((inner - pad) / 2) or inner
    local fs = 26

    local function meter(col, label, pct, value)
        local lw = math.floor(colw * 0.2)
        local vw = math.floor(colw * 0.3)
        local bw = colw - lw - vw - 2 * gap
        local row = HorizontalGroup:new{ align = "center" }
        table.insert(row, text(label, fs, true, lw))
        table.insert(row, HorizontalSpan:new{ width = math.max(1, lw - text(label, fs, true, lw):getSize().w + gap) })
        table.insert(row, BarWidget:new{ width = bw, height = Screen:scaleBySize(22), pct = pct })
        table.insert(row, HorizontalSpan:new{ width = gap })
        table.insert(row, text(value, fs - 2, false, vw))
        table.insert(col, row)
        table.insert(col, VerticalSpan:new{ width = gap })
    end
    local function line(col, str, bold)
        table.insert(col, TextBoxWidget:new{
            text = str, face = Font:getFace(bold and "tfont" or "cfont", fs), width = colw })
        table.insert(col, VerticalSpan:new{ width = gap })
    end

    local left = VerticalGroup:new{ align = "left" }
    line(left, "System", true)
    meter(left, "CPU", s.cpu or 0, (s.cpu or 0) .. "%")
    local m = s.mem or {}
    meter(left, "RAM", m.pct or 0, fmtBytes(m.used) .. " / " .. fmtBytes(m.total))
    for _, d in ipairs(s.disks or {}) do
        meter(left, d.path == "/" and "Disk" or d.path:match("[^/]+$") or d.path, d.pct or 0,
            fmtBytes(d.used) .. " / " .. fmtBytes(d.total))
    end

    local right = VerticalGroup:new{ align = "left" }
    line(right, "Status", true)
    local temps = {}
    for _, k in ipairs({ "CPU", "GPU", "SSD" }) do
        if s.temps and s.temps[k] then table.insert(temps, k .. " " .. s.temps[k] .. "°C") end
    end
    if #temps > 0 then line(right, "Temps   " .. table.concat(temps, "   ")) end
    if s.net then
        line(right, "Network   down " .. fmtRate(s.net.down) .. "   up " .. fmtRate(s.net.up))
    end
    line(right, "Uptime   " .. fmtUptime(s.uptime) .. "     Load " .. tostring(s.load or 0))
    if s.services and #s.services > 0 then
        line(right, "Services", true)
        for _, v in ipairs(s.services) do
            line(right, (v.ok and "[ OK ]   " or "[DOWN]   ") .. v.name)
        end
    end

    if landscape then
        table.insert(group, HorizontalGroup:new{ align = "top", left,
            HorizontalSpan:new{ width = pad }, right })
    else
        table.insert(group, left)
        table.insert(group, VerticalSpan:new{ width = gap })
        table.insert(group, right)
    end
end

-- Inbox: your PC's notifications. Tap one to dismiss it.
function DashScreen:buildInbox(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local gap = math.floor(pad / 3)
    local box = self.inbox
    if not box then
        table.insert(group, text("Can't reach PC", 36, false, inner))
        return
    end
    local head = text("Inbox", 30, true, inner)
    table.insert(group, head)
    table.insert(group, VerticalSpan:new{ width = gap })
    local used = head:getSize().h + gap
    local items = box.items or {}
    if #items == 0 then
        local msg = "No notifications. You're all caught up."
        if box.enabled == false then
            msg = "The inbox is turned off in server.py (INBOX_ENABLED)."
        elseif not box.ok then
            msg = "Waiting for the notification monitor on the PC.\nIf this stays, install dbus-monitor (package 'dbus') and restart server.py."
        end
        table.insert(group, TextBoxWidget:new{
            text = msg, face = Font:getFace("cfont", 30), width = inner })
        return
    end
    local th = Screen:scaleBySize(86)
    local n = math.max(1, math.floor((avail_h - used - gap - Screen:scaleBySize(30)) / (th + math.floor(pad / 2))))
    local entries = {}
    for i = 1, math.min(n, #items) do
        local it = items[i]
        local title = it.summary ~= "" and it.summary or it.app
        local body = (it.body or ""):gsub("%s+", " ")
        local sub = (it.app ~= "" and (it.app .. "  ") or "") .. it.time
        if body ~= "" then sub = sub .. "  -  " .. body end
        entries[i] = { label = truncate(title, 60), sublabel = truncate(sub, 110) }
    end
    table.insert(group, self:tileGrid(entries, 1, inner, pad, avail_h - used - gap, 0.2, "notif", nil,
        { th = th, font = 28 }))
    if #items > #entries then
        table.insert(group, text("+" .. (#items - #entries) .. " older (tap to dismiss one)", 22, false, inner))
    end
end

function DashScreen:buildDevices(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local gap = math.floor(pad / 3)
    local head = text("Dashboard servers", 30, true, inner)
    table.insert(group, head)
    local used = head:getSize().h
    if self.dev_msg then
        local m = text(self.dev_msg, 28, false, inner)
        table.insert(group, m)
        used = used + m:getSize().h
    end
    table.insert(group, VerticalSpan:new{ width = gap })
    local list = self.servers or {}
    if #list == 0 then
        if not self.dev_msg then
            table.insert(group, TextBoxWidget:new{
                text = "No servers found on this network.\nIs server.py running, and is port " .. PORT
                    .. " open to the Kindle? Tap Rescan to try again.",
                face = Font:getFace("cfont", 30), width = inner })
        end
        return
    end
    local entries = {}
    for i, sv in ipairs(list) do
        local addr = (sv.url or ""):gsub("^http://", "")
        entries[i] = { label = (sv.name or "?") .. "\n" .. addr,
                       inverted = (current ~= nil and sv.url == current.url) }
    end
    table.insert(group, self:tileGrid(entries, 1, inner, pad, avail_h - used - gap, 0.2, "server", nil))
end

-- Up next: what Spotify will play after the current song, as many as fit.
function DashScreen:buildQueue(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local q = self.queue
    if not q then
        table.insert(group, text("Can't reach PC", 36, false, inner))
        return
    end
    if q.error then  -- Spotify not set up / needs a fresh login: just say so
        table.insert(group, TextBoxWidget:new{
            text = q.error, face = Font:getFace("cfont", 34), width = inner })
        return
    end
    local gap = math.floor(pad / 3)
    local head = text("Up next", 30, true, inner)
    table.insert(group, head)
    table.insert(group, VerticalSpan:new{ width = gap })
    local used = head:getSize().h + gap
    local function label(it)
        local s = truncate(it.name or "", 70)
        if it.artist and it.artist ~= "" then s = s .. "  -  " .. truncate(it.artist, 50) end
        return s
    end
    if q.now then
        local now = TextBoxWidget:new{
            text = "Now: " .. label(q.now), face = Font:getFace("tfont", 26), width = inner }
        table.insert(group, now)
        table.insert(group, VerticalSpan:new{ width = pad })
        used = used + now:getSize().h + pad
    end
    local list = q.queue or {}
    if #list == 0 then
        table.insert(group, text("Queue is empty", 34, false, inner))
        return
    end
    local more_h = text("+99 more", 24):getSize().h + gap
    local shown = 0
    for i, it in ipairs(list) do
        local line = TextBoxWidget:new{
            text = string.format("%d.  %s", i, label(it)),
            face = Font:getFace("cfont", 26), width = inner }
        local lh = line:getSize().h
        local reserve = (i < #list) and more_h or 0  -- leave room for "+N more"
        if shown > 0 and used + lh + gap + reserve > avail_h then break end
        table.insert(group, line)
        table.insert(group, VerticalSpan:new{ width = gap })
        used = used + lh + gap
        shown = shown + 1
    end
    if shown < #list then
        table.insert(group, text(string.format("+%d more", #list - shown), 24, false, inner))
    end
end

-- Lyrics page: synced (current line big, neighbours smaller) or full text.
function DashScreen:buildLyrics(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local np = self.data.np or {}
    if not np.title then
        table.insert(group, text("Nothing playing", 40, false, inner))
        return
    end
    local head = text(np.title .. " - " .. (np.artist or ""), 30, true, inner)
    table.insert(group, head)
    local gap = math.floor(pad / 2)
    table.insert(group, VerticalSpan:new{ width = gap })
    local body_h = avail_h - head:getSize().h - gap

    local ly = self.lyrics
    local view = self:lyricsView()
    if not ly then
        table.insert(group, text("Couldn't load lyrics - tap Retry", 34, false, inner))
        return
    elseif ly.instrumental and view == "none" then
        table.insert(group, text("Instrumental", 40, false, inner))
        return
    elseif view == "none" then
        table.insert(group, text("No lyrics found for this track", 36, false, inner))
        return
    end

    if view == "synced" then
        local lines = ly.synced
        local idx = self:lyricsIndex() or 0
        self.lyric_idx = idx
        local function line(i, size, bold)
            local l = lines[i]
            local s = l and l[2] or ""
            if s == "" then s = "..." end
            return TextBoxWidget:new{
                text = s, face = Font:getFace(bold and "tfont" or "cfont", size),
                width = inner, alignment = "center",
            }
        end
        local box = VerticalGroup:new{ align = "center" }
        for i = idx - 2, idx - 1 do
            if i >= 1 then
                table.insert(box, line(i, 30, false))
                table.insert(box, VerticalSpan:new{ width = gap })
            end
        end
        if idx >= 1 then
            table.insert(box, line(idx, 50, true))
        else
            table.insert(box, TextBoxWidget:new{
                text = "...", face = Font:getFace("tfont", 50), width = inner, alignment = "center" })
        end
        for i = idx + 1, idx + 2 do
            if lines[i] then
                table.insert(box, VerticalSpan:new{ width = gap })
                table.insert(box, line(i, 30, false))
            end
        end
        table.insert(group, CenterContainer:new{ dimen = Geom:new{ w = inner, h = body_h }, box })
    else
        -- full text, paged
        local all = {}
        for l in ((ly.plain or "") .. "\n"):gmatch("(.-)\n") do
            table.insert(all, (l:gsub("\r", "")))
        end
        local line_h = text("Ag", 26):getSize().h
        local per = math.max(1, math.floor(body_h / line_h) - 1)  -- 1 row for the page counter
        local pages = math.max(1, math.ceil(#all / per))
        self.plain_page = math.max(1, math.min(self.plain_page or 1, pages))
        local start = (self.plain_page - 1) * per
        for r = 1, per do
            local s = all[start + r]
            if s ~= nil then
                table.insert(group, text(s == "" and " " or s, 26, false, inner))
            end
        end
        table.insert(group, text(string.format("Page %d/%d", self.plain_page, pages), 24, false, inner))
    end
end

-- Shared by Deck and Controls: a grid of big tappable tiles.
-- entries = { { label = "...", inverted = bool }, ... }
function DashScreen:tileGrid(entries, cols, inner, pad, avail_h, aspect, kind, page, opts)
    cols = math.max(1, cols or 2)
    local rows = math.max(1, math.ceil(#entries / cols))
    local gap = math.floor(pad / 2)
    local bs = 3
    local tw = math.floor((inner - (cols - 1) * gap) / cols)
    local th = math.floor((avail_h - (rows - 1) * gap) / rows)
    th = math.max(math.min(math.floor(tw * aspect), th), Screen:scaleBySize(60))
    if opts and opts.th then th = opts.th end
    local fsize = opts and opts.font or 34

    local grid = VerticalGroup:new{ align = "left" }
    for r = 1, rows do
        if r > 1 then table.insert(grid, VerticalSpan:new{ width = gap }) end
        local row = HorizontalGroup:new{ align = "top" }
        for c = 1, cols do
            if c > 1 then table.insert(row, HorizontalSpan:new{ width = gap }) end
            local i = (r - 1) * cols + c
            local e = entries[i]
            if e then
                local label = e.label
                if not label or label == "" then label = " " end
                local fg = e.inverted and Blitbuffer.COLOR_WHITE or Blitbuffer.COLOR_BLACK
                local content
                if e.sublabel then  -- list row: title over subtitle, each on one line
                    local mw = tw - 2 * bs - pad
                    content = VerticalGroup:new{ align = "left" }
                    table.insert(content, TextWidget:new{
                        text = label, face = Font:getFace("tfont", fsize), max_width = mw, fgcolor = fg })
                    table.insert(content, TextWidget:new{
                        text = e.sublabel, face = Font:getFace("cfont", fsize - 4), max_width = mw, fgcolor = fg })
                else
                    content = TextBoxWidget:new{
                        text = label,
                        face = Font:getFace("cfont", fsize),
                        width = tw - 2 * bs - pad,
                        alignment = "center",
                        fgcolor = fg,
                    }
                end
                local frame = FrameContainer:new{
                    bordersize = bs, margin = 0, padding = 0,
                    radius = Screen:scaleBySize(8),
                    background = e.inverted and Blitbuffer.COLOR_BLACK or Blitbuffer.COLOR_WHITE,
                    width = tw, height = th,
                    CenterContainer:new{
                        dimen = Geom:new{ w = tw - 2 * bs, h = th - 2 * bs },
                        content,
                    },
                }
                table.insert(row, frame)
                table.insert(self.tiles, { frame = frame, kind = kind, page = page, idx = i })
            else
                table.insert(row, HorizontalSpan:new{ width = tw })
            end
        end
        table.insert(grid, row)
    end
    return grid
end

------------------------------------------------------------ liked songs ----
function DashScreen:loadLiked()
    self.liked = getJSON(string.format("/liked?offset=%d&limit=%d",
        self.liked_offset or 0, LIKED_FETCH), 15)
end

-- Pages hold as many rows as fit, so "next" advances by however many were shown
-- and "prev" walks back through the offsets we came from.
function DashScreen:likedMove(dir)
    self.liked_stack = self.liked_stack or {}
    local total = self.liked and self.liked.total or 0
    local off = self.liked_offset or 0
    local new
    if dir > 0 then
        new = off + math.max(1, self.liked_shown or 1)
        if new >= total then return end
        table.insert(self.liked_stack, off)
    else
        new = table.remove(self.liked_stack)
        if not new then return end
    end
    self.liked_offset = new
    self.liked_msg = nil
    self:loadLiked()
    self:render(false)
end

function DashScreen:likedShuffle()
    self.liked_msg = "Starting shuffle..."
    self:render(false)
    UIManager:scheduleIn(0.3, function()
        self:likedResult(postJSON("/liked/shuffle", 25))
    end)
end

function DashScreen:likedResult(d)
    if d and d.ok then
        self.liked_msg = "Playing..."
        self:render(false)
        UIManager:scheduleIn(1.5, function()  -- give Spotify a moment, then show the player
            if not self.done and self.page == "liked" then self:setPage("music") end
        end)
    else
        self.liked_msg = (d and d.error) or "Can't reach PC"
        self:render(false)
    end
end

-- Tap a song to play it (and the next 49 liked songs after it).
-- Rows size themselves to their text (long names wrap, nothing is cut off).
function DashScreen:buildLiked(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local ld = self.liked
    if not ld then
        table.insert(group, text("Can't reach PC", 36, false, inner))
        return
    end
    if ld.error then  -- Spotify not set up / not reachable: just say so
        table.insert(group, TextBoxWidget:new{
            text = ld.error, face = Font:getFace("cfont", 34), width = inner })
        return
    end
    local tracks = ld.tracks or {}
    local off = ld.offset or 0
    local total = ld.total or 0
    local gap = math.floor(pad / 3)

    local used = text("Liked Songs", 30, true, inner):getSize().h + gap
    local msg
    if self.liked_msg then
        msg = text(self.liked_msg, 28, false, inner)
        used = used + msg:getSize().h
    end
    local body_h = avail_h - used

    local bs = 3
    local hp, vp = Screen:scaleBySize(10), Screen:scaleBySize(6)
    local mw = inner - 2 * bs - 2 * hp
    local min_h = Screen:scaleBySize(50)  -- keep rows comfortably tappable
    local rows, filled = {}, 0
    for i, t in ipairs(tracks) do
        local name = truncate(t.name or "", 80)
        local artist = truncate(t.artist or "", 60)
        local pressed = (self.pressed == ("liked:" .. i))
        local fg = pressed and Blitbuffer.COLOR_WHITE or Blitbuffer.COLOR_BLACK
        local content
        if LIKED_LAYOUT == "stacked" then
            content = VerticalGroup:new{ align = "left" }
            table.insert(content, TextBoxWidget:new{
                text = name, face = Font:getFace("tfont", 24), width = mw, fgcolor = fg })
            if artist ~= "" then
                table.insert(content, TextBoxWidget:new{
                    text = artist, face = Font:getFace("cfont", 20), width = mw, fgcolor = fg })
            end
        else
            content = TextBoxWidget:new{
                text = (artist ~= "") and (name .. "  -  " .. artist) or name,
                face = Font:getFace("cfont", 24), width = mw, fgcolor = fg }
        end
        local rh = math.max(min_h, content:getSize().h + 2 * vp + 2 * bs)
        if #rows > 0 and filled + rh + gap > body_h then break end  -- always show at least one
        local frame = FrameContainer:new{
            bordersize = bs, margin = 0, padding = 0,
            radius = Screen:scaleBySize(8),
            background = pressed and Blitbuffer.COLOR_BLACK or Blitbuffer.COLOR_WHITE,
            width = inner, height = rh,
            CenterContainer:new{ dimen = Geom:new{ w = inner - 2 * bs, h = rh - 2 * bs }, content },
        }
        table.insert(rows, frame)
        table.insert(self.tiles, { frame = frame, kind = "liked", idx = i })
        filled = filled + rh + gap
    end
    self.liked_shown = #rows

    table.insert(group, text(string.format("Liked Songs  %d-%d of %d",
        total > 0 and (off + 1) or 0, off + #rows, total), 30, true, inner))
    if msg then table.insert(group, msg) end
    table.insert(group, VerticalSpan:new{ width = gap })
    if #rows == 0 then
        table.insert(group, text("No liked songs here", 34, false, inner))
        return
    end
    for i, r in ipairs(rows) do
        if i > 1 then table.insert(group, VerticalSpan:new{ width = gap }) end
        table.insert(group, r)
    end
end

function DashScreen:buildDeck(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local deck = self.deck
    if not deck or not deck.pages or #deck.pages == 0 then
        table.insert(group, text("Can't load deck", 36, false, inner))
        return
    end
    local pi = (self.deck_page <= #deck.pages) and self.deck_page or 1
    local entries = {}
    for i, b in ipairs(deck.pages[pi].buttons or {}) do
        entries[i] = { label = b.label, inverted = (self.pressed == (pi .. ":" .. i)) }
    end
    table.insert(group, self:tileGrid(entries, deck.cols or 3, inner, pad, avail_h, 1.0, "deck", pi))
end

-- Controls page: audio output tiles (selected one inverted) + frontlight row.
function DashScreen:buildControls(group, w, pad, avail_h)
    local inner = w - 2 * pad
    local function btn(label, fn) return { text = label, callback = fn } end

    local lightbar
    local fl = frontlight()
    if fl then
        local label = "Off"
        if fl.on then
            local range = math.max(1, fl.max - fl.min)
            label = string.format("Light %d%%", math.floor(((fl.cur or fl.min) - fl.min) * 100 / range + 0.5))
        end
        lightbar = ButtonTable:new{
            width = inner, show_parent = self,
            buttons = { {
                btn("Light -", function() self:adjustLight(-1) end),
                { text = label, enabled = false },
                btn("Light +", function() self:adjustLight(1) end),
                btn(fl.on and "Light off" or "Light on", function() self:toggleLight() end),
            } },
        }
    end

    local header = text("Audio output", 32, true, inner)
    local reserved = header:getSize().h + math.floor(pad / 2)
    if lightbar then reserved = reserved + lightbar:getSize().h + pad end
    local tiles_h = avail_h - reserved

    table.insert(group, header)
    table.insert(group, VerticalSpan:new{ width = math.floor(pad / 2) })
    local a = self.audio
    if not a then
        table.insert(group, text("Can't load audio outputs", 32, false, inner))
    elseif not a.sinks or #a.sinks == 0 then
        table.insert(group, text("No outputs found (is pactl installed?)", 32, false, inner))
    else
        local entries = {}
        for i, s in ipairs(a.sinks) do
            entries[i] = { label = s.label, inverted = (s.name == a.current) }
        end
        table.insert(group, self:tileGrid(entries, a.cols or 2, inner, pad, tiles_h, 0.55, "audio", nil))
    end
    if lightbar then
        table.insert(group, VerticalSpan:new{ width = pad })
        table.insert(group, lightbar)
    else
        table.insert(group, VerticalSpan:new{ width = pad })
        table.insert(group, text("No frontlight", 28, false, inner))
    end
end

function DashScreen:buildMusic(group, w, h, pad, landscape)
    local np = self.data.np or {}
    local inner = w - 2 * pad
    if not np.title then
        table.insert(group, text("Nothing playing", 40, false, inner))
        return
    end
    local state = np.state == "Playing" and "Playing" or "Paused"
    local art_size = landscape and math.floor(h * 0.5) or math.min(inner, math.floor(h * 0.4))
    local art
    if self.art_id then
        art = ImageWidget:new{
            file = ART_PATH, width = art_size, height = art_size,
            scale_factor = 0, file_do_cache = false,
        }
    end

    if landscape then
        local row = HorizontalGroup:new{ align = "center" }
        local textw = inner
        if art then
            table.insert(row, art)
            table.insert(row, HorizontalSpan:new{ width = 2 * pad })
            textw = inner - art_size - 2 * pad
        end
        local info = VerticalGroup:new{ align = "left" }
        table.insert(info, text(np.title, 52, true, textw))
        table.insert(info, text(np.artist or "", 38, false, textw))
        table.insert(info, text(np.album or "", 30, false, textw))
        table.insert(info, VerticalSpan:new{ width = pad })
        table.insert(info, text(state, 30, false, textw))
        table.insert(row, info)
        table.insert(group, row)
    else
        if art then
            table.insert(group, art)
            table.insert(group, VerticalSpan:new{ width = pad })
        end
        table.insert(group, text(np.title, 44, true, inner))
        table.insert(group, text(np.artist or "", 34, false, inner))
        table.insert(group, text(np.album or "", 26, false, inner))
        table.insert(group, VerticalSpan:new{ width = pad })
        table.insert(group, text(state, 28, false, inner))
    end
end

function DashScreen:buildWeather(group, w, pad, landscape)
    local wx = self.data.weather
    local inner = w - 2 * pad
    if not wx then
        table.insert(group, text("No weather data", 36, false, inner))
        return
    end
    local colw = landscape and math.floor((inner - 2 * pad) / 2) or inner

    local cur = VerticalGroup:new{ align = "left" }
    table.insert(cur, text(string.format("%d°  %s", wx.temp, wx.desc), 60, true, colw))
    table.insert(cur, text(string.format("Feels like %d°", wx.feels_like), 32, false, colw))
    table.insert(cur, text(string.format("Humidity %d%%   Wind %d %s",
        wx.humidity, wx.wind, wx.wind_unit), 32, false, colw))
    table.insert(cur, text(string.format("Sunrise %s   Sunset %s", wx.sunrise, wx.sunset), 32, false, colw))

    local fc = VerticalGroup:new{ align = "left" }
    for _, d in ipairs(wx.forecast or {}) do
        table.insert(fc, text(string.format("%s  %d° / %d°  %d%% rain  %s",
            d.day, d.hi, d.lo, d.rain or 0, d.desc), 28, false, colw))
    end

    if landscape then
        local row = HorizontalGroup:new{ align = "top" }
        table.insert(row, cur)
        table.insert(row, HorizontalSpan:new{ width = 2 * pad })
        table.insert(row, fc)
        table.insert(group, row)
    else
        table.insert(group, cur)
        table.insert(group, VerticalSpan:new{ width = pad })
        table.insert(group, fc)
    end
end

---------------------------------------------------------------------------
-- Pick a server (last used -> single one found -> ask), then show the dashboard.
local function openDashboard()
    local list, connected = {}, false
    if BASE_OVERRIDE ~= "" then
        BASE, current = BASE_OVERRIDE, { url = BASE_OVERRIDE, name = BASE_OVERRIDE }
        connected = true
    else
        BASE, current = nil, nil
        local last = lastServer()
        local sv = last and probe(last.url, 1.5)  -- quick path: same PC as last time
        if sv then
            setServer(sv)
            connected = true
        else
            local info = InfoMessage:new{ text = "Looking for your PC..." }
            UIManager:show(info)
            UIManager:forceRePaint()
            list = discover()
            UIManager:close(info)
            local pick
            for _, s in ipairs(list) do
                if last and s.id == last.id then pick = s end  -- same PC, new address
            end
            if not pick and #list == 1 and AUTO_CONNECT_SINGLE then pick = list[1] end
            if pick then
                setServer(pick)
                connected = true
            end
        end
    end
    UIManager:show(DashScreen:new{
        servers = list,
        start_page = (not connected) and "devices" or nil,
    })
end

local Dashboard = WidgetContainer:extend{ name = "dashboard" }

function Dashboard:init()
    self.ui.menu:registerToMainMenu(self)
end

function Dashboard:addToMainMenu(menu_items)
    menu_items.pc_dashboard = {
        text = "PC Dashboard",
        sorting_hint = "tools",
        callback = function()
            NetworkMgr:runWhenOnline(openDashboard)
        end,
    }
end

return Dashboard
