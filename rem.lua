local env=getfenv()
if env.Rem and env.Rem.Destroy then env.Rem:Destroy() end
if env.Rimuru and env.Rimuru.Destroy then env.Rimuru:Destroy() end
if env["Nine".."MfgUI"] and env["Nine".."MfgUI"].Destroy then env["Nine".."MfgUI"]:Destroy() end
assert(Drawing and Drawing.new,"rimuru requires the Matcha Drawing API")
local V,RGB=Vector2.new,Color3.fromRGB
local unpackArgs=table.unpack or unpack
local themes={
 {Name="Purple",Accent=RGB(184,156,255),Text=RGB(239,230,255),Muted=RGB(185,169,213),Base=RGB(13,12,20)},
 {Name="Green",Accent=RGB(114,230,173),Text=RGB(224,255,239),Muted=RGB(153,200,178),Base=RGB(10,17,16)},
 {Name="Blue",Accent=RGB(124,185,255),Text=RGB(226,240,255),Muted=RGB(161,187,216),Base=RGB(11,15,23)},
 {Name="Black",Accent=RGB(208,211,223),Text=RGB(242,243,248),Muted=RGB(169,172,187),Base=RGB(8,9,13)}
}
local black,white=RGB(0,0,0),RGB(255,255,255)
local function clamp(n,a,b) return math.max(a,math.min(b,n)) end
local function mix(a,b,t) return Color3.new(a.R+(b.R-a.R)*t,a.G+(b.G-a.G)*t,a.B+(b.B-a.B)*t) end
local function short(s,n) s=tostring(s or "");return #s>n and s:sub(1,n-3).."..." or s end
local app={StartupSound=true,Effects=true,ReducedMotion=false,EffectStrength=0.8,PixelRem=true,Alive=true,Tabs={},Theme="Purple",Keybind=0xA1,Visible=true,_idRegistry={}}
env.Rem=app;env.Rimuru=app;env["Nine".."MfgUI"]=app
local run=game:GetService("RunService")
local workspace=game:GetService("Workspace")
local players=game:GetService("Players")
local mouse=players.LocalPlayer:GetMouse()
local pool,animations,notices={},{open=0},{}
local sequence,frame,connection=0,0,nil
local x,y,S,W,H=100,100,1,800,450
local a,contentA,dt,last=0,1,0,tick()
local mx,my,down,click,active=0,0,false,false,true
local previousDown,previousKey=false,false
local drag,slide,popup,capture=nil,nil,nil,nil
local tabOffset,selected=0,nil
local sidebarOpen,sidebarWidth,contentLeft=0,66,99
local sidebarLeaveTime=0
local closeConfirm=false
local closeConfirmClosing=false
local closingStarted=nil
local closeCenterX,closeCenterY,closeBaseS=nil,nil,nil
local CLOSE_DURATION=1.28
animations.sidebar=0
local targetTheme=1
local tint,ink,muted,accent=themes[1].Base,themes[1].Text,themes[1].Muted,themes[1].Accent
local avatarBytes=nil

-- intro state
local introDone=false
local introStart=nil
local introSound=nil
local introChimed=false
local motionClock=0
local visitTime=0
local pulsePoints={}

-- background state (self-contained: drawn, no network)
local imageFailed=false

local PIXEL_REM_LINES={"Oh hi","<3","Nice!","Sob"}

local pixelRem={
 awake=false,awakeUntil=0,wakeStart=-100,sleepStart=tick(),
 talk=nil,talkStart=0,talkUntil=0,lastTalk=nil,reactUntil=0,
 blinkAt=0,blinkUntil=0
}
local function pixelRemTalk(now)
 local value=nil
 local tries=0
 repeat
  value=PIXEL_REM_LINES[math.random(1,#PIXEL_REM_LINES)]
  tries=tries+1
 until value~=pixelRem.lastTalk or tries>=5
 pixelRem.lastTalk=value
 pixelRem.talk=value
 pixelRem.talkStart=now
 pixelRem.talkUntil=now+2.35
 animations["pixelRemTalk"]=0
end
local function uid() sequence=sequence+1;return "r"..sequence end
local function ease(id,target,rate)
 local v=animations[id];if v==nil then v=target end
 v=app.ReducedMotion and target or v+(target-v)*(1-math.exp(-dt*(rate or 14)));animations[id]=v;return v
end
local function obj(id,kind)
 local e=pool[id]
 if not e then
  local raw=Drawing.new(kind)
  local cache={}
  local d=setmetatable({}, {
   __index=function(_,key)
    if key=="Remove" then return function() raw:Remove() end end
    return cache[key]
   end,
   __newindex=function(_,key,value)
    if cache[key]~=value then raw[key]=value;cache[key]=value end
   end
  })
  e={d=d};pool[id]=e
  if kind=="Square" then d.Filled=true elseif kind=="Text" then d.Outline=false end
 end
 e.frame=frame;return e.d
end
local function rect(id,px,py,w,h,c,alpha,r,z)
 local d=obj(id,"Square");d.Position=V(px,py);d.Size=V(math.max(0,w),math.max(0,h));d.Color=c
 d.Transparency=clamp(alpha,0,1);d.Corner=r or 0;d.ZIndex=z or 20;d.Visible=alpha>0.005 and w>0 and h>0
end
local function txt(id,value,px,py,size,c,alpha,bold,z)
 local d=obj(id,"Text");d.Text=tostring(value);d.Position=V(px,py);d.Size=math.floor(size+0.5)
 d.Font=bold and Drawing.Fonts.SystemBold or Drawing.Fonts.System
 d.Color=c;d.Transparency=clamp(alpha,0,1);d.ZIndex=z or 40;d.Visible=alpha>0.005
end
local function box(id,px,py,w,h,c,opacity,r,z) rect(id,x+px*S,y+py*S,w*S,h*S,c,a*opacity,(r or 10)*S,z) end
local function label(id,value,px,py,size,c,opacity,bold,z) txt(id,value,x+px*S,y+py*S,size*S,c,a*(opacity or 1),bold,z) end
local function line(id,x1,y1,x2,y2,c,opacity,z,thickness)
 local d=obj(id,"Line");d.From=V(x+x1*S,y+y1*S);d.To=V(x+x2*S,y+y2*S)
 d.Thickness=math.max(1,(thickness or 1.65)*S);d.Color=c;d.Transparency=a*opacity;d.ZIndex=z or 45;d.Visible=a*opacity>0.005
end
local paths={
 rimuru={{2,10,10,1},{10,1,18,10},{18,10,10,19},{10,19,2,10},{6,10,10,5},{10,5,14,10},{14,10,10,15},{10,15,6,10}},
 spark={{10,1,12,8},{12,8,19,10},{19,10,12,12},{12,12,10,19},{10,19,8,12},{8,12,1,10},{1,10,8,8},{8,8,10,1}},
 layers={{2,6,10,2},{10,2,18,6},{18,6,10,10},{10,10,2,6},{2,10,10,14},{10,14,18,10},{2,14,10,18},{10,18,18,14}},
 bolt={{11,1,3,11},{3,11,9,11},{9,11,8,19},{8,19,17,8},{17,8,11,8},{11,8,11,1}},
 shield={{3,3,10,1},{10,1,17,3},{17,3,16,12},{16,12,10,19},{10,19,4,12},{4,12,3,3},{7,9,9,12},{9,12,14,6}},
 palette={{3,4,17,4},{17,4,17,16},{17,16,3,16},{3,16,3,4},{7,4,7,16},{12,4,12,16}},
 power={{10,1,10,10},{5,4,2,8},{2,8,2,14},{2,14,6,18},{6,18,14,18},{14,18,18,14},{18,14,18,8},{18,8,15,4}},
 sliders={{2,5,6,5},{10,5,18,5},{6,2,6,8},{10,2,10,8},{6,2,10,2},{6,8,10,8},{2,15,11,15},{15,15,18,15},{11,12,15,12},{11,18,15,18},{11,12,11,18},{15,12,15,18}},
 home={{1,9,10,1},{10,1,19,9},{3,8,3,18},{3,18,8,18},{8,18,8,12},{8,12,12,12},{12,12,12,18},{12,18,17,18},{17,18,17,8},{13,3,13,1},{13,1,16,1},{16,1,16,6},{6,8,8,8}},
 close={{5,5,15,15},{15,5,5,15}},
 script={{6,4,2,10},{2,10,6,16},{14,4,18,10},{18,10,14,16},{12,3,8,17}},
 down={{5,7,10,12},{10,12,15,7}},up={{5,12,10,7},{10,7,15,12}},
 left={{12,5,7,10},{7,10,12,15}},right={{7,5,12,10},{12,10,7,15}},
 check={{4,10,8,14},{8,14,16,5}},key={{3,6,17,6},{17,6,17,15},{17,15,3,15},{3,15,3,6},{6,10,7,10},{10,10,11,10},{13,10,14,10},{7,13,13,13}},
 info={{10,5,10,6},{10,9,10,15},{8,15,12,15}},
}
local gear={}
for i=0,11 do
 local t=i*math.pi/6;local u=(i+1)*math.pi/6
 gear[#gear+1]={10+math.cos(t)*7,10+math.sin(t)*7,10+math.cos(u)*7,10+math.sin(u)*7}
 if i%2==0 then gear[#gear+1]={10+math.cos(t)*7,10+math.sin(t)*7,10+math.cos(t)*10,10+math.sin(t)*10} end
end
for i=0,7 do local t=i*math.pi/4;local u=(i+1)*math.pi/4;gear[#gear+1]={10+math.cos(t)*2.5,10+math.sin(t)*2.5,10+math.cos(u)*2.5,10+math.sin(u)*2.5} end
paths.gear=gear
local function icon(id,name,px,py,c,opacity,z,angle,scale)
 local strokes=type(name)=="table" and name or paths[name] or paths.script
 local cs,sn=math.cos(angle or 0),math.sin(angle or 0);scale=scale or 1
 for i,p in ipairs(strokes) do
  local ax,ay,bx,by=(p[1]-10)*scale,(p[2]-10)*scale,(p[3]-10)*scale,(p[4]-10)*scale
  line(id..i,px+10+ax*cs-ay*sn,py+10+ax*sn+ay*cs,px+10+bx*cs-by*sn,py+10+bx*sn+by*cs,c,opacity,z)
 end
end
local function bitmap(id,bytes,px,py,width,height,opacity,radius,z)
 if not bytes then return false end
 local ok=pcall(function()
  local d=obj(id,"Image")
  d.Data=bytes;d.Position=V(px,py);d.Size=V(width,height)
  d.Color=white;d.Rounding=radius;d.Transparency=clamp(opacity,0,1)
  d.ZIndex=z;d.Visible=opacity>.005
 end)
 if not ok and pool[id] then pcall(function() pool[id].d.Visible=false end) end
 return ok
end

function app:SetAvatarData(bytes)
 assert(type(bytes)=="string" and #bytes>0,"Expected raw avatar image bytes")
 avatarBytes=bytes;self.AvatarStatus="ready"
end
local function httpGetBytes(url)
 local ok,body=pcall(function()
  return game:HttpGet(url,{["User-Agent"]="Mozilla/5.0 (Windows NT 10.0; Win64; x64)"})
 end)
 if ok and type(body)=="string" and #body>8 then return body end
 local requestFn=env.request or env.http_request
 if type(requestFn)~="function" and type(env.http)=="table" then requestFn=env.http.request end
 if type(requestFn)=="function" then
  local ok2,response=pcall(requestFn,{Url=url,Method="GET",Timeout=10})
  if ok2 then
   if type(response)=="string" then return response end
   if type(response)=="table" then
    local status=tonumber(response.StatusCode or response.Status or 200)
    if status and status>=200 and status<300 then return response.Body or response.body end
   end
  end
 end
 if type(env.httpget)=="function" then
  local ok3,body2=pcall(env.httpget,url);if ok3 and type(body2)=="string" then return body2 end
 end
 return nil
end
local function isPng(b) return type(b)=="string" and b:sub(1,8)=="\137PNG\13\10\26\10" end
local function loadAvatar()
 app.AvatarStatus="loading"
 task.spawn(function()
  local ok=pcall(function()
   local player=players.LocalPlayer
   local userId=tonumber(player and player.UserId)
   if not userId or userId<=0 then return end
   local endpoint="https://thumbnails.roblox.com/v1/users/avatar-headshot?userIds="..math.floor(userId).."&size=100x100&format=Png&isCircular=false"
   for attempt=1,3 do
    if not app.Alive then return end
    local body=httpGetBytes(endpoint)
    if body then
     local url=body:match('"imageUrl"%s*:%s*"([^"%s]+)"')
     if url then
      url=url:gsub("\\/","/")
      if url:match("^https://[%w%-%.]+%.rbxcdn%.com/") then
       local bytes=httpGetBytes(url)
       if not app.Alive then return end
       if isPng(bytes) then app:SetAvatarData(bytes);return end
      end
     end
    end
    if attempt<3 and type(task.wait)=="function" then task.wait(attempt) else break end
   end
  end)
  if app.Alive and not avatarBytes then app.AvatarStatus=ok and "unavailable" or "failed" end
 end)
end

local function hit(px,py,w,h,modal)
 local normalAllowed=not closeConfirm and not closeConfirmClosing and not closingStarted
 return introDone and active and app.Visible and a>0.9 and not (popup and popup.Closing) and (modal or (normalAllowed and not popup and not capture)) and mx>=x+px*S and mx<=x+(px+w)*S and my>=y+py*S and my<=y+(py+h)*S
end
local function fire(fn,...)
 if type(fn)~="function" then return end
 local args={...}
 task.spawn(function()
  local ok,err=pcall(function() fn(unpackArgs(args)) end)
  if not ok and app.Alive then app:Notify({Title="Script error",Content=tostring(err),Type="error",Duration=6}) end
 end)
end
function app:Notify(options,message)
 if not self.Alive then return end
 if type(options)~="table" then options={Title=options,Content=message} end
 local n={id=uid(),title=short(options.Title or "rimuru",32),message=short(options.Content or "",48),
  kind=options.Type or "info",duration=clamp(tonumber(options.Duration) or 4,1,20),time=tick()}
 notices[#notices+1]=n
 if #notices>4 then local old=table.remove(notices,1);animations[old.id.."y"]=nil end
 return n.id
end
function app:SetTheme(name)
 for i,t in ipairs(themes) do if string.lower(t.Name)==string.lower(tostring(name)) then targetTheme=i;self.Theme=t.Name;return true end end
 return false
end
local function keyName(k)
 local names={[0xA0]="Left Shift",[0xA1]="Right Shift",[0xA2]="Left Ctrl",[0xA3]="Right Ctrl",[0xA4]="Left Alt",[0xA5]="Right Alt",[0x2D]="Insert",[0x24]="Home",[0x23]="End",[0x20]="Space",[0x09]="Tab",[0x0D]="Enter",[0x2E]="Delete"}
 if names[k] then return names[k] end
 if k>=0x70 and k<=0x87 then return "F"..(k-0x6F) end
 if k>=0x30 and k<=0x5A then return string.char(k) end
 return string.format("Key 0x%02X",k)
end
function app:SetKeybind(vk)
 assert(type(vk)=="number" and vk>=8 and vk<=254 and vk==math.floor(vk) and vk~=27,"Use a VK key code (8..254), except Escape")
 self.Keybind=vk;previousKey=iskeypressed(vk)
end
function app:GetKeybind() return self.Keybind end
function app:GetValue(id) local c=self._idRegistry[id];return c and c.Value or nil end
function app:SetValue(id,value,silent) local c=self._idRegistry[id];if c and c.SetValue then c:SetValue(value,silent) end end
function app:Destroy()
 if not self.Alive then return end
 self.Alive=false
 if connection then connection:Disconnect() end
 if introSound then pcall(function() introSound:Destroy() end);introSound=nil end
 for _,e in pairs(pool) do pcall(function()
  if e.d.Data~=nil then e.d.Data=nil end
  e.d:Remove()
 end) end
 pool={};notices={};animations={}
 if env.Rem==self then env.Rem=nil end
 if env.Rimuru==self then env.Rimuru=nil end
 if env["Nine".."MfgUI"]==self then env["Nine".."MfgUI"]=nil end
end
local function requestClose()
 if not app.Alive or closingStarted or closeConfirm or closeConfirmClosing then return end
 popup=nil;capture=nil;slide=nil;drag=nil
 closeConfirm=true;closeConfirmClosing=false
 animations.closeConfirm=0
end
local function cancelClose()
 if closeConfirm and not closingStarted then closeConfirmClosing=true end
end
local function beginCloseAnimation()
 if closingStarted or not app.Alive then return end
 closeConfirm=false;closeConfirmClosing=false
 popup=nil;capture=nil;slide=nil;drag=nil
 app.Visible=true
 closingStarted=tick()
 closeCenterX=x+W*S*.5;closeCenterY=y+H*S*.5;closeBaseS=S
end
function app:RequestClose() requestClose() end
local Tab={};Tab.__index=Tab
local Control={};Control.__index=Control
function Control:GetValue() return self.Value end
function Control:SetValue(value,silent)
 if self.Kind=="toggle" then value=not not value
 elseif self.Kind=="slider" then value=clamp(tonumber(value) or self.Min,self.Min,self.Max);value=self.Min+math.floor((value-self.Min)/self.Step+0.5)*self.Step;value=clamp(value,self.Min,self.Max)
 elseif self.Kind=="dropdown" then
  local found=false;for _,item in ipairs(self.Options) do if item==value then found=true;break end end
  if not found then return self end
 end
 local changed=self.Value~=value;self.Value=value
 if changed and not silent then fire(self.Callback,value) end
 return self
end
local defaultIcons={button="bolt",toggle="power",slider="sliders",dropdown="layers",keybind="key",label="spark"}
function Tab:_add(kind,o)
 assert(app.Alive,"rimuru has been destroyed")
 o=o or {};local c=setmetatable({Id=uid(),Kind=kind,Title=short(o.Title or kind,52),Description=short(o.Description or "",68),Callback=o.Callback},Control)
 c.Icon=o.Icon or defaultIcons[kind]
 c.ButtonText=short(o.ButtonText or "Run",9)
 c.Min=tonumber(o.Min) or 0;c.Max=tonumber(o.Max) or 100;c.Step=tonumber(o.Step) or 1
 if kind=="slider" then assert(c.Max>c.Min and c.Step>0,"Slider requires Max > Min and Step > 0") end
 c.Options=o.Options or {};if kind=="dropdown" then assert(#c.Options>0,"Dropdown requires Options") end
 c.Value=o.Default
 if kind=="toggle" then c.Value=not not o.Default elseif kind=="slider" then c:SetValue(o.Default or c.Min,true)
 elseif kind=="dropdown" then c:SetValue(o.Default or c.Options[1],true) end
 animations[c.Id.."appear"]=0
 self.Controls[#self.Controls+1]=c
 if o.Id then
  assert(not app._idRegistry[o.Id],"duplicate control Id: "..tostring(o.Id))
  app._idRegistry[o.Id]=c;c.PublicId=o.Id
 end
 return c
end
function Tab:AddButton(o) return self:_add("button",o) end
function Tab:AddToggle(o) return self:_add("toggle",o) end
function Tab:AddSlider(o) return self:_add("slider",o) end
function Tab:AddDropdown(o) return self:_add("dropdown",o) end
function Tab:AddKeybind(o) return self:_add("keybind",o) end
function Tab:AddLabel(o) if type(o)=="string" then o={Title=o} end;return self:_add("label",o) end
local function replayTab(tab)
 animations.content=0;contentA=0;visitTime=motionClock;popup=nil;slide=nil;capture=nil
 for _,c in ipairs(tab.Controls) do
  local id=c.Id
  animations[id.."appear"]=0
  animations[id.."hover"]=0;animations[id.."cardhover"]=0
  animations[id.."press"]=0;animations[id.."rotate"]=0;animations[id.."record"]=0
  if c.Kind=="toggle" then animations[id.."switch"]=0 end
  if c.Kind=="slider" then animations[id.."fill"]=0;animations[id.."number"]=c.Min end
 end
end
function Tab:Select()
 if selected~=self then selected=self;replayTab(self) end
 for i,t in ipairs(app.Tabs) do if t==self then tabOffset=clamp(tabOffset,math.max(0,i-5),i-1) end end
 return self
end
function app:AddTab(o,builder)
 if type(o)=="string" then o={Title=o} end
 o=o or {};local tab=setmetatable({Id=uid(),Title=short(o.Title or "Tab",18),Icon=o.Icon or "script",Controls={},Page=1},Tab)
 animations[tab.Id.."appear"]=0
 self.Tabs[#self.Tabs+1]=tab;if not selected then selected=tab end
 if type(builder)=="function" then
  local ok,err=pcall(builder,tab)
  if not ok then task.spawn(function()
   if app.Alive then app:Notify({Title="Tab builder error",Content=tostring(err),Type="error",Duration=6}) end
  end) end
 end
 return tab
end
local home=app:AddTab({Title="Home",Icon="home"});app.Home=home
local settings=app:AddTab({Title="Settings",Icon="gear"});app.Settings=settings
home:AddLabel({Title="Welcome.",Icon="home"})
local themeControl=settings:AddDropdown({Id="theme",Title="Theme",Description="colors",Options={"Purple","Green","Blue","Black"},Default="Purple",Callback=function(v) app:SetTheme(v) end})
settings:AddToggle({Id="pixel_rimuru",Title="Pixel Rimuru",Description="Click her when shes asleep.",Default=true,Callback=function(v) app.PixelRem=v end})
settings:AddKeybind({Title="Menu keybind",Description="Click to record a key. Escape cancels."})
settings:AddButton({Id="test_notify",Title="Test notification",Description="Test.",Icon="info",ButtonText="Test",Callback=function()
 app:Notify({Title="Notification test",Content="it works.",Type="success",Duration=5})
end})

local function glow(id,px,py,w,h,strength,z)
 if not app.Effects then return end
 for j=3,1,-1 do
  local spread=j*3
  box(id..j,px-spread,py-spread,w+spread*2,h+spread*2,accent,strength*app.EffectStrength*(4-j)*0.035,12+spread,z or 18)
 end
end

local function pixelZ(id,px,py,size,alpha,z)
 size=math.max(1,math.floor(size or 2))
 box(id.."a",px,py,size*4,size,ink,alpha,0,z)
 box(id.."b",px+size*3,py+size,size,size,ink,alpha,0,z)
 box(id.."c",px+size*2,py+size*2,size,size,ink,alpha,0,z)
 box(id.."d",px+size,py+size*3,size,size,ink,alpha,0,z)
 box(id.."e",px,py+size*4,size*4,size,ink,alpha,0,z)
end

local function pixelSpark(id,px,py,alpha,z)
 box(id.."h",px-4,py,9,2,accent,alpha,0,z)
 box(id.."v",px,py-4,2,9,accent,alpha,0,z)
 box(id.."c",px,py,2,2,white,alpha,0,z+1)
end

local function pixelHeart(id,px,py,alpha,z)
 local p=2
 box(id.."1",px,py,p*2,p*2,accent,alpha,0,z)
 box(id.."2",px+p*3,py,p*2,p*2,accent,alpha,0,z)
 box(id.."3",px-p,py+p,p*7,p*2,accent,alpha,0,z)
 box(id.."4",px,py+p*3,p*5,p*2,accent,alpha,0,z)
 box(id.."5",px+p,py+p*5,p*3,p,accent,alpha,0,z)
end

-- rimuru slime drawn from primitives (no external image needed)
local function drawSlime(id,cx,cy,s,alpha,z,awake)
 local bodyW,bodyH=34*s,26*s
 local bodyCol=RGB(122,191,235)
 local bodyLight=RGB(180,220,245)
 local eyeCol=RGB(30,42,66)
 box(id.."_shadow",cx-bodyW*.5,cy+bodyH*.5,bodyW,2*s,black,alpha*.18,2*s,z-1)
 local rows=10
 for i=0,rows-1 do
  local t=i/(rows-1)
  local rowW=bodyW*(0.55+0.45*math.sin(t*math.pi))
  local rowY=cy-bodyH*.5+t*bodyH
  local col=i<2 and bodyLight or bodyCol
  box(id.."_b"..i,cx-rowW*.5,rowY,rowW,bodyH/rows+1,col,alpha,0,z)
 end
 box(id.."_hl",cx-bodyW*.28,cy-bodyH*.3,bodyW*.18,bodyH*.12,white,alpha*.7,2*s,z+1)
 if awake then
  box(id.."_eyeL",cx-bodyW*.18,cy-bodyH*.05,3*s,4*s,eyeCol,alpha,1*s,z+2)
  box(id.."_eyeR",cx+bodyW*.10,cy-bodyH*.05,3*s,4*s,eyeCol,alpha,1*s,z+2)
  box(id.."_shineL",cx-bodyW*.16,cy-bodyH*.03,1*s,1*s,white,alpha,0,z+3)
  box(id.."_shineR",cx+bodyW*.12,cy-bodyH*.03,1*s,1*s,white,alpha,0,z+3)
  box(id.."_mouth",cx-1.5*s,cy+bodyH*.18,3*s,1*s,eyeCol,alpha*.8,0,z+2)
 else
  box(id.."_eyeL",cx-bodyW*.18,cy,4*s,1.5*s,eyeCol,alpha,0,z+2)
  box(id.."_eyeR",cx+bodyW*.10,cy,4*s,1.5*s,eyeCol,alpha,0,z+2)
 end
end

local function renderPixelRem(now)
 local fade=ease("pixelRemVisible",app.PixelRem and app.Visible and introDone and 1 or 0,14)
 if fade<=0.005 then return end

 local anchorX=W-146
 local hUI=164
 local wUI=hUI*(385/796)
 local seatRatio=.752
 local topY=-(hUI*seatRatio)
 local slimeCX=anchorX
 local slimeCY=topY+hUI*.48

 if (not pixelRem.awake) and click and now>=pixelRem.reactUntil then
  local cx=x+anchorX*S
  local cy=y+(topY+hUI*.47)*S
  if math.abs(mx-cx)<=50*S and math.abs(my-cy)<=88*S then
   pixelRem.awake=true
   pixelRem.awakeUntil=now+20
   pixelRem.wakeStart=now
   pixelRem.blinkAt=now+2.8+math.random()*2.4
   pixelRem.blinkUntil=0
   pixelRemTalk(now)
   pixelRem.reactUntil=now+.45
  end
 end

 if pixelRem.awake and now>=pixelRem.awakeUntil then
  pixelRem.awake=false
  pixelRem.sleepStart=now
  pixelRem.talk=nil
  pixelRem.blinkAt=0
  pixelRem.blinkUntil=0
  animations["pixelRemTalk"]=0
 end
 if pixelRem.talk and now>=pixelRem.talkUntil then
  pixelRem.talk=nil
  animations["pixelRemTalk"]=0
 end

 local showAwake=pixelRem.awake
 if pixelRem.awake then
  if pixelRem.blinkAt==0 then pixelRem.blinkAt=now+2.8+math.random()*2.4 end
  if now>=pixelRem.blinkAt and pixelRem.blinkUntil==0 then pixelRem.blinkUntil=now+.12 end
  if pixelRem.blinkUntil>0 then
   if now<pixelRem.blinkUntil then showAwake=false
   else pixelRem.blinkUntil=0;pixelRem.blinkAt=now+2.8+math.random()*2.8 end
  end
  if pixelRem.talk=="Sob" and math.floor((now-pixelRem.talkStart)*6)%2==0 then showAwake=false end
 end

 drawSlime("pixelRemSlime",slimeCX,slimeCY,S*1.6,a*fade,63,showAwake)

 box("pixelRemSeatShadow",anchorX-23,-2,46,2,black,.16*fade,0,59)

 if not pixelRem.awake then
  local sleepAge=math.max(0,now-pixelRem.sleepStart)
  if not app.ReducedMotion then
   local zs=math.floor(sleepAge*1.35)%4
   pixelZ("pixelRemZMain",anchorX+wUI*.39+9,topY+22-zs,1,.60*fade,67)
   if zs>=2 then pixelZ("pixelRemZSoft",anchorX+wUI*.39+17,topY+11-zs,1,.27*fade,67) end
  else
   pixelZ("pixelRemZStatic",anchorX+wUI*.39+9,topY+20,1,.48*fade,67)
  end
 else
  local wakeAge=now-pixelRem.wakeStart
  if wakeAge>=0 and wakeAge<.42 and app.Effects then
   local wf=math.floor(wakeAge/.07)
   local p=(1-wakeAge/.42)*fade
   pixelSpark("pixelRemWakeA",anchorX+wUI*.42+7+(wf%2),topY+35-(wf%2),p,69)
  end
 end

 if pixelRem.talk then
  local age=math.max(0,now-pixelRem.talkStart)
  local remaining=math.max(0,pixelRem.talkUntil-now)
  local step=math.min(3,math.floor(age/.045))
  local bubbleA=fade*clamp(remaining/.15,0,1)
  local textValue=pixelRem.talk
  local bw=clamp(31+#textValue*6.4,72,126)
  local bh=29
  local bx=clamp(anchorX-wUI*.5-bw-10,12,W-bw-12)
  local by=topY+34-math.min(2,step)

  box("pixelRemBubbleShadow",bx+2,by+2,bw,bh,black,.27*bubbleA,0,65)
  box("pixelRemBubble",bx+2,by,bw-4,bh,mix(tint,white,.11),.98*bubbleA,0,66)
  box("pixelRemBubbleL",bx,by+3,2,bh-6,mix(tint,white,.11),.98*bubbleA,0,66)
  box("pixelRemBubbleR",bx+bw-2,by+3,2,bh-6,mix(tint,white,.11),.98*bubbleA,0,66)
  box("pixelRemBubbleEdge",bx+4,by+2,bw-8,2,accent,.30*bubbleA,0,67)
  box("pixelRemBubbleTail1",bx+bw-2,by+bh-8,5,5,mix(tint,white,.11),.98*bubbleA,0,66)
  box("pixelRemBubbleTail2",bx+bw+2,by+bh-4,4,4,mix(tint,white,.11),.98*bubbleA,0,66)
  label("pixelRemTalkText",textValue,bx+9,by+7,10.5,ink,bubbleA,true,68)

  if textValue=="<3" then
   local hp=(age*.85)%1
   local hs=math.floor(hp*7)
   pixelHeart("pixelRemHeart",anchorX+18+hs%2,topY+38-hs*2,(1-hp)*.82*bubbleA,71)
  elseif textValue=="Sob" then
   local drop=math.floor((age*12)%15)
   local faceX=anchorX+wUI*.18
   local faceY=topY+hUI*.24
   box("pixelRemTear1",faceX+8,faceY+10+drop,2,4,RGB(124,185,255),.84*bubbleA,0,71)
   box("pixelRemTear2",faceX+13,faceY+16+((drop+7)%15),2,3,RGB(124,185,255),.57*bubbleA,0,71)
  elseif textValue=="Oh hi" then
   local flash=(math.floor(age*7)%2==0) and .88 or .32
   pixelSpark("pixelRemHiSpark",anchorX+wUI*.37+10,topY+42,flash*bubbleA,71)
  end
 end
end
local function smallButton(id,glyph,px,py,fn,modal,z)
 local over=hit(px,py,28,28,modal)
 box(id,px,py,28,28,ink,ease(id.."h",over and 0.16 or 0.045),8,z or 35)
 local hover=ease(id.."ink",over and 1 or 0)
 icon(id.."i",glyph,px+4,py+4-hover,mix(muted,accent,hover),1,(z or 35)+1,0,1+hover*.12)
 if over and click then click=false;fn() end
end
local function beginCapture()
 capture={keys={}};popup=nil
 for k=8,254 do capture.keys[k]=iskeypressed(k) end
end
local function renderControl(c,py,index)
 local id=c.Id;local px=contentLeft;local width=761-px
 local enter=ease(id.."appear",(app.ReducedMotion or motionClock-visitTime>(index-1)*0.045) and 1 or 0,13)
 local cardA=contentA*enter
 py=py+(1-enter)*10
 local hovered=hit(px,py,width,65)
 local hover=ease(id.."cardhover",hovered and 1 or 0,14)
 local surface=mix(tint,white,0.035+hover*0.022)
 box(id.."border",px-hover,py-hover,width+hover*2,65+hover*2,mix(ink,accent,hover),(.065+hover*.13)*cardA,12,22)
 box(id.."card",px+1,py+1,width-2,63,surface,(.48+hover*.14)*cardA,11,23)
 box(id.."badge",px+13,py+17,31,31,accent,(.055+hover*.07)*cardA,9,25)
 icon(id.."customicon",c.Icon,px+18.5,py+22.5-hover*2,mix(muted,accent,hover),cardA,28,hover*.08,1+hover*.1)
 local right=c.Kind=="label" and 0 or 195
 label(id.."title",short(c.Title,right>0 and 28 or 52),px+57+hover*3,py+13,14,ink,cardA,true)
 label(id.."description",short(c.Description,right>0 and 38 or 66),px+57+hover*3,py+37,11,muted,cardA)
 if hovered and click and not app.ReducedMotion then
  pulsePoints[#pulsePoints+1]={x=clamp((mx-x)/S,px+10,px+width-10),y=clamp((my-y)/S,py+10,py+55),time=motionClock}
  if #pulsePoints>6 then table.remove(pulsePoints,1) end
 end
 if c.Kind=="button" then
  local over=hit(650,py+15,94,34)
  local pulse=ease(id.."press",0,9)
  box(id.."button",650+pulse*2,py+15+pulse,94-pulse*4,34-pulse*2,accent,(0.14+pulse*0.25+ease(id.."hover",over and 0.13 or 0))*cardA,9,30)
  label(id.."run",c.ButtonText,667,py+24,12,ink,cardA,true);icon(id.."arrow","right",717,py+22,accent,cardA)
  if over and click then click=false;animations[id.."press"]=1;fire(c.Callback) end
 elseif c.Kind=="toggle" then
  local v=ease(id.."switch",c.Value and 1 or 0)
  glow(id.."toggleGlow",699,py+25,38,16,v*cardA,29)
  box(id.."switch",695,py+21,46,24,mix(muted,accent,v),(0.16+v*0.5)*cardA,12,30)
  box(id.."knob",699+22*v,py+25,16,16,ink,cardA,8,31)
  if hit(680,py+12,65,42) and click then click=false;c:SetValue(not c.Value) end
 elseif c.Kind=="dropdown" then
  local over=hit(579,py+15,165,35)
  box(id.."select",579,py+15,165,35,ink,(0.055+ease(id.."hover",over and 0.065 or 0))*cardA,8,30)
  label(id.."value",short(c.Value,17),592,py+25,12,ink,cardA,true)
  local rotate=ease(id.."rotate",popup and popup.control==c and not popup.Closing and 1 or 0)
  line(id.."chevron1",724,py+30+5*rotate,729,py+35-5*rotate,accent,cardA)
  line(id.."chevron2",729,py+35-5*rotate,734,py+30+5*rotate,accent,cardA)
  if over and click then click=false;popup={control=c,x=579,y=math.min(py+53,H-186),offset=0};animations.dropdown=0 end
 elseif c.Kind=="keybind" then
  box(id.."key",579,py+15,165,35,accent,(0.07+ease(id.."record",capture and 0.16 or hit(579,py+15,165,35) and 0.06 or 0))*cardA,8,30)
  icon(id.."keyicon","key",588,py+22,accent,cardA)
  label(id.."value",capture and "Press a key..." or keyName(app.Keybind),617,py+25,12,ink,cardA,true)
  if hit(579,py+15,165,35) and click then click=false;beginCapture() end
 elseif c.Kind=="slider" then
  local sx,sw=584,156
  label(id.."value",string.format("%.2f",ease(id.."number",c.Value,18)):gsub("%.?0+$",""),680,py+8,11,accent,cardA,true)
  if hit(sx-6,py+26,sw+12,28) and click then slide=c;click=false end
  if slide==c and down and active and not popup and not capture then c:SetValue(c.Min+clamp((mx-x-sx*S)/(sw*S),0,1)*(c.Max-c.Min)) end
  local t=ease(id.."fill",(c.Value-c.Min)/(c.Max-c.Min))
  box(id.."track",sx,py+39,sw,3,ink,0.14*cardA,2,30)
  box(id.."fill",sx,py+39,sw*t,3,accent,cardA,2,31)
  glow(id.."sliderGlow",sx+sw*t-3,py+37,7,7,cardA,30)
  box(id.."thumb",sx+sw*t-5,py+35,11,11,ink,cardA,6,32)
 end
end
local function renderPopup()
 if not popup then return end
 local p=popup;local c=p.control;local reveal=ease("dropdown",p.Closing and 0 or 1,20);local py=p.y+(1-reveal)*-6
 if p.Closing and reveal<0.01 then popup=nil;return end
 local count=math.min(4,#c.Options-p.offset);local extra=#c.Options>4 and 29 or 0
 local height=count*32+12+extra
 box("dropdownshadow",p.x-4,py+3,173,height+5,black,.4*reveal,13,68)
 box("dropdownrim",p.x-1,py-1,167,height+2,accent,.25*reveal,11,69)
 box("dropdown",p.x,py,165,height,mix(tint,white,.045),reveal,10,70)
 for j=1,count do
  local value=c.Options[p.offset+j];local rowY=py+6+(j-1)*32
  local over=hit(p.x+5,rowY,155,30,true)
  local chosen=c.Value==value
  local hover=ease("optionmotion"..j,over and 1 or 0,16)
  box("optionrail"..j,p.x+6,rowY+8,2,14,accent,hover*reveal,1,72)
  box("option"..j,p.x+5,rowY,155,30,accent,ease("optionhover"..j,chosen and 0.22+hover*.08 or hover*.16)*reveal,7,71)
  label("optiontext"..j,short(value,17),p.x+12+hover*4,rowY+9,12,mix(chosen and accent or ink,accent,hover*.6),reveal,chosen,73)
  if chosen then icon("optioncheck"..j,"check",p.x+136,rowY+5,accent,reveal,73) end
  if over and click then click=false;c:SetValue(value);p.Closing=true;break end
 end
 if popup and extra>0 then
  smallButton("optionsprev","left",p.x+100,py+height-29,function() p.offset=math.max(0,p.offset-4) end,true,74)
  smallButton("optionsnext","right",p.x+130,py+height-29,function() p.offset=math.min(math.floor((#c.Options-1)/4)*4,p.offset+4) end,true,74)
 end
 if popup and click and not hit(p.x,py,165,height,true) then p.Closing=true;click=false end
end
local borderRadius=17
local borderHorizontal=W-2*borderRadius
local borderVertical=H-2*borderRadius
local borderArc=math.pi*borderRadius/2
local borderLength=2*borderHorizontal+2*borderVertical+4*borderArc
local function borderPoint(distance)
 local d=distance%borderLength;local r=borderRadius
 if d<borderHorizontal then return r+d,0 end;d=d-borderHorizontal
 if d<borderArc then local t=d/r-math.pi/2;return W-r+math.cos(t)*r,r+math.sin(t)*r end;d=d-borderArc
 if d<borderVertical then return W,r+d end;d=d-borderVertical
 if d<borderArc then local t=d/r;return W-r+math.cos(t)*r,H-r+math.sin(t)*r end;d=d-borderArc
 if d<borderHorizontal then return W-r-d,H end;d=d-borderHorizontal
 if d<borderArc then local t=d/r+math.pi/2;return r+math.cos(t)*r,H-r+math.sin(t)*r end;d=d-borderArc
 if d<borderVertical then return 0,H-r-d end;d=d-borderVertical
 local t=d/r+math.pi;return r+math.cos(t)*r,r+math.sin(t)*r
end
local function smooth(t) t=clamp(t,0,1);return t*t*t*(t*(t*6-15)+10) end

local function renderCloseConfirm()
 if not closeConfirm and not closeConfirmClosing then return end
 local target=closeConfirmClosing and 0 or 1
 local reveal=ease("closeConfirm",target,closeConfirmClosing and 24 or 17)
 if closeConfirmClosing and reveal<0.015 then closeConfirm=false;closeConfirmClosing=false;return end

 local pop=app.ReducedMotion and 1 or (.965+.035*smooth(reveal))
 local mw,mh=400*pop,188*pop
 local px,py=W*.5-mw*.5,H*.5-mh*.5
 local aa=reveal

 box("closeConfirmDim",0,0,W,H,black,.24*aa,17,145)
 box("closeConfirmShadow",px-4,py+5,mw+8,mh+7,black,.16*aa,18,146)
 box("closeConfirmRim",px-1,py-1,mw+2,mh+2,mix(ink,accent,.22),.13*aa,17,147)
 box("closeConfirmPanel",px,py,mw,mh,mix(tint,black,.10),.72*aa,16,148)

 box("closeConfirmBadge",px+24,py+21,37,37,accent,.095*aa,10,150)
 icon("closeConfirmIcon","close",px+31.5,py+28.5,accent,.92*aa,153,0,1.02)
 label("closeConfirmKicker","UNLOAD RIMURU",px+75,py+20,9,accent,.72*aa,true,153)
 label("closeConfirmTitle","Are you sure?",px+75,py+37,22,ink,.96*aa,true,153)
 label("closeConfirmBody","This will completely unload the menu.",px+25,py+75,11,muted,.78*aa,false,153)
 box("closeConfirmRule",px+25,py+103,mw-50,1,ink,.055*aa,0,150)

 local by=py+119
 local gap=10
 local bw=(mw-50-gap)*.5
 local bh=43
 local noX=px+25
 local yesX=noX+bw+gap
 local noOver=hit(noX,by,bw,bh,true)
 local yesOver=hit(yesX,by,bw,bh,true)
 local nh=ease("closeNoHover",noOver and 1 or 0,18)
 local yh=ease("closeYesHover",yesOver and 1 or 0,18)

 box("closeNo",noX,by,bw,bh,mix(tint,white,.025),(.30+.08*nh)*aa,10,151)
 box("closeNoRail",noX,by+11,2,21,muted,.22*nh*aa,1,154)
 label("closeNoText","No, keep it",noX+41+nh*2,by+14,12,mix(ink,accent,nh*.18),.92*aa,true,154)

 box("closeYesRim",yesX-1,by-1,bw+2,bh+2,accent,(.14+.13*yh)*aa,11,150)
 box("closeYes",yesX,by,bw,bh,accent,(.075+.10*yh)*aa,10,151)
 box("closeYesRail",yesX,by+11,2,21,accent,(.42+.28*yh)*aa,1,154)
 label("closeYesText","Yes, unload",yesX+37+yh*2,by+14,12,ink,.95*aa,true,154)
 icon("closeYesArrow","right",yesX+bw-30+yh*2,by+11,accent,.92*aa,155,0,.82+yh*.06)

 if noOver and click then click=false;cancelClose() end
 if yesOver and click then click=false;beginCloseAnimation() end
end

local function renderCloseEffects(now)
 if not closingStarted then return false end
 local elapsed=now-closingStarted
 local duration=app.ReducedMotion and .42 or CLOSE_DURATION
 local cx,cy=closeCenterX or (x+W*S*.5),closeCenterY or (y+H*S*.5)
 local bs=closeBaseS or S
 if not app.ReducedMotion then
  local gather=smooth((elapsed-.10)/.72)
  for j=1,20 do
   local angle=j*2.399963229728653
   local radius=(1-gather)*(116+(j%5)*24)*bs
   local wobble=math.sin(elapsed*14+j)*3*bs*(1-gather)
   local px=cx+math.cos(angle)*radius+wobble
   local py=cy+math.sin(angle)*radius*.55-wobble*.35
   local sz=(j%3==0 and 3 or 2)*math.max(.65,bs)
   rect("closeShard"..j,px-sz*.5,py-sz*.5,sz,sz,accent,(1-gather)*.72,0,171)
  end
  local scan=smooth((elapsed-.08)/.55)
  for j=1,5 do
   local offset=(1-scan)*(70+j*19)*bs
   local yy=cy+((j%2==0) and offset or -offset)
   local width=(150+j*38)*bs*(1-scan*.35)
   rect("closeScan"..j,cx-width*.5,yy,width,math.max(1,1.2*bs),j%2==0 and ink or accent,(1-scan)*(.14+j*.035),0,169)
  end
 end
 local lineIn=smooth((elapsed-.44)/(duration*.38))
 local lineOut=smooth((elapsed-duration*.80)/(duration*.20))
 local lineW=math.max(0,230*bs*lineIn*(1-lineOut))
 if lineW>0.5 then
  rect("closeCoreGlow",cx-lineW*.5-5*bs,cy-3*bs,lineW+10*bs,6*bs,accent,.10*(1-lineOut),3*bs,173)
  rect("closeCore",cx-lineW*.5,cy-math.max(.5,bs*.65),lineW,math.max(1,1.3*bs),accent,.90*(1-lineOut),1,174)
 end
 local wordA=(1-smooth((elapsed-duration*.58)/(duration*.22)))*smooth(elapsed/(duration*.16))
 if wordA>.01 then txt("closeWord","rimuru",cx-28*bs,cy-27*bs,16*bs,ink,wordA,true,175) end
 if elapsed>=duration then app:Destroy();return true end
 return false
end

local function measureText(value,size,bold)
 local d=obj("__measure","Text")
 d.Text=tostring(value);d.Size=math.floor(size+0.5)
 d.Font=bold and Drawing.Fonts.SystemBold or Drawing.Fonts.System
 d.Visible=false
 local ok,bounds=pcall(function() return d.TextBounds end)
 if ok and type(bounds)=="Vector2" then return bounds.X end
 return #tostring(value)*size*0.55
end

local function renderIntro(now,vp)
 if introDone then return end
 if not introStart then introStart=now end
 local elapsed=now-introStart
 if app.ReducedMotion then elapsed=3.3 end
 if elapsed>=3.3 then
  introDone=true;animations.content=0;visitTime=motionClock
  for id,e in pairs(pool) do
   if id:sub(1,6)=="intro:" then pcall(function() e.d:Remove() end);pool[id]=nil end
  end
  if introSound then pcall(function() introSound:Destroy() end);introSound=nil end
  return
 end
 if elapsed>=.90 and not introChimed then
  introChimed=true
  if app.StartupSound then task.spawn(function()
   if not app.Alive or introDone then return end
   pcall(function()
    if not Instance or type(Instance.new)~="function" then return end
    local sound=Instance.new("Sound");introSound=sound
    sound.SoundId="rbxasset://sounds/electronicpingshort.wav"
    sound.Volume=.12;sound.PlaybackSpeed=1.18
    local ok2=pcall(function()
     sound.Parent=game:GetService("SoundService");sound:Play()
    end)
    if not ok2 then introSound=nil end
   end)
  end) end
 end

 local reveal=smooth(elapsed/.95)
 local leave=smooth((elapsed-2.65)/.60)
 local opacity=reveal*(1-leave)
 local scale=math.min(1,(vp.X-24)/420,(vp.Y-24)/136)
 local cx,cy=vp.X/2,vp.Y/2+(1-reveal)*8-leave*8

 local wordT=smooth((elapsed-1.10)/.42)
 local wordAlpha=opacity*wordT
 local wordY=cy - 25*scale + (1-wordT)*10*scale
 local wordSize=40*scale*(0.92+0.08*wordT)
 local word="rimuru"
 local wordW=measureText(word,wordSize,true)
 local wordX=cx - wordW/2

 txt("intro:echo",word,wordX-2*scale,wordY+1*scale,wordSize,white,wordAlpha*(1-wordT)*.22,true,116)
 txt("intro:word",word,wordX,wordY,wordSize,white,wordAlpha,true,117)

 local slimeAlpha=opacity*wordT
 if slimeAlpha>.01 then
  local slimeSize=wordSize*0.9
  local slimeCX=wordX-slimeSize*0.9
  local slimeCY=wordY+slimeSize*0.45
  local s=slimeSize/44
  local function slimeBox(id,bx,by,bw,bh,c,alpha,r)
   local d=obj("intro:"..id,"Square")
   d.Position=V(bx,by);d.Size=V(bw,bh);d.Color=c
   d.Transparency=clamp(alpha,0,1);d.Corner=r or 0;d.ZIndex=115
   d.Visible=alpha>0.005
  end
  local bodyW,bodyH=34*s,26*s
  local bodyCol=RGB(122,191,235)
  local bodyLight=RGB(180,220,245)
  local eyeCol=RGB(30,42,66)
  local rows=10
  for i=0,rows-1 do
   local t=i/(rows-1)
   local rowW=bodyW*(0.55+0.45*math.sin(t*math.pi))
   local rowY=slimeCY-bodyH*.5+t*bodyH
   local col=i<2 and bodyLight or bodyCol
   slimeBox("b"..i,slimeCX-rowW*.5,rowY,rowW,bodyH/rows+1,col,slimeAlpha,0)
  end
  slimeBox("hl",slimeCX-bodyW*.28,slimeCY-bodyH*.3,bodyW*.18,bodyH*.12,white,slimeAlpha*.7,2*s)
  slimeBox("eyeL",slimeCX-bodyW*.18,slimeCY-bodyH*.05,3*s,4*s,eyeCol,slimeAlpha,1*s)
  slimeBox("eyeR",slimeCX+bodyW*.10,slimeCY-bodyH*.05,3*s,4*s,eyeCol,slimeAlpha,1*s)
  slimeBox("shL",slimeCX-bodyW*.16,slimeCY-bodyH*.03,1*s,1*s,white,slimeAlpha,0)
  slimeBox("shR",slimeCX+bodyW*.12,slimeCY-bodyH*.03,1*s,1*s,white,slimeAlpha,0)
 end

 local lock=smooth((elapsed-1.64)/.34)
 local sweepW=wordW*lock
 rect("intro:logoSweep",
  wordX + (wordW-sweepW)/2,
  wordY+42*scale,
  sweepW,
  math.max(1,1.15*scale),
  white,
  opacity*(1-lock)*.34,
  1,
  116)
end

local function render()
 local now=tick();dt=clamp(now-last,0,0.1);last=now;frame=frame+1
 if not app.ReducedMotion then motionClock=motionClock+dt end
 active=type(isrbxactive)~="function" or isrbxactive()
 down=active and ismouse1pressed();click=down and not previousDown;previousDown=down
 mx,my=mouse.X,mouse.Y
 if not down then drag=nil;slide=nil end
 local wasCapture=capture~=nil
 if capture and active then
  for k=8,254 do
   local held=iskeypressed(k)
   if held and not capture.keys[k] and k~=16 and k~=17 and k~=18 then
    if k~=27 then app:SetKeybind(k) end
    capture=nil;break
   end
   capture.keys[k]=held
  end
 end
 local key=active and iskeypressed(app.Keybind)
 if key and not previousKey and not wasCapture and introDone and not closeConfirm and not closeConfirmClosing and not closingStarted then app.Visible=not app.Visible;popup=nil;capture=nil end
 previousKey=key
 local camera=workspace.CurrentCamera;local vp=camera and camera.ViewportSize or V(1280,720)
 renderIntro(now,vp)
 S=math.max(0.2,math.min(1,(vp.X-24)/W,(vp.Y-24)/H))
 if frame==1 then x=(vp.X-W*S)/2;y=(vp.Y-H*S)/2 end
 if click and not closeConfirm and not closeConfirmClosing and not closingStarted and hit(0,0,W-65,69) then drag={mx-x,my-y};click=false end
 if drag and down then x=mx-drag[1];y=my-drag[2] end
 x=clamp(x,8,math.max(8,vp.X-W*S-8));y=clamp(y,8,math.max(8,vp.Y-H*S-8))
 a=ease("open",app.Visible and (introDone or (introStart and now-introStart>=2.98)) and 1 or 0,13);contentA=ease("content",1,15)
 if closingStarted then
  local elapsed=now-closingStarted
  local duration=app.ReducedMotion and .42 or CLOSE_DURATION
  local compress=smooth((elapsed-duration*.17)/(duration*.68))
  local fade=smooth((elapsed-duration*.45)/(duration*.45))
  local pulse=app.ReducedMotion and 0 or math.sin(clamp(elapsed/(duration*.18),0,1)*math.pi)*.012
  local scaleMul=math.max(.035,1+pulse-compress*.945)
  S=(closeBaseS or S)*scaleMul
  x=(closeCenterX or (x+W*S*.5))-W*S*.5
  y=(closeCenterY or (y+H*S*.5))-H*S*.5
  a=a*(1-fade);contentA=contentA*(1-fade)
 end
 local b=1-math.exp(-dt*9);local theme=themes[targetTheme]
 tint=mix(tint,theme.Base,b);ink=mix(ink,theme.Text,b);muted=mix(muted,theme.Muted,b);accent=mix(accent,theme.Accent,b)
 if themeControl.Value~=app.Theme then themeControl:SetValue(app.Theme,true) end
 local restY=y;y=y+(1-a)*15*S
 local sidebarOver=hit(10,10,sidebarWidth,H-20) and not slide and not drag
 if sidebarOver then sidebarLeaveTime=now end
 local expand=sidebarOver or (sidebarOpen>.01 and now-sidebarLeaveTime<.12)
 sidebarOpen=ease("sidebar",expand and 1 or 0,expand and 14 or 12)
 sidebarWidth=66+108*sidebarOpen;contentLeft=99+108*sidebarOpen
 local sidebarText=clamp((sidebarOpen-.60)/.40,0,1)
 local navWidth=43+108*sidebarOpen
 if a>0.005 then
  for j=4,1,-1 do box("shadow"..j,-j*4,j*2,W+j*8,H+j*4,black,.035,18+j*4,4+j) end
  box("rim",-1,-1,W+2,H+2,ink,0.13,18,9)
  box("base",0,0,W,H,tint,.68,17,10)

  -- self-contained background (gradient, no network)
  box("bgTop",0,0,W,H*.5,mix(tint,accent,.05),.30,17,11)
  box("bgBot",0,H*.5,W,H*.5,mix(tint,black,.18),.30,17,11)

  box("tint",0,0,W,H,tint,0.18,17,12)
  if app.Effects then
   local strength=app.EffectStrength
   for j=1,14 do
    local px=200+((j*139.7+motionClock*(3+j%3))%570)
    local py=84+((j*71.1-motionClock*(2+j%4))%326)
    local flicker=.12+.16*(.5+.5*math.sin(motionClock*1.2+j*2))
    box("dust"..j,px,py,j%3==0 and 2 or 1.2,j%3==0 and 2 or 1.2,accent,flicker*strength,1,14)
   end
   local head=motionClock*190
   for j=1,28 do
    local px,py=borderPoint(head-(j-1)*5)
    local qx,qy=borderPoint(head-j*5)
    local fade=(1-(j-1)/28)^2
    local id="lightTrail"..j
    line(id.."soft",px,py,qx,qy,accent,fade*.45*strength,18,8)
    line(id,px,py,qx,qy,accent,fade*1.95*strength,19,2.5)
   end
  end
  renderPixelRem(now)
  box("sidebar",10,10,sidebarWidth,H-20,mix(tint,black,.24),.58,12,15)
  box("sidebarRule",10+sidebarWidth,25,1,H-50,ink,.06,0,16)
  box("brandBadge",25,25,35,35,accent,.12,10,20)
  glow("brandHalo",30,30,25,25,.8,18)
  if not bitmap("brandPortrait",avatarBytes,x+26*S,y+26*S,33*S,33*S,a,9*S,42) then
   icon("brandMark","rimuru",32.5,32.5,accent,1,42)
  end
  label("brand","rimuru",70,25,27,ink,sidebarText,true)

  box("headerRule",contentLeft,78,761-contentLeft,1,ink,.075,0,20)
  label("sectionSub","",contentLeft+1,59,11,muted,contentA)

  for i=1,math.min(5,#app.Tabs-tabOffset) do
   local tab=app.Tabs[i+tabOffset];local enter=ease(tab.Id.."appear",1,11);local py=101+(i-1)*53+(1-enter)*9
   local over=hit(21,py,navWidth,43)
   local weight=ease(tab.Id.."selected",selected==tab and 1 or 0,15)
   local hover=ease(tab.Id.."hover",over and 1 or 0,14)
   box(tab.Id.."nav",21,py,navWidth,43,accent,(weight*.16+hover*.09)*enter,10,21)
   box(tab.Id.."rail",21,py+12,2,19,accent,weight*enter,1,24)
   icon(tab.Id.."icon",tab.Icon,33+hover*2,py+11-hover*2,mix(muted,accent,math.max(weight,hover)),enter,45,tab.Icon=="gear" and (weight*.35+hover*.4) or hover*.035,1+hover*.12)
   label(tab.Id.."name",short(tab.Title,math.max(4,math.floor((navWidth-48)/7))),64+hover*4,py+15,13,mix(muted,ink,weight),enter*sidebarText,selected==tab)
   if over and click then click=false;tab:Select() end
  end
  if #app.Tabs>5 then
   smallButton("tabsprev","up",29+16*sidebarOpen,350+24*sidebarOpen,function() tabOffset=math.max(0,tabOffset-1) end)
   smallButton("tabsnext","down",29+87*sidebarOpen,381-7*sidebarOpen,function() tabOffset=math.min(math.max(0,#app.Tabs-5),tabOffset+1) end)
  end
  box("keyhintBg",24,413,44+104*sidebarOpen,22,ink,.04,6,20)
  icon("keyhintIcon","key",29,414,muted,.7,42,0,.65)
  label("keyhint",string.upper(keyName(app.Keybind)),56,420,9,muted,0.9*sidebarText,true)
  label("title",selected.Title,contentLeft,29,25,ink,contentA,true)
  smallButton("close","close",752,23,requestClose)
  local pages=math.max(1,math.ceil(#selected.Controls/4));selected.Page=clamp(selected.Page,1,pages)
  if selected==home and #home.Controls==1 then
   local ca=contentA
   local bob=app.ReducedMotion and 0 or math.sin(motionClock*1.5)*2
   local enter=1-contentA
   glow("welcomeHalo",contentLeft+35,220+bob,28,28,.65*ca,24)
   icon("welcomeHouse","home",contentLeft+39,224+bob+enter*10,accent,ca,43,0,2.5)
   label("welcomeText","Welcome.",contentLeft+97,211+enter*12,34,ink,ca,true)
  else
  for i=1,4 do local c=selected.Controls[(selected.Page-1)*4+i];if c then renderControl(c,99+(i-1)*77,i);if not app.Alive then return end end end
  end
  if pages>1 then
   label("pagenumber",selected.Page.." / "..pages,632,421,11,muted,1)
   smallButton("prevpage","left",681,410,function() selected.Page=math.max(1,selected.Page-1);replayTab(selected) end)
   smallButton("nextpage","right",719,410,function() selected.Page=math.min(pages,selected.Page+1);replayTab(selected) end)
  end
  for i=#pulsePoints,1,-1 do
   local p=pulsePoints[i];local age=motionClock-p.time
   if age>.45 or app.ReducedMotion then table.remove(pulsePoints,i)
   elseif app.Effects then
    for k=0,3 do
     local angle=k*math.pi/2+.785;local radius=4+age*23
     line("tap"..i.."_"..k,p.x+math.cos(angle)*radius,p.y+math.sin(angle)*radius,p.x+math.cos(angle)*(radius+3),p.y+math.sin(angle)*(radius+3),accent,(1-age/.45)*.65*app.EffectStrength,48)
    end
   end
  end
  if not closeConfirm and not closeConfirmClosing and not closingStarted then renderPopup() end
  renderCloseConfirm()
  if not app.Alive then return end
 end
 if renderCloseEffects(now) then return end
 y=restY
 for i=#notices,1,-1 do if now-notices[i].time>notices[i].duration+0.35 then animations[notices[i].id.."y"]=nil;table.remove(notices,i) end end
 for i,n in ipairs(notices) do
  local elapsed=now-n.time;local enter=app.ReducedMotion and 1 or clamp(elapsed/0.38,0,1);enter=1-(1-enter)^3
  local leave=clamp((elapsed-n.duration)/0.35,0,1);local opacity=enter*(1-leave*leave)
  local tx=18-(1-opacity)*340;local ty=ease(n.id.."y",18+(i-1)*80,13)
  local id="notice"..i;local c=accent
  local statusColor=n.kind=="error" and RGB(255,143,163) or n.kind=="success" and RGB(115,230,174) or accent
  rect(id.."rim",tx-1,ty-1,332,70,c,.23*opacity,13,99)
  rect(id.."base",tx,ty,330,68,tint,0.98*opacity,12,100)
  rect(id.."progress",tx+12,ty+65,306*clamp(1-elapsed/n.duration,0,1),1.5,c,.65*opacity,1,104)
  rect(id.."badge",tx+13,ty+16,33,33,c,0.17*opacity,9,101)
  txt(id.."title",n.title,tx+59,ty+14,14,ink,opacity,true,103)
  txt(id.."body",n.message,tx+59,ty+39,11,muted,opacity,false,103)
  local avatarShown=bitmap(id.."avatar",avatarBytes,tx+13,ty+16,33,33,opacity,9,102)
  if avatarShown then
   rect(id.."statusrim",tx+36,ty+40,11,11,tint,opacity,6,104)
   rect(id.."status",tx+38,ty+42,7,7,statusColor,opacity,4,105)
  end
  local strokes=paths[n.kind=="success" and "check" or n.kind=="error" and "close" or "info"]
  if not avatarShown then
  for j,p in ipairs(strokes) do
   local d=obj(id.."icon"..j,"Line");d.From=V(tx+20+p[1],ty+22+p[2]);d.To=V(tx+20+p[3],ty+22+p[4]);d.Thickness=1.6
   d.Color=c;d.Transparency=opacity;d.ZIndex=103;d.Visible=true
  end
 end
 end
 for _,e in pairs(pool) do if e.frame~=frame then e.d.Visible=false end end
end
loadAvatar()
connection=run.RenderStepped:Connect(function()
 if not app.Alive then return end
 local ok,err=pcall(render)
 if not ok then warn("rimuru stopped: "..tostring(err));app:Destroy() end
end)
print("RIMURU UI loaded. "..keyName(app.Keybind).." toggles the menu.")

-- =========================================================================
-- [ YOUR SCRIPTS HERE ]
-- =========================================================================
-- app:AddTab({Title="Combat", Icon="bolt"}, function(tab)
--   tab:AddToggle({Id="aim_on", Title="Aimbot", Description="hold to aim", Default=false})
--   tab:AddKeybind({Title="Aim key"})
--   tab:AddSlider({Id="aim_fov", Title="FOV", Min=10, Max=800, Step=1, Default=180})
--   tab:AddDropdown({Id="aim_bone", Title="Hitbox", Options={"Head","Torso","Nearest"}, Default="Head"})
-- end)
-- run.RenderStepped:Connect(function()
--   if app:GetValue("aim_on") then
--     local fov=app:GetValue("aim_fov")
--     local bone=app:GetValue("aim_bone")
--     -- your code here
--   end
-- end)
-- =========================================================================
