// --- BLE & constants ---
const FTMS_SERVICE = 0x1826, FTMS_CP = 0x2AD9, FTMS_DATA = 0x2ACD;
const REQ_CONTROL = Uint8Array.from([0x00]), START_CMD = Uint8Array.from([0x07]), PAUSE_CMD = Uint8Array.from([0x08,0x02]), STOP_CMD = Uint8Array.from([0x08,0x01]);
const mphToUnits = m => Math.round(m * 160), MIN_SPEED = 0.6, MAX_SPEED = 3.8;
const M_PER_MI = 1609.34;
const RESERVED_BIT13 = 0x2000; // observed with zeroed packets
const MAX_REASONABLE_KPH = 30;

// --- 13-bit elapsed-time wrap constants (device quirk) ---
const ELAPSED_WRAP_13S = 8192;                    // seconds in 13-bit counter (0..8191)
const ELAPSED_WRAP_THRESHOLD_HIGH = 7000;         // consider "near max" if prev raw > 7000 s
const ELAPSED_WRAP_THRESHOLD_LOW  = 200;          // consider "near zero" if new raw < 200 s

// --- NEW: Avg-speed consistency helpers ---
const AVG_SPEED_EPS = 0.05; // mph tolerance for reconciliation nudges

function milesFromMeters(m){
  // includes user distance scaling
  return (m * getDistanceScale()) / M_PER_MI;
}

/**
 * Given distance (raw meters), raw elapsed seconds (0..8191), and instantaneous mph (if any),
 * return W >= 0 so that avg speed = D / ((raw + W*8192)/3600) is within [MIN_SPEED, MAX_SPEED].
 * If mph is known, pick W that gets avg closest to mph while honoring bounds.
 */
function estimateWrapsFor(distanceM, rawElapsedS, mph){
  const Dmi = milesFromMeters(distanceM);
  if (!isFinite(Dmi) || Dmi <= 0 || !isFinite(rawElapsedS) || rawElapsedS < 0) return 0;

  // Times (sec) to cover D at the legal extremes
  const tAtMax = (Dmi / MAX_SPEED) * 3600; // minimum time allowed (fastest)
  const tAtMin = (Dmi / MIN_SPEED) * 3600; // maximum time allowed (slowest)

  // Integer wrap bounds that make elapsed in [tAtMax, tAtMin]
  let wMin = Math.ceil((tAtMax - rawElapsedS) / ELAPSED_WRAP_13S);
  let wMax = Math.floor((tAtMin - rawElapsedS) / ELAPSED_WRAP_13S);
  wMin = Math.max(0, wMin);
  if (wMax < wMin) wMax = wMin; // ensure feasible

  // Prefer matching current mph, if present
  if (isFinite(mph) && mph > 0.1){
    const mphClamped = Math.max(MIN_SPEED, Math.min(MAX_SPEED, mph));
    const tTarget = (Dmi / mphClamped) * 3600;
    let wTarget = Math.round((tTarget - rawElapsedS) / ELAPSED_WRAP_13S);
    if (wTarget < wMin) wTarget = wMin;
    if (wTarget > wMax) wTarget = wMax;
    return wTarget;
  }
  // Otherwise pick minimal wraps that avoid impossible avg (> MAX)
  return wMin;
}

/**
 * If avg speed computed with current wrap offset drifts outside bounds,
 * nudge the offset by integer wraps to bring it back. Returns wraps applied (+/-).
 */
function reconcileWrapOffsetWithDistance(distanceM, rawElapsedS){
  const Dmi = milesFromMeters(distanceM);
  if (!isFinite(Dmi) || Dmi <= 0) return 0;

  let adjS = rawElapsedS + elapsedWrapOffsetS;
  if (adjS <= 0) return 0;

  let avg = Dmi / (adjS / 3600);

  // Too fast? (avg > MAX + eps) -> add wraps (increase time)
  if (avg > MAX_SPEED + AVG_SPEED_EPS){
    const needS = (Dmi / MAX_SPEED) * 3600 - adjS; // seconds short
    const addWraps = Math.ceil(needS / ELAPSED_WRAP_13S);
    if (addWraps > 0){
      elapsedWrapOffsetS += addWraps * ELAPSED_WRAP_13S;
      return +addWraps;
    }
  }

  // Too slow? (avg < MIN - eps) -> remove wraps (decrease time)
  if (avg < MIN_SPEED - AVG_SPEED_EPS){
    const extraS = adjS - (Dmi / MIN_SPEED) * 3600; // seconds too many
    let subWraps = Math.floor(extraS / ELAPSED_WRAP_13S);
    if (subWraps > 0){
      const old = elapsedWrapOffsetS;
      elapsedWrapOffsetS = Math.max(0, elapsedWrapOffsetS - subWraps * ELAPSED_WRAP_13S);
      const deltaWraps = Math.round((elapsedWrapOffsetS - old) / ELAPSED_WRAP_13S);
      return deltaWraps;
    }
  }
  return 0;
}

// --- State ---
let dev=null,srv=null,cp=null,data=null,connected=false,running=false,target=0.6;
let baseMs=0,startMs=0,timer=null,totalDist=0,steps=0,calories=0,chart=null;
let lastKnownMph=0;          // last interpreted mph from device
let lastBleTs=0;             // Date.now() when last BLE packet processed
let lastComputeAt=Date.now();
let lastNonzeroTs=0;
let syncedTargetFromDevice=false, attachedToActiveSession=false;
let elapsedWrapOffsetS=0;    // accumulated 13-bit wrap offset
let prevRawElapsedS=0;       // tracks LAST raw elapsed time to detect true wraps

// --- NEW state for attach-time inference ---
let initialWrapGuessed = false;
let lastRawElapsedSeenS = 0; // most recent raw elapsed (0..8191)

// --- UI ---
const el={
  c:document.getElementById('connect'),toggle:document.getElementById('toggleRun'),e:document.getElementById('end'),
  up:document.getElementById('increase'),dn:document.getElementById('decrease'),spd:document.getElementById('speed'),
  st:document.getElementById('status'),dot:document.getElementById('statusDot'),elapsed:document.getElementById('elapsed'),
  dist:document.getElementById('distance'),stepsCal:document.getElementById('stepsCal'),t:document.getElementById('target'),
  log:document.getElementById('log'),stats:document.getElementById('sessionStats'),clear:document.getElementById('clearSessions'),
  backup:document.getElementById('backupSessions'),importBtn:document.getElementById('importSessions'),importFile:document.getElementById('importFile'),
  graphView:document.getElementById('graphView'),summary:document.getElementById('summaryTotals'),
  calPerMileInput:document.getElementById('calPerMileInput'),distanceScaleInput:document.getElementById('distanceScaleInput'),
  holdWhenHidden:document.getElementById('holdWhenHidden'), holdMaxMinutes:document.getElementById('holdMaxMinutes')
};

// --- Prefs ---
function getCalPerMile(){ const v=parseFloat(localStorage.getItem('calPerMile')||'47.2'); return isNaN(v)?47.2:v; }
function setCalPerMile(v){ const n=Math.max(0,parseFloat(v)); localStorage.setItem('calPerMile',String(n)); el.calPerMileInput.value=n.toFixed(1); }
function getDistanceScale(){ const v=parseFloat(localStorage.getItem('distanceScale')||'1'); return isNaN(v)?1:v; }
function setDistanceScale(v){ const n=Math.max(0.1,parseFloat(v)); localStorage.setItem('distanceScale',String(n)); el.distanceScaleInput.value=n.toFixed(2); }
function getHoldWhenHidden(){ return (localStorage.getItem('holdWhenHidden')??'true')==='true'; }
function setHoldWhenHidden(b){ localStorage.setItem('holdWhenHidden', b?'true':'false'); el.holdWhenHidden.checked=b; }
function getHoldMaxMinutes(){ const v=parseFloat(localStorage.getItem('holdMaxMinutes')||'240'); return isNaN(v)?240:v; }
function setHoldMaxMinutes(v){ const n=Math.max(1, parseFloat(v)); localStorage.setItem('holdMaxMinutes', String(n)); el.holdMaxMinutes.value = n.toFixed(0); }

// --- Log ---
const log=m=>{const t=`[${new Date().toLocaleTimeString()}] ${m}`; el.log.textContent=t+'\n'+el.log.textContent.split('\n').slice(0,100).join('\n');}

// --- UI state ---
function setConnected(state){
  connected=state;[el.toggle,el.e,el.up,el.dn,el.t].forEach(b=>b.disabled=!state);
  if(!state){ running=false; setStatus(false); el.spd.textContent='0.0 mph'; stopTimer(true); }
}
function setStatus(run){
  running=run;
  if(run){
    el.st.textContent='Running';
    el.dot.classList.remove('bg-gray-400');
    el.dot.classList.add('bg-green-500','status-running');
    el.toggle.textContent='Pause';
    startTimer();
    lastComputeAt=Date.now();
  } else {
    el.st.textContent='Idle';
    el.dot.classList.remove('bg-green-500','status-running');
    el.dot.classList.add('bg-gray-400');
    el.toggle.textContent='Start';
    pauseTimer();
  }
}
function formatHMS(sec){
  sec = Math.floor(sec);
  const h = Math.floor(sec / 3600);
  const m = Math.floor((sec % 3600) / 60);
  const s = sec % 60;
  return String(h).padStart(2,'0') + ':' + String(m).padStart(2,'0') + ':' + String(s).padStart(2,'0');
}
function startTimer(){ if(timer) return; startMs=performance.now(); timer=setInterval(()=>{const ms=baseMs+(performance.now()-startMs); el.elapsed.textContent=formatHMS(ms/1000);},250); }
function pauseTimer(){ if(!timer) return; baseMs+=performance.now()-startMs; clearInterval(timer); timer=null; }
function stopTimer(reset){ if(timer){clearInterval(timer);timer=null;} if(reset) baseMs=0; el.elapsed.textContent=formatHMS(baseMs/1000); }

// --- BLE helpers ---
async function tx(b){ if(!cp) return; try{ await cp.writeValue(b);}catch(e){ log('TX error '+e); } }
async function setSpeed(m){ const bounded=Math.max(MIN_SPEED,Math.min(MAX_SPEED,m)); const u=mphToUnits(bounded); await tx(Uint8Array.from([0x02,u&0xFF,(u>>8)&0xFF])); log(`Speed set to ${bounded.toFixed(1)} mph`); }

// --- FTMS decode ---
function decodeFtmsTreadmill(dv){
  const flags = dv.getUint16(0,true);
  let i = 2;
  const o = { flags };
  if (dv.byteLength < 4) return null;
  // C1 Instantaneous Speed (uint16, *0.01 km/h)
  const sp = dv.getUint16(i,true); i+=2; o.speedKph = sp/100;
  if (flags & (1<<1)) { o.avgSpeedKph = dv.getUint16(i,true)/100; i+=2; }
  if (flags & (1<<2)) { o.totalDistanceM = dv.getUint8(i) | (dv.getUint8(i+1)<<8) | (dv.getUint8(i+2)<<16); i+=3; }
  if (flags & (1<<3)) { o.inclinationPct = dv.getInt16(i,true)/10; i+=2; o.rampAngleDeg = dv.getInt16(i,true)/10; i+=2; }
  if (flags & (1<<4)) { o.posElevGainM = dv.getUint16(i,true)/10; i+=2; o.negElevGainM = dv.getUint16(i,true)/10; i+=2; }
  if (flags & (1<<5)) { o.instPaceKmPerMin = dv.getUint8(i)/10; i+=1; }
  if (flags & (1<<6)) { o.avgPaceKmPerMin = dv.getUint8(i)/10; i+=1; }
  if (flags & (1<<7)) { o.totalEnergyKcal = dv.getUint16(i,true); i+=2; o.energyPerHourKcal = dv.getUint16(i,true); i+=2; o.energyPerMinKcal = dv.getUint8(i); i+=1; }
  if (flags & (1<<8)) { o.heartRateBpm = dv.getUint8(i); i+=1; }
  if (flags & (1<<9)) { o.mets = dv.getUint8(i)/10; i+=1; }
  if (flags & (1<<10)) { o.elapsedTimeS = dv.getUint16(i,true); i+=2; }
  if (flags & (1<<11)) { o.remainingTimeS = dv.getUint16(i,true); i+=2; }
  if (flags & (1<<12)) { o.forceN = dv.getInt16(i,true); i+=2; o.powerW = dv.getInt16(i,true); i+=2; }
  o.bytesUsed = i; o.len = dv.byteLength;
  return o;
}
function isAllZero(o){
  const z = (v)=> (typeof v === 'number' ? v === 0 : true);
  return (o.speedKph===0) && z(o.totalDistanceM) && z(o.totalEnergyKcal) && z(o.elapsedTimeS);
}

// --- Integration tick (uses wall clock; supports long gaps when hidden) ---
function integrateTick(){
  const now = Date.now();
  let dt = (now - lastComputeAt) / 1000;
  if (dt <= 0) { lastComputeAt = now; return; }

  if (connected && running){
    const hidden = document.hidden;
    const secsSinceBle = (now - lastBleTs) / 1000;
    const holdOK = el.holdWhenHidden.checked && hidden;
    const allowHold = holdOK || secsSinceBle <= 3; // when visible, require recent BLE

    if (allowHold && lastKnownMph > 0){
      const maxGapS = Math.max(1, getHoldMaxMinutes() * 60);
      dt = Math.min(dt, maxGapS);
      const scale = getDistanceScale();
      totalDist += (lastKnownMph * M_PER_MI / 3600) * dt * scale;
      const miles = totalDist / M_PER_MI;
      steps = Math.floor(totalDist / 0.8);
      calories = miles * getCalPerMile();
      el.dist.textContent = miles.toFixed(2) + ' mi';
      el.stepsCal.textContent = `${steps} / ${calories.toFixed(2)}`;
    }
  }
  lastComputeAt = now;
}

// Background timer (throttled in background; we catch up on next tick)
setInterval(integrateTick, 1000);
document.addEventListener('visibilitychange', () => { integrateTick(); });

// --- Connect ---
el.c.onclick=async()=>{
  try{
    if(dev&&dev.gatt.connected){ dev.gatt.disconnect(); setConnected(false); return; }
    dev=await navigator.bluetooth.requestDevice({filters:[{services:[FTMS_SERVICE]}]});
    dev.addEventListener('gattserverdisconnected',()=>{
      syncedTargetFromDevice=false;
      attachedToActiveSession=false;
      elapsedWrapOffsetS=0;        // reset wrap accumulator
      prevRawElapsedS=0;           // reset last raw marker
      // NEW resets
      initialWrapGuessed=false;
      lastRawElapsedSeenS=0;

      setStatus(false);
      saveSession();
      setConnected(false);
    });
    srv=await dev.gatt.connect();
    const svc=await srv.getPrimaryService(FTMS_SERVICE);
    cp=await svc.getCharacteristic(FTMS_CP);
    data=await svc.getCharacteristic(FTMS_DATA);
    await data.startNotifications();

    data.addEventListener('characteristicvaluechanged',evt=>{
      const dv=evt.target.value; 
      const pkt = decodeFtmsTreadmill(dv);
      if(!pkt){ return; }

      // Basic sanity
      if (pkt.speedKph < 0 || pkt.speedKph > MAX_REASONABLE_KPH) { log('Ignored out-of-range speed'); return; }

      // Ignore known bogus "all zero" frames (often with reserved bit 13 set)
      if ((pkt.flags & RESERVED_BIT13) && isAllZero(pkt)) {
        log('Ignored zeroed FTMS packet (reserved flag set)');
        return; // don't overwrite lastKnownMph or timers
      }

      const now = Date.now();
      const mph = pkt.speedKph * 0.621371;

      // If everything reports 0 but we were just moving, treat as transient glitch
      if (isAllZero(pkt)) {
        if (now - lastNonzeroTs < 5000) { // 5s grace
          log('Ignored transient all-zero frame');
          return;
        }
      }

      // Accept packet
      lastBleTs = now;
      lastKnownMph = mph;
      el.spd.textContent = mph.toFixed(1) + ' mph';

      // If we connected mid-session, auto-mark running and sync the target control once
      if (mph > 0.1 && !running) {
        setStatus(true);
        attachedToActiveSession = true;
        if (!syncedTargetFromDevice) {
          const rounded = Math.round(mph*10)/10;
          target = Math.max(MIN_SPEED, Math.min(MAX_SPEED, rounded));
          el.t.value = target.toFixed(1);
          syncedTargetFromDevice = true;
          log(`Synced control target to device speed ${el.t.value} mph`);
        }
        log('Detected treadmill already running');
      }

      if (mph > 0.1) lastNonzeroTs = now;
      if (mph <= 0.1 && running && (now - lastNonzeroTs) > 5000) { setStatus(false); }

      // --- Elapsed time handling (with observed rollovers + attach-time inference) ---
      if (typeof pkt.elapsedTimeS === 'number'){
        const rawS = pkt.elapsedTimeS;

        // NEW: remember latest raw for later reconciliation/estimation
        lastRawElapsedSeenS = rawS;

        // NEW: If we attached mid-session and haven't estimated prior wraps yet,
        // do it as soon as distance is available in the same packet.
        if (attachedToActiveSession && !initialWrapGuessed && typeof pkt.totalDistanceM === 'number'){
          const wraps = estimateWrapsFor(pkt.totalDistanceM, rawS, mph);
          if (wraps > 0){
            elapsedWrapOffsetS = wraps * ELAPSED_WRAP_13S;
            const Dmi = milesFromMeters(pkt.totalDistanceM);
            const avg = Dmi / ((rawS + elapsedWrapOffsetS)/3600);
            log(`Estimated ${wraps} prior elapsed wrap(s) at attach (avg≈${avg.toFixed(2)} mph)`);
          } else {
            log('Estimated 0 prior elapsed wraps at attach');
          }
          initialWrapGuessed = true;
        }

        // Detect a true rollover: previous raw near max, new raw near zero
        if (prevRawElapsedS > ELAPSED_WRAP_THRESHOLD_HIGH && rawS < ELAPSED_WRAP_THRESHOLD_LOW) {
          elapsedWrapOffsetS += ELAPSED_WRAP_13S;
          log('Detected true 13-bit elapsed time rollover; continuing session');
        }

        const adjS = rawS + elapsedWrapOffsetS;
        const ms = adjS * 1000;

        // Update display/timebase
        if (ms >= baseMs) {
          baseMs = ms;
          if (timer){ clearInterval(timer); timer=null; }
          if (running) startTimer(); else el.elapsed.textContent = formatHMS(adjS);
        }

        // Update previous raw AFTER checks so detection uses prior packet
        prevRawElapsedS = rawS;
      }

      // --- Distance handling (with reconciliation) ---
      if (typeof pkt.totalDistanceM === 'number'){
        const scaledM = pkt.totalDistanceM * getDistanceScale();
        if (scaledM >= totalDist - 0.5) { totalDist = scaledM; }
        const miles = totalDist / M_PER_MI;
        steps = Math.floor(totalDist / 0.8);
        if (typeof pkt.totalEnergyKcal === 'number' && pkt.totalEnergyKcal > 0) {
          calories = pkt.totalEnergyKcal;
        } else {
          calories = miles * getCalPerMile();
        }
        el.dist.textContent = miles.toFixed(2) + ' mi';
        el.stepsCal.textContent = `${steps} / ${calories.toFixed(2)}`;

        // NEW: If we attached mid-session but couldn't estimate earlier (no elapsed block hit yet),
        // or if the earlier packet lacked distance, do the attach-time estimate now.
        if (attachedToActiveSession && !initialWrapGuessed && lastRawElapsedSeenS > 0){
          const wraps = estimateWrapsFor(pkt.totalDistanceM, lastRawElapsedSeenS, lastKnownMph);
          if (wraps > 0){
            elapsedWrapOffsetS = wraps * ELAPSED_WRAP_13S;
            const Dmi = milesFromMeters(pkt.totalDistanceM);
            const avg = Dmi / ((lastRawElapsedSeenS + elapsedWrapOffsetS)/3600);
            log(`Estimated ${wraps} prior elapsed wrap(s) at attach (avg≈${avg.toFixed(2)} mph)`);
          } else {
            log('Estimated 0 prior elapsed wraps at attach');
          }
          initialWrapGuessed = true;

          // ensure UI time reflects new offset immediately
          const adjS0 = lastRawElapsedSeenS + elapsedWrapOffsetS;
          const ms0 = adjS0 * 1000;
          if (ms0 >= baseMs) {
            baseMs = ms0;
            if (timer){ clearInterval(timer); timer=null; }
            if (running) startTimer(); else el.elapsed.textContent = formatHMS(adjS0);
          }
        }

        // NEW: Ongoing reconciliation (rare; guards against +/-1 wrap mis-guess as distance advances)
        if (lastRawElapsedSeenS > 0){
          const deltaWraps = reconcileWrapOffsetWithDistance(pkt.totalDistanceM, lastRawElapsedSeenS);
          if (deltaWraps !== 0){
            const adjS1 = lastRawElapsedSeenS + elapsedWrapOffsetS;
            const ms1 = adjS1 * 1000;
            if (ms1 >= 0){
              baseMs = ms1;
              if (timer){ clearInterval(timer); timer=null; }
              if (running) startTimer(); else el.elapsed.textContent = formatHMS(adjS1);
            }
            const Dmi = milesFromMeters(pkt.totalDistanceM);
            const avg = Dmi / ((lastRawElapsedSeenS + elapsedWrapOffsetS)/3600);
            log(`Adjusted wrap offset by ${deltaWraps} to satisfy speed bounds (avg≈${avg.toFixed(2)} mph)`);
          }
        }
      } else {
        // No distance field: let integrator update based on lastKnownMph
        integrateTick();
      }
    });

    await tx(REQ_CONTROL);
    setConnected(true);
    log('Connected');
  }catch(e){ log('Error '+e); setConnected(false); }
};

// --- Controls ---
el.toggle.onclick=async()=>{ if(!connected) return; if(!running){ setStatus(true); attachedToActiveSession=false; syncedTargetFromDevice=false; await tx(START_CMD); await new Promise(r=>setTimeout(r,150)); target=MIN_SPEED; el.t.value=target.toFixed(1); await setSpeed(target); } else { setStatus(false); await tx(PAUSE_CMD); } };
el.e.onclick=async()=>{ setStatus(false); stopTimer(false); saveSession(); await tx(STOP_CMD); updateChart(); };
el.up.onclick=async()=>{ if(!connected) return; let v=parseFloat(el.t.value)||0; v=Math.min(MAX_SPEED,v+0.1); el.t.value=v.toFixed(1); target=v; await setSpeed(v); };
el.dn.onclick=async()=>{ if(!connected) return; let v=parseFloat(el.t.value)||0; v=Math.max(MIN_SPEED,v-0.1); el.t.value=v.toFixed(1); target=v; await setSpeed(v); };

// --- Sessions ---
function loadSessions(){ try { return JSON.parse(localStorage.getItem('walkingpad_sessions')||'[]'); } catch(e){ return []; } }
function saveSessions(a){ localStorage.setItem('walkingpad_sessions', JSON.stringify(a)); }
function saveSession(){
  const miles=totalDist/M_PER_MI;
  if(miles>0){ const s=loadSessions(); s.push({ time:new Date().toISOString(), duration:el.elapsed.textContent, distance:miles.toFixed(2), steps:steps, calories:calories.toFixed(2) }); saveSessions(s); renderSessions(); updateChart(); }
  totalDist=0; steps=0; calories=0; baseMs=0; startMs=0; lastBleTs=0; elapsedWrapOffsetS=0; prevRawElapsedS=0; lastComputeAt=Date.now();
  // NEW resets
  initialWrapGuessed=false; lastRawElapsedSeenS=0;

  el.elapsed.textContent='00:00:00'; el.dist.textContent='0.00 mi'; el.stepsCal.textContent='0 / 0.00';
}
function renderSessions(){ const s=loadSessions(); if(s.length===0){ el.stats.innerHTML='<p class="text-gray-500 text-center">No sessions yet.</p>'; return; } el.stats.innerHTML = s.slice().reverse().map(x=>`<div class='border-b py-1'><strong>${new Date(x.time).toLocaleString()}</strong><br><span>${x.duration}</span> — <span>${x.distance} mi</span> — <span>${x.steps} steps</span> — <span>${x.calories}</span></div>`).join(''); }

// --- Import/Export ---
el.clear.onclick=()=>{ if(window.confirm('Are you sure?')){ localStorage.removeItem('walkingpad_sessions'); renderSessions(); updateChart(); updateSummary(); } };
el.backup.onclick=()=>{ const d=JSON.stringify(loadSessions(),null,2); const b=new Blob([d],{type:'application/json'}); const u=URL.createObjectURL(b); const a=document.createElement('a'); a.href=u; a.download='walkingpad_sessions_backup.json'; a.click(); URL.revokeObjectURL(u); };
el.importBtn.onclick=()=>el.importFile.click();
el.importFile.onchange=async e=>{ const f=e.target.files[0]; if(!f) return; const text=await f.text(); const incoming=JSON.parse(text); const existing=loadSessions(); const merged=[...existing,...incoming]; saveSessions(merged); renderSessions(); updateChart(); updateSummary(); e.target.value=''; };

// --- Charts & summary ---
function groupSessions(period) {
  const sessions = loadSessions();
  const buckets = {};

  sessions.forEach(session => {
    const date = new Date(session.time);
    let key = '';

    switch (period) {
      case 'day':
        key = date.toLocaleDateString();
        break;
      case 'week':
        // Calculation for week number
        const startOfYear = new Date(date.getFullYear(), 0, 1);
        const pastDays = (date - startOfYear) / 86400000;
        const weekNum = Math.ceil((pastDays + startOfYear.getDay() + 1) / 7);
        key = 'Week ' + weekNum + ' - ' + date.getFullYear();
        break;
      case 'month':
        key = date.toLocaleString('default', { month: 'short' }) + ' ' + date.getFullYear();
        break;
      case 'year':
        key = date.getFullYear();
        break;
    }

    buckets[key] = (buckets[key] || 0) + parseFloat(session.distance);
  });

  return {
    labels: Object.keys(buckets),
    data: Object.values(buckets)
  };
}

function updateChart() {
  const ctx = document.getElementById('distanceChart').getContext('2d');
  const period = 'day'; // Default view
  const graphData = groupSessions(period);

  if (chart) {
    chart.destroy();
  }

  chart = new Chart(ctx, {
    type: 'line',
    data: {
      labels: graphData.labels,
      datasets: [{
        label: 'Cumulative Distance',
        data: graphData.data,
        borderColor: '#3b82f6',
        backgroundColor: 'rgba(59,130,246,0.2)',
        fill: true,
        tension: 0.3
      }]
    },
    options: {
      responsive: true,
      scales: {
        y: {
          beginAtZero: true,
          title: {
            display: true,
            text: 'Miles'
          }
        }
      }
    }
  });

  el.summary.textContent = '';
  updateSummary();
}

// --- NEW: Summary totals ---
function updateSummary() {
  const sessions = loadSessions();
  let today = 0, week = 0, month = 0, year = 0;
  const now = new Date();
  const todayStr = now.toLocaleDateString();
  const yearNum = now.getFullYear();
  const monthNum = now.getMonth();
  // Find Monday of current week
  const monday = new Date(now);
  monday.setHours(0,0,0,0);
  monday.setDate(now.getDate() - ((now.getDay() + 6) % 7)); // Monday as start

  sessions.forEach(s => {
    const d = new Date(s.time);
    const dist = parseFloat(s.distance) || 0;
    // Today
    if (d.toLocaleDateString() === todayStr) today += dist;
    // This week (starting Monday)
    const weekStart = new Date(d);
    weekStart.setHours(0,0,0,0);
    weekStart.setDate(d.getDate() - ((d.getDay() + 6) % 7));
    if (weekStart.getTime() === monday.getTime()) week += dist;
    // This month
    if (d.getFullYear() === yearNum && d.getMonth() === monthNum) month += dist;
    // This year
    if (d.getFullYear() === yearNum) year += dist;
  });

  el.summary.innerHTML = `
    <div class="grid grid-cols-2 gap-2 text-lg">
      <div><span class="font-bold">Today:</span> ${today.toFixed(2)} mi</div>
      <div><span class="font-bold">This Week:</span> ${week.toFixed(2)} mi</div>
      <div><span class="font-bold">This Month:</span> ${month.toFixed(2)} mi</div>
      <div><span class="font-bold">This Year:</span> ${year.toFixed(2)} mi</div>
    </div>
  `;
}

// --- Init ---
setCalPerMile(getCalPerMile()); 
el.calPerMileInput.addEventListener('change',e=>setCalPerMile(e.target.value));
setDistanceScale(getDistanceScale()); 
el.distanceScaleInput.addEventListener('change',e=>setDistanceScale(e.target.value));
setHoldWhenHidden(getHoldWhenHidden()); 
el.holdWhenHidden.addEventListener('change',e=>setHoldWhenHidden(e.target.checked));
setHoldMaxMinutes(getHoldMaxMinutes()); 
el.holdMaxMinutes.addEventListener('change',e=>setHoldMaxMinutes(e.target.value));
renderSessions(); 
updateChart();
updateSummary(); // <-- ensure summary is shown on load