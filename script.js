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
function getDistanceScale(){ const v=parseFloat(localStorage.getItem('distanceScale')||'1'); return isNaN(v)?