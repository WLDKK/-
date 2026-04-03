// ==UserScript==
// @name         超星学习通名著阅读脚本
// @namespace    https://mooc1.chaoxing.com/
// @version      3.7.0
// @description  专为《名著阅读》刷时长打造，可以缩小框或切到后台刷时长，自动滚动 + 动态等待翻页 + 刷新/SPA恢复；支持快/中/慢和无级变速、翻页秒数自定义。完全免费无广，WLD版权所有，此脚本供研究学习使用，不承担任何不当使用造成的后果。刷阅读时长请选择页数较多的书，此插件仅在阅读页面完全加载完成后可正常工作，为确保稳定运行，建议等他完整翻页一次后再切入后台。如有问题和建议，请联系1310205058@qq.com或直接添加本人qq1310205058
// @author       WLD
// @license      MIT
// @match        *://mooc1.chaoxing.com/*
// @match        *://mooc1-1.chaoxing.com/*
// @match        *://mooc1-2.chaoxing.com/*
// @match        *://*.chaoxing.com/mycourse/*
// @match        *://*.chaoxing.com/course/*
// @match        *://*.chaoxing.com/knowledge/*
// @match        *://*.chaoxing.com/ananas/*
// @grant        none
// @run-at       document-end
// @downloadURL none
// ==/UserScript==
(function () {
  'use strict';
  if (window.top !== window.self) return;

  const CFG = {
    scrollInterval: 80,
    mouseMoveInterval: 6000,
    maxTimerDriftCompensate: 40,
    foregroundMaxTimerDriftCompensate: 4,
    maxStepPerTick: 20,
    targetCacheMs: 2400,
    scrollElCacheMs: 2400,
    scrollNoProgressLimit: 14,
    contextCheckIntervalMs: 1800,
    nonReadingLogGapMs: 12000,
    waitTimeout: 25000,
    waitPollInterval: 180,
    nextAssistRetryMs: 3200,
    nextInFlightTimeoutMs: 38000,
    atBottomRescueMs: 5000,
    minTargetScore: 2.6,
    pageReadySelectors: [
      '#content',
      '.mainCon',
      '.article',
      '.chapter',
      '.reader-content',
      '.textLayer',
      'article',
      '.book-content',
      '.bookReader',
      '.book-reader',
      '.read-content',
      '.view-content',
      '[class*="reader"]',
      '[class*="read"]'
    ],
    speedMin: 0.5,
    speedMax: 8,
    speedStep: 0.1,
    speedPresetMap: { slow: 1.2, medium: 3.2, fast: 5.2 },
    speedLabel: { slow: '慢', medium: '中', fast: '快', custom: '无级' },
    bottomPauseMin: 1,
    bottomPauseMax: 600,
    enableBackgroundKeepAlive: true,
    keepAlivePingInterval: 15000,
    keepAliveOscFrequency: 18000,
    keepAliveGain: 0.00001,
    audioPulseTickMs: 180,
    audioPulseRespawnMs: 6500,
    workerTickInterval: 180,
    workerAssistGapVisibleMs: 420,
    workerAssistGapHiddenMs: 120,
    workerMouseAssistMs: 4500,
    workerRespawnGapMs: 5000,
    hiddenHardRecoverMs: 18000,
    watchdogInterval: 2500,
    watchdogStallMs: 12000,
    nextFailureBackoffBaseMs: 1800,
    nextFailureBackoffMaxMs: 12000,
    logLimit: 20,
    resumeTTL: 24 * 60 * 60 * 1000
  };

  const NEXT_SELECTORS = [
    '.orientationright',
    '.jb_btn.jb_btn_92',
    '.nextBtn',
    '#nextBtn',
    'a.jb_btn[title="下一节"]',
    'a[title="下一页"]',
    '.btn-next',
    '.next_btn',
    '[class*="nextBtn"]',
    '[class*="next_btn"]',
    '[class*="next-page"]',
    '[class*="page-next"]',
    '[aria-label*="下一"]',
    '[title*="下一"]',
    '#prev_next .right a',
    '.prev_next .right a',
    '.prevNextFocus .right a'
  ];

  const PAGE_INDEX_SELECTORS = [
    '.current',
    '.curr',
    '.current-page',
    '.page-current',
    '.pageNo',
    '.page-no',
    '.currentPage',
    '[class*="pageCurrent"]',
    '[class*="currentPage"]',
    '[class*="pageNo"]',
    '[class*="pageIndex"]'
  ];

  const STORE_KEY = 'cx:auto-read:state:v3_7';
  const LEGACY_STORE_KEYS = ['cx:auto-read:state:v3_6'];
  const DEFAULT_STATE = {
    running: false,
    lastAction: 'idle',
    panelPos: null,
    updatedAt: 0,
    href: '',
    settings: {
      speedPreset: 'medium',
      speedValue: CFG.speedPresetMap.medium,
      bottomPauseSec: 12
    }
  };

  let state = loadState();
  let scrollTid = null;
  let mouseTid = null;
  let nextTid = null;
  let waitAborter = null;
  let atBottom = false;
  let atBottomSince = 0;
  let nextDueAt = 0;
  let nextInFlight = false;
  let nextInFlightAt = 0;
  let nextAssistTid = null;
  let lastNextAssistAt = 0;
  let lastScrollTs = 0;
  let keepAliveCtx = null;
  let keepAliveOsc = null;
  let keepAliveGain = null;
  let keepAliveDest = null;
  let keepAliveAudio = null;
  let audioTickerNode = null;
  let audioTickerUrl = '';
  let audioTickerMode = '';
  let audioTickerStarting = false;
  let keepAlivePingTid = null;
  let keepAliveLastLogAt = 0;
  let workerTicker = null;
  let workerTickerUrl = '';
  let watchdogTid = null;
  let lastHeartbeatTs = 0;
  let lastWorkerTickTs = 0;
  let lastWorkerRespawnTs = 0;
  let lastAudioPulseTs = 0;
  let targetCache = null;
  let targetCacheAt = 0;
  let scrollElCache = null;
  let scrollElCacheDoc = null;
  let scrollElCacheAt = 0;
  let scrollNoProgressTicks = 0;
  let lastEffectiveScrollTs = 0;
  let nextFailStreak = 0;
  let lastWorkerMouseTs = 0;
  let lastNonReadingCheckTs = 0;
  let nonReadingCached = false;
  let nonReadingHint = '';
  let lastNonReadingLogAt = 0;
  let routeChangeTid = null;
  let inited = false;

  const nativeDocProto = (typeof Document !== 'undefined') ? Document.prototype : null;
  const nativeHiddenGetter = nativeDocProto ? (Object.getOwnPropertyDescriptor(nativeDocProto, 'hidden') || {}).get : null;
  const nativeVisibilityGetter = nativeDocProto ? (Object.getOwnPropertyDescriptor(nativeDocProto, 'visibilityState') || {}).get : null;

  function clamp(v, min, max) {
    return Math.min(max, Math.max(min, v));
  }

  function fixed1(n) {
    return Math.round(n * 10) / 10;
  }

  function invalidateTargetCache() {
    targetCache = null;
    targetCacheAt = 0;
    scrollElCache = null;
    scrollElCacheDoc = null;
    scrollElCacheAt = 0;
    lastNonReadingCheckTs = 0;
    nonReadingCached = false;
    nonReadingHint = '';
  }

  function loadStateByKey(key) {
    try {
      const raw = localStorage.getItem(key);
      if (!raw) return null;
      const parsed = JSON.parse(raw);
      if (!parsed || typeof parsed !== 'object') return null;
      return parsed;
    } catch (e) {
      return null;
    }
  }

  function normalizeSettings(raw) {
    const s = Object.assign({}, DEFAULT_STATE.settings, raw || {});

    if (!['slow', 'medium', 'fast', 'custom'].includes(s.speedPreset)) {
      s.speedPreset = 'medium';
    }

    let speed = Number.parseFloat(s.speedValue);
    if (!Number.isFinite(speed)) {
      speed = CFG.speedPresetMap[s.speedPreset] || CFG.speedPresetMap.medium;
    }
    speed = fixed1(clamp(speed, CFG.speedMin, CFG.speedMax));
    if (s.speedPreset !== 'custom' && CFG.speedPresetMap[s.speedPreset]) {
      speed = CFG.speedPresetMap[s.speedPreset];
    }
    s.speedValue = speed;

    let sec = Number.parseFloat(s.bottomPauseSec);
    if (!Number.isFinite(sec)) sec = 12;
    s.bottomPauseSec = Math.round(clamp(sec, CFG.bottomPauseMin, CFG.bottomPauseMax));

    return s;
  }

  function normalizeState(raw) {
    const st = Object.assign({}, DEFAULT_STATE, raw || {});
    st.settings = normalizeSettings(st.settings);
    return st;
  }

  function loadState() {
    try {
      const keys = [STORE_KEY].concat(LEGACY_STORE_KEYS);
      let parsed = null;
      let sourceKey = '';

      for (let i = 0; i < keys.length; i++) {
        const candidate = loadStateByKey(keys[i]);
        if (!candidate) continue;
        parsed = candidate;
        sourceKey = keys[i];
        break;
      }

      const st = normalizeState(parsed || {});

      if (st.running && st.updatedAt && (Date.now() - st.updatedAt > CFG.resumeTTL)) {
        st.running = false;
        st.lastAction = 'stale-reset';
      }

      if (sourceKey && sourceKey !== STORE_KEY) {
        try { localStorage.setItem(STORE_KEY, JSON.stringify(st)); } catch (e) {}
      }
      return st;
    } catch (e) {
      return normalizeState({});
    }
  }

  function saveState(patch) {
    const next = Object.assign({}, state, patch || {});
    if (patch && patch.settings) {
      next.settings = normalizeSettings(Object.assign({}, state.settings, patch.settings));
    } else {
      next.settings = normalizeSettings(next.settings);
    }
    next.updatedAt = Date.now();
    next.href = location.href;
    state = next;
    try { localStorage.setItem(STORE_KEY, JSON.stringify(state)); } catch (e) {}
    return state;
  }

  function getSpeed() {
    return state.settings.speedValue;
  }

  function getBottomPauseMs() {
    return state.settings.bottomPauseSec * 1000;
  }

  function isActuallyHidden() {
    try {
      if (nativeHiddenGetter) return !!nativeHiddenGetter.call(document);
      if (nativeVisibilityGetter) return nativeVisibilityGetter.call(document) === 'hidden';
    } catch (e) {}
    return false;
  }

  function getHeartbeatLimitMs() {
    const base = CFG.watchdogStallMs;
    const pagePause = getBottomPauseMs() + 4000;
    return Math.max(base, pagePause);
  }

  function heartbeat() {
    lastHeartbeatTs = Date.now();
  }

  function setupAntiDetect() {
    try {
      Object.defineProperty(document, 'hidden', {
        get: function () { return false; },
        configurable: true
      });
      Object.defineProperty(document, 'visibilityState', {
        get: function () { return 'visible'; },
        configurable: true
      });
      Object.defineProperty(document, 'webkitHidden', {
        get: function () { return false; },
        configurable: true
      });
      Object.defineProperty(document, 'webkitVisibilityState', {
        get: function () { return 'visible'; },
        configurable: true
      });
    } catch (e) {}

    try { document.hasFocus = function () { return true; }; } catch (e) {}
    try { window.hasFocus = function () { return true; }; } catch (e) {}

    document.addEventListener('visibilitychange', function (e) {
      if (state.running) {
        if (isActuallyHidden()) {
          startAudioKeepAlive();
          maybeLogKeepAlive('页面进入后台，已启用保活');
        } else {
          refreshRuntimeAfterLifecycle('visible');
        }
      }
      e.stopImmediatePropagation();
    }, true);
    document.addEventListener('webkitvisibilitychange', function (e) {
      e.stopImmediatePropagation();
    }, true);
    document.addEventListener('freeze', function (e) {
      maybeLogKeepAlive('检测到页面冻结事件', 5000);
      e.stopImmediatePropagation();
    }, true);
    document.addEventListener('resume', function (e) {
      if (state.running) refreshRuntimeAfterLifecycle('resume-event');
      e.stopImmediatePropagation();
    }, true);
    window.addEventListener('blur', function (e) {
      e.stopImmediatePropagation();
    }, true);
    document.addEventListener('blur', function (e) {
      e.stopImmediatePropagation();
    }, true);
    window.addEventListener('focusout', function (e) {
      e.stopImmediatePropagation();
    }, true);
    window.addEventListener('pagehide', function (e) {
      e.stopImmediatePropagation();
    }, true);
  }

  function maybeLogKeepAlive(msg, minGapMs) {
    const gap = typeof minGapMs === 'number' ? minGapMs : 12000;
    const now = Date.now();
    if (now - keepAliveLastLogAt < gap) return;
    keepAliveLastLogAt = now;
    log(msg);
  }

  function driveBackgroundPulse(now) {
    if (!state.running) return;
    const ts = typeof now === 'number' ? now : Date.now();
    const hidden = isActuallyHidden();
    const minGap = hidden ? CFG.workerAssistGapHiddenMs : CFG.workerAssistGapVisibleMs;

    if (ts - lastScrollTs >= minGap) {
      doScroll();
    }

    if (hidden && atBottom && !nextInFlight && nextDueAt && ts >= nextDueAt) {
      if (nextTid) {
        clearTimeout(nextTid);
        nextTid = null;
      }
      nextDueAt = 0;
      clickNextAndWait(getTarget());
      return;
    }

    if (hidden && nextInFlight && (!lastNextAssistAt || ts - lastNextAssistAt >= CFG.nextAssistRetryMs)) {
      lastNextAssistAt = ts;
      const t = getTarget();
      const docs = collectDocs(t && t.doc);
      const btn = findNextButton(docs, true);
      if (btn) {
        dispatchClick(btn);
      } else {
        triggerNextFallback(t);
      }
    }

    if (hidden && ts - lastWorkerMouseTs >= CFG.workerMouseAssistMs) {
      lastWorkerMouseTs = ts;
      simulateMouse();
    }
  }

  function stopAudioPulseTicker() {
    audioTickerStarting = false;

    if (audioTickerNode) {
      try {
        if (audioTickerMode === 'worklet' && audioTickerNode.port) {
          audioTickerNode.port.onmessage = null;
        } else if (audioTickerMode === 'script') {
          audioTickerNode.onaudioprocess = null;
        }
      } catch (e) {}

      try { audioTickerNode.disconnect(); } catch (e) {}
      audioTickerNode = null;
    }

    if (audioTickerUrl) {
      try { URL.revokeObjectURL(audioTickerUrl); } catch (e) {}
      audioTickerUrl = '';
    }

    audioTickerMode = '';
    lastAudioPulseTs = 0;
  }

  function startScriptAudioPulseTicker() {
    if (!keepAliveCtx || audioTickerNode || typeof keepAliveCtx.createScriptProcessor !== 'function') return;

    try {
      const processor = keepAliveCtx.createScriptProcessor(2048, 0, 1);
      let lastTick = 0;
      processor.onaudioprocess = function () {
        const now = Date.now();
        if (now - lastTick < Math.max(80, CFG.audioPulseTickMs - 20)) return;
        lastTick = now;
        lastAudioPulseTs = now;
        driveBackgroundPulse(now);
      };
      processor.connect(keepAliveGain || keepAliveCtx.destination);
      audioTickerNode = processor;
      audioTickerMode = 'script';
      lastAudioPulseTs = Date.now();
      maybeLogKeepAlive('音频脉冲保活已启动', 8000);
    } catch (e) {}
  }

  function startAudioPulseTicker() {
    if (!keepAliveCtx || audioTickerNode || audioTickerStarting) return;

    if (!keepAliveCtx.audioWorklet || typeof keepAliveCtx.audioWorklet.addModule !== 'function') {
      startScriptAudioPulseTicker();
      return;
    }

    audioTickerStarting = true;
    try {
      const src =
        'class CXPulseProcessor extends AudioWorkletProcessor {' +
        'constructor(){super();this.acc=0;this.frames=Math.max(128,Math.floor(sampleRate*' + (CFG.audioPulseTickMs / 1000).toFixed(4) + '));}' +
        'process(inputs,outputs){this.acc+=128;if(this.acc>=this.frames){this.acc=0;this.port.postMessage(1);}return true;}' +
        '}' +
        'registerProcessor("cx-pulse-processor",CXPulseProcessor);';
      const blob = new Blob([src], { type: 'text/javascript' });
      audioTickerUrl = URL.createObjectURL(blob);
      keepAliveCtx.audioWorklet.addModule(audioTickerUrl).then(function () {
        audioTickerStarting = false;
        if (!keepAliveCtx || audioTickerNode) return;

        try {
          const node = new AudioWorkletNode(keepAliveCtx, 'cx-pulse-processor', {
            numberOfInputs: 0,
            numberOfOutputs: 1,
            outputChannelCount: [1]
          });
          node.port.onmessage = function () {
            const now = Date.now();
            lastAudioPulseTs = now;
            driveBackgroundPulse(now);
          };
          node.connect(keepAliveGain || keepAliveCtx.destination);
          audioTickerNode = node;
          audioTickerMode = 'worklet';
          lastAudioPulseTs = Date.now();
          maybeLogKeepAlive('音频脉冲保活已启动', 8000);
        } catch (e) {
          stopAudioPulseTicker();
          startScriptAudioPulseTicker();
        }
      }).catch(function () {
        audioTickerStarting = false;
        stopAudioPulseTicker();
        startScriptAudioPulseTicker();
      });
    } catch (e) {
      audioTickerStarting = false;
      stopAudioPulseTicker();
      startScriptAudioPulseTicker();
    }
  }

  function startAudioKeepAlive() {
    if (!CFG.enableBackgroundKeepAlive || !state.running) return;

    const AudioCtor = window.AudioContext || window.webkitAudioContext;
    if (!AudioCtor) return;

    try {
      if (!keepAliveCtx) {
        keepAliveCtx = new AudioCtor();
        keepAliveGain = keepAliveCtx.createGain();
        keepAliveGain.gain.value = CFG.keepAliveGain;
        keepAliveOsc = keepAliveCtx.createOscillator();
        keepAliveOsc.type = 'sine';
        keepAliveOsc.frequency.value = CFG.keepAliveOscFrequency;
        keepAliveOsc.connect(keepAliveGain);
        keepAliveGain.connect(keepAliveCtx.destination);
        keepAliveOsc.start();

        if (typeof keepAliveCtx.createMediaStreamDestination === 'function') {
          keepAliveDest = keepAliveCtx.createMediaStreamDestination();
          keepAliveGain.connect(keepAliveDest);

          keepAliveAudio = document.createElement('audio');
          keepAliveAudio.autoplay = true;
          keepAliveAudio.loop = true;
          keepAliveAudio.preload = 'auto';
          keepAliveAudio.playsInline = true;
          keepAliveAudio.style.display = 'none';
          keepAliveAudio.srcObject = keepAliveDest.stream;
          try { document.documentElement.appendChild(keepAliveAudio); } catch (e) {}
        }
      }

      if (keepAliveCtx.state === 'suspended') {
        const p = keepAliveCtx.resume();
        if (p && typeof p.catch === 'function') p.catch(function () {});
      }

      startAudioPulseTicker();

      if (keepAliveAudio && keepAliveAudio.paused) {
        const playPromise = keepAliveAudio.play();
        if (playPromise && typeof playPromise.catch === 'function') playPromise.catch(function () {});
      }

      if (!keepAlivePingTid) {
        keepAlivePingTid = setInterval(function () {
          if (!state.running || !keepAliveCtx) return;
          if (keepAliveCtx.state === 'suspended') {
            const p = keepAliveCtx.resume();
            if (p && typeof p.catch === 'function') p.catch(function () {});
          }
          if (!audioTickerNode || (lastAudioPulseTs && Date.now() - lastAudioPulseTs > CFG.audioPulseRespawnMs)) {
            stopAudioPulseTicker();
            startAudioPulseTicker();
          }
          if (keepAliveAudio && keepAliveAudio.paused) {
            const playPromise = keepAliveAudio.play();
            if (playPromise && typeof playPromise.catch === 'function') playPromise.catch(function () {});
          }
        }, CFG.keepAlivePingInterval);
      }
    } catch (e) {}
  }

  function stopAudioKeepAlive() {
    if (keepAlivePingTid) {
      clearInterval(keepAlivePingTid);
      keepAlivePingTid = null;
    }

    stopAudioPulseTicker();

    if (keepAliveOsc) {
      try { keepAliveOsc.stop(); } catch (e) {}
      try { keepAliveOsc.disconnect(); } catch (e) {}
      keepAliveOsc = null;
    }

    if (keepAliveGain) {
      try { keepAliveGain.disconnect(); } catch (e) {}
      keepAliveGain = null;
    }

    if (keepAliveDest) {
      try { keepAliveDest.disconnect(); } catch (e) {}
      keepAliveDest = null;
    }

    if (keepAliveAudio) {
      try { keepAliveAudio.pause(); } catch (e) {}
      try { keepAliveAudio.srcObject = null; } catch (e) {}
      try { if (keepAliveAudio.parentNode) keepAliveAudio.parentNode.removeChild(keepAliveAudio); } catch (e) {}
      keepAliveAudio = null;
    }

    if (keepAliveCtx) {
      const ctx = keepAliveCtx;
      keepAliveCtx = null;
      try {
        const p = ctx.close();
        if (p && typeof p.catch === 'function') p.catch(function () {});
      } catch (e) {}
    }
  }

  function startWorkerTicker() {
    if (!state.running || workerTicker || typeof Worker === 'undefined' || typeof Blob === 'undefined') return;

    try {
      lastWorkerRespawnTs = Date.now();
      const src =
        'var tid=null;var iv=300;' +
        'onmessage=function(e){' +
        'var d=e&&e.data?e.data:{};' +
        'if(d.type==="start"){iv=(d.interval>0?d.interval:300);if(tid)clearInterval(tid);tid=setInterval(function(){postMessage({type:"tick",now:Date.now()});},iv);}' +
        'else if(d.type==="stop"){if(tid){clearInterval(tid);tid=null;}}' +
        '};';
      const blob = new Blob([src], { type: 'text/javascript' });
      workerTickerUrl = URL.createObjectURL(blob);
      workerTicker = new Worker(workerTickerUrl);
      workerTicker.onmessage = function (evt) {
        const msg = evt && evt.data;
        if (!msg || msg.type !== 'tick') return;
        if (!state.running) return;
        const now = Date.now();
        lastWorkerTickTs = now;
        driveBackgroundPulse(now);
      };
      workerTicker.onerror = function () {
        maybeLogKeepAlive('后台心跳线程异常，已回退主线程');
        lastWorkerTickTs = 0;
        stopWorkerTicker();
      };
      workerTicker.postMessage({ type: 'start', interval: CFG.workerTickInterval });
      lastWorkerTickTs = Date.now();
      maybeLogKeepAlive('后台心跳线程已启动', 8000);
    } catch (e) {}
  }

  function stopWorkerTicker() {
    if (workerTicker) {
      try { workerTicker.postMessage({ type: 'stop' }); } catch (e) {}
      try { workerTicker.terminate(); } catch (e) {}
      workerTicker = null;
    }
    lastWorkerTickTs = 0;
    if (workerTickerUrl) {
      try { URL.revokeObjectURL(workerTickerUrl); } catch (e) {}
      workerTickerUrl = '';
    }
  }

  function startWatchdog() {
    if (watchdogTid) return;
    heartbeat();
    watchdogTid = setInterval(function () {
      if (!state.running) return;
      const now = Date.now();
      const hidden = isActuallyHidden();
      const workerSupported = typeof Worker !== 'undefined' && typeof Blob !== 'undefined';

      if (hidden) {
        if (CFG.enableBackgroundKeepAlive) {
          if (!keepAliveCtx) {
            maybeLogKeepAlive('检测到音频保活缺失，尝试恢复', 7000);
            startAudioKeepAlive();
          } else {
            if (keepAliveCtx.state === 'suspended') {
              const p = keepAliveCtx.resume();
              if (p && typeof p.catch === 'function') p.catch(function () {});
            }
            if (!audioTickerNode || (lastAudioPulseTs && now - lastAudioPulseTs > CFG.audioPulseRespawnMs)) {
              maybeLogKeepAlive('检测到音频脉冲停顿，正在恢复', 7000);
              stopAudioPulseTicker();
              startAudioPulseTicker();
            }
          }
        }

        if (workerSupported) {
          if (!workerTicker && now - lastWorkerRespawnTs >= CFG.workerRespawnGapMs) {
            maybeLogKeepAlive('检测到后台心跳缺失，尝试自动重建', 7000);
            startWorkerTicker();
          } else if (workerTicker && lastWorkerTickTs && (now - lastWorkerTickTs > CFG.workerRespawnGapMs * 2)) {
            maybeLogKeepAlive('检测到后台心跳停顿，正在重拉线程', 7000);
            stopWorkerTicker();
            startWorkerTicker();
          }
        }

        if (!atBottom && !nextInFlight && lastEffectiveScrollTs && (now - lastEffectiveScrollTs > CFG.hiddenHardRecoverMs)) {
          maybeLogKeepAlive('后台滚动长时间无进展，已触发强恢复', 9000);
          refreshRuntimeAfterLifecycle('hidden-stall');
          heartbeat();
          return;
        }
      }

      if (nextInFlight && nextInFlightAt && (now - nextInFlightAt > CFG.nextInFlightTimeoutMs)) {
        if (waitAborter) {
          try { waitAborter.abort(); } catch (e) {}
          waitAborter = null;
        }
        if (nextAssistTid) {
          clearTimeout(nextAssistTid);
          nextAssistTid = null;
        }
        nextInFlight = false;
        nextInFlightAt = 0;
        markNextFailure('next-stall', '翻页等待超时，已自动重试');
        invalidateTargetCache();
        return;
      }

      if (
        atBottom &&
        !nextInFlight &&
        (
          (nextDueAt && now > nextDueAt + CFG.atBottomRescueMs) ||
          (!nextTid && atBottomSince && now - atBottomSince > getBottomPauseMs() + CFG.atBottomRescueMs)
        )
      ) {
        maybeLogKeepAlive('检测到页底翻页链路停住，正在补触发', 6000);
        if (nextTid) {
          clearTimeout(nextTid);
          nextTid = null;
        }
        nextDueAt = 0;
        clickNextAndWait(getTarget(true));
        return;
      }

      const stall = now - lastHeartbeatTs;
      if (stall <= getHeartbeatLimitMs()) return;
      maybeLogKeepAlive('检测到停滞，已自动恢复（' + stall + 'ms）');
      refreshRuntimeAfterLifecycle('watchdog');
      heartbeat();
    }, CFG.watchdogInterval);
  }

  function stopWatchdog() {
    if (watchdogTid) {
      clearInterval(watchdogTid);
      watchdogTid = null;
    }
  }

  function getLifecycleReasonLabel(reason) {
    const r = String(reason || '').toLowerCase();
    if (r === 'visible') return '页面可见';
    if (r === 'pageshow') return '页面展示';
    if (r === 'focus') return '窗口聚焦';
    if (r === 'resume-event') return '系统恢复事件';
    if (r === 'online') return '网络恢复';
    if (r === 'watchdog') return '看门狗恢复';
    if (r === 'hidden-stall') return '后台强恢复';
    if (r === 'route') return '路由切换';
    return '未命名事件';
  }

  function refreshRuntimeAfterLifecycle(reason) {
    if (!state.running) return;
    const reasonText = getLifecycleReasonLabel(reason);
    invalidateTargetCache();
    clearRuntime();
    ensureRuntime();
    atBottom = false;
    atBottomSince = 0;
    nextInFlightAt = 0;
    lastNextAssistAt = 0;
    lastEffectiveScrollTs = Date.now();
    maybeLogKeepAlive('页面恢复后已重启运行（' + reasonText + '）');
  }

  function installLifecycleHooks() {
    window.addEventListener('pageshow', function () {
      refreshRuntimeAfterLifecycle('pageshow');
    });

    window.addEventListener('focus', function () {
      refreshRuntimeAfterLifecycle('focus');
    });

    document.addEventListener('freeze', function () {
      maybeLogKeepAlive('检测到页面冻结事件', 5000);
    });

    document.addEventListener('resume', function () {
      refreshRuntimeAfterLifecycle('resume-event');
    });

    window.addEventListener('online', function () {
      refreshRuntimeAfterLifecycle('online');
    });
  }

  function waitForElement(opts) {
    const root = (opts && opts.root) || document;
    const selector = opts && opts.selector;
    const timeout = typeof (opts && opts.timeout) === 'number' ? opts.timeout : 15000;
    const pollInterval = typeof (opts && opts.pollInterval) === 'number' ? opts.pollInterval : 200;
    const predicate = opts && typeof opts.predicate === 'function' ? opts.predicate : null;
    const signal = opts && opts.signal;

    return new Promise(function (resolve, reject) {
      if (!selector && !predicate) {
        reject(new Error('waitForElement: selector/predicate required'));
        return;
      }

      const queryRoot = root;
      const observeRoot = root.nodeType === 9 ? (root.documentElement || root.body) : root;
      if (!observeRoot) {
        reject(new Error('waitForElement: invalid root'));
        return;
      }

      let done = false;
      let timer = null;
      let poll = null;
      let observer = null;

      function cleanup() {
        if (timer) clearTimeout(timer);
        if (poll) clearInterval(poll);
        if (observer) observer.disconnect();
        if (signal) signal.removeEventListener('abort', onAbort);
      }

      function finish(fn, value) {
        if (done) return;
        done = true;
        cleanup();
        fn(value);
      }

      function scan() {
        let nodes;
        try {
          nodes = selector ? queryRoot.querySelectorAll(selector) : [queryRoot];
        } catch (e) {
          finish(reject, e);
          return null;
        }

        for (let i = 0; i < nodes.length; i++) {
          const el = nodes[i];
          try {
            if (!predicate || predicate(el)) return el;
          } catch (e) {}
        }
        return null;
      }

      function onAbort() {
        const err = typeof DOMException === 'function'
          ? new DOMException('Aborted', 'AbortError')
          : new Error('Aborted');
        finish(reject, err);
      }

      const immediate = scan();
      if (immediate) {
        finish(resolve, immediate);
        return;
      }

      observer = new MutationObserver(function () {
        const found = scan();
        if (found) finish(resolve, found);
      });
      observer.observe(observeRoot, { childList: true, subtree: true, attributes: true });

      poll = setInterval(function () {
        const found = scan();
        if (found) finish(resolve, found);
      }, Math.max(80, pollInterval));

      if (timeout > 0) {
        timer = setTimeout(function () {
          finish(reject, new Error('waitForElement timeout: ' + (selector || 'predicate')));
        }, timeout);
      }

      if (signal) {
        if (signal.aborted) {
          onAbort();
          return;
        }
        signal.addEventListener('abort', onAbort, { once: true });
      }
    });
  }

  function waitForCondition(opts) {
    const check = opts && opts.check;
    const timeout = typeof (opts && opts.timeout) === 'number' ? opts.timeout : 15000;
    const interval = typeof (opts && opts.interval) === 'number' ? opts.interval : 120;
    const signal = opts && opts.signal;

    return new Promise(function (resolve, reject) {
      if (typeof check !== 'function') {
        reject(new Error('waitForCondition: check must be function'));
        return;
      }

      let done = false;
      let tid = null;
      let timeoutTid = null;

      function cleanup() {
        if (tid) clearInterval(tid);
        if (timeoutTid) clearTimeout(timeoutTid);
        if (signal) signal.removeEventListener('abort', onAbort);
      }

      function finish(fn, val) {
        if (done) return;
        done = true;
        cleanup();
        fn(val);
      }

      function onAbort() {
        const err = typeof DOMException === 'function'
          ? new DOMException('Aborted', 'AbortError')
          : new Error('Aborted');
        finish(reject, err);
      }

      try {
        if (check()) {
          finish(resolve, true);
          return;
        }
      } catch (e) {}

      tid = setInterval(function () {
        try {
          if (check()) finish(resolve, true);
        } catch (e) {}
      }, Math.max(80, interval));

      if (timeout > 0) {
        timeoutTid = setTimeout(function () {
          finish(reject, new Error('waitForCondition timeout'));
        }, timeout);
      }

      if (signal) {
        if (signal.aborted) {
          onAbort();
          return;
        }
        signal.addEventListener('abort', onAbort, { once: true });
      }
    });
  }

  function waitForAny(promises) {
    return new Promise(function (resolve, reject) {
      if (!promises || !promises.length) {
        reject(new Error('waitForAny: empty'));
        return;
      }
      let pending = promises.length;
      let firstErr = null;
      for (let i = 0; i < promises.length; i++) {
        Promise.resolve(promises[i]).then(resolve).catch(function (err) {
          if (!firstErr) firstErr = err;
          pending -= 1;
          if (pending === 0) reject(firstErr || new Error('all failed'));
        });
      }
    });
  }

  function getDocScrollElement(doc) {
    if (!doc) return null;
    return doc.scrollingElement || doc.documentElement || doc.body || null;
  }

  function canScrollY(el) {
    if (!el) return false;
    const sh = Number(el.scrollHeight || 0);
    const ch = Number(el.clientHeight || 0);
    return sh > ch + 8;
  }

  function pickScrollableElement(doc) {
    if (!doc) return null;
    const root = getDocScrollElement(doc);
    let best = canScrollY(root) ? root : null;
    let bestScore = best ? (best.scrollHeight - best.clientHeight) : -1;

    const selectors = [
      '.reader-content',
      '.mainCon',
      '.chapter',
      '#content',
      'article',
      '[class*="reader"]',
      '[class*="content"]',
      '[class*="chapter"]'
    ];
    const cands = [];
    for (let i = 0; i < selectors.length; i++) {
      let list;
      try { list = doc.querySelectorAll(selectors[i]); } catch (e) { continue; }
      for (let j = 0; j < list.length; j++) cands.push(list[j]);
    }

    let generic;
    try { generic = doc.querySelectorAll('div,section,main'); } catch (e) {}
    if (generic) {
      const limit = Math.min(generic.length, 140);
      for (let i = 0; i < limit; i++) cands.push(generic[i]);
    }

    for (let i = 0; i < cands.length; i++) {
      const el = cands[i];
      if (!isVisible(el) || !canScrollY(el)) continue;
      const score = (el.scrollHeight - el.clientHeight) + (el.clientHeight * 0.4);
      if (score > bestScore) {
        bestScore = score;
        best = el;
      }
    }
    return best || root;
  }

  function collectTargetCandidates(doc, win, depth, out) {
    if (!doc || depth > 6 || !out) return;
    let exists = false;
    for (let i = 0; i < out.length; i++) {
      if (out[i].doc === doc) {
        exists = true;
        break;
      }
    }
    if (!exists) out.push({ doc: doc, win: win || window, depth: depth || 0 });

    let frames;
    try { frames = doc.querySelectorAll('iframe,frame'); } catch (e) { return; }
    for (let i = 0; i < frames.length; i++) {
      try {
        const fd = frames[i].contentDocument || (frames[i].contentWindow && frames[i].contentWindow.document);
        const fw = frames[i].contentWindow || win || window;
        if (!fd || !fd.body) continue;
        collectTargetCandidates(fd, fw, depth + 1, out);
      } catch (e) {}
    }
  }

  function getDocHref(doc, win) {
    try {
      if (win && win.location && win.location.href) return String(win.location.href);
      if (doc && doc.location && doc.location.href) return String(doc.location.href);
    } catch (e) {}
    return String(location.href || '');
  }

  function getPageIndexText(doc) {
    if (!doc) return '';
    for (let i = 0; i < PAGE_INDEX_SELECTORS.length; i++) {
      let list;
      try { list = doc.querySelectorAll(PAGE_INDEX_SELECTORS[i]); } catch (e) { continue; }
      for (let j = 0; j < list.length; j++) {
        const txt = ((list[j].innerText || list[j].textContent || '').replace(/\s+/g, ' ').trim());
        if (txt && txt.length <= 32) return txt;
      }
    }
    return '';
  }

  function getDocTextWeight(doc) {
    if (!doc) return 0;
    try {
      const root = doc.body || doc.documentElement;
      if (!root) return 0;
      const txt = (root.innerText || root.textContent || '').replace(/\s+/g, ' ').trim();
      return Math.min(txt.length, 5000);
    } catch (e) {
      return 0;
    }
  }

  function evaluateDocContext(target, scrollEl) {
    const t = target || { win: window, doc: document, depth: 0 };
    const doc = t.doc || document;
    const href = getDocHref(doc, t.win).toLowerCase();
    const readyEl = getReadyElement(doc);
    const el = scrollEl || pickScrollableElement(doc) || getDocScrollElement(doc);
    const scrollSpan = el ? Math.max(0, Number(el.scrollHeight || 0) - Number(el.clientHeight || 0)) : 0;
    const nextBtn = findNextButton([doc], true);
    const pageIndexText = getPageIndexText(doc);
    const textWeight = getDocTextWeight(doc);

    let readingScore = 0;
    let nonReadingScore = 0;

    if (/studentstudy|chapter|knowledge|book|read|ebook/.test(href)) readingScore += 1.6;
    if (readyEl) readingScore += 2.6;
    if (nextBtn) readingScore += 2.2;
    if (pageIndexText) readingScore += 0.6;
    if (scrollSpan > 180) readingScore += 1.1;
    if (scrollSpan > 1200) readingScore += 0.7;
    if (textWeight > 150) readingScore += 0.8;
    if (textWeight > 1000) readingScore += 0.4;

    if (hasSelector(doc, 'video,.video-js,[class*="video-player"],iframe[src*="video"],[class*="ans-video"]')) {
      nonReadingScore += 2.3;
    }
    if (hasSelector(doc, '.TiMu,[class*="question"],[class*="answer"],.mark_answer,.exam,[data-type*="question"]')) {
      nonReadingScore += 2.5;
    }
    if (hasSelector(doc, '[class*="work"],[class*="quiz"],[class*="test"],form[action*="work"]')) {
      nonReadingScore += 1.2;
    }

    let targetScore = readingScore - (nonReadingScore * 0.9);
    if (!canScrollY(el) && !nextBtn && !readyEl) targetScore -= 1.6;
    if (t.depth) targetScore += Math.min(t.depth * 0.08, 0.24);

    return {
      targetScore: targetScore,
      readingScore: readingScore,
      nonReadingScore: nonReadingScore,
      scrollSpan: scrollSpan,
      nextBtn: nextBtn,
      pageIndexText: pageIndexText,
      textWeight: textWeight
    };
  }

  function getTarget(force) {
    const now = Date.now();
    if (!force && targetCache && now - targetCacheAt < CFG.targetCacheMs) {
      return targetCache;
    }

    const candidates = [];
    collectTargetCandidates(document, window, 0, candidates);
    if (!candidates.length) candidates.push({ win: window, doc: document, depth: 0 });

    let bestTarget = { win: window, doc: document, depth: 0 };
    let bestScore = -Infinity;
    let bestSpan = -1;

    for (let i = 0; i < candidates.length; i++) {
      const ctx = evaluateDocContext(candidates[i]);
      if (
        ctx.targetScore > bestScore ||
        (Math.abs(ctx.targetScore - bestScore) < 0.01 && ctx.scrollSpan > bestSpan)
      ) {
        bestTarget = candidates[i];
        bestScore = ctx.targetScore;
        bestSpan = ctx.scrollSpan;
      }
    }

    const t = bestTarget || { win: window, doc: document, depth: 0 };
    targetCache = t;
    targetCacheAt = now;
    return t;
  }

  function getScrollableElement(target, force) {
    const t = target || getTarget();
    if (!t || !t.doc) return null;

    const now = Date.now();
    if (
      !force &&
      scrollElCache &&
      scrollElCacheDoc === t.doc &&
      now - scrollElCacheAt < CFG.scrollElCacheMs &&
      (!('isConnected' in scrollElCache) || scrollElCache.isConnected) &&
      canScrollY(scrollElCache)
    ) {
      return scrollElCache;
    }

    let el = getDocScrollElement(t.doc);
    if (!canScrollY(el)) {
      el = pickScrollableElement(t.doc) || el;
    }

    scrollElCache = el || null;
    scrollElCacheDoc = t.doc;
    scrollElCacheAt = now;
    return el;
  }

  function hasSelector(doc, selector) {
    if (!doc || !selector) return false;
    try { return !!doc.querySelector(selector); } catch (e) { return false; }
  }

  function detectNonReadingContext(target, scrollEl, force) {
    const now = Date.now();
    if (!force && now - lastNonReadingCheckTs < CFG.contextCheckIntervalMs) {
      return { nonReading: nonReadingCached, hint: nonReadingHint };
    }

    const t = target || getTarget();
    const ctx = evaluateDocContext(t, scrollEl);
    const nonReading = ctx.nonReadingScore >= (ctx.readingScore + 2) && ctx.targetScore < CFG.minTargetScore;
    const hint = nonReading
      ? ('非阅读特征:' + ctx.nonReadingScore.toFixed(1) + ' 阅读特征:' + ctx.readingScore.toFixed(1))
      : '';

    lastNonReadingCheckTs = now;
    nonReadingCached = nonReading;
    nonReadingHint = hint;
    return { nonReading: nonReading, hint: hint };
  }

  function isVisible(el) {
    return !!(el && (el.offsetParent !== null || el.offsetWidth > 0 || el.offsetHeight > 0));
  }

  function collectDocs(preferredDoc) {
    const docs = [];

    function add(doc) {
      if (!doc) return;
      if (docs.indexOf(doc) === -1) docs.push(doc);
    }

    function walk(doc, depth) {
      if (!doc || depth > 4) return;
      let frames;
      try { frames = doc.querySelectorAll('iframe,frame'); } catch (e) { return; }
      for (let i = 0; i < frames.length; i++) {
        try {
          const fd = frames[i].contentDocument || (frames[i].contentWindow && frames[i].contentWindow.document);
          if (!fd) continue;
          add(fd);
          walk(fd, depth + 1);
        } catch (e) {}
      }
    }

    add(document);
    add(preferredDoc);
    walk(document, 0);
    return docs;
  }

  function getReadyElement(doc) {
    try {
      return doc.querySelector(CFG.pageReadySelectors.join(','));
    } catch (e) {
      return null;
    }
  }

  function fingerprint(el) {
    if (!el) return '';
    const txt = (el.innerText || el.textContent || '').replace(/\s+/g, ' ').trim();
    return txt.length + '|' + (el.childElementCount || 0) + '|' + (el.scrollHeight || 0) + '|' + txt.slice(0, 80) + '|' + txt.slice(-40);
  }

  function matchesNextText(text) {
    const txt = String(text || '').replace(/\s+/g, ' ').trim();
    if (!txt) return false;
    return /^(下一(页|节|章|步)|后一(页|节|章)|next\b)/i.test(txt) || txt.indexOf('下一') === 0;
  }

  function isActionable(el, allowHidden) {
    if (!el || !el.isConnected) return false;
    if (el.disabled) return false;
    if (String(el.getAttribute('aria-disabled') || '').toLowerCase() === 'true') return false;
    if (!allowHidden && !isVisible(el)) return false;
    return true;
  }

  function findNextButton(docs, allowHidden) {
    let hiddenFallback = null;

    for (let d = 0; d < docs.length; d++) {
      const doc = docs[d];

      for (let i = 0; i < NEXT_SELECTORS.length; i++) {
        try {
          const list = doc.querySelectorAll(NEXT_SELECTORS[i]);
          for (let j = 0; j < list.length; j++) {
            const btn = list[j];
            if (!isActionable(btn, allowHidden)) continue;
            if (isVisible(btn)) return btn;
            if (!hiddenFallback) hiddenFallback = btn;
          }
        } catch (e) {}
      }

      try {
        const all = doc.querySelectorAll('a,button,span,div,[role="button"]');
        for (let j = 0; j < all.length; j++) {
          const el = all[j];
          const txt = (el.innerText || el.textContent || '').trim();
          const title = (el.getAttribute('title') || el.getAttribute('aria-label') || el.getAttribute('data-tip') || '').trim();
          if (!matchesNextText(txt) && !matchesNextText(title)) continue;
          if (!isActionable(el, allowHidden)) continue;
          if (isVisible(el)) return el;
          if (!hiddenFallback) hiddenFallback = el;
        }
      } catch (e) {}
    }
    return hiddenFallback;
  }

  function dispatchClick(el) {
    if (!el) return;
    const doc = el.ownerDocument || document;
    const view = doc.defaultView || window;

    try { if (typeof el.focus === 'function') el.focus(); } catch (e) {}
    try {
      if (typeof view.PointerEvent === 'function') {
        el.dispatchEvent(new view.PointerEvent('pointerdown', { bubbles: true, cancelable: true, view: view, pointerType: 'mouse', isPrimary: true }));
        el.dispatchEvent(new view.PointerEvent('pointerup', { bubbles: true, cancelable: true, view: view, pointerType: 'mouse', isPrimary: true }));
      }
      el.dispatchEvent(new view.MouseEvent('mousedown', { bubbles: true, cancelable: true, view: view }));
      el.dispatchEvent(new view.MouseEvent('mouseup', { bubbles: true, cancelable: true, view: view }));
      el.dispatchEvent(new view.MouseEvent('click', { bubbles: true, cancelable: true, view: view }));
    } catch (e) {}
    try { el.click(); } catch (e) {}
  }

  function dispatchKey(doc, key, code, keyCode) {
    if (!doc) return;
    const view = doc.defaultView || window;
    const target = doc.activeElement || doc.body || doc.documentElement;
    if (!target) return;

    try { if (typeof target.focus === 'function') target.focus(); } catch (e) {}

    ['keydown', 'keyup'].forEach(function (type) {
      try {
        const evt = new view.KeyboardEvent(type, {
          bubbles: true,
          cancelable: true,
          key: key,
          code: code,
          keyCode: keyCode,
          which: keyCode
        });
        target.dispatchEvent(evt);
      } catch (e) {}
    });
  }

  function triggerNextFallback(target) {
    const t = target || getTarget();
    const doc = (t && t.doc) || document;
    const view = (t && t.win) || window;

    dispatchKey(doc, 'ArrowRight', 'ArrowRight', 39);
    dispatchKey(doc, 'PageDown', 'PageDown', 34);
    dispatchKey(doc, ' ', 'Space', 32);

    try {
      if (view && typeof view.dispatchEvent === 'function') {
        const Evt = view.Event || Event;
        view.dispatchEvent(new Evt('scroll', { bubbles: true }));
      }
    } catch (e) {}

    return true;
  }

  function getDocScrollTop(doc) {
    const root = getDocScrollElement(doc);
    return Number(root && root.scrollTop || 0);
  }

  function captureDocSnapshot(doc) {
    const readyEl = getReadyElement(doc);
    const root = getDocScrollElement(doc);
    return {
      doc: doc,
      readyEl: readyEl,
      mark: fingerprint(readyEl),
      pageIndexText: getPageIndexText(doc),
      scrollTop: getDocScrollTop(doc),
      scrollHeight: Number(root && root.scrollHeight || 0),
      href: getDocHref(doc, doc && doc.defaultView)
    };
  }

  function hasSnapshotChanged(snapshot) {
    if (!snapshot || !snapshot.doc) return false;
    const doc = snapshot.doc;
    const readyEl = getReadyElement(doc);

    if (!snapshot.readyEl && readyEl) return true;
    if (snapshot.readyEl && !snapshot.readyEl.isConnected) return true;
    if (readyEl !== snapshot.readyEl) return true;
    if (fingerprint(readyEl) !== snapshot.mark) return true;

    const pageIndexText = getPageIndexText(doc);
    if (pageIndexText && pageIndexText !== snapshot.pageIndexText) return true;

    const root = getDocScrollElement(doc);
    const scrollTop = Number(root && root.scrollTop || 0);
    const scrollHeight = Number(root && root.scrollHeight || 0);
    if (snapshot.scrollTop > 30 && scrollTop <= 3) return true;
    if (Math.abs(scrollHeight - snapshot.scrollHeight) > 20) return true;

    const href = getDocHref(doc, doc && doc.defaultView);
    if (href !== snapshot.href) return true;

    return false;
  }

  function clearNextAssist() {
    if (nextAssistTid) {
      clearTimeout(nextAssistTid);
      nextAssistTid = null;
    }
  }

  function scheduleNextAssist(target) {
    clearNextAssist();
    nextAssistTid = setTimeout(function () {
      nextAssistTid = null;
      if (!state.running || !nextInFlight) return;
      lastNextAssistAt = Date.now();

      const docs = collectDocs(target && target.doc);
      const btn = findNextButton(docs, true);
      if (btn) {
        maybeLogKeepAlive('翻页等待中，执行按钮补触发', 5000);
        dispatchClick(btn);
      } else {
        maybeLogKeepAlive('翻页等待中，执行键盘补触发', 5000);
        triggerNextFallback(target);
      }

      if (state.running && nextInFlight) {
        scheduleNextAssist(target);
      }
    }, CFG.nextAssistRetryMs);
  }

  function clearRuntime() {
    if (scrollTid) { clearInterval(scrollTid); scrollTid = null; }
    if (mouseTid) { clearInterval(mouseTid); mouseTid = null; }
    if (nextTid) { clearTimeout(nextTid); nextTid = null; }
    clearNextAssist();
    stopWorkerTicker();
    stopWatchdog();
    if (waitAborter) {
      try { waitAborter.abort(); } catch (e) {}
      waitAborter = null;
    }
    atBottom = false;
    atBottomSince = 0;
    nextDueAt = 0;
    nextInFlight = false;
    nextInFlightAt = 0;
    lastNextAssistAt = 0;
    lastScrollTs = 0;
    scrollNoProgressTicks = 0;
    lastEffectiveScrollTs = 0;
    nextFailStreak = 0;
    lastWorkerMouseTs = 0;
    lastWorkerTickTs = 0;
    lastNonReadingLogAt = 0;
    invalidateTargetCache();
    if (!state.running) stopAudioKeepAlive();
  }

  function ensureRuntime() {
    if (!scrollTid) scrollTid = setInterval(doScroll, CFG.scrollInterval);
    if (!mouseTid) mouseTid = setInterval(simulateMouse, CFG.mouseMoveInterval);
    startWorkerTicker();
    startWatchdog();
    startAudioKeepAlive();
    if (!lastEffectiveScrollTs) lastEffectiveScrollTs = Date.now();
    heartbeat();
  }

  function resetScrollPosition() {
    try {
      const t = getTarget(true);
      const el = getScrollableElement(t, true);
      if (el) el.scrollTop = 0;
      if (t.win && typeof t.win.scrollTo === 'function') t.win.scrollTo(0, 0);
    } catch (e) {}
    atBottom = false;
    atBottomSince = 0;
    scrollNoProgressTicks = 0;
  }

  function markNextFailure(action, msg) {
    clearNextAssist();
    nextFailStreak = Math.min(nextFailStreak + 1, 6);
    const delay = Math.min(
      CFG.nextFailureBackoffBaseMs * Math.pow(2, nextFailStreak - 1),
      CFG.nextFailureBackoffMaxMs
    );
    saveState({ lastAction: action || 'next-fail' });
    nextDueAt = Date.now() + delay;
    nextInFlightAt = 0;
    lastNextAssistAt = 0;
    log(msg + '（' + Math.round(delay / 1000) + ' 秒后重试）');
  }

  async function clickNextAndWait(target) {
    if (nextInFlight) return false;
    nextInFlight = true;
    nextInFlightAt = Date.now();
    nextDueAt = 0;
    invalidateTargetCache();

    const docs = collectDocs(target && target.doc);
    const btn = findNextButton(docs, true);
    const snapshots = docs.map(captureDocSnapshot);

    if (waitAborter) {
      try { waitAborter.abort(); } catch (e) {}
    }
    waitAborter = new AbortController();

    let triggerLabel = '';
    if (btn) {
      dispatchClick(btn);
      triggerLabel = '按钮';
    } else if (triggerNextFallback(target)) {
      triggerLabel = '键盘';
    } else {
      markNextFailure('no-next-trigger', '未找到可用翻页方式');
      nextInFlight = false;
      return false;
    }

    lastNextAssistAt = Date.now();
    scheduleNextAssist(target);
    saveState({ lastAction: 'clicked-next' });
    log('已触发下一页（' + triggerLabel + '），等待新内容加载...');

    const waits = [];
    waits.push(waitForCondition({
      check: function () {
        for (let i = 0; i < snapshots.length; i++) {
          if (hasSnapshotChanged(snapshots[i])) return true;
        }
        return false;
      },
      timeout: CFG.waitTimeout,
      interval: 120,
      signal: waitAborter.signal
    }));

    try {
      await waitForAny(waits);
      clearNextAssist();
      resetScrollPosition();
      saveState({ lastAction: 'next-ready' });
      nextFailStreak = 0;
      nextInFlightAt = 0;
      lastNextAssistAt = 0;
      log('新内容已就绪，继续阅读');
      return true;
    } catch (e) {
      markNextFailure('wait-timeout', '等待新内容超时');
      return false;
    } finally {
      clearNextAssist();
      if (waitAborter) {
        try { waitAborter.abort(); } catch (e) {}
        waitAborter = null;
      }
      nextInFlight = false;
      nextInFlightAt = 0;
      if (!nextInFlight) lastNextAssistAt = 0;
    }
  }

  function scheduleNext(target) {
    if (!state.running || nextInFlight) return;
    if (!nextDueAt) nextDueAt = Date.now() + getBottomPauseMs();
    const delay = Math.max(60, nextDueAt - Date.now());
    if (nextTid) return;
    nextTid = setTimeout(function () {
      nextTid = null;
      if (!state.running || nextInFlight) return;
      if (Date.now() < nextDueAt - 30) {
        scheduleNext(target);
        return;
      }
      nextDueAt = 0;
      clickNextAndWait(target);
    }, delay);
  }

  function rescheduleNextIfNeeded() {
    if (!state.running || !atBottom) return;
    if (nextTid) {
      clearTimeout(nextTid);
      nextTid = null;
    }
    nextDueAt = 0;
    scheduleNext(getTarget());
  }

  function doScroll() {
    if (!state.running) return;
    try {
      heartbeat();

      const now = Date.now();
      if (!lastScrollTs) lastScrollTs = now;
      const elapsed = Math.max(CFG.scrollInterval, now - lastScrollTs);
      lastScrollTs = now;

      const t = getTarget();
      const el = getScrollableElement(t);
      if (!el) {
        invalidateTargetCache();
        maybeLogKeepAlive('未找到可滚动容器，正在自动重试', 8000);
        return;
      }

      const top = el.scrollTop;
      const total = el.scrollHeight;
      const vh = el.clientHeight || t.win.innerHeight || 0;

      if (top + vh >= total - 5) {
        scrollNoProgressTicks = 0;
        lastEffectiveScrollTs = now;
        if (!atBottom) {
          atBottom = true;
          atBottomSince = now;
          log('已到底部，等待 ' + state.settings.bottomPauseSec + ' 秒后翻页...');
          scheduleNext(t);
        } else if (!nextTid && !nextInFlight) {
          scheduleNext(t);
        }

        if (nextDueAt && Date.now() >= nextDueAt && !nextInFlight) {
          if (nextTid) { clearTimeout(nextTid); nextTid = null; }
          nextDueAt = 0;
          clickNextAndWait(t);
        }
        return;
      }

      atBottom = false;
      atBottomSince = 0;
      if (nextTid) { clearTimeout(nextTid); nextTid = null; }
      nextDueAt = 0;

      const speed = getSpeed();
      const hidden = isActuallyHidden();
      const maxDrift = hidden ? CFG.maxTimerDriftCompensate : CFG.foregroundMaxTimerDriftCompensate;
      const driftFactorRaw = clamp(elapsed / CFG.scrollInterval, 1, maxDrift);
      const driftFactor = hidden ? Math.min(driftFactorRaw, 12) : Math.min(driftFactorRaw, 1.35);
      const jitterCap = hidden ? Math.min(0.3, speed * 0.1) : Math.min(0.16, speed * 0.06);
      const jitter = Math.random() * jitterCap;
      const rawStep = (speed + jitter) * driftFactor;
      const maxStep = hidden
        ? Math.max(CFG.maxStepPerTick * 6, speed * 18)
        : (CFG.maxStepPerTick + speed * 2.1);
      const step = Math.min(rawStep, maxStep);

      const before = el.scrollTop;
      el.scrollTop += step;
      const moved = Math.abs((el.scrollTop || 0) - before);
      if (moved < 0.8) {
        scrollNoProgressTicks += 1;
      } else {
        scrollNoProgressTicks = 0;
        lastEffectiveScrollTs = now;
      }

      if (scrollNoProgressTicks >= CFG.scrollNoProgressLimit) {
        scrollNoProgressTicks = 0;
        invalidateTargetCache();
        maybeLogKeepAlive('检测到滚动停滞，已自动重新定位滚动容器', 8000);
      }

      try {
        el.dispatchEvent(new Event('scroll', { bubbles: true }));
        t.win.dispatchEvent(new Event('scroll', { bubbles: true }));
        t.doc.dispatchEvent(new Event('scroll', { bubbles: true }));
      } catch (e) {}
    } catch (e) {
      invalidateTargetCache();
      maybeLogKeepAlive('滚动线程异常，已自动恢复', 8000);
    }
  }

  function simulateMouse() {
    try {
      const t = getTarget();
      const view = (t && t.doc && t.doc.defaultView) || (t && t.win) || window;
      const w = (t.doc.body ? t.doc.body.clientWidth : 800) || 800;
      const h = (t.doc.body ? t.doc.body.clientHeight : 600) || 600;
      const evt = new view.MouseEvent('mousemove', {
        bubbles: true,
        cancelable: true,
        clientX: 80 + Math.floor(Math.random() * Math.max(w - 160, 100)),
        clientY: 80 + Math.floor(Math.random() * Math.max(h - 160, 100))
      });
      t.doc.dispatchEvent(evt);
      if (t.doc !== document) document.dispatchEvent(evt);
    } catch (e) {}

    if (Math.random() < 0.15) {
      try {
        dispatchKey((getTarget() && getTarget().doc) || document, 'ArrowDown', 'ArrowDown', 40);
      } catch (e) {}
    }
  }

  function start(reason) {
    if (!state.running) {
      saveState({ running: true, lastAction: 'start:' + (reason || 'manual') });
      log('自动阅读已启动');
    }
    const now = Date.now();
    atBottom = false;
    atBottomSince = 0;
    lastScrollTs = 0;
    scrollNoProgressTicks = 0;
    lastEffectiveScrollTs = now;
    nextFailStreak = 0;
    nextInFlightAt = 0;
    lastNextAssistAt = 0;
    lastWorkerMouseTs = 0;
    lastWorkerTickTs = 0;
    lastWorkerRespawnTs = 0;
    lastNonReadingLogAt = 0;
    invalidateTargetCache();
    ensureRuntime();
    if (isActuallyHidden()) startAudioKeepAlive();
    updateUI();
  }

  function stop(reason) {
    if (!state.running && !scrollTid && !mouseTid && !nextTid) return;
    saveState({ running: false, lastAction: 'stop:' + (reason || 'manual') });
    clearRuntime();
    stopAudioKeepAlive();
    atBottom = false;
    atBottomSince = 0;
    scrollNoProgressTicks = 0;
    lastEffectiveScrollTs = 0;
    nextFailStreak = 0;
    nextInFlightAt = 0;
    lastNextAssistAt = 0;
    lastWorkerMouseTs = 0;
    lastWorkerTickTs = 0;
    lastWorkerRespawnTs = 0;
    lastNonReadingLogAt = 0;
    invalidateTargetCache();
    log('自动阅读已暂停');
    updateUI();
  }

  function updatePresetButtons() {
    const btns = document.querySelectorAll('.cx-speed-btn');
    for (let i = 0; i < btns.length; i++) {
      const btn = btns[i];
      const preset = btn.getAttribute('data-preset');
      const active = state.settings.speedPreset === preset;
      btn.style.opacity = active ? '1' : '0.78';
      btn.style.transform = active ? 'translateY(-1px)' : 'translateY(0)';
      btn.style.boxShadow = active ? '0 0 0 2px rgba(255,255,255,.55) inset' : 'none';
    }
  }

  function updateSettingsUI(previewSpeed) {
    const range = document.getElementById('cx-speed-range');
    const speedValue = document.getElementById('cx-speed-value');
    const speedMode = document.getElementById('cx-speed-mode');
    const secInput = document.getElementById('cx-bottom-sec');

    const hasPreview = Number.isFinite(previewSpeed);
    const speed = hasPreview ? clamp(previewSpeed, CFG.speedMin, CFG.speedMax) : state.settings.speedValue;

    if (range && !hasPreview) range.value = String(state.settings.speedValue);
    if (speedValue) speedValue.textContent = speed.toFixed(1) + ' px/次';

    if (speedMode) {
      speedMode.textContent = hasPreview
        ? '模式：无级预览'
        : ('模式：' + (CFG.speedLabel[state.settings.speedPreset] || '中'));
    }

    if (secInput) secInput.value = String(state.settings.bottomPauseSec);
    updatePresetButtons();
  }

  function setSpeedPreset(preset) {
    if (!CFG.speedPresetMap[preset]) return;
    const speed = CFG.speedPresetMap[preset];
    const changed = state.settings.speedPreset !== preset || state.settings.speedValue !== speed;
    saveState({ settings: { speedPreset: preset, speedValue: speed } });
    updateSettingsUI();
    updateUI();
    if (changed) log('滚动速度切换为' + CFG.speedLabel[preset] + '速（' + speed.toFixed(1) + ' px/次）');
  }

  function setCustomSpeed(v, withLog) {
    let speed = Number.parseFloat(v);
    if (!Number.isFinite(speed)) speed = state.settings.speedValue;
    speed = fixed1(clamp(speed, CFG.speedMin, CFG.speedMax));

    const changed = state.settings.speedPreset !== 'custom' || Math.abs(state.settings.speedValue - speed) > 0.001;
    saveState({ settings: { speedPreset: 'custom', speedValue: speed } });
    updateSettingsUI();
    updateUI();

    if (withLog && changed) {
      log('滚动速度调整为无级 ' + speed.toFixed(1) + ' px/次');
    }
  }

  function setBottomPauseSec(v) {
    let sec = Number.parseFloat(v);
    if (!Number.isFinite(sec)) sec = state.settings.bottomPauseSec;
    sec = Math.round(clamp(sec, CFG.bottomPauseMin, CFG.bottomPauseMax));

    const changed = sec !== state.settings.bottomPauseSec;
    saveState({ settings: { bottomPauseSec: sec } });
    updateSettingsUI();
    updateUI();

    if (changed) {
      log('翻页等待已设置为 ' + sec + ' 秒');
      rescheduleNextIfNeeded();
    }
  }

  function bindSettingEvents(container) {
    const speedBtns = container.querySelectorAll('.cx-speed-btn');
    for (let i = 0; i < speedBtns.length; i++) {
      speedBtns[i].addEventListener('click', function () {
        setSpeedPreset(this.getAttribute('data-preset'));
      });
    }

    const range = container.querySelector('#cx-speed-range');
    if (range) {
      range.addEventListener('input', function () {
        const v = Number.parseFloat(this.value);
        if (Number.isFinite(v)) updateSettingsUI(v);
      });
      range.addEventListener('change', function () {
        setCustomSpeed(this.value, true);
      });
    }

    const secInput = container.querySelector('#cx-bottom-sec');
    const secApply = container.querySelector('#cx-bottom-apply');

    function applySec() {
      if (!secInput) return;
      setBottomPauseSec(secInput.value);
    }

    if (secApply) secApply.addEventListener('click', applySec);
    if (secInput) {
      secInput.addEventListener('keydown', function (e) {
        if (e.key === 'Enter') applySec();
      });
      secInput.addEventListener('blur', applySec);
    }
  }

  function createUI() {
    if (document.getElementById('cx-auto-panel')) return;
    if (!document.body) return;

    const container = document.createElement('div');
    container.id = 'cx-auto-panel';
    container.style.cssText =
      'position:fixed;bottom:24px;right:24px;z-index:2147483647;' +
      'font-family:"Microsoft YaHei","PingFang SC",sans-serif;font-size:14px;user-select:none;';

    const btnStyle = 'border:none;border-radius:8px;color:#fff;cursor:pointer;font-size:13px;font-weight:600;';

    container.innerHTML =
      '<div id="cx-panel-body" style="' +
      'background:linear-gradient(135deg,#0f766e 0%,#0284c7 100%);' +
      'color:#fff;padding:16px 16px 14px;border-radius:14px;' +
      'box-shadow:0 8px 28px rgba(0,0,0,.35);min-width:274px;cursor:move;">' +
      '<div style="font-weight:700;font-size:15px;margin-bottom:8px;">自动阅读 v3.7（强后台）</div>' +
      '<div id="cx-status" style="margin-bottom:8px;">状态：⚪ 就绪</div>' +
      '<div style="display:flex;gap:8px;margin-bottom:10px;">' +
      '<button id="cx-btn-go" style="flex:1;padding:7px 0;background:#16a34a;' + btnStyle + '">开始</button>' +
      '<button id="cx-btn-stop" style="flex:1;padding:7px 0;background:#dc2626;' + btnStyle + '">暂停</button>' +
      '</div>' +

      '<div style="font-size:12px;opacity:.92;">滚动速度</div>' +
      '<div style="display:flex;gap:6px;margin-top:6px;">' +
      '<button class="cx-speed-btn" data-preset="slow" style="flex:1;padding:5px 0;background:#0ea5e9;' + btnStyle + '">慢</button>' +
      '<button class="cx-speed-btn" data-preset="medium" style="flex:1;padding:5px 0;background:#0284c7;' + btnStyle + '">中</button>' +
      '<button class="cx-speed-btn" data-preset="fast" style="flex:1;padding:5px 0;background:#0369a1;' + btnStyle + '">快</button>' +
      '</div>' +
      '<div style="display:flex;align-items:center;gap:8px;margin-top:6px;">' +
      '<input id="cx-speed-range" type="range" min="' + CFG.speedMin + '" max="' + CFG.speedMax + '" step="' + CFG.speedStep + '" style="flex:1;cursor:pointer;">' +
      '<span id="cx-speed-value" style="min-width:74px;text-align:right;font-size:12px;">-</span>' +
      '</div>' +
      '<div id="cx-speed-mode" style="font-size:11px;opacity:.88;margin-top:3px;">模式：中</div>' +

      '<div style="font-size:12px;opacity:.92;margin-top:10px;">翻页等待（秒）</div>' +
      '<div style="display:flex;gap:8px;align-items:center;margin-top:6px;">' +
      '<input id="cx-bottom-sec" type="number" min="' + CFG.bottomPauseMin + '" max="' + CFG.bottomPauseMax + '" step="1" style="flex:1;padding:6px 8px;border:none;border-radius:8px;outline:none;font-size:13px;">' +
      '<button id="cx-bottom-apply" style="padding:6px 10px;background:#155e75;' + btnStyle + '">应用</button>' +
      '</div>' +

      '<div id="cx-logbox" style="margin-top:10px;font-size:12px;opacity:.9;max-height:90px;overflow-y:auto;line-height:1.5;"></div>' +
      '</div>';

    document.body.appendChild(container);

    const btnGo = document.getElementById('cx-btn-go');
    const btnStop = document.getElementById('cx-btn-stop');
    if (btnGo) btnGo.onclick = function () { start('manual'); };
    if (btnStop) btnStop.onclick = function () { stop('manual'); };

    bindSettingEvents(container);

    if (state.panelPos && typeof state.panelPos.left === 'number' && typeof state.panelPos.top === 'number') {
      container.style.left = state.panelPos.left + 'px';
      container.style.top = state.panelPos.top + 'px';
      container.style.right = 'auto';
      container.style.bottom = 'auto';
    }

    const panel = document.getElementById('cx-panel-body');
    let dragging = false;
    let dx = 0;
    let dy = 0;

    panel.addEventListener('mousedown', function (e) {
      if (e.target && (e.target.tagName === 'BUTTON' || e.target.tagName === 'INPUT')) return;
      dragging = true;
      const rect = container.getBoundingClientRect();
      dx = e.clientX - rect.left;
      dy = e.clientY - rect.top;
      e.preventDefault();
    });

    document.addEventListener('mousemove', function (e) {
      if (!dragging) return;
      container.style.left = (e.clientX - dx) + 'px';
      container.style.top = (e.clientY - dy) + 'px';
      container.style.right = 'auto';
      container.style.bottom = 'auto';
    });

    document.addEventListener('mouseup', function () {
      if (!dragging) return;
      dragging = false;
      const rect = container.getBoundingClientRect();
      saveState({
        panelPos: {
          left: Math.round(rect.left),
          top: Math.round(rect.top)
        }
      });
    });

    updateSettingsUI();
    updateUI();
  }

  function updateUI() {
    const el = document.getElementById('cx-status');
    if (!el) return;
    const info = state.settings.speedValue.toFixed(1) + ' px/次，翻页 ' + state.settings.bottomPauseSec + ' 秒';
    const mode = isActuallyHidden() ? '后台' : '前台';
    el.textContent = state.running
      ? ('状态：🟢 运行中（' + mode + '，' + info + '）')
      : ('状态：🔴 已暂停（' + info + '）');
  }

  function log(msg) {
    console.log('[CX自动阅读]', msg);
    const box = document.getElementById('cx-logbox');
    if (!box) return;

    const t = new Date();
    const ts =
      ('0' + t.getHours()).slice(-2) + ':' +
      ('0' + t.getMinutes()).slice(-2) + ':' +
      ('0' + t.getSeconds()).slice(-2);

    const line = document.createElement('div');
    line.textContent = ts + ' ' + msg;
    box.insertBefore(line, box.firstChild);

    while (box.children.length > CFG.logLimit) {
      box.removeChild(box.lastChild);
    }
  }

  function installRouteHooks() {
    function onRouteChanged() {
      if (routeChangeTid) clearTimeout(routeChangeTid);
      routeChangeTid = setTimeout(function () {
        routeChangeTid = null;
        state = loadState();
        updateSettingsUI();
        updateUI();

        if (state.running) {
          invalidateTargetCache();
          clearRuntime();
          ensureRuntime();
          atBottom = false;
          lastEffectiveScrollTs = Date.now();
          log('检测到页面切换，已自动恢复运行（强后台）');
        } else {
          clearRuntime();
        }
      }, 120);
    }

    window.addEventListener('popstate', onRouteChanged);
    window.addEventListener('hashchange', onRouteChanged);
    window.addEventListener('pageshow', onRouteChanged);

    ['pushState', 'replaceState'].forEach(function (key) {
      const raw = history[key];
      if (!raw || raw.__cxWrapped) return;
      const wrapped = function () {
        const ret = raw.apply(this, arguments);
        onRouteChanged();
        return ret;
      };
      wrapped.__cxWrapped = true;
      history[key] = wrapped;
    });
  }

  function init() {
    if (inited) return;
    inited = true;

    setupAntiDetect();
    state = loadState();

    createUI();
    installRouteHooks();
    installLifecycleHooks();

    log('脚本已就绪（v3.7 强后台）');

    if (state.running) {
      start('resume-after-refresh');
      log('已从本地缓存恢复运行状态');
    } else {
      updateSettingsUI();
      updateUI();
    }
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function () {
      setTimeout(init, 120);
    }, { once: true });
  } else {
    setTimeout(init, 120);
  }
})();
