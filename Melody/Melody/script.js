// script.js
window.onload = () => {
  const VF = Vex.Flow;

  // DOM Elements
  const startBtn = document.getElementById("startBtn");
  const bpmSlider = document.getElementById("bpm");
  const bpmVal = document.getElementById("bpmVal");
  const toggleMetronomeBtn = document.getElementById("toggleMetronome");
  const toggleFreeModeBtn = document.getElementById("toggleFreeMode");
  const clearFreeNotesBtn = document.getElementById("clearFreeNotes");
  const pitchDiv = document.getElementById("pitch");
  const doremiDiv = document.getElementById("doremi");
  const octaveDiv = document.getElementById("octave");
  const frequencyDiv = document.getElementById("frequency");
  const statusDiv = document.getElementById("status");
  const metronomeSound = document.getElementById("metronomeSound");
  const outputDiv = document.getElementById("output");
  const metronomeVolumeSlider = document.getElementById("metronomeVolume");
  const volValSpan = document.getElementById("volVal");
  const numeratorInput = document.getElementById("numerator");
  const denominatorInput = document.getElementById("denominator");

  // Lyrics elements
  const lyricsInput = document.getElementById("lyricsInput");
  const loadLyricsBtn = document.getElementById("loadLyricsBtn");

  // Audio Context and Analysis Variables
  let audioContext = null;
  let analyser = null;
  let microphone = null;
  let scriptProcessor = null;
  let metronomeGainNode = null;
  let metronomeInterval = null;
  let metronomeOn = false;

  // Realtime state
  let pitchHistory = [];
  const maxHistory = 10;

  // Metronome-based notes (legacy)
  let staveNotes = [];

  // Free transcription notes (onset-based)
  let freeModeOn = true;
  let freeNotes = []; // { key:"c/4", duration:"q", lyric:"안" }
  const maxFreeNotes = 32;

  // Onset detection state
  let prevSpectrum = null;
  let fluxHistory = []; // recent spectral flux values
  const fluxWindow = 20; // threshold window
  const fluxK = 1.5; // threshold sensitivity
  const minIOI = 0.12; // 120 ms
  const minDur = 0.08; // 80 ms
  let lastOnsetTime = null;

  // Current segment state
  let segmentActive = false;
  let segmentStartTime = 0;
  let segmentPitchFrames = [];
  let lastVoicedTime = 0;

  // IOI list to estimate base quarter duration
  let ioiList = []; // seconds
  const ioiWindow = 16;

  // Lyrics state
  let lyricsTokens = [];
  let lyricsIndex = 0;
  let lyricMode = "syllable"; // "syllable" | "word"

  // Note mapping for Korean notation
  const noteToDoremiMap = {
    C: "도", "C#": "도#", D: "레", "D#": "레#",
    E: "미", F: "파", "F#": "파#", G: "솔",
    "G#": "솔#", A: "라", "A#": "라#", B: "시",
  };

  // ===== Utility Functions =====
  function noteToVexflow(n) {
    let match = n.match(/^([A-G]#?)(\d)$/);
    if (!match) return null;
    const step = match[1].toLowerCase();
    const octave = match[2];
    return `${step}/${octave}`;
  }

  function getDoremi(n) {
    const match = n.match(/^([A-G]#?)(\d)$/);
    if (!match) return "--";
    const note = match[1];
    return noteToDoremiMap[note] || "--";
  }

  function getOctave(n) {
    const match = n.match(/^([A-G]#?)(\d)$/);
    if (!match) return "--";
    return match[2];
  }

  function updateStatus(message, type = 'normal') {
    statusDiv.textContent = message;
    statusDiv.classList.remove('loading');
    if (type === 'loading') statusDiv.classList.add('loading');
  }

  function calcRMS(buf) {
    let sum = 0;
    for (let i = 0; i < buf.length; i++) sum += buf[i] * buf[i];
    return Math.sqrt(sum / buf.length);
  }

  function autoCorrelate(buffer, sampleRate) {
    const SIZE = buffer.length;
    const MAX_SAMPLES = Math.floor(SIZE / 2);
    let bestOffset = -1;
    let bestCorrelation = 0;
    let rms = 0;
    const correlations = new Array(MAX_SAMPLES);

    for (let i = 0; i < SIZE; i++) {
      const val = buffer[i];
      rms += val * val;
    }
    rms = Math.sqrt(rms / SIZE);
    if (rms < 0.01) return -1;

    let lastCorrelation = 1;
    let foundGoodCorrelation = false;
    for (let offset = 0; offset < MAX_SAMPLES; offset++) {
      let correlation = 0;
      for (let i = 0; i < MAX_SAMPLES; i++) {
        correlation += Math.abs(buffer[i] - buffer[i + offset]);
      }
      correlation = 1 - correlation / MAX_SAMPLES;
      correlations[offset] = correlation;

      if (correlation > 0.9 && correlation > lastCorrelation) {
        foundGoodCorrelation = true;
        if (correlation > bestCorrelation) {
          bestCorrelation = correlation;
          bestOffset = offset;
        }
      } else if (foundGoodCorrelation) {
        const shift = (correlations[bestOffset + 1] - correlations[bestOffset - 1]) / correlations[bestOffset];
        return sampleRate / (bestOffset + 8 * shift);
      }
      lastCorrelation = correlation;
    }
    if (bestCorrelation > 0.01) {
      return sampleRate / bestOffset;
    }
    return -1;
  }

  function frequencyToNote(freq) {
    if (freq === -1) return "--";
    const noteNum = 12 * (Math.log2(freq / 440)) + 69;
    const noteIndex = Math.round(noteNum) % 12;
    const octave = Math.floor(Math.round(noteNum) / 12) - 1;
    const noteStrings = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
    return noteStrings[noteIndex] + octave;
  }

  function weightedAverage(arr) {
    let weightSum = 0;
    let weightedValSum = 0;
    for (let i = 0; i < arr.length; i++) {
      const weight = i + 1;
      weightSum += weight;
      weightedValSum += arr[i] * weight;
    }
    return weightedValSum / weightSum;
  }

  function median(arr) {
    if (!arr.length) return 0;
    const a = arr.slice().sort((x, y) => x - y);
    const m = Math.floor(a.length / 2);
    return a.length % 2 ? a[m] : (a[m - 1] + a[m]) / 2;
  }

  function spectralFlux(curr, prev) {
    if (!prev || prev.length !== curr.length) return 0;
    let sum = 0;
    for (let i = 0; i < curr.length; i++) {
      const d = curr[i] - prev[i];
      if (d > 0) sum += d;
    }
    return sum;
  }

  function dbToMag(db) {
    // convert dB to linear magnitude
    return Math.pow(10, db / 20);
  }

  function adaptiveThreshold(values, k = 1.5) {
    if (values.length < 2) return Infinity;
    const mean = values.reduce((a, b) => a + b, 0) / values.length;
    const variance = values.reduce((a, b) => a + (b - mean) * (b - mean), 0) / values.length;
    const std = Math.sqrt(Math.max(variance, 1e-8));
    return mean + k * std;
  }

  // ===== VexFlow Rendering =====
  function drawEmptyStave(timeSignature = "4/4") {
    outputDiv.innerHTML = "";
    const renderer = new VF.Renderer(outputDiv, VF.Renderer.Backends.SVG);
    renderer.resize(600, 180);
    const context = renderer.getContext();
    const stave = new VF.Stave(10, 40, 580);
    stave.addClef("treble").addTimeSignature(timeSignature);
    stave.setContext(context).draw();
  }

  function buildStaveNote(VF, key, duration, lyricText = "") {
    const note = new VF.StaveNote({ clef: "treble", keys: [key], duration });
    // Accidentals
    if (key.includes("#")) {
      note.addAccidental(0, new VF.Accidental("#"));
    }
    // Lyric annotation (below staff)
    if (lyricText) {
      const ann = new VF.Annotation(lyricText);
      ann.setJustification(VF.Annotation.Justify.CENTER);
      ann.setVerticalJustification(VF.Annotation.VerticalJustify.BOTTOM);
      note.addModifier(ann);
    }
    return note;
  }

  function drawNotesWithObjects(noteObjs, timeSignature = "4/4") {
    if (!noteObjs.length) {
      drawEmptyStave(timeSignature);
      return;
    }
    outputDiv.innerHTML = "";
    const renderer = new VF.Renderer(outputDiv, VF.Renderer.Backends.SVG);
    renderer.resize(900, 220);
    const context = renderer.getContext();
    const stave = new VF.Stave(10, 40, 880);
    stave.addClef("treble").addTimeSignature(timeSignature);
    stave.setContext(context).draw();

    const notes = noteObjs.map(o => buildStaveNote(VF, o.key, o.duration, o.lyric || ""));

    const beats = parseInt(timeSignature.split("/")[0]);
    const beatValue = parseInt(timeSignature.split("/")[1]);

    const voice = new VF.Voice({
      num_beats: Math.max(beats, notes.length),
      beat_value: beatValue,
      strict: false,
    });
    voice.addTickables(notes);

    new VF.Formatter().joinVoices([voice]).format([voice], 820);
    voice.draw(context, stave);
  }

  // Initialize empty stave
  drawEmptyStave("4/4");

  // ===== Metronome (unchanged) =====
  function setupMetronomeAudio() {
    if (!audioContext) audioContext = new (window.AudioContext || window.webkitAudioContext)();
    if (!metronomeGainNode) {
      metronomeGainNode = audioContext.createGain();
      metronomeGainNode.gain.value = metronomeVolumeSlider.value / 100;
      metronomeGainNode.connect(audioContext.destination);
    }
  }

  function playMetronomeClick() {
    setupMetronomeAudio();
    const source = audioContext.createBufferSource();
    const request = new XMLHttpRequest();
    request.open("GET", metronomeSound.src, true);
    request.responseType = "arraybuffer";
    request.onload = () => {
      audioContext.decodeAudioData(request.response, (buffer) => {
        source.buffer = buffer;
        source.connect(metronomeGainNode);
        source.start(0);
      });
    };
    request.send();
  }

  function drawNotesLegacy(notesArr, timeSignature = "4/4") {
    if (notesArr.length === 0) {
      drawEmptyStave(timeSignature);
      return;
    }
    outputDiv.innerHTML = "";
    const renderer = new VF.Renderer(outputDiv, VF.Renderer.Backends.SVG);
    renderer.resize(600, 160);
    const context = renderer.getContext();
    const stave = new VF.Stave(10, 40, 580);
    stave.addClef("treble").addTimeSignature(timeSignature);
    stave.setContext(context).draw();

    const notes = notesArr.map(noteStr =>
      new VF.StaveNote({ clef: "treble", keys: [noteStr], duration: "q" })
    );

    const beats = parseInt(timeSignature.split("/")[0]);
    const beatValue = parseInt(timeSignature.split("/")[1]);

    const voice = new VF.Voice({
      num_beats: Math.max(beats, notesArr.length),
      beat_value: beatValue,
      strict: false,
    });
    voice.addTickables(notes);

    new VF.Formatter().joinVoices([voice]).format([voice], 500);
    voice.draw(context, stave);
  }

  function startMetronome() {
    const intervalMs = Math.floor(60000 / bpmSlider.value);
    if (metronomeInterval) clearInterval(metronomeInterval);

    metronomeInterval = setInterval(() => {
      // If free mode is on, avoid overwriting free transcription rendering
      if (freeModeOn) {
        playMetronomeClick();
        return;
      }

      playMetronomeClick();

      if (pitchHistory.length) {
        const avgPitch = weightedAverage(pitchHistory);
        const noteName = frequencyToNote(avgPitch);
        const vfNote = noteToVexflow(noteName);
        if (vfNote) {
          staveNotes.push(vfNote);
          if (staveNotes.length > 16) staveNotes.shift();
          const numerator = parseInt(numeratorInput.value);
          const denominator = parseInt(denominatorInput.value);
          const validNumerator = numerator >= 1 && numerator <= 16 ? numerator : 4;
          const validDenominator = [1, 2, 4, 8, 16, 32].includes(denominator) ? denominator : 4;
          const timeSignature = `${validNumerator}/${validDenominator}`;
          drawNotesLegacy(staveNotes, timeSignature);
        }
      }
    }, intervalMs);

    toggleMetronomeBtn.innerHTML = '<span class="btn-icon">⏹️</span>메트로놈 끄기';
    metronomeOn = true;
    updateStatus(`메트로놈 작동 중 (BPM: ${bpmSlider.value})`);
  }

  function stopMetronome() {
    clearInterval(metronomeInterval);
    metronomeInterval = null;
    toggleMetronomeBtn.innerHTML = '<span class="btn-icon">⏱️</span>메트로놈 켜기';
    metronomeOn = false;
    updateStatus("메트로놈 정지됨");
  }

  // ===== Lyrics handling =====
  function splitHangulSyllables(str) {
    const chars = Array.from(str).filter(ch => /\p{Script=Hangul}/u.test(ch));
    return chars;
  }

  function splitByWords(str) {
    return str.trim().split(/\s+/).filter(Boolean);
  }

  loadLyricsBtn.onclick = () => {
    const val = lyricsInput.value || "";
    const sel = document.querySelector('input[name="lyrMode"]:checked').value;
    lyricMode = sel;
    if (sel === "syllable") {
      lyricsTokens = splitHangulSyllables(val);
    } else {
      lyricsTokens = splitByWords(val);
    }
    lyricsIndex = 0;
    updateStatus(`가사 로드됨 (${lyricsTokens.length} 토큰)`);
  };

  // ===== Duration quantization =====
  function currentBaseQuarterSec() {
    if (!ioiList.length) return 0.5; // fallback quarter ≈ 0.5s
    return median(ioiList);
  }

  function quantizeDuration(dSec) {
    const Q = currentBaseQuarterSec();
    const candidates = [
      { name: "32", sec: Q / 8 },
      { name: "16", sec: Q / 4 },
      { name: "8", sec: Q / 2 },
      { name: "q", sec: Q },
      { name: "h", sec: 2 * Q },
      { name: "w", sec: 4 * Q },
    ];
    let best = candidates[0];
    let minErr = Math.abs(dSec - candidates[0].sec);
    for (let i = 1; i < candidates.length; i++) {
      const e = Math.abs(dSec - candidates[i].sec);
      if (e < minErr) {
        minErr = e;
        best = candidates[i];
      }
    }
    return best.name;
  }

  // ===== Free transcription (onset-based) =====
  function startSegment(t) {
    segmentActive = true;
    segmentStartTime = t;
    segmentPitchFrames = [];
  }

  function finalizeSegment(tEnd) {
    if (!segmentActive) return;
    const dur = tEnd - segmentStartTime;
    segmentActive = false;
    if (dur < minDur) return;

    // Representative pitch
    const validPitches = segmentPitchFrames.filter(p => p > 0);
    if (!validPitches.length) return;
    const repHz = median(validPitches);
    const noteName = frequencyToNote(repHz);
    const vfKey = noteToVexflow(noteName);
    if (!vfKey) return;

    // IOI update
    if (lastOnsetTime != null) {
      const ioi = segmentStartTime - lastOnsetTime;
      if (ioi > minIOI) {
        ioiList.push(ioi);
        if (ioiList.length > ioiWindow) ioiList.shift();
      }
    }
    lastOnsetTime = segmentStartTime;

    // Duration quantization
    const durName = quantizeDuration(dur);

    // Lyric token
    let lyr = "";
    if (lyricsIndex < lyricsTokens.length) {
      lyr = lyricsTokens[lyricsIndex++];
    }

    freeNotes.push({ key: vfKey, duration: durName, lyric: lyr });
    if (freeNotes.length > maxFreeNotes) freeNotes.shift();

    // Render
    const numerator = parseInt(numeratorInput.value);
    const denominator = parseInt(denominatorInput.value);
    const validNum = numerator >= 1 && numerator <= 16 ? numerator : 4;
    const validDen = [1, 2, 4, 8, 16, 32].includes(denominator) ? denominator : 4;
    const timeSignature = `${validNum}/${validDen}`;
    drawNotesWithObjects(freeNotes, timeSignature);
  }

  function processOnsetAndPitch(arrayTD, timeNow) {
    // Pitch
    const pitch = autoCorrelate(arrayTD, audioContext.sampleRate);

    // Display panels
    if (pitch !== -1) {
      pitchHistory.push(pitch);
      if (pitchHistory.length > maxHistory) pitchHistory.shift();

      const avgPitch = weightedAverage(pitchHistory);
      const noteName = frequencyToNote(avgPitch);
      pitchDiv.textContent = noteName;
      doremiDiv.textContent = getDoremi(noteName);
      octaveDiv.textContent = getOctave(noteName);
      frequencyDiv.textContent = `${avgPitch.toFixed(2)} Hz`;

      lastVoicedTime = timeNow;
      if (segmentActive) segmentPitchFrames.push(pitch);
    } else {
      // keep UI calm when unvoiced
      pitchDiv.textContent = "--";
      doremiDiv.textContent = "--";
      octaveDiv.textContent = "--";
      frequencyDiv.textContent = "-- Hz";
    }

    // RMS for gate
    const rms = calcRMS(arrayTD);

    // Spectrum and spectral flux
    const freqBins = analyser.frequencyBinCount;
    const specDb = new Float32Array(freqBins);
    analyser.getFloatFrequencyData(specDb);
    // Convert to magnitudes for flux
    const specMag = new Float32Array(freqBins);
    for (let i = 0; i < freqBins; i++) {
      specMag[i] = dbToMag(specDb[i]);
    }

    let flux = 0;
    if (prevSpectrum) {
      flux = spectralFlux(specMag, prevSpectrum);
      fluxHistory.push(flux);
      if (fluxHistory.length > fluxWindow) fluxHistory.shift();
    }
    prevSpectrum = specMag;

    // Adaptive thresholding
    const thr = adaptiveThreshold(fluxHistory, fluxK);

    // Onset decision
    const voiced = (pitch !== -1) && (rms > 0.01);
    const tooSoon = (lastOnsetTime != null) && ((timeNow - lastOnsetTime) < minIOI);
    const isOnset = voiced && (flux > thr) && !tooSoon;

    if (isOnset) {
      // close previous segment
      if (segmentActive) {
        finalizeSegment(timeNow);
      }
      // start new
      startSegment(timeNow);
      updateStatus("🎶 온셋 감지됨");
    }

    // End segment on sustained silence/unvoiced
    const sinceVoiced = timeNow - lastVoicedTime;
    if (segmentActive && sinceVoiced > 0.25 && rms < 0.008) {
      finalizeSegment(timeNow);
      updateStatus("🛑 구간 종료");
    }
  }

  // ===== Event Listeners =====
  toggleMetronomeBtn.onclick = () => {
    if (metronomeOn) stopMetronome();
    else startMetronome();
  };

  toggleFreeModeBtn.onclick = () => {
    freeModeOn = !freeModeOn;
    toggleFreeModeBtn.textContent = `🎶 자유 채보: ${freeModeOn ? "켜짐" : "꺼짐"}`;
    if (freeModeOn) {
      // prefer showing free notes if exist
      drawNotesWithObjects(freeNotes, `${numeratorInput.value}/${denominatorInput.value}`);
    } else {
      // fall back to legacy view
      drawNotesLegacy(staveNotes, `${numeratorInput.value}/${denominatorInput.value}`);
    }
  };

  clearFreeNotesBtn.onclick = () => {
    freeNotes = [];
    drawEmptyStave(`${numeratorInput.value}/${denominatorInput.value}`);
  };

  bpmSlider.oninput = () => {
    bpmVal.textContent = bpmSlider.value;
    if (metronomeOn) {
      stopMetronome();
      startMetronome();
    }
  };

  metronomeVolumeSlider.oninput = () => {
    const vol = metronomeVolumeSlider.value;
    volValSpan.textContent = vol;
    if (metronomeGainNode) {
      metronomeGainNode.gain.value = vol / 100;
    }
  };

  numeratorInput.oninput = denominatorInput.oninput = () => {
    const numerator = parseInt(numeratorInput.value);
    const denominator = parseInt(denominatorInput.value);
    const validNum = numerator >= 1 && numerator <= 16 ? numerator : 4;
    const validDen = [1, 2, 4, 8, 16, 32].includes(denominator) ? denominator : 4;
    if (freeModeOn) drawEmptyStave(`${validNum}/${validDen}`);
    else drawEmptyStave(`${validNum}/${validDen}`);
  };

  // ===== Main Audio Processing =====
  let isRunning = false; // track start/stop state

  startBtn.onclick = async () => {
    if (!isRunning) {
      // ===== START =====
      try {
        updateStatus("마이크 권한 요청 중...", 'loading');

        if (!audioContext) audioContext = new (window.AudioContext || window.webkitAudioContext)();
        if (audioContext.state === "suspended") await audioContext.resume();

        const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
        microphone = audioContext.createMediaStreamSource(stream);
        analyser = audioContext.createAnalyser();
        analyser.fftSize = 2048;
        analyser.smoothingTimeConstant = 0.0;
        scriptProcessor = audioContext.createScriptProcessor(2048, 1, 1);

        microphone.connect(analyser);
        analyser.connect(scriptProcessor);
        scriptProcessor.connect(audioContext.destination);

        scriptProcessor.onaudioprocess = () => {
          const arrayTD = new Float32Array(analyser.fftSize);
          analyser.getFloatTimeDomainData(arrayTD);

          if (freeModeOn) {
            const now = audioContext.currentTime;
            processOnsetAndPitch(arrayTD, now);
          } else {
            const pitch = autoCorrelate(arrayTD, audioContext.sampleRate);
            if (pitch !== -1) {
              pitchHistory.push(pitch);
              if (pitchHistory.length > maxHistory) pitchHistory.shift();
              const avgPitch = weightedAverage(pitchHistory);
              const noteName = frequencyToNote(avgPitch);
              pitchDiv.textContent = noteName;
              doremiDiv.textContent = getDoremi(noteName);
              octaveDiv.textContent = getOctave(noteName);
              frequencyDiv.textContent = `${avgPitch.toFixed(2)} Hz`;
              updateStatus("🎵 음성 분석 중");
            } else {
              pitchDiv.textContent = "--";
              doremiDiv.textContent = "--";
              octaveDiv.textContent = "--";
              frequencyDiv.textContent = "-- Hz";
              updateStatus("🎤 음성 대기 중");
            }
          }
        };

        // update button state
        startBtn.innerHTML = '<span class="btn-icon">⏹️</span>종료하기';
        startBtn.classList.add("running");
        updateStatus("🎵 마이크 활성화 완료");
        isRunning = true;

      } catch (err) {
        updateStatus("❌ 마이크 권한이 거부되었습니다");
        console.error("마이크 접근 오류:", err);
      }

    } else {
      // ===== STOP =====
      if (scriptProcessor) {
        scriptProcessor.disconnect();
        scriptProcessor = null;
      }
      if (analyser) {
        analyser.disconnect();
        analyser = null;
      }
      if (microphone) {
        microphone.disconnect();
        microphone = null;
      }
      if (audioContext && audioContext.state !== "closed") {
        audioContext.close();
        audioContext = null;
      }

      // update button state
      startBtn.innerHTML = '<span class="btn-icon">🎤</span>시작하기';
      startBtn.classList.remove("running");
      updateStatus("🛑 분석 종료됨");
      isRunning = false;
    }
  };
}