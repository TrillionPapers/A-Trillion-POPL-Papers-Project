// Plays a talk as a video. The page holds a frame with the scenes of the talk and, below it, the
// lines that are said. This script hands the lines, one by one, to the speech synthesis of the
// browser and tells the frame how far the talk has come, so that the picture moves with the
// voice. Where there is no voice, a line stays for as long as reading it takes.
//
// The frame runs no script and loads nothing from outside. It is drawn by style sheets alone, and
// this script only sets classes in it; site/talk-scene.css says which. Without this script the
// page shows the text of the talk.
(() => {
  "use strict";

  const root = document.querySelector(".talk");
  if (!root) return;
  const screen = root.querySelector(".screen");
  const frame = root.querySelector("iframe");
  const scenes = Array.from({ length: Number(root.dataset.scenes) || 0 }, () => []);
  for (const span of document.querySelectorAll(".transcript [data-scene]")) {
    const scene = scenes[Number(span.dataset.scene)];
    if (scene) scene.push(span);
  }
  if (!screen || !frame || !scenes.length) return;
  const synth = "speechSynthesis" in window && "SpeechSynthesisUtterance" in window
    ? window.speechSynthesis : null;

  const PACE = 60 / 185;   // seconds for a word, as measured with one voice in one browser
  const GAP = 0.3;         // seconds between two scenes
  const rates = [0.85, 1, 1.2, 1.5];
  const wordsOf = text => (text.trim() ? text.trim().split(/\s+/).length : 0);
  const starts = [];       // for every scene, the time at which each of its lines begins
  let total = 0;
  for (const scene of scenes) {
    const times = [];
    for (const span of scene) {
      times.push(total);
      total += Math.max(0.7, wordsOf(span.textContent) * PACE);
    }
    if (!scene.length) {
      times.push(total);
      total += 1.5;
    }
    starts.push(times);
    total += GAP;
  }

  let at = 0;            // the scene that is shown
  let line = 0;          // the line of that scene
  let playing = false;
  let begun = false;     // whether the talk has been played or stepped through at all
  let ended = false;
  let rested = true;     // the picture is the still picture of its line
  let turn = 0;          // counts what is started, so that an answer to something older is ignored
  let timer = 0;
  let speech = null;     // the utterance in the air; some browsers drop one that nothing refers to
  let cutAt = 0;         // when the voice was last cut off
  let voices = [];
  let voice = null;      // null: no voice, the text alone
  let rate = 1;
  let captions = true;
  let stage = [];        // the scenes inside the frame

  const recall = key => {
    try { return localStorage.getItem(key); } catch (error) { return null; }
  };
  const remember = (key, value) => {
    try { localStorage.setItem(key, value); } catch (error) { /* the choice lasts for this visit */ }
  };

  // ---------------------------------------------------------------------------------------
  // The picture

  const doc = () => {
    try { return frame.contentDocument; } catch (error) { return null; }
  };
  const number = value => Math.round(value).toLocaleString("en-US");
  const counting = new WeakMap();

  function setStep(index, step) {
    const el = stage[index];
    if (!el) return;
    for (let k = 1; k <= Math.max(scenes[index].length, 1); k++) el.classList.toggle(`s${k}`, k <= step);
    el.dataset.step = String(step);
    for (const item of el.querySelectorAll("[data-in]")) item.classList.toggle("in", Number(item.dataset.in) <= step);
    for (const item of el.querySelectorAll("[data-out]")) item.classList.toggle("out", Number(item.dataset.out) <= step);
    for (const item of el.querySelectorAll("[data-fade]")) item.classList.toggle("faded", Number(item.dataset.fade) <= step);
    for (const item of el.querySelectorAll("[data-hot]")) {
      item.classList.toggle("hot", item.dataset.hot.split(/\s+/).includes(String(step)));
    }
  }

  // Numbers that count up when they come in. A still picture shows where they end.
  function setCounts(index, step, still) {
    const el = stage[index];
    if (!el) return;
    for (const item of el.querySelectorAll("[data-count]")) {
      const from = Number(item.dataset.from) || 0;
      const to = Number(item.dataset.count) || 0;
      const due = (Number(item.dataset.in) || 1) <= step;
      const state = counting.get(item) || {};
      if (!due || still) {
        cancelAnimationFrame(state.frame);
        counting.set(item, { done: due });
        item.textContent = number(due ? to : from);
        continue;
      }
      if (state.done || state.frame) continue;
      const length = Number(item.dataset.ms) || 1400;
      const began = performance.now();
      const tick = now => {
        const t = Math.min(1, (now - began) / length);
        const eased = "even" in item.dataset ? t : 1 - (1 - t) ** 3;
        item.textContent = number(from + (to - from) * eased);
        counting.set(item, t < 1 ? { frame: requestAnimationFrame(tick) } : { done: true });
      };
      counting.set(item, { frame: requestAnimationFrame(tick) });
    }
  }

  // Ends whatever is still moving, so that a picture is the picture of its line.
  function settle(page) {
    if (!page.getAnimations) return;
    for (const animation of page.getAnimations()) {
      try {
        if (animation.effect.getComputedTiming().iterations !== Infinity) animation.finish();
      } catch (error) { /* one that never ends */ }
    }
  }

  const show = index => stage.forEach((el, i) => el.classList.toggle("current", i === index));

  // The still picture of a line.
  function still(index, step) {
    const page = doc();
    if (!page || !stage.length) return;
    const html = page.documentElement;
    html.classList.add("snap");
    setStep(index, step);
    setCounts(index, step, true);
    show(index);
    void html.offsetWidth;
    settle(page);
    html.classList.remove("snap");
    rested = true;
  }

  // A line begins: the picture of the line before it, and then what the line sets in motion.
  function enter(index, step) {
    const page = doc();
    if (!page || !stage.length) return;
    const html = page.documentElement;
    html.classList.add("snap");
    setStep(index, step - 1);
    setCounts(index, step - 1, true);
    void html.offsetWidth;
    settle(page);
    html.classList.remove("snap");
    show(index);
    setStep(index, step);
    setCounts(index, step, false);
    rested = false;
  }

  function fit() {
    const page = doc();
    if (page) page.documentElement.style.setProperty("--k", String(frame.clientWidth / 1280));
  }

  function bind() {
    const page = doc();
    stage = page ? Array.from(page.querySelectorAll("section.scene")) : [];
    if (!stage.length) return;
    page.documentElement.classList.add("driven");
    fit();
    if (playing) enter(at, line + 1);
    else still(at, line + 1);
    render();
  }

  // ---------------------------------------------------------------------------------------
  // The controls

  const icons = {
    play: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 5v14l11-7z"/></svg>',
    pause: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M6 5h4v14H6zm8 0h4v14h-4z"/></svg>',
    again: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 5V1.5L6.5 6 12 10.5V7a5 5 0 1 1-5 5H5a7 7 0 1 0 7-7z"/></svg>',
    full: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M5 5h5v2H7v3H5zm9 0h5v5h-2V7h-3zM5 14h2v3h3v2H5zm12 0h2v5h-5v-2h3z"/></svg>',
  };
  const make = (tag, name, text) => {
    const el = document.createElement(tag);
    if (name) el.className = name;
    if (text) el.textContent = text;
    if (tag === "button") el.type = "button";
    return el;
  };
  const big = make("div", "bigplay");
  const caption = make("p", "caption");
  const controls = make("div", "controls");
  const playButton = make("button", "play");
  const track = make("div", "track");
  const time = make("span", "time");
  const captionButton = make("button", "cc", "CC");
  const rateSelect = make("select");
  const voiceSelect = make("select");
  const fullButton = make("button", "full");
  const note = make("p", "note");
  const titles = Array.from(document.querySelectorAll(".transcript li"), item => {
    const heading = item.querySelector("h3");
    return heading ? heading.textContent : "";
  });
  const segments = scenes.map((scene, index) => {
    const segment = make("button", "seg");
    segment.style.flexGrow = String((starts[index + 1] ? starts[index + 1][0] : total) - starts[index][0]);
    segment.title = titles[index] || `Scene ${index + 1}`;
    segment.setAttribute("aria-label", `Scene ${index + 1}: ${segment.title}`);
    segment.append(make("i"));
    segment.addEventListener("click", () => go(index, 0));
    track.append(segment);
    return segment;
  });
  captionButton.setAttribute("aria-label", "Captions");
  fullButton.setAttribute("aria-label", "Full screen");
  fullButton.innerHTML = icons.full;
  rateSelect.setAttribute("aria-label", "Speed");
  voiceSelect.setAttribute("aria-label", "Voice");
  for (const value of rates) rateSelect.append(new Option(`${value}×`, String(value)));
  screen.append(big, caption);
  controls.append(playButton, track, time, captionButton, rateSelect, voiceSelect, fullButton);
  root.append(controls, note);
  root.classList.add("player");
  const transcript = document.querySelector(".transcript");
  if (transcript) transcript.open = false;

  const clock = value => `${Math.floor(value / 60)}:${String(Math.floor(value % 60)).padStart(2, "0")}`;

  function render() {
    const said = scenes[at][line];
    caption.textContent = begun && !ended && said ? said.textContent : "";
    caption.hidden = !captions || !caption.textContent;
    segments.forEach((segment, index) => {
      const done = ended || index < at ? 1 : index > at ? 0 : line / Math.max(scenes[index].length, 1);
      segment.firstChild.style.width = `${100 * done}%`;
    });
    time.textContent = `${clock(ended ? total : starts[at][line] || 0)} / ${clock(total)}`;
    playButton.innerHTML = playing ? icons.pause : ended ? icons.again : icons.play;
    playButton.setAttribute("aria-label", playing ? "Pause" : ended ? "Play again" : "Play");
    big.innerHTML = ended ? icons.again : icons.play;
    big.hidden = playing;
    captionButton.classList.toggle("on", captions);
    captionButton.setAttribute("aria-pressed", String(captions));
    root.dataset.state = playing ? "playing" : ended ? "ended" : "paused";
    scenes.forEach((scene, index) => scene.forEach((span, n) => {
      span.classList.toggle("now", begun && !ended && index === at && n === line);
    }));
    const page = doc();
    if (page) page.documentElement.classList.toggle("paused", !playing);
  }

  function tell(problem) {
    const keys = " Space plays and pauses, and the arrow keys move by one line.";
    if (problem) note.textContent = problem + keys;
    else if (!synth) note.textContent = "This browser has no speech synthesis, so the talk plays without a voice." + keys;
    else if (!voices.length && begun) note.textContent = "This browser offers no English voice, so the talk plays without a voice." + keys;
    else if (!voice && voices.length) note.textContent = "No voice is chosen, so the talk plays without one." + keys;
    else note.textContent = "The voice is the speech synthesis of your browser." + keys;
  }

  // ---------------------------------------------------------------------------------------
  // Voices

  // Voices of macOS that are jokes or sound like a machine of 1984.
  const odd = /^(Albert|Bad News|Bahh|Bells|Boing|Bubbles|Cellos|Good News|Jester|Organ|Superstar|Trinoids|Whisper|Wobble|Zarvox|Fred|Junior|Kathy|Ralph|Eddy|Flo|Grandma|Grandpa|Reed|Rocko|Sandy|Shelley)\b/;
  const known = /^(Samantha|Daniel|Karen|Moira|Tessa|Ava|Allison|Susan|Tom|Evan|Zoe|Alex|Serena|Kate|Oliver|Nicky)\b/;

  function worth(candidate) {
    let points = 0;
    if (/natural|neural/i.test(candidate.name)) points += 6;
    if (/premium|enhanced/i.test(candidate.name)) points += 5;
    if (/^Google (US|UK) English/.test(candidate.name)) points += 4;
    if (known.test(candidate.name)) points += 3;
    if (candidate.default) points += 2;
    if (/^en[-_]US/i.test(candidate.lang)) points += 1;
    if (odd.test(candidate.name)) points -= 9;
    return points;
  }

  function loadVoices() {
    const found = synth ? synth.getVoices().filter(item => /^en([-_]|$)/i.test(item.lang)) : [];
    found.sort((a, b) => worth(b) - worth(a) || a.name.localeCompare(b.name));
    voices = found;
    const wanted = recall("talk.voice");
    let pick = voices.findIndex(item => item.name === wanted);
    if (pick < 0 && wanted !== "none" && voices.length) pick = 0;
    voice = pick < 0 ? null : voices[pick];
    voiceSelect.replaceChildren();
    voices.forEach((item, index) => voiceSelect.append(new Option(item.name, String(index))));
    voiceSelect.append(new Option("No voice", "none"));
    voiceSelect.value = pick < 0 ? "none" : String(pick);
    voiceSelect.disabled = !voices.length;
    tell();
  }

  // ---------------------------------------------------------------------------------------
  // Speaking

  function cut() {
    turn++;
    clearTimeout(timer);
    if (synth && (synth.speaking || synth.pending)) {
      synth.cancel();
      cutAt = Date.now();
    }
  }

  function say() {
    const mine = ++turn;
    clearTimeout(timer);
    const said = scenes[at][line];
    const text = said ? said.textContent.trim() : "";
    const words = wordsOf(text);
    let over = false;
    const done = () => {
      if (over || mine !== turn) return;
      over = true;
      clearTimeout(timer);
      if (playing) advance();
    };
    if (!text || !voice) {
      timer = setTimeout(done, text ? (300 + 1000 * PACE * words) / rate : 1500);
      return;
    }
    const silent = reason => {
      // the voice failed: the talk goes on without one, from this line
      if (over || mine !== turn) return;
      over = true;
      synth.cancel();
      voice = null;
      voiceSelect.value = "none";
      tell(`The voice failed (${reason}), so the talk goes on without one.`);
      if (playing) say();
    };
    const utterance = new SpeechSynthesisUtterance(text);
    utterance.voice = voice;
    utterance.lang = voice.lang.replace("_", "-");
    utterance.rate = rate;
    utterance.onend = done;
    utterance.onerror = event => {
      if (event.error !== "interrupted" && event.error !== "canceled") silent(event.error || "error");
    };
    speech = utterance;
    const start = () => {
      if (mine !== turn) return;
      const began = Date.now();
      synth.speak(utterance);
      // Some browsers do not report the end of every utterance. So the script also looks:
      // when the voice has fallen silent, the line is over.
      const look = () => {
        if (over || mine !== turn) return;
        if (!synth.speaking && !synth.pending) done();
        else if (Date.now() - began > (8000 + 1500 * words) / rate) silent("no end");
        else timer = setTimeout(look, 700);
      };
      timer = setTimeout(look, (1500 + 600 * words) / rate);
    };
    // A voice that was cut off a moment ago may swallow what is said right after.
    if (Date.now() - cutAt < 200) timer = setTimeout(start, 200);
    else start();
  }

  function advance() {
    if (line + 1 < scenes[at].length) {
      line++;
      setStep(at, line + 1);
      setCounts(at, line + 1, false);
      render();
      say();
    } else if (at + 1 < scenes.length) {
      at++;
      line = 0;
      enter(at, 1);
      render();
      const mine = ++turn;
      timer = setTimeout(() => { if (mine === turn && playing) say(); }, 1000 * GAP);
    } else {
      playing = false;
      ended = true;
      render();
    }
  }

  function play() {
    if (ended) {
      at = 0;
      line = 0;
      ended = false;
      rested = true;
    }
    begun = true;
    playing = true;
    if (!voices.length) loadVoices();
    if (rested) enter(at, line + 1);
    render();
    say();
  }

  function pause() {
    playing = false;
    cut();
    render();
  }

  const toggle = () => (playing ? pause() : play());

  // Moves to a line. A talk that was playing goes on from there.
  function go(scene, sentence) {
    cut();
    at = Math.max(0, Math.min(scenes.length - 1, scene));
    line = Math.max(0, Math.min(scenes[at].length - 1, sentence));
    begun = true;
    ended = false;
    if (playing) enter(at, line + 1);
    else still(at, line + 1);
    render();
    if (playing) say();
  }

  const nextScene = () => { if (at + 1 < scenes.length) go(at + 1, 0); };
  const backScene = () => go(line > 0 || at === 0 ? at : at - 1, 0);

  function step(by) {
    if (by > 0) {
      if (line + 1 < scenes[at].length) go(at, line + 1);
      else nextScene();
    } else if (line > 0) go(at, line - 1);
    else if (at > 0) go(at - 1, scenes[at - 1].length - 1);
  }

  // ---------------------------------------------------------------------------------------
  // Wiring

  playButton.addEventListener("click", toggle);
  screen.addEventListener("click", toggle);
  captionButton.addEventListener("click", () => {
    captions = !captions;
    remember("talk.captions", captions ? "on" : "off");
    render();
  });
  voiceSelect.addEventListener("change", () => {
    voice = voiceSelect.value === "none" ? null : voices[Number(voiceSelect.value)] || null;
    remember("talk.voice", voice ? voice.name : "none");
    tell();
    if (playing) go(at, line);
  });
  rateSelect.addEventListener("change", () => {
    rate = Number(rateSelect.value) || 1;
    remember("talk.rate", String(rate));
    if (playing) go(at, line);
  });
  const enterFull = root.requestFullscreen || root.webkitRequestFullscreen;
  const leaveFull = document.exitFullscreen || document.webkitExitFullscreen;
  if (!enterFull || !leaveFull) fullButton.hidden = true;
  fullButton.addEventListener("click", () => {
    if (document.fullscreenElement || document.webkitFullscreenElement) leaveFull.call(document);
    else enterFull.call(root);
  });
  if (transcript) {
    transcript.addEventListener("click", event => {
      const span = event.target.closest("[data-scene]");
      if (span) go(Number(span.dataset.scene), Number(span.dataset.line));
    });
  }
  document.addEventListener("keydown", event => {
    if (event.defaultPrevented || event.altKey || event.ctrlKey || event.metaKey) return;
    const target = event.target instanceof Element ? event.target : document.body;
    if (target.closest("input, select, textarea")) return;
    const key = event.key;
    if (key === " " || key === "k") {
      if (key === " " && target.closest("button, a, summary")) return;   // it does that itself
      toggle();
    } else if (key === "ArrowRight") step(1);
    else if (key === "ArrowLeft") step(-1);
    else if (key === "PageDown") nextScene();
    else if (key === "PageUp") backScene();
    else if (key === "c") captionButton.click();
    else if (key === "f" && !fullButton.hidden) fullButton.click();
    else return;
    event.preventDefault();
  });
  window.addEventListener("pagehide", () => { if (synth) synth.cancel(); });
  if ("ResizeObserver" in window) new ResizeObserver(fit).observe(frame);
  else window.addEventListener("resize", fit);
  frame.addEventListener("load", bind);

  const saved = Number(recall("talk.rate"));
  if (rates.includes(saved)) rate = saved;
  rateSelect.value = String(rate);
  captions = recall("talk.captions") !== "off";
  const linked = /^#scene-(\d+)$/.exec(location.hash);
  if (linked) at = Math.max(0, Math.min(scenes.length - 1, Number(linked[1]) - 1));
  if (synth) {
    synth.cancel();   // a voice may still be speaking for the page that was here before
    if (synth.addEventListener) synth.addEventListener("voiceschanged", loadVoices);
    else synth.onvoiceschanged = loadVoices;
  }
  loadVoices();
  bind();
  render();
})();
