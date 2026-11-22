// Plays a talk as a video. The page holds a frame with the scenes of the talk and, below it, the
// lines that are said. This script hands the lines, one by one, to the speech synthesis of the
// browser and tells the frame how far the talk has come, down to the word, so that the picture
// moves with the voice. Where there is no voice, a line stays for as long as reading it takes.
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

  const PACE = 60 / 185;   // seconds for a word, until the voice in use has been measured
  const GAP = 0.3;         // seconds between two scenes
  const MEMORY = 400;      // words of earlier visits that count when the pace is measured
  const TRUST = 40;        // words that a pace counts for before this visit has measured any
  const rates = [0.85, 1, 1.2, 1.5];
  const textOf = span => span.textContent.trim();
  const startsOf = text => Array.from(text.matchAll(/\S+/g), match => match.index);
  // for every line, where its words begin in its text
  const words = scenes.map(scene => scene.map(span => startsOf(textOf(span))));

  let at = 0;             // the scene that is shown
  let line = 0;           // the line of that scene
  let word = 0;           // how many words of that line have begun
  let playing = false;
  let begun = false;      // whether the talk has been played or stepped through at all
  let ended = false;
  let turn = 0;           // counts what is started, so that an answer to something older is ignored
  let timer = 0;
  let beat = 0;           // the timer that guesses the word when the voice does not report it
  let speech = null;      // the utterance in the air; some browsers drop one that nothing refers to
  let cutAt = 0;          // when the voice was last cut off
  let lineBegan = 0;      // when the line that is being said began
  let voices = [];
  let voice = null;       // null: no voice, the text alone
  let rate = 1;
  let pace = PACE;        // seconds for a word at speed 1, measured as the voice speaks
  let measured = { seconds: 0, words: 0 };
  let captions = true;
  let stage = [];         // the scenes inside the frame
  let starts = [];        // for every scene, the time at which each of its lines begins
  let total = 0;

  const recall = key => {
    try { return localStorage.getItem(key); } catch (error) { return null; }
  };
  const remember = (key, value) => {
    try { localStorage.setItem(key, value); } catch (error) { /* the choice lasts for this visit */ }
  };

  // ---------------------------------------------------------------------------------------
  // Time. Nothing says in advance how long a voice takes, so the length of a line is its number
  // of words times the pace of the voice, and the pace is measured while the voice speaks.

  const lengthOf = (scene, n) => (scenes[scene].length
    ? Math.max(0.7, words[scene][n].length * pace) / rate : 1.5);

  function schedule() {
    starts = [];
    total = 0;
    scenes.forEach((scene, index) => {
      const times = [];
      for (let n = 0; n < Math.max(scene.length, 1); n++) {
        times.push(total);
        total += lengthOf(index, n);
      }
      starts.push(times);
      total += GAP;
    });
  }

  function learn(seconds, count) {
    measured.seconds += seconds * rate;
    measured.words += count;
    if (measured.words < 10) return;
    pace = Math.max(0.15, Math.min(1.2, measured.seconds / measured.words));
    if (voice) remember(`talk.pace.${voice.name}`, `${pace.toFixed(4)} ${Math.min(measured.words, MEMORY)}`);
    schedule();
    lay();
  }

  // Starts from what earlier visits measured for the voice. That measurement keeps its weight,
  // up to MEMORY words, so that a few lines of this visit do not replace a whole talk.
  function forget() {
    const [known, count] = String((voice && recall(`talk.pace.${voice.name}`)) || "").split(" ").map(Number);
    const good = known > 0.1 && known < 1.5;
    const weight = good ? Math.max(TRUST, Math.min(count || 0, MEMORY)) : TRUST;
    pace = good ? known : PACE;
    measured = { seconds: pace * weight, words: weight };
    schedule();
    lay();
  }

  // Where the talk is, in seconds: the start of the line, and what has passed of it.
  function position() {
    if (ended) return total;
    const into = playing && lineBegan ? (performance.now() - lineBegan) / 1000 : 0;
    return (starts[at][line] || 0) + Math.min(into, lengthOf(at, line));
  }

  // ---------------------------------------------------------------------------------------
  // The picture. A mark in the frame names the line at which it applies, "3", or the line and
  // the word, "3:5".

  // The document of the frame, once it has a root: a frame that is still loading has none.
  const doc = () => {
    try {
      const page = frame.contentDocument;
      return page && page.documentElement ? page : null;
    } catch (error) { return null; }
  };
  const number = value => Math.round(value).toLocaleString("en-US");
  const counting = new WeakMap();
  const cueOf = text => {
    const [first, second] = String(text).split(":");
    return [Number(first) || 0, Number(second) || 0];
  };
  const reached = (cue, step, said) => cue[0] < step || (cue[0] === step && cue[1] <= said);

  // Puts a scene into the state of a line, after `said` words of it.
  function setStep(index, step, said) {
    const el = stage[index];
    if (!el) return;
    for (let k = 1; k <= Math.max(scenes[index].length, 1); k++) el.classList.toggle(`s${k}`, k <= step);
    for (const name of (el.dataset.cues || "").split(/\s+/).filter(Boolean)) {
      el.classList.toggle(`c${name.replace(":", "-")}`, reached(cueOf(name), step, said));
    }
    el.dataset.step = String(step);
    for (const item of el.querySelectorAll("[data-in]")) item.classList.toggle("in", reached(cueOf(item.dataset.in), step, said));
    for (const item of el.querySelectorAll("[data-out]")) item.classList.toggle("out", reached(cueOf(item.dataset.out), step, said));
    for (const item of el.querySelectorAll("[data-fade]")) item.classList.toggle("faded", reached(cueOf(item.dataset.fade), step, said));
    for (const item of el.querySelectorAll("[data-hot]")) {
      item.classList.toggle("hot", item.dataset.hot.split(/\s+/).includes(String(step)));
    }
  }

  // Numbers that count up when they come in. A still picture shows where they end.
  function setCounts(index, step, said, still) {
    const el = stage[index];
    if (!el) return;
    for (const item of el.querySelectorAll("[data-count]")) {
      const from = Number(item.dataset.from) || 0;
      const to = Number(item.dataset.count) || 0;
      const due = reached(cueOf(item.dataset.in || "1"), step, said);
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

  // The scene that is shown is "current", and the scenes before it are "past".
  const show = index => stage.forEach((el, i) => {
    el.classList.toggle("current", i === index);
    el.classList.toggle("past", i < index);
  });

  // The still picture of the end of a line.
  function still(index, step) {
    const page = doc();
    if (!page || !stage.length) return;
    const html = page.documentElement;
    html.classList.add("snap");
    setStep(index, step, Infinity);
    setCounts(index, step, Infinity, true);
    show(index);
    void html.offsetWidth;
    settle(page);
    html.classList.remove("snap");
  }

  // A line begins: the picture of the line before it, and then what the line sets in motion.
  function enter(index, step) {
    const page = doc();
    if (!page || !stage.length) return;
    const html = page.documentElement;
    html.classList.add("snap");
    setStep(index, step - 1, Infinity);
    setCounts(index, step - 1, Infinity, true);
    void html.offsetWidth;
    settle(page);
    html.classList.remove("snap");
    show(index);
    setStep(index, step, 0);
    setCounts(index, step, 0, false);
  }

  // Text of the class "words" is cut into words, so that it can come in word by word. With
  // the class "sync" as well, each word comes in when the voice reaches it: the mark of the
  // text names the word of the line at which its first word is said.
  function cut(page) {
    for (const el of page.querySelectorAll(".words")) {
      let count = 0;
      // a word keeps the tint of the text around it, because a tint does not reach into a word
      const walk = (node, tint) => {
        for (const child of Array.from(node.childNodes)) {
          if (child.nodeType === 1) {
            const tinted = child.classList.contains("grad");
            walk(child, tint || tinted);
            child.classList.remove("grad");
          }
          if (child.nodeType !== 3) continue;
          const pieces = page.createDocumentFragment();
          for (const part of child.textContent.split(/(\s+)/)) {
            if (!part) continue;
            if (/^\s+$/.test(part)) {
              pieces.append(" ");
              continue;
            }
            const outer = page.createElement("span");
            const inner = page.createElement("i");
            outer.className = "w";
            if (tint) inner.className = "grad";
            inner.textContent = part;
            inner.style.setProperty("--i", String(count++));
            outer.append(inner);
            pieces.append(outer);
          }
          child.replaceWith(pieces);
        }
      };
      walk(el, el.classList.contains("grad"));
      el.classList.remove("grad");
      if (el.classList.contains("sync") && el.dataset.in) {
        const [first, from] = cueOf(el.dataset.in);
        el.querySelectorAll(".w").forEach((item, n) => { item.dataset.in = `${first}:${from + n}`; });
      }
    }
  }

  function fit() {
    const page = doc();
    const width = frame.clientWidth;   // none while the frame is not laid out
    if (page && width) page.documentElement.style.setProperty("--k", String(width / 1280));
  }

  function bind() {
    const page = doc();
    stage = page ? Array.from(page.querySelectorAll("section.scene")) : [];
    if (!stage.length) return;
    if (!page.documentElement.classList.contains("driven")) cut(page);
    page.documentElement.classList.add("driven");
    fit();
    if (playing) {
      enter(at, line + 1);
      setStep(at, line + 1, word);
    } else still(at, line + 1);
    root.classList.add("ready");   // until now the frame is hidden: it has not been told what to show
    render();
  }

  // ---------------------------------------------------------------------------------------
  // The controls

  const icons = {
    play: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 5v14l11-7z"/></svg>',
    pause: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M6 5h4v14H6zm8 0h4v14h-4z"/></svg>',
    again: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 5V1.5L6.5 6 12 10.5V7a5 5 0 1 1-5 5H5a7 7 0 1 0 7-7z"/></svg>',
    full: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M5 5h5v2H7v3H5zm9 0h5v5h-2V7h-3zM5 14h2v3h3v2H5zm12 0h2v5h-5v-2h3z"/></svg>',
    small: '<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 5h2v5H5V8h3zm6 0h2v3h3v2h-5zM5 14h5v5H8v-3H5zm9 0h5v2h-3v3h-2z"/></svg>',
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

  // The track: every scene is as wide as it is long.
  function lay() {
    segments.forEach((segment, index) => {
      const end = starts[index + 1] ? starts[index + 1][0] : total;
      segment.style.flexGrow = String(Math.max(0.1, end - starts[index][0]));
    });
    progress();
  }

  // The clock and the track, which move while a line is said.
  function progress() {
    const now = position();
    time.textContent = `${clock(now)} / ${clock(total)}`;
    segments.forEach((segment, index) => {
      const from = starts[index][0];
      const end = starts[index + 1] ? starts[index + 1][0] : total;
      const done = ended || index < at ? 1 : index > at ? 0 : (now - from) / (end - from);
      segment.firstChild.style.width = `${100 * Math.max(0, Math.min(1, done))}%`;
    });
  }

  // What is said, word by word: the words that were said, the one that is said, and the rest.
  function subtitle() {
    const said = scenes[at][line];
    const show = begun && !ended && said;
    if (!show) caption.replaceChildren();
    else if (caption.dataset.for !== `${at}:${line}`) {
      caption.replaceChildren();
      textOf(said).split(/\s+/).forEach((part, n) => {
        if (n) caption.append(" ");
        caption.append(make("span", "", part));
      });
    }
    caption.dataset.for = show ? `${at}:${line}` : "";
    Array.from(caption.children).forEach((item, n) => {
      item.className = !playing || n < word - 1 ? "said" : n === word - 1 ? "now" : "";
    });
    caption.hidden = !captions || !show;
  }

  function render() {
    subtitle();
    progress();
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
    else note.textContent = "The voice is the speech synthesis of your browser. The times are estimates that get better as it speaks." + keys;
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
    const chosen = pick < 0 ? null : voices[pick];
    const changed = (chosen && chosen.name) !== (voice && voice.name);
    voice = chosen;
    voiceSelect.replaceChildren();
    voices.forEach((item, index) => voiceSelect.append(new Option(item.name, String(index))));
    voiceSelect.append(new Option("No voice", "none"));
    voiceSelect.value = pick < 0 ? "none" : String(pick);
    voiceSelect.disabled = !voices.length;
    if (changed) forget();
    tell();
  }

  // ---------------------------------------------------------------------------------------
  // Speaking

  function hush() {
    turn++;
    clearTimeout(timer);
    clearTimeout(beat);
    lineBegan = 0;
    if (synth && (synth.speaking || synth.pending)) {
      synth.cancel();
      cutAt = Date.now();
    }
  }

  // The voice has reached a word of the line.
  function reach(count) {
    if (count <= word) return;
    word = count;
    setStep(at, line + 1, word);
    setCounts(at, line + 1, word, false);
    subtitle();
  }

  function say() {
    const mine = ++turn;
    clearTimeout(timer);
    clearTimeout(beat);
    const said = scenes[at][line];
    const text = said ? textOf(said) : "";
    const offsets = said ? words[at][line] : [];
    const length = lengthOf(at, line) * 1000;
    let over = false;
    let heard = 0;      // when the voice last reported a word
    const done = natural => {
      if (over || mine !== turn) return;
      over = true;
      clearTimeout(timer);
      clearTimeout(beat);
      if (natural && voice && offsets.length) learn((performance.now() - lineBegan) / 1000, offsets.length);
      reach(offsets.length);
      if (playing) advance();
    };
    // Between the reports of the voice, or without them, the word is guessed from the time.
    const guess = () => {
      if (over || mine !== turn) return;
      const now = performance.now();
      if (lineBegan && now - heard > 700) {
        reach(Math.min(offsets.length, Math.floor((now - lineBegan) / length * offsets.length) + 1));
      }
      progress();
      beat = setTimeout(guess, 80);
    };
    if (!text || !voice) {
      lineBegan = performance.now();
      guess();
      timer = setTimeout(() => done(false), text ? 300 + length : 1500);
      return;
    }
    const silent = reason => {
      // the voice failed: the talk goes on without one, from this line
      if (over || mine !== turn) return;
      over = true;
      clearTimeout(beat);
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
    utterance.onend = () => done(true);
    utterance.onboundary = event => {
      if (over || mine !== turn || event.name === "sentence") return;
      heard = performance.now();
      reach(offsets.filter(offset => offset <= event.charIndex).length);
    };
    utterance.onerror = event => {
      if (event.error !== "interrupted" && event.error !== "canceled") silent(event.error || "error");
    };
    speech = utterance;
    const start = () => {
      if (mine !== turn) return;
      lineBegan = performance.now();
      synth.speak(utterance);
      guess();
      // Some browsers do not report the end of every utterance. So the script also looks:
      // when the voice has fallen silent, the line is over.
      const look = () => {
        if (over || mine !== turn) return;
        if (!synth.speaking && !synth.pending) done(true);
        else if (performance.now() - lineBegan > (8000 + 1500 * offsets.length) / rate) silent("no end");
        else timer = setTimeout(look, 700);
      };
      timer = setTimeout(look, (1500 + 600 * offsets.length) / rate);
    };
    // A voice that was cut off a moment ago may swallow what is said right after.
    if (Date.now() - cutAt < 200) timer = setTimeout(start, 200);
    else start();
  }

  function advance() {
    lineBegan = 0;
    word = 0;
    if (line + 1 < scenes[at].length) {
      line++;
      setStep(at, line + 1, 0);
      setCounts(at, line + 1, 0, false);
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
    }
    begun = true;
    playing = true;
    word = 0;
    if (!voices.length) loadVoices();
    enter(at, line + 1);
    render();
    say();
  }

  function pause() {
    playing = false;
    hush();
    render();
  }

  const toggle = () => (playing ? pause() : play());

  // Moves to a line. A talk that was playing goes on from there.
  function go(scene, sentence) {
    hush();
    at = Math.max(0, Math.min(scenes.length - 1, scene));
    line = Math.max(0, Math.min(scenes[at].length - 1, sentence));
    word = 0;
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
  // Full screen. The player fills the window, and the page asks the browser for the whole
  // screen. It is the page that goes full screen, not the player: a browser that lifts one
  // part of a page out has to draw that part anew, the frame included, and browsers differ in
  // how well they do. Where a browser does not give the screen, the player still fills the
  // window.

  const whole = document.documentElement;
  const enterFull = whole.requestFullscreen || whole.webkitRequestFullscreen;
  const leaveFull = document.exitFullscreen || document.webkitExitFullscreen;
  const inFull = () => Boolean(document.fullscreenElement || document.webkitFullscreenElement);
  const quietly = call => {
    try { Promise.resolve(call()).catch(() => {}); } catch (error) { /* refused: the window it is */ }
  };
  let wide = false;       // whether the player fills the window

  // The widest picture of 16 by 9 that fits above the controls.
  function size() {
    if (!wide) return;
    const width = Math.min(root.clientWidth, (root.clientHeight - controls.offsetHeight) * 16 / 9);
    if (width > 0) root.style.setProperty("--wide", `${Math.floor(width)}px`);
  }

  function setWide(on) {
    if (on !== wide) {
      wide = on;
      whole.classList.toggle("talk-wide", on);
      if (!on) root.style.removeProperty("--wide");
      fullButton.innerHTML = on ? icons.small : icons.full;
      fullButton.setAttribute("aria-label", on ? "Leave full screen" : "Full screen");
    }
    size();
    fit();
  }

  function toggleWide() {
    if (wide) {
      setWide(false);
      if (inFull() && leaveFull) quietly(() => leaveFull.call(document));
    } else {
      setWide(true);
      if (enterFull) quietly(() => enterFull.call(whole));
    }
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
    forget();
    tell();
    if (playing) go(at, line);
  });
  rateSelect.addEventListener("change", () => {
    rate = Number(rateSelect.value) || 1;
    remember("talk.rate", String(rate));
    schedule();
    lay();
    if (playing) go(at, line);
  });
  fullButton.addEventListener("click", toggleWide);
  // The browser gave the screen, or took it back: on Escape, for one.
  for (const name of ["fullscreenchange", "webkitfullscreenchange"]) {
    document.addEventListener(name, () => setWide(inFull()));
  }
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
    else if (key === "f" || (key === "Escape" && wide)) toggleWide();
    else return;
    event.preventDefault();
  });
  window.addEventListener("pagehide", () => { if (synth) synth.cancel(); });
  if ("ResizeObserver" in window) {
    new ResizeObserver(fit).observe(frame);
    new ResizeObserver(size).observe(root);
  }
  window.addEventListener("resize", () => { size(); fit(); });
  frame.addEventListener("load", bind);

  const saved = Number(recall("talk.rate"));
  if (rates.includes(saved)) rate = saved;
  rateSelect.value = String(rate);
  captions = recall("talk.captions") !== "off";
  const linked = /^#scene-(\d+)$/.exec(location.hash);
  if (linked) at = Math.max(0, Math.min(scenes.length - 1, Number(linked[1]) - 1));
  schedule();
  lay();
  if (synth) {
    synth.cancel();   // a voice may still be speaking for the page that was here before
    if (synth.addEventListener) synth.addEventListener("voiceschanged", loadVoices);
    else synth.onvoiceschanged = loadVoices;
  }
  loadVoices();
  bind();
  render();
})();
