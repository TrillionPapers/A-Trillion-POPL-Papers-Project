// Plays a talk. A talk page holds slides, and with every slide the sentences that are said about
// it. This script shows one slide at a time and hands the sentences, one by one, to the speech
// synthesis of the browser. A part of a slide appears when the first sentence about it begins.
// Where there is no voice, every sentence is shown for as long as reading it takes.
//
// The page can be read without this script: then every slide stands with its text.
(() => {
  "use strict";

  const root = document.querySelector(".talk");
  if (!root) return;
  const slides = Array.from(root.querySelectorAll(".slide"), el => ({
    el,
    parts: Array.from(el.querySelectorAll(".part")),
    says: Array.from(el.querySelectorAll(".say span")),
  }));
  if (!slides.length) return;
  const synth = "speechSynthesis" in window && "SpeechSynthesisUtterance" in window
    ? window.speechSynthesis : null;
  const steps = slides.reduce((sum, slide) => sum + Math.max(slide.says.length, 1), 0);
  const rates = [0.85, 1, 1.2, 1.5];

  let at = 0;           // the slide that is shown
  let line = 0;         // the sentence of that slide
  let playing = false;
  let begun = false;    // whether the talk has been played or stepped through at all
  let ended = false;
  let turn = 0;         // counts what is started, so that an answer to something older is ignored
  let timer = 0;
  let speech = null;    // the utterance in the air; some browsers drop one that nothing refers to
  let cutAt = 0;        // when the voice was last cut off
  let voices = [];
  let voice = null;     // null: no voice, the text alone
  let rate = 1;

  const recall = key => {
    try { return localStorage.getItem(key); } catch (error) { return null; }
  };
  const remember = (key, value) => {
    try { localStorage.setItem(key, value); } catch (error) { /* the choice lasts for this visit */ }
  };

  // ---------------------------------------------------------------------------------------
  // The controls

  const make = (tag, name, text) => {
    const el = document.createElement(tag);
    if (name) el.className = name;
    if (text) el.textContent = text;
    if (tag === "button") el.type = "button";
    return el;
  };
  const bar = make("div", "bar");
  const fill = bar.appendChild(make("i"));
  const caption = make("p", "caption");
  const controls = make("div", "controls");
  const playButton = make("button", "main", "Play");
  const backButton = make("button", "", "Back");
  const nextButton = make("button", "", "Next");
  const where = make("span", "where");
  const voiceSelect = make("select");
  const rateSelect = make("select");
  const allButton = make("button", "toggle", "All slides");
  const fullButton = make("button", "", "Full screen");
  const note = make("p", "note");
  voiceSelect.setAttribute("aria-label", "Voice");
  rateSelect.setAttribute("aria-label", "Speed");
  for (const value of rates) rateSelect.append(new Option(`Speed ${value}×`, String(value)));
  controls.append(playButton, backButton, nextButton, where, voiceSelect, rateSelect, allButton,
                  fullButton);
  root.append(bar, caption, controls, note);
  root.classList.add("player");

  function render() {
    const slide = slides[at];
    slides.forEach((item, index) => item.el.classList.toggle("current", index === at));
    const said = slide.says[line];
    const shown = said ? Number(said.dataset.at) : Infinity;
    for (const part of slide.parts) part.classList.toggle("wait", Number(part.dataset.at) > shown);
    caption.textContent = begun && !ended && said ? said.textContent : "";
    let before = 0;
    for (let index = 0; index < at; index++) before += Math.max(slides[index].says.length, 1);
    fill.style.width = `${100 * (ended ? steps : before + line) / steps}%`;
    where.textContent = `Slide ${at + 1} of ${slides.length}`;
    playButton.textContent = playing ? "Pause" : ended ? "Again" : "Play";
    root.dataset.state = playing ? "playing" : ended ? "ended" : "paused";
  }

  function tell(problem) {
    const keys = " Space plays and pauses, and the arrow keys move by one sentence.";
    if (problem) note.textContent = problem + keys;
    else if (!synth) note.textContent = "This browser has no speech synthesis, so the talk plays as text." + keys;
    else if (!voices.length && begun) note.textContent = "This browser offers no English voice, so the talk plays as text." + keys;
    else if (!voice && voices.length) note.textContent = "No voice is chosen, so the talk plays as text." + keys;
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
    voiceSelect.append(new Option("No voice, text only", "none"));
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
    const said = slides[at].says[line];
    const text = said ? said.textContent.trim() : "";
    const words = text ? text.split(/\s+/).length : 0;
    let over = false;
    const done = () => {
      if (over || mine !== turn) return;
      over = true;
      clearTimeout(timer);
      if (playing) advance();
    };
    if (!text || !voice) {
      timer = setTimeout(done, text ? (600 + 340 * words) / rate : 1500);
      return;
    }
    const silent = reason => {
      // the voice failed: the talk goes on as text, from this sentence
      if (over || mine !== turn) return;
      over = true;
      synth.cancel();
      voice = null;
      voiceSelect.value = "none";
      tell(`The voice failed (${reason}), so the talk goes on as text.`);
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
      // when the voice has fallen silent, the sentence is over.
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
    if (line + 1 < slides[at].says.length) {
      line++;
      render();
      say();
    } else if (at + 1 < slides.length) {
      at++;
      line = 0;
      render();
      const mine = ++turn;
      timer = setTimeout(() => { if (mine === turn && playing) say(); }, 450);
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
    if (!voices.length) loadVoices();
    render();
    say();
  }

  function pause() {
    playing = false;
    cut();
    render();
  }

  const toggle = () => (playing ? pause() : play());

  // Moves to a sentence. A talk that was playing goes on from there.
  function go(slide, sentence) {
    cut();
    at = Math.max(0, Math.min(slides.length - 1, slide));
    line = Math.max(0, Math.min(slides[at].says.length - 1, sentence));
    begun = true;
    ended = false;
    render();
    if (playing) say();
  }

  const nextSlide = () => { if (at + 1 < slides.length) go(at + 1, 0); };
  const backSlide = () => go(line > 0 || at === 0 ? at : at - 1, 0);

  function step(by) {
    if (by > 0) {
      if (line + 1 < slides[at].says.length) go(at, line + 1);
      else nextSlide();
    } else if (line > 0) go(at, line - 1);
    else if (at > 0) go(at - 1, slides[at - 1].says.length - 1);
  }

  // ---------------------------------------------------------------------------------------
  // Wiring

  playButton.addEventListener("click", toggle);
  backButton.addEventListener("click", backSlide);
  nextButton.addEventListener("click", nextSlide);
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
  allButton.addEventListener("click", () => {
    if (playing) pause();
    const all = root.classList.toggle("all");
    allButton.textContent = all ? "One slide at a time" : "All slides";
  });
  const enter = root.requestFullscreen || root.webkitRequestFullscreen;
  const leave = document.exitFullscreen || document.webkitExitFullscreen;
  if (!enter || !leave) fullButton.hidden = true;
  fullButton.addEventListener("click", () => {
    if (document.fullscreenElement || document.webkitFullscreenElement) leave.call(document);
    else enter.call(root);
  });
  root.addEventListener("click", event => {
    if (root.classList.contains("all") || !event.target.closest(".frame")) return;
    if (!event.target.closest("a")) toggle();
  });
  document.addEventListener("keydown", event => {
    if (event.defaultPrevented || event.altKey || event.ctrlKey || event.metaKey) return;
    if (root.classList.contains("all")) return;
    const target = event.target instanceof Element ? event.target : document.body;
    if (target.closest("input, select, textarea")) return;
    const key = event.key;
    if (key === " " || key === "k") {
      if (key === " " && target.closest("button, a")) return;   // the button does it itself
      toggle();
    } else if (key === "ArrowRight") step(1);
    else if (key === "ArrowLeft") step(-1);
    else if (key === "PageDown") nextSlide();
    else if (key === "PageUp") backSlide();
    else if (key === "f" && !fullButton.hidden) fullButton.click();
    else return;
    event.preventDefault();
  });
  window.addEventListener("pagehide", () => { if (synth) synth.cancel(); });

  const saved = Number(recall("talk.rate"));
  if (rates.includes(saved)) rate = saved;
  rateSelect.value = String(rate);
  const linked = /^#slide-(\d+)$/.exec(location.hash);
  if (linked) at = Math.max(0, Math.min(slides.length - 1, Number(linked[1]) - 1));
  if (synth) {
    synth.cancel();   // a voice may still be speaking for the page that was here before
    if (synth.addEventListener) synth.addEventListener("voiceschanged", loadVoices);
    else synth.onvoiceschanged = loadVoices;
  }
  loadVoices();
  render();
})();
