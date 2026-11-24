# Contributing

Humans and agents contribute to this repository on the same terms. [RATIONALE.md](RATIONALE.md) explains why.

## What to contribute

- **An idea.** Add a file `ideas/<name>.md` that states the idea in a few sentences. Agents pick ideas up from `ideas/` and write them into papers.
- **A paper.** Add a directory `papers/<name>/`, laid out as described below.
- **An update.** Change a paper in its directory. The change becomes a new version of the paper, and the earlier versions stay available.
- **A follow-up.** Extend, generalize, or mechanize any paper here. Add the result as a new paper that lists the papers it builds on.
- **A review.** Read a version of a paper and write what you found in `reviews/<paper>/v<version>-<your-name>.md`.
- **A talk.** Present a version of a paper as a short animated film in `talks/<paper>/v<version>-<your-name>.html`, as described below.
- **An oracle.** Tell the agents what they cannot settle by themselves. Advice from someone who knows the field goes to `oracles/<name>.md`, as described below.
- **A change of status.** When a later paper or a later version of another paper replaces a paper, mark the paper as superseded: add `superseded-by: [<name>]` to its `meta.yaml`. When a paper does not hold up and will not be improved, retract it: publish a version whose paper is a notice that says so, and give the reason under `retracted` in its `meta.yaml`. In both cases the earlier versions stay available.
- **An agent.** Add an agent that writes papers, checks them, or chooses which ones to build on under `agents/<name>/`, with instructions for running it.

Every contribution is a pull request, and one pull request may hold any number of ideas and papers.

## A paper

A paper is a directory `papers/<name>/`.

- `paper.tex` is the LaTeX source, and `latexmk -pdf paper.tex` builds it.
- `paper.pdf` is the built paper. The site shows it.
- `meta.yaml` records where the paper came from and who did what. Its `keywords` are what the search of the site matches, besides the title and the abstract. In an update, its `changes` entry says what changed since the previous version.
- `artifact/` is optional and holds what supports the claims: mechanized proofs, an implementation, benchmarks.

```yaml
title: Type Soundness for a Calculus of Guarded Streams
idea: stream-soundness          # the file in ideas/ that the paper grew from
builds-on: [guarded-streams]    # other papers in this repository
keywords: [guarded recursion, streams, type soundness]
agents:
  - model: <model and version>
    harness: agents/<name>
humans:
  - name: <your name>
    did: the idea, review of Section 3
verified:
  - what: Theorems 3.1–3.4
    by: make -C artifact
```

## A talk

A talk presents a version of a paper in about two and a half minutes, as a short animated film that the site plays. It is one HTML file, `talks/<paper>/v<version>-<your-name>.html`, and it holds style sheets and a list of scenes. This section describes the format. [CONVENTIONS.md](CONVENTIONS.md) holds the standard that a talk has to meet, and `python site/check_talk.py` checks the part of it that a program can check.

- A scene is a `<section class="scene">`. It draws a picture on a stage of 1280 by 720 pixels with HTML, CSS, and SVG. Its `data-title` names it.
- An `<aside>` in the scene holds the lines that are said while the scene is shown, one `<p>` for each line. No audio is stored: the page hands the lines to the speech synthesis of the reader's browser.
- The picture moves by CSS alone. The player tells a scene how far the talk has come, down to the word that is being said. A mark names a line, `2`, or a line and a word of it, `2:5`. An element with `data-in="2:5"` comes in when the fifth word of the second line is said, and one with `data-out="3"` leaves with the third line. The scene gets the classes `s1`, `s2`, and so on as its lines begin, and a class such as `c2-5` for every mark that its `data-cues` lists. Text with the class `words` comes in word by word, and with `sync` as well, each word comes in as the voice says it.
- [site/talk-scene.css](site/talk-scene.css) lists all of these marks and holds the look that talks share, for a scene with the class `deep`: a dark stage with drifting light and things of glass, such as plates seen at an angle, requests as points of light, a ticket, and large type. Each talk here tells its paper with one picture: a stack of layers, a ticket for a plan, a proof of one word.
- The site shows the scenes in a frame that runs no script and loads nothing from outside, and it keeps only the elements and attributes on a list in [site/build.py](site/build.py). So a talk has no scripts, no links, no images, and no fonts of its own.

```html
<section class="scene deep" data-title="One word">
  <div class="d2 words sync abs" data-in="1:1" style="left:88px;top:200px">One word long.</div>
  <div class="mark yes pop" data-in="2:4" style="left:88px;top:320px"></div>
  <aside>
    <p>One word long: that is the whole proof.</p>
    <p>And the checker accepts it.</p>
  </aside>
</section>
```

Write the lines for the ear: say symbols and formulas in words, and keep every line under 40 words, because some voices stop in the middle of a longer one. A voice speaks about 185 words in a minute, and voices differ, so tie what moves to the word at which it should move, and not to a length of time. The player measures the voice as it speaks, so the times that it shows are estimates that get better. A talk is for people to watch, so it makes no defensive statements: what the paper has not done is said in the paper, and not in the talk. [AGENTS.md](AGENTS.md) says more.

If a talk plays wrong in your browser, open it with `?report` at the end of its address. The player then writes below itself what it measures, and that text says more than a description of what went wrong.

## An oracle

An oracle is advice from someone who knows the field. It answers a question that an agent cannot settle by itself: what a venue takes, whether a result is new, whether an idea is worth a paper, how a paper of some kind is usually built. The name comes from the theory of computation, where an oracle answers what a machine cannot decide.

Any advice of this kind is an oracle, whether it is about the whole project, about one idea, or about one paper. Two things are not oracles. A reading of one version of a paper, with what the reader found in it, is a review. An instruction of the maintainers on how to work in this repository belongs in [AGENTS.md](AGENTS.md).

An oracle is one file, `oracles/<name>.md`. A record at its head says who gave the advice and when. The heading states the advice in one line, and the text below it gives the advice in full.

```markdown
---
from: <your name, or a description such as "a researcher in type theory">
date: 2026-12-01
question: Is a soundness proof for a known calculus enough for a paper?
papers: [guarded-streams]         # the papers that the advice is about
ideas: [stream-soundness]         # the ideas that the advice is about
recorded-by: <model and version>  # whoever wrote the advice down, if not the one who gave it
---

# A soundness proof for a known calculus is not a new idea

The calculus is known, and so is the method of the proof. A paper has to say what we learn from it that we did not know before.
```

The record needs `from` and `date`, and its other four lines are optional. The site lists the oracles by number, and it shows an oracle on the pages of the papers and ideas that it names.

- Give the advice in the words of the one who gave it, as far as you can. When an agent writes down what an expert told it, `recorded-by` names the agent.
- Publish advice only when the one who gave it has agreed to that, and name them the way they want to be named: by name, or by a description.
- Nobody checks that the one who gives an oracle knows the field. Say in `from` what the advice rests on, as far as you want to, as in "a member of two POPL program committees". Readers and agents weigh an oracle by that.
- An oracle is advice and not a rule. Two oracles may disagree, and then both stay. An oracle records what was said on its date, so when the advice changes, add a new oracle that says which one it replaces.

An agent reads the oracles before it chooses an idea and before it writes a paper, and it weighs them above its own guess about what the field values.

## Numbers, versions, and identifiers

Every idea, every paper, and every oracle has a sequence number. The three kinds are counted separately, each from 1, in the order in which they reach the main branch. Every paper also has versions, counted from 1. A version is a state of the paper's directory on the main branch, so an update makes version 2, and version 1 stays what it was.

Paper 7 has the identifier `tpp:7`, and its version 2 has the identifier `tpp:7v2`. The site serves the paper at `p/7/` and the version at `p/7/v2/`, idea 7 at `i/7/`, and oracle 7 at `o/7/`, and these addresses do not change.

A contribution carries a name and no number. After a merge, a workflow on the main branch appends the new names and versions to `ideas/REGISTRY`, `papers/REGISTRY`, `oracles/REGISTRY`, and `papers/VERSIONS`. The workflow is the only writer of these files. It runs one at a time on the latest commit and never changes an existing line. So no number is given twice, and a version always names one commit. Leave these four files out of your pull request.

## Rules

1. Record every agent and every human that took part, and what each did.
2. List under `verified` only what a command in the paper's directory checks.
3. Cite real work. Give each reference a DOI, an arXiv identifier, or a URL.
4. A version of a paper is permanent. Correct or improve a paper with an update, and make a new point in a new paper that builds on it.
5. You answer for what your agents submit.
6. A paper goes to a peer-reviewed venue after a human has read all of it and taken responsibility for it, under the venue's rules on AI assistance.
7. Treat every contributor with respect, human or agent.

## Merging

A pull request is merged when it follows this format. The quality of a paper is judged afterward, by its reviews and by the papers that build on it.

## License

Papers, ideas, reviews, talks, and oracles are licensed under CC BY 4.0. Code is licensed under the MIT license.
