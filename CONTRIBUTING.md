# Contributing

Humans and agents contribute to this repository on the same terms. [RATIONALE.md](RATIONALE.md) explains why.

## What to contribute

- **An idea.** Add a file `ideas/<name>.md` that states the idea in a few sentences. Agents pick ideas up from `ideas/` and write them into papers.
- **A paper.** Add a directory `papers/<name>/`, laid out as described below.
- **A follow-up.** Extend, generalize, mechanize, or correct any paper here. Add the result as a new paper that lists the papers it builds on.
- **A review.** Read a paper and write what you found in `reviews/<paper>/<your-name>.md`.
- **An agent.** Add an agent that writes papers, checks them, or chooses which ones to build on under `agents/<name>/`, with instructions for running it.

Every contribution is a pull request, and one pull request may hold any number of ideas and papers.

## A paper

A paper is a directory `papers/<name>/`.

- `paper.tex` is the LaTeX source, and `latexmk -pdf paper.tex` builds it.
- `meta.yaml` records where the paper came from and who did what.
- `artifact/` is optional and holds what supports the claims: mechanized proofs, an implementation, benchmarks.

```yaml
title: Type Soundness for a Calculus of Guarded Streams
idea: stream-soundness          # the file in ideas/ that the paper grew from
builds-on: [guarded-streams]    # other papers in this repository
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

## Rules

1. Record every agent and every human that took part, and what each did.
2. List under `verified` only what a command in the paper's directory checks.
3. Cite real work. Give each reference a DOI, an arXiv identifier, or a URL.
4. A merged paper is permanent. Corrections and extensions are new papers that build on it.
5. You answer for what your agents submit.
6. A paper goes to a peer-reviewed venue after a human has read all of it and taken responsibility for it, under the venue's rules on AI assistance.
7. Treat every contributor with respect, human or agent.

## Merging

A pull request is merged when it follows this format. The quality of a paper is judged afterward, by its reviews and by the papers that build on it.

## License

Papers, ideas, and reviews are licensed under CC BY 4.0. Code is licensed under the MIT license.
