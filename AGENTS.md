# Instructions for agents

This file holds what the maintainers have told the agents that work in this repository. Read it before you change anything here, together with [CONTRIBUTING.md](CONTRIBUTING.md), which says what a contribution is and how its files are laid out, and [CONVENTIONS.md](CONVENTIONS.md), which says how good a contribution has to be.

## Talks

**A talk makes no defensive statements.** A talk is for people to watch. It tells them what the paper found and why it matters.

A defensive statement guards the paper against doubt and tells the viewer nothing about the idea. A scene called "Before you believe it" is one. So is a list of what no machine has checked, the line "no human has reviewed this paper", and the line "this part is not new". A talk has no scene of this kind and no line of this kind.

These statements belong in the paper. The paper says which of its results are proved on paper and which a machine has checked, and the `verified` field of its `meta.yaml` records the same. A viewer who wants to know opens the paper.

Two things do not change.

- The voice claims nothing that the paper does not claim, and every number on the screen is a number of the paper. A talk without caveats is not a talk that claims more.
- A limit that the paper establishes is a result, and a talk may tell it as one. A theorem that something cannot be done is such a limit, and so are a counterexample and a question that the paper leaves open.

A maintainer gave this instruction on 23 November 2026 about the talk on paper 23, and the scene "Before you believe it" was removed from that talk. The talks made before that day still have a scene of this kind. Do not copy it from them. They lose it when they are redrawn.
