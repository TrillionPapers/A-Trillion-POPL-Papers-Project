# The Prover Pays

Advice and a price for conversion in proof checking

> A proof in type theory may be a single word, and checking it may take longer than anyone is willing to wait. The checker has to find out, by computation, that two terms are equal. How it computes is decided by a strategy that is built into the checker.

> Today, proofs are written by programs and submitted in bulk. Then the time to check a proof is part of what the proof costs.

---

## One equation, two ways to check it

```
pow2 10  =  id (pow2 10)
```

```stat
122,034 | steps: unfold both sides
```

> Take this equation. On the left is two to the power ten. On the right is the identity function, applied to the same number. A checker that unfolds both sides computes a tower of a thousand successors, twice, and compares the towers. That takes more than a hundred and twenty thousand steps.

```stat
48 | steps: unfold the identity, then compare the arguments
```

> A checker that unfolds only the identity sees the same function with the same argument on both sides. That takes forty-eight steps.

---

## The checker cannot know. The prover can.

- Unfold the definition that came later.
- Compare the arguments first.

> Kernels decide such questions by rules of thumb, like these two. Each rule is right for some equations and wrong for others.

The prover constructed both terms. It knows why they are equal.

> The checker cannot know which side is the expensive one. The prover can. It constructed the two terms, and it knows why they are equal.

---

## A proof is a term, advice, and a price

```flow
term | refl -> *advice | R S -> *price | 48 steps
```

> So we let the prover say it. A proof becomes a term, together with advice and a price.

- **Advice** answers each question of the conversion test: left, right, both, or compare the arguments.
- **Price** is a number of steps that the checker will not exceed.

> The advice is a string of letters, one for each question that the conversion test asks: unfold the left side, the right side, or both, or compare the arguments. The price is a number of steps. The checker counts its steps, and gives up when the count passes the price.

---

## Advice is only advice

- Wrong advice never changes the verdict. It changes the cost.
- The checker stops within the price.

> Advice is not trusted, and need not be. Whatever the advice says, the checker never accepts terms that are not equal, and never rejects terms that are, as long as the price suffices.

> Bad advice only makes a proof expensive. And the price says how expensive, before anyone runs the check. So a registry of proofs can refuse what it does not want to pay for.

---

## No rule of thumb replaces it

For every strategy that decides by the ranks of two definitions, some equations of size *n* take more than 2<sup>n</sup> steps. Two letters of advice check them in a number of steps linear in *n*.

> Advice also does something that no built-in strategy of this kind can do. For every strategy that decides by the ranks of the two definitions, there are equations on which it takes exponentially many steps, while two letters of advice make the check linear.

```stat
8,550 | steps for a library of seven theorems, with advice
374,525 | steps without
```

> In our measurements, a library of seven small theorems costs about eight and a half thousand steps with advice, and about three hundred seventy thousand without.

---

## What is tested

- 3,000 random pairs of terms, against a separate evaluator
- Five deliberate mistakes, each noticed

> A script tests these claims on three thousand random pairs of terms, against a separate evaluator.

The proofs are on paper. No machine has checked them, and nobody has reviewed the paper.

> The proofs are on paper. No machine has checked them, and nobody has reviewed the paper.
