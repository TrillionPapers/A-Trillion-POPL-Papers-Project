# A Plan Is a Language

Typed approvals for what comes next

> An agent that is given a task first proposes a plan, and a person approves it. Today the plan is prose, and the approval is a click. Nothing ties what the agent does afterwards to what was approved.

---

## An approval that binds nothing

- **Order.** The plan: test, then push. The agent: push, edit, push again.

> The plan says that the tests run before the push. The agent pushes, finds a problem, edits, and pushes again. Every action occurs in the plan. The sequence does not.

- **Scope.** The plan names two files. The agent edits a third.

> The plan names two files. A few steps later, the agent is editing a third.

- **Parts.** A helper that inherits the approval may also push.

> And when the agent hands the edits to a helper, the helper inherits the whole approval, and may also push.

---

## A plan is a regular expression

```
edit(x ≤ 2)*  ·  test  ·  push(x = 1)
```

> We make the plan a type. A plan is a regular expression over actions, with conditions on what they act on. This one allows any number of edits to the first two files, then one test, then one push to branch one.

- The approval is a value that cannot be copied.
- Its type is the plan.

> The approval is a value that cannot be copied, and its type is the plan.

---

## Acting uses the plan up

| the agent does | what is left of the plan |
| --- | --- |
| edits file 1 | `edit* · test · push` |
| runs the test | `push` |
| pushes to branch 1 | nothing |
| pushes again | *does not type check* |

> Performing an action replaces the plan in the type by what is left of it. After an edit, the whole plan is left. After the test, only the push is left. After the push, nothing is left, and a second push does not type check.

---

## Less is free, more needs a question

| the agent wants to | within what is left? | the person |
| --- | --- | --- |
| stop after the test | yes | is not asked |
| push to branch 2 | no | must be asked |

> An approval for a plan serves for every plan that it contains. So the agent may always do less. If it decides not to push, it needs no new question. If it wants to push to another branch, that is not contained in what it holds, and the program must ask.

> Containment of regular languages is decidable. So the type checker settles, before anything runs, whether the person is asked.

---

## Handing work on

| code that the model writes | the checker says |
| --- | --- |
| edits twice, gives the approval back | accepted |
| runs the test, gives the approval back | a result of another type |
| edits, keeps the approval | a result of another type |

> Now suppose the edits are made by code that the model writes on the spot. The approval cannot be split in two, because a plan that prescribes an order cannot be cut into independent pieces. But it can be lent. The code takes the approval, and must give back one for the same plan.

> Code that only edits can do that. Code that runs the test cannot, because then only the push is left. So the caller knows what the code did not do, without reading it.

---

## What is proved, and what is tested

**Consent.** What happens under an approval begins something that was approved.

> We prove that whatever happens under an approval is the beginning of something that was approved, on every behavior of the model.

```stat
6,000 | random programs
2,000 | pairs of plans
10 | weakened rules, each refuted
```

> A script tests the theorems on six thousand random programs, and refutes ten weakened rules, each by a program.

The proofs are on paper. No machine has checked them, and nobody has reviewed the paper.

> The proofs are on paper. No machine has checked them, and nobody has reviewed the paper.
