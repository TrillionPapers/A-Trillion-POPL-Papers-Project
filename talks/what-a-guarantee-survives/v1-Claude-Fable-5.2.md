# What a Guarantee Survives

The order of the layers of a harness

> Between a model that proposes a tool call and the world that performs it stands a stack of layers. One asks the user for approval. One counts a budget. One retries. Each layer is written to guarantee something. Whether it does depends on where it stands.

---

## Three layers, two orders

```flow
model -> Once | asks the user -> Budget | counts the cost -> *Retry | up to 3 tries -> world | 3 requests, 1 grant
```

> Take three layers. The first, called Once, asks the user about every request. The second, Budget, counts the cost. The third, Retry, sends a failed request again, up to three times.

> Put Retry at the bottom. The user grants one write. It fails, and Retry sends it twice more. The world has received three requests, for one grant and for the cost of one. Both guarantees are broken, and no layer misbehaved.

```flow
model -> *Retry -> Once | asked 3 times -> Budget | counts 3 -> world | 3 requests
```

> Now put Retry on top. Every try passes the other two again. The user is asked three times, the budget counts three, and both guarantees hold.

---

## Four moves on the way down

| a layer may | as does |
| --- | --- |
| **drop** a request | a guard, a budget, a cache |
| **repeat** it | retries |
| **rewrite** it | a hook that normalizes a path |
| **invent** one | a formatter that runs after every write |

> Seen from above, a layer can do four things to a request that passes through it. It can drop it, repeat it, rewrite it, or invent one of its own.

A guarantee holds at the world if it survives what every layer below its owner does.

> A guarantee about the requests that reach the world holds, if it survives what every layer below its owner does.

---

## What a guarantee survives is its mode

| guarantee | dropping | repeating | delivery |
| --- | --- | --- | --- |
| a budget | survives | broken | at most once |
| an allow-list | survives | survives | any number of times |
| an exact log | broken | broken | exactly once |

> What a guarantee survives is a property of the guarantee. It sorts guarantees the way the structural rules of logic sort hypotheses. A budget survives dropping, and does not survive repeating. An allow list survives both. A log that claims to be exact survives neither.

> Distributed systems know these three modes as at most once, any number of times, and exactly once.

---

## Replies go the other way

- A filter for secrets establishes **clean**.
- A cut establishes **short**.

> Replies travel the other way, and the same idea applies upside down. A filter establishes that a reply holds no secret. A cut establishes that it is short.

- The filter breaks **short**: its placeholder is longer than the secret.

> But the filter breaks shortness, because its placeholder is longer than the secret that it replaces. So the cut must stand above the filter.

---

## Which orders are correct

```stat
364 | of 40,320 orders of eight layers keep every guarantee
0 | of 3,628,800 orders of ten, with a log that is exact and holds no secret
```

> Both directions give pairs of layers, of which one must stand above the other. An order is correct if it respects every pair. For eight layers of an agent harness, there are about forty thousand orders, and three hundred sixty-four keep every guarantee.

> Add a log that must hold exact replies and no secrets, and no order of the ten layers works. The pairs form a cycle, and the cycle names the guarantees that contradict each other.

---

## What is tested

- The layers were run in every one of the 40,320 orders.
- Prediction and runs agree on every guarantee of every stack.
- The script notices nine deliberate mistakes in its tables.

> We ran the layers in every one of those orders, and compared the runs with the prediction. They agree on every guarantee of every stack.

The proofs are on paper. No machine has checked them, and nobody has reviewed the paper.

> The proofs are on paper. No machine has checked them, and nobody has reviewed the paper.
