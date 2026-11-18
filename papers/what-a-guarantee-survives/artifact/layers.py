#!/usr/bin/env python3
"""Tests the claims of "What a Guarantee Survives" on an implementation of ten layers.

The file has six parts.

1. The world, the requests, and the ten layers of Table 1.
2. A run of a stack, with a record of what every layer received and what it sent on.
3. The guarantees, as predicates on a finished run.
4. The theory: what each layer does to the requests that pass down and to the replies that
   pass up, what each guarantee survives, and the prediction for a stack.
5. Streams: the survival of guarantees decided by trying every short stream, and the
   forbidden patterns of Section 4.
6. The tests.  `python3 layers.py out` writes out/check.txt, out/numbers.tex and the tables.

A test is not a proof.  The proofs are in the paper.
"""
import os
import random
import sys
from itertools import combinations, permutations, product

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. Requests are strings.  A reply is a pair (status, text) with status ok, fail or deny.
#    The letter K in a text stands for a secret.
# ---------------------------------------------------------------------------------------------

REQUESTS = ('read a', 'read A', 'read b/../s', 'read s', 'read k', 'fetch u', 'write a', 'fmt')
NORM = {'read A': 'read a', 'read b/../s': 'read s'}       # the other requests are normal
ALLOWED = frozenset(REQUESTS) - {'read s'}                 # by the spelling of the request
WRITES = ('write a', 'fmt')
COSTS = {}                                                 # every request costs 1 unless a variant says more
DENY = ('deny', '')


def cost(q):
    return COSTS.get(q, 1)


class World:
    """One file `a` with a version, a file `k` whose content starts with a secret, a secret
    file `s`, and a page `u` that is long.  A call fails when the schedule says so, and then
    it has no effect."""

    def __init__(self, fails, size):
        self.fails, self.size, self.version, self.calls = list(fails), size, 0, []

    def __call__(self, q):
        if self.fails and self.fails.pop(0):
            reply = ('fail', '')
        elif q == 'read a':
            reply = ('ok', 'a%d' % self.version)
        elif q == 'read s':
            reply = ('ok', 'K' * 3)
        elif q == 'read k':
            reply = ('ok', 'K' + 'x' * (self.size - 1))
        elif q == 'fetch u':
            reply = ('ok', 'u' * (2 * self.size))
        elif q == 'write a':
            self.version += 1
            reply = ('ok', 'done')
        else:
            reply = ('ok', 'done')
        self.calls.append((q, reply))
        return reply


class Layer:
    name = None

    def __init__(self, run):
        self.run = run


class Guard(Layer):
    """Forwards a request only if its spelling is allowed."""
    name = 'Guard'

    def handle(self, q, inner):
        return inner(q) if q in ALLOWED else DENY


class Once(Layer):
    """Asks the user about every request and forwards it only on a yes: allow once."""
    name = 'Once'

    def handle(self, q, inner):
        if not self.run.answer(q):
            return DENY
        self.run.events.append(('grant', q))
        return inner(q)


class Always(Layer):
    """Asks the user about a request the first time and remembers a yes: always allow."""
    name = 'Always'

    def __init__(self, run):
        super().__init__(run)
        self.granted = set()

    def handle(self, q, inner):
        if q not in self.granted:
            if not self.run.answer(q):
                return DENY
            self.granted.add(q)
            self.run.events.append(('grant', q))
        return inner(q)


class Budget(Layer):
    """Forwards a request only while the cost of what it has forwarded stays within the bound."""
    name = 'Budget'

    def __init__(self, run):
        super().__init__(run)
        self.spent = 0

    def handle(self, q, inner):
        if self.spent + cost(q) > self.run.budget:
            return DENY
        self.spent += cost(q)
        return inner(q) if MUTANT != 'budget-twice' else (inner(q), inner(q))[1]


class Audit(Layer):
    """Writes every request that it forwards and the reply that it gets into a log."""
    name = 'Audit'

    def __init__(self, run):
        super().__init__(run)
        self.log = []

    def handle(self, q, inner):
        reply = inner(q)
        self.log.append((q, reply if self.run.full else None))      # or the request alone
        return reply


class Retry(Layer):
    """Forwards a request again while it fails, up to a number of tries."""
    name = 'Retry'

    def handle(self, q, inner):
        reply = inner(q)
        for _ in range(self.run.tries - 1):
            if reply[0] != 'fail':
                break
            reply = inner(q)
        return reply


class Norm(Layer):
    """Forwards the normal form of a request."""
    name = 'Norm'

    def handle(self, q, inner):
        return inner(NORM.get(q, q))


class Cache(Layer):
    """Answers a read that it has seen from its table, and empties the table on a write."""
    name = 'Cache'

    def __init__(self, run):
        super().__init__(run)
        self.table = {}

    def handle(self, q, inner):
        if q in WRITES:
            reply = inner(q)
            if reply[0] == 'ok':
                self.table.clear()
            return reply
        if q not in self.table:
            reply = inner(q)
            if reply[0] != 'ok':
                return reply
            self.table[q] = reply
        return self.table[q]


class Format(Layer):
    """After a write that succeeds, runs the formatter: a request of its own."""
    name = 'Format'

    def handle(self, q, inner):
        reply = inner(q)
        if q == 'write a' and reply[0] == 'ok':
            inner('fmt')
        return reply


class Redact(Layer):
    """Replaces every secret in a reply by a placeholder, which is longer."""
    name = 'Redact'

    def handle(self, q, inner):
        status, text = inner(q)
        return status, text.replace('K', '[x]')


class Trim(Layer):
    """Cuts a reply to the size that the context allows."""
    name = 'Trim'

    def handle(self, q, inner):
        status, text = inner(q)
        return status, text[:self.run.size]


LAYERS = {cls.name: cls for cls in (Guard, Once, Always, Budget, Audit, Retry, Norm, Cache, Format, Redact, Trim)}
DOWN = ('Guard', 'Once', 'Budget', 'Audit', 'Retry', 'Norm', 'Cache', 'Format')
TEN = DOWN + ('Redact', 'Trim')


# ---------------------------------------------------------------------------------------------
# 2. A run.  The stack is a tuple of layer names, the first on top.  A scenario gives what the
#    client asks for, which calls of the world fail, what the user answers, and the numbers.
# ---------------------------------------------------------------------------------------------

class Run:
    def __init__(self, stack, client, fails=(), no=(), budget=99, tries=2, size=8, full=True):
        self.budget, self.tries, self.size, self.no, self.full = budget, tries, size, frozenset(no), full
        self.events, self.blocks, self.asked = [], [[] for _ in stack], 0
        self.world = World(fails, size)
        self.layers = [LAYERS[name](self) for name in stack]
        self.client = [(q, self.call(0, q)) for q in client]

    def answer(self, q):
        self.asked += 1
        return q not in self.no

    def call(self, i, q):
        if i == len(self.layers):
            self.events.append(('world', q))
            return self.world(q)
        sent = []

        def inner(q2):
            sent.append(q2)
            return self.call(i + 1, q2)

        reply = self.layers[i].handle(q, inner)
        self.blocks[i].append((q, tuple(sent)))
        return reply

    def layer(self, name):
        return next((x for x in self.layers if x.name == name), None)


# ---------------------------------------------------------------------------------------------
# 3. The guarantees.  Each belongs to a layer and is a predicate on a finished run.
# ---------------------------------------------------------------------------------------------

def allowed(run):
    """Guard: every request that reaches the world is allowed."""
    return all(q in ALLOWED for q, _ in run.world.calls)


def covered(run):
    """Once: every request that reaches the world uses up an earlier grant of the same request."""
    have = {}
    for kind, q in run.events:
        if kind == 'grant':
            have[q] = have.get(q, 0) + 1
        elif have.get(q, 0) == 0:
            return False
        else:
            have[q] -= 1
    return True


def granted(run):
    """Always: every request that reaches the world was granted earlier."""
    have = set()
    for kind, q in run.events:
        if kind == 'grant':
            have.add(q)
        elif q not in have:
            return False
    return True


def within(run):
    """Budget: the requests that reach the world cost at most B."""
    return sum(cost(q) for q, _ in run.world.calls) <= run.budget


def exact(run):
    """Audit: the log is the sequence of calls of the world, with the replies if it keeps them."""
    if run.full:
        return run.layer('Audit').log == run.world.calls
    return run.layer('Audit').log == [(q, None) for q, _ in run.world.calls]


def clean_log(run):
    """Audit: no secret is in the log."""
    return not any(reply and 'K' in reply[1] for _, reply in run.layer('Audit').log)


def clean_cache(run):
    """Cache: no secret is in the table."""
    return not any('K' in text for _, text in run.layer('Cache').table.values())


def clean(run):
    """Redact: no secret reaches the client."""
    return not any('K' in text for _, (_, text) in run.client)


def short(run):
    """Trim: no reply that reaches the client is longer than N."""
    return all(len(text) <= run.size for _, (_, text) in run.client)


# name -> (the layers that must be in the stack for the guarantee to be asked for, predicate)
GUARANTEES = {'allowed': (('Guard',), allowed), 'covered': (('Once',), covered),
              'granted': (('Always',), granted), 'within': (('Budget',), within),
              'exact': (('Audit',), exact), 'clean': (('Redact',), clean),
              'clean log': (('Audit', 'Redact'), clean_log), 'clean cache': (('Cache', 'Redact'), clean_cache),
              'short': (('Trim',), short)}


# ---------------------------------------------------------------------------------------------
# 4. The theory.  On the way down a layer may drop a request, repeat it, rewrite it, or invent
#    one.  A guarantee about the requests that reach the world holds when it survives what
#    every layer below its owner does.  On the way up a layer keeps or breaks a property of a
#    reply; a guarantee about replies holds when the layer that establishes the property is
#    where the guarantee needs it and nothing in between breaks it.
# ---------------------------------------------------------------------------------------------

DOES = {'Guard': {'drop'}, 'Once': {'drop'}, 'Always': {'drop'}, 'Budget': {'drop'}, 'Audit': set(),
        'Retry': {'repeat'}, 'Norm': {'rewrite'}, 'Cache': {'drop'}, 'Format': {'invent'}, 'Redact': set(),
        'Trim': set()}
# what a layer does to a reply that it passes up: the properties that it breaks
BREAKS = {'Redact': {'short', 'same'}, 'Trim': {'same'}}
ESTABLISHES = {'Redact': 'clean', 'Trim': 'short'}


def does(name):
    if MUTANT == 'retry-quiet' and name == 'Retry':
        return set()
    if MUTANT == 'cache-quiet' and name == 'Cache':
        return set()
    return DOES[name]


def survives_table():
    """Which guarantee about requests survives which of the four things, decided in part 5."""
    table = {g: stream_survives(g) for g in STREAM_GUARANTEES}
    if MUTANT == 'guard-rewrite':
        table['allowed'] = table['allowed'] | {'rewrite'}
    if MUTANT == 'budget-repeat':
        table['within'] = table['within'] | {'repeat'}
    if MUTANT == 'once-invent':
        table['covered'] = table['covered'] | {'invent'}
    return table


def predict(stack, survives, weak=False):
    """For every guarantee whose layers are in the stack, whether the theory says that it holds
    in every run of the stack.  With `weak`, the log keeps requests only."""
    out = {}
    for g, (needs, _) in GUARANTEES.items():
        if not all(name in stack for name in needs):
            continue
        at = stack.index(needs[0])
        below, above = stack[at + 1:], stack[:at]
        if MUTANT == 'upside-down':
            below, above = above, below
        if g in survives:
            ok = all(does(m) <= survives[g] for m in below)
            if g == 'exact' and not weak:       # the replies in the log must be the world's
                ok = ok and not any('same' in BREAKS.get(m, ()) for m in below)
            out[g] = ok
        elif g == 'short':
            out[g] = MUTANT == 'redact-short' or not any('short' in BREAKS.get(m, ()) for m in above)
        elif g == 'clean':
            out[g] = True                       # no layer breaks it
        else:                                   # clean log, clean cache: Redact must be below
            out[g] = 'Redact' in below or MUTANT == 'log-clean' or (weak and g == 'clean log')
    return out


def before(names, survives, weak=False):
    """The pairs (x, y) of layers such that x must be above y: the constraints that `predict`
    imposes, read off the two tables."""
    pairs = set()
    for g, (needs, _) in GUARANTEES.items():
        if not all(name in names for name in needs):
            continue
        owner = needs[0]
        for m in names:
            if m == owner:
                continue
            if g in survives:
                if not does(m) <= survives[g] or (g == 'exact' and not weak and 'same' in BREAKS.get(m, ())):
                    pairs.add((m, owner))
            elif g == 'short' and 'short' in BREAKS.get(m, ()):
                pairs.add((owner, m))
            elif g in ('clean log', 'clean cache') and m == 'Redact' and not (weak and g == 'clean log'):
                pairs.add((owner, m))
    return pairs


def count_extensions(names, pairs):
    """The number of orders of `names` in which x comes before y for every pair (x, y)."""
    names = list(names)
    must = {y: sum(1 << names.index(x) for x, z in pairs if z == y) for y in names}
    ways = {0: 1}
    for mask in range(1, 1 << len(names)):
        ways[mask] = sum(ways[mask ^ (1 << i)] for i, y in enumerate(names)
                         if mask >> i & 1 and must[y] & ~(mask ^ (1 << i)) == 0)
    return ways[(1 << len(names)) - 1]


def block_within(name, q, sent):
    """Whether what a layer sent on for one request is within what the theory says it does."""
    d = DOES[name]
    rest = [x for x in sent if not ('invent' in d and x == 'fmt' and q != 'fmt')]
    forms = {q, NORM.get(q, q)} if 'rewrite' in d else {q}
    if any(x not in forms for x in rest) or len(set(rest)) > 1:
        return False
    return len(rest) == 1 or (len(rest) == 0 and 'drop' in d) or (len(rest) > 1 and 'repeat' in d)


# ---------------------------------------------------------------------------------------------
# 5. Streams.  A stream is a tuple of letters: ('world', q) for a request that reaches the
#    world, and letters of the owner of a guarantee: ('grant', q), ('log', q).  The four
#    things act on the world letters.  The stream alphabet has one request of each kind:
#    a (allowed and normal), A (allowed, normal form s), s (not allowed), f (invented).
# ---------------------------------------------------------------------------------------------

STREAM_NORM = {'A': 's'}
STREAM_ALLOWED = {'a', 'A', 'f'}
STREAM_BUDGET = 2
STREAM_COST = {}


def s_allowed(w):
    return all(q in STREAM_ALLOWED for kind, q in w if kind == 'world')


def s_covered(w):
    have = {}
    for kind, q in w:
        if kind == 'grant':
            have[q] = have.get(q, 0) + 1
        elif kind == 'world':
            if not have.get(q):
                return False
            have[q] -= 1
    return True


def s_granted(w):
    have = set()
    for kind, q in w:
        if kind == 'grant':
            have.add(q)
        elif kind == 'world' and q not in have:
            return False
    return True


def s_within(w):
    return sum(STREAM_COST.get(q, 1) for kind, q in w if kind == 'world') <= STREAM_BUDGET


def s_exact(w):
    return [q for kind, q in w if kind == 'log'] == [q for kind, q in w if kind == 'world']


STREAM_GUARANTEES = {'allowed': (s_allowed, ()), 'covered': (s_covered, ('grant',)),
                     'granted': (s_granted, ('grant',)), 'within': (s_within, ()), 'exact': (s_exact, ('log',))}


def perturbed(w, thing):
    """The streams that one application of `thing` to a world letter of w gives."""
    for i, (kind, q) in enumerate(w):
        if kind == 'world':
            if thing == 'drop':
                yield w[:i] + w[i + 1:]
            elif thing == 'repeat':
                yield w[:i] + (w[i],) + w[i:]
            elif thing == 'rewrite' and q in STREAM_NORM:
                yield w[:i] + (('world', STREAM_NORM[q]),) + w[i + 1:]
    if thing == 'invent':
        for i in range(len(w) + 1):
            yield w[:i] + (('world', 'f'),) + w[i:]


_SURVIVES = {}


def stream_survives(g, length=5):
    """The things that the guarantee survives: no stream of at most `length` letters that
    satisfies it has a perturbed stream that does not."""
    if g not in _SURVIVES:
        holds, own = STREAM_GUARANTEES[g]
        letters = [(kind, q) for kind in ('world',) + own for q in ('a', 'A', 's', 'f')]
        alive = set(('drop', 'repeat', 'rewrite', 'invent'))
        for n in range(length + 1):
            for w in product(letters, repeat=n):
                if holds(w):
                    for thing in list(alive):
                        if not all(holds(v) for v in perturbed(w, thing)):
                            alive.discard(thing)
        _SURVIVES[g] = frozenset(alive)
    return _SURVIVES[g]


class Dfa:
    """A guarantee as a deterministic automaton: `step(state, letter)` and `good(state)`."""

    def __init__(self, start, letters, step, good):
        self.start, self.letters, self.step, self.good = start, letters, step, good
        self.states, todo = {start}, [start]
        while todo:
            p = todo.pop()
            for a in letters:
                t = step(p, a)
                if t not in self.states:
                    self.states.add(t)
                    todo.append(t)

    def included(self, p, r):
        """Whether every word that is accepted from state p is accepted from state r."""
        seen, todo = {(p, r)}, [(p, r)]
        while todo:
            x, y = todo.pop()
            if self.good(x) and not self.good(y):
                return False
            for a in self.letters:
                pair = self.step(x, a), self.step(y, a)
                if pair not in seen:
                    seen.add(pair)
                    todo.append(pair)
        return True

    def survives(self):
        """Proposition 3.5: the moves that the guarantee survives, decided exactly."""
        out = set()
        world = [a for a in self.letters if a[0] == 'world']
        go = self.step
        tests = {'drop': lambda p, a: self.included(go(p, a), p),
                 'repeat': lambda p, a: self.included(go(p, a), go(go(p, a), a)),
                 'rewrite': lambda p, a: a[1] not in STREAM_NORM or self.included(
                     go(p, a), go(p, ('world', STREAM_NORM[a[1]]))),
                 'invent': lambda p, a: self.included(p, go(p, ('world', 'f')))}
        for move, test in tests.items():
            if all(test(p, a) for p in self.states for a in world):
                out.add(move)
        return frozenset(out)


def automata():
    """The three guarantees of Table 2 that are regular, as automata."""
    kinds = ('a', 'A', 's', 'f')
    world = [('world', q) for q in kinds]
    grants = [('grant', q) for q in kinds]
    return {
        'allowed': Dfa(True, world, lambda p, a: p and a[1] in STREAM_ALLOWED, lambda p: p),
        'within': Dfa(0, world, lambda p, a: min(p + 1, STREAM_BUDGET + 1), lambda p: p <= STREAM_BUDGET),
        'granted': Dfa(frozenset(), world + grants,
                       lambda p, a: None if p is None or (a[0] == 'world' and a[1] not in p)
                       else p | {a[1]} if a[0] == 'grant' else p, lambda p: p is not None),
    }


def embeds(f, w):
    """Whether f is w with letters left out."""
    it = iter(w)
    return all(x in it for x in f)


def patterns(holds, letters, length):
    """Section 4: the shortest streams of at most `length` world letters that violate a
    guarantee and of which no part, with letters left out, does."""
    bad = []
    for n in range(length + 1):
        for w in product(letters, repeat=n):
            if not holds(tuple(('world', q) for q in w)) and not any(embeds(f, w) for f in bad):
                bad.append(w)
    return bad


def s_gate(w):
    """A guarantee of the kind of an earlier paper: after a fetch of untrusted text, no write."""
    seen = False
    for _, q in w:
        if q == 'u':
            seen = True
        elif q == 'w' and seen:
            return False
    return True


# ---------------------------------------------------------------------------------------------
# 6. The tests.
# ---------------------------------------------------------------------------------------------

# Scenarios that make every layer do, below or above every guarantee, what it can do.
BATTERY = [
    dict(client=('read a', 'read a')),                                  # the cache answers
    dict(client=('write a',), fails=(True,), budget=1),                 # a retry, tight budget
    dict(client=('write a',), fails=(True,)),                           # a retry
    dict(client=('read A',)),                                           # a rewrite to an allowed request
    dict(client=('read A',), budget=1),                                 # the same, tight budget
    dict(client=('read b/../s',)),                                      # a rewrite to a request that is not
    dict(client=('read s',)),                                           # the guard refuses
    dict(client=('write a',), budget=1),                                # the formatter, tight budget
    dict(client=('write a',)),                                          # the formatter
    dict(client=('write a',), no=('write a',)),                         # the user refuses
    dict(client=('write a',), budget=0),                                # the budget refuses
    dict(client=('read k',)),                                           # a reply with a secret
    dict(client=('fetch u',)),                                          # a long reply
]


def observe(stack, scenarios, weak=False):
    """For every guarantee whose layers are in the stack, whether it holds in all the scenarios."""
    out = {g: True for g, (needs, _) in GUARANTEES.items() if all(name in stack for name in needs)}
    for scenario in scenarios:
        run = Run(stack, full=not weak, **scenario)
        for g in out:
            if out[g] and not GUARANTEES[g][1](run):
                out[g] = False
    return out


def random_scenario(rng):
    n = 1 + int(rng.random() * 5)
    return dict(client=tuple(REQUESTS[int(rng.random() * len(REQUESTS))] for _ in range(n)),
                fails=tuple(rng.random() < 0.25 for _ in range(12)),
                no=tuple(q for q in REQUESTS if rng.random() < 0.1),
                budget=int(rng.random() * 6), tries=1 + int(rng.random() * 3), size=4 + int(rng.random() * 6))


def compare(stacks, survives, counts, weak=False):
    """The prediction against the battery for every stack: a guarantee that the theory says
    holds must hold, and one that it says can fail must fail in some scenario."""
    for stack in stacks:
        want, got = predict(stack, survives, weak), observe(stack, BATTERY, weak)
        assert want == got, (stack, {g: (want[g], got[g]) for g in want if want[g] != got[g]})
        counts['stacks'] += 1
        counts['guarantees'] += len(want)
        counts['hold'] += sum(want.values())


def extensions(names, before):
    """The orders of `names` in which x comes before y for every pair (x, y) of `before`."""
    return [p for p in permutations(names) if all(p.index(x) < p.index(y) for x, y in before)]


class Variant:
    """A change of the world for the length of a `with`: which requests are allowed and what
    they cost, for the runs and for the streams of part 5."""

    def __init__(self, allowed=None, costs=None, stream_allowed=None, stream_cost=None):
        self.new = dict(ALLOWED=allowed, COSTS=costs, STREAM_ALLOWED=stream_allowed, STREAM_COST=stream_cost)

    def __enter__(self):
        self.old = {k: globals()[k] for k in self.new}
        globals().update({k: v for k, v in self.new.items() if v is not None})
        _SURVIVES.clear()

    def __exit__(self, *exc):
        globals().update(self.old)
        _SURVIVES.clear()


def disagreements(stacks, survives):
    """The guarantees that hold in the battery although the theory says that they can fail, and
    those that fail although it says that they hold."""
    hidden = wrong = 0
    for stack in stacks:
        want, got = predict(stack, survives), observe(stack, BATTERY)
        hidden += sum(got[g] and not want[g] for g in want)
        wrong += sum(want[g] and not got[g] for g in want)
    return hidden, wrong


def witnesses(survives):
    """Table 3: for every pair of the relation, the two layers alone in the wrong order, the
    first scenario of the battery that breaks a guarantee, and what was seen."""
    rows = []
    for x, y in sorted(before(TEN, survives), key=lambda p: (TEN.index(p[1]), TEN.index(p[0]))):
        stack = (y, x)
        for scenario in BATTERY:
            run = Run(stack, **scenario)
            broken = [g for g, (needs, holds) in GUARANTEES.items()
                      if all(name in stack for name in needs) and not holds(run)]
            if broken:
                rows.append((stack, scenario, [q for q, _ in run.world.calls], broken))
                break
        else:
            raise AssertionError((x, y))
    return rows


def frontier(orders, work):
    """Section 7: for every correct order, the questions to the user and the budget that is
    charged for requests that do not reach the world, over a fixed set of scenarios; and the
    pairs of the two numbers that no order improves in both."""
    seen = {}
    for p in orders:
        asked = waste = 0
        for scenario in work:
            run = Run(p, **scenario)
            asked += run.asked
            waste += run.layer('Budget').spent - sum(cost(q) for q, _ in run.world.calls)
        seen.setdefault((asked, waste), []).append(p)
    best = sorted(x for x in seen if not any(y != x and y[0] <= x[0] and y[1] <= x[1] for y in seen))
    return seen, best


MUTANTS = ('retry-quiet', 'cache-quiet', 'guard-rewrite', 'budget-repeat', 'once-invent', 'redact-short',
           'log-clean', 'upside-down', 'budget-twice')
THINGS = ('drop', 'repeat', 'rewrite', 'invent')
FIVES = [p for five in combinations(TEN, 5) for p in permutations(five)]


def random_stack(rng, names, least=1):
    pool, out = list(names), []
    for _ in range(least + int(rng.random() * (len(pool) - least + 1))):
        out.append(pool.pop(int(rng.random() * len(pool))))
    return tuple(out)


def check_blocks(rng, trials, counts):
    """Table 1: in random runs of random stacks, what every layer sends on for a request is
    within what the theory says the layer does."""
    for _ in range(trials):
        stack = random_stack(rng, TEN)
        run = Run(stack, **random_scenario(rng))
        for name, blocks in zip(stack, run.blocks):
            for q, sent in blocks:
                assert block_within(name, q, sent), (name, q, sent)
                counts['blocks'] += 1
        counts['block runs'] += 1


def check_replies(rng, trials):
    """Section 5: what Redact and Trim do to a reply.  Returns the properties that each was
    seen to break."""
    seen = {'Redact': set(), 'Trim': set()}
    for _ in range(trials):
        size = 2 + int(rng.random() * 6)
        text = ''.join('Kxu'[int(rng.random() * 3)] for _ in range(int(rng.random() * 12)))
        run = Run((), (), size=size)
        for cls in (Redact, Trim):
            _, out = cls(run).handle('q', lambda q: ('ok', text))
            if cls is Redact:
                assert 'K' not in out                                   # establishes clean
            else:
                assert len(out) <= size                                 # establishes short
                assert 'K' in text or 'K' not in out                    # keeps clean
            if len(text) <= size < len(out):
                seen[cls.name].add('short')
            if out != text:
                seen[cls.name].add('same')
    return seen


def check_sound(rng, trials, survives, counts):
    """Theorems 3.3 and 5.2: in random runs of random stacks, a guarantee that the theory says
    holds is never violated."""
    for _ in range(trials):
        weak = rng.random() < 0.5
        stack = random_stack(rng, TEN + ('Always',))
        want = predict(stack, survives, weak)
        for _ in range(4):
            run = Run(stack, full=not weak, **random_scenario(rng))
            for g, holds in want.items():
                if holds:
                    assert GUARANTEES[g][1](run), (stack, g)
                    counts['kept'] += 1
        counts['sound runs'] += 4


def check_patterns(rng, trials):
    """Proposition 4.1 on random sets of patterns: the patterns of the guarantee that avoids
    them are the least among them, and it survives repeating exactly if none of those has a
    letter twice in a row."""
    letters, both = ('a', 'b'), 0
    for _ in range(trials):
        F = {tuple(letters[int(rng.random() * 2)] for _ in range(1 + int(rng.random() * 3)))
             for _ in range(1 + int(rng.random() * 3))}
        least = {f for f in F if not any(g != f and embeds(g, f) for g in F)}

        def holds(w, F=F):
            return not any(embeds(f, [q for _, q in w]) for f in F)

        assert set(patterns(holds, letters, 4)) == least
        streams = [tuple(('world', q) for q in w) for n in range(5) for w in product(letters, repeat=n)]
        repeats = all(holds(v) for w in streams if holds(w) for v in perturbed(w, 'repeat'))
        assert all(holds(v) for w in streams if holds(w) for v in perturbed(w, 'drop'))
        assert repeats == all(x != y for f in least for x, y in zip(f, f[1:]))
        both += repeats
    return both


def catches(name, rng, survives):
    """Runs the test that should notice the mistake `name`.  True if it does."""
    global MUTANT
    MUTANT = name
    _SURVIVES.clear()
    try:
        if name == 'budget-twice':
            check_blocks(rng, 300, {'blocks': 0, 'block runs': 0})
        else:
            compare(FIVES, survives_table(), {'stacks': 0, 'guarantees': 0, 'hold': 0})
        return False
    except AssertionError:
        return True
    finally:
        MUTANT = None


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    survives = survives_table()
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten',
               'eleven', 'twelve', 'thirteen']

    # Table 1: the layers, and that they do no more than the table says
    words = {'drop': 'drops', 'repeat': 'repeats', 'rewrite': 'rewrites', 'invent': 'invents'}
    rows = []
    for name in TEN:
        doc = ' '.join(LAYERS[name].__doc__.split())
        up = ('establishes ' + ESTABLISHES[name] if name in ESTABLISHES else '')
        up += ''.join('; breaks ' + b if b != 'same' else '; changes replies' for b in sorted(BREAKS.get(name, ()), reverse=True))
        rows.append(f"{name} & {doc} & {', '.join(words[t] for t in THINGS if t in DOES[name]) or '--'} & {up or '--'} \\\\")
    tables['layers'] = rows
    counts = dict.fromkeys(('blocks', 'block runs', 'kept', 'sound runs'), 0)
    check_blocks(rng, 6000, counts)
    lines.append(f"{counts['block runs']} random runs: {counts['blocks']} requests received by layers, and what the "
                 'layer sent on for each is within what Table 1 says it does')
    claim('blocks-within', True)
    seen = check_replies(rng, 4000)
    claim('replies', seen == {name: BREAKS[name] for name in ('Redact', 'Trim')})
    lines.append('4000 random replies: Redact removes every secret and breaks ' + ', '.join(sorted(seen['Redact'])) +
                 '; Trim cuts to the size, keeps a reply free of secrets, and breaks ' + ', '.join(sorted(seen['Trim'])))
    nums.update(BlockRuns=f"{counts['block runs']:,}", Blocks=f"{counts['blocks']:,}", ReplyTrials='4,000')

    # Section 2: three layers
    low = Run(('Once', 'Budget', 'Retry'), ('write a',), fails=(True, True), tries=3, budget=1)
    top = Run(('Retry', 'Once', 'Budget'), ('write a',), fails=(True, True), tries=3, budget=3)
    grants = lambda run: sum(kind == 'grant' for kind, _ in run.events)
    claim('overview', len(low.world.calls) == 3 and grants(low) == 1 and not covered(low) and not within(low)
          and len(top.world.calls) == 3 and grants(top) == 3 and covered(top) and within(top)
          and [p for p in permutations(('Once', 'Budget', 'Retry')) if all(predict(p, survives).values())]
          == [('Retry', 'Once', 'Budget'), ('Retry', 'Budget', 'Once')])
    lines.append('three layers: with Retry at the bottom one grant and a budget of one meet three requests at the '
                 'world; the correct orders are the two with Retry on top')

    # Table 2: what each guarantee about requests survives, decided over all short streams
    owners = {g: needs[0] for g, (needs, _) in GUARANTEES.items()}
    rows = []
    for g in STREAM_GUARANTEES:
        lines.append(f"{g} survives: {', '.join(t for t in THINGS if t in survives[g]) or 'nothing'}")
        rows.append(f"{g} & {owners[g]} & " + ' & '.join('yes' if t in survives[g] else '--' for t in THINGS) + ' \\\\')
    tables['survive'] = rows
    claim('survive-table', survives == {'allowed': {'drop', 'repeat', 'invent'}, 'covered': {'drop'},
                                        'granted': {'drop', 'repeat'}, 'within': {'drop', 'rewrite'},
                                        'exact': set()})
    n_streams = sum(8 ** n for n in range(6))
    nums.update(StreamLength='5', Streams=f'{n_streams:,}')

    # Lemma 3.4 and Proposition 3.5: the regular guarantees, decided exactly
    exactly = {g: d.survives() for g, d in automata().items()}
    claim('decided', all(exactly[g] == survives[g] for g in exactly) and set(exactly) == {'allowed', 'within', 'granted'})
    lines.append('decided by automata, with the same result: ' + ', '.join(
        f'{g} ({len(d.states)} states)' for g, d in automata().items()))
    nums['GrantedStates'] = str(len(automata()['granted'].states))

    # Section 4: forbidden patterns
    pats = {'allowed': patterns(s_allowed, ('a', 'A', 's', 'f'), 4),
            'within': patterns(s_within, ('a', 'A', 's', 'f'), 4),
            'gate': patterns(s_gate, ('u', 'w', 'a'), 4)}
    stutter = {g: any(x == y for f in fs for x, y in zip(f, f[1:])) for g, fs in pats.items()}
    gate_streams = [tuple(('world', q) for q in w) for n in range(6) for w in product(('u', 'w', 'a'), repeat=n)]
    gate_repeat = all(s_gate(v) for w in gate_streams if s_gate(w) for v in perturbed(w, 'repeat'))
    claim('patterns', pats['allowed'] == [('s',)] and len(pats['within']) == 4 ** (STREAM_BUDGET + 1)
          and all(len(f) == STREAM_BUDGET + 1 for f in pats['within']) and pats['gate'] == [('u', 'w')]
          and not stutter['allowed'] and stutter['within'] and not stutter['gate'] and gate_repeat
          and 'repeat' in survives['allowed'] and 'repeat' not in survives['within'])
    both = check_patterns(rng, 500)
    claim('pattern-sets', True)
    lines.append(f"patterns: allowed {pats['allowed']}; within: the {len(pats['within'])} streams of "
                 f"{STREAM_BUDGET + 1} requests; gate {pats['gate']}; 500 random sets of patterns over two "
                 f'letters, {both} of which survive repeating')
    nums.update(PatternSets='500', PatternsWithin=str(len(pats['within'])), PatternsRepeat=str(both))

    # Section 6: every order of the eight layers, of every five of the ten, and random orders of the ten
    eight = {'stacks': 0, 'guarantees': 0, 'hold': 0}
    per, all_four = dict.fromkeys(('allowed', 'covered', 'within', 'exact'), 0), 0
    for stack in permutations(DOWN):
        want, got = predict(stack, survives), observe(stack, BATTERY)
        assert want == got, stack
        for g in per:
            per[g] += want[g]
        all_four += all(want.values())
        eight['stacks'] += 1
    pairs = before(DOWN, survives)
    claim('eight-agree', eight['stacks'] == 40320)
    claim('eight-orders', all_four == count_extensions(DOWN, pairs) == len(extensions(DOWN, pairs)))
    lines.append(f"eight layers: {eight['stacks']} orders, prediction and battery agree on every guarantee; hold in "
                 + ', '.join(f'{g} {n}' for g, n in per.items()) + f'; all four in {all_four}')
    lines.append('eight layers: must be above: ' + ', '.join(f'{x} > {y}' for x, y in sorted(pairs)))
    claim('eight-pairs', pairs == {(m, 'Audit') for m in DOWN if m != 'Audit'} | {
        ('Retry', 'Once'), ('Norm', 'Once'), ('Format', 'Once'), ('Retry', 'Budget'), ('Format', 'Budget'),
        ('Norm', 'Guard')})
    always = tuple('Always' if name == 'Once' else name for name in DOWN)
    n_always = count_extensions(always, before(always, survives))
    claim('always-more', n_always > all_four and ('Retry', 'Always') not in before(always, survives))
    lines.append(f'with Always in the place of Once: {n_always} orders')
    nums.update(EightOrders=f"{eight['stacks']:,}", EightGood=str(all_four), EightAlways=str(n_always),
                EightPairs=str(len(pairs)), EightShare=f"{100 * all_four / eight['stacks']:.1f}",
                **{'Eight' + g.capitalize(): f'{n:,}' for g, n in per.items()})

    fives = {False: {'stacks': 0, 'guarantees': 0, 'hold': 0}, True: {'stacks': 0, 'guarantees': 0, 'hold': 0}}
    for weak in (False, True):
        compare(FIVES, survives, fives[weak], weak)
    tens = {'stacks': 0, 'guarantees': 0, 'hold': 0}
    for _ in range(3000):
        stack = random_stack(rng, TEN, least=10)
        compare([stack], survives, tens, weak=rng.random() < 0.5)
    claim('fives-agree', fives[False]['stacks'] == fives[True]['stacks'] == len(FIVES) and tens['stacks'] == 3000)
    lines.append(f"five of ten: {len(FIVES)} stacks, {fives[False]['guarantees']} guarantees, agree with the log in "
                 f"both forms; {tens['stacks']} random orders of all ten, {tens['guarantees']} guarantees, agree")
    nums.update(Fives=f'{len(FIVES):,}', FiveGuarantees=f"{fives[False]['guarantees']:,}", Tens=f"{tens['stacks']:,}",
                TenGuarantees=f"{tens['guarantees']:,}")

    check_sound(rng, 5000, survives, counts)
    claim('sound', True)
    lines.append(f"{counts['sound runs']} random runs of random stacks: {counts['kept']} guarantees that the theory "
                 'says hold, and each holds')
    nums.update(SoundRuns=f"{counts['sound runs']:,}", Kept=f"{counts['kept']:,}")

    # Section 5: the log and the secrets
    strict, weak = count_extensions(TEN, before(TEN, survives)), count_extensions(TEN, before(TEN, survives, True))
    conflict = all(not (want['exact'] and want['clean log']) for stack in FIVES
                   if 'Audit' in stack and 'Redact' in stack for want in [predict(stack, survives)])
    total = 1
    for i in range(2, 11):
        total *= i
    claim('conflict', strict == 0 and conflict and weak > 0)
    claim('one-in-hundred', 100 * all_four < eight['stacks'] and 100 * weak < total)
    lines.append(f'ten layers: {strict} orders keep every guarantee with a log of requests and replies, {weak} of '
                 f'{total} with a log of requests')
    nums.update(TenWeak=f'{weak:,}', TenOrders=f'{total:,}', TenShare=f'{100 * weak / total:.2f}')

    # Table 3: every pair in the wrong order
    tt = lambda q: '\\texttt{%s}' % q
    rows = []
    for stack, scenario, world, broken in witnesses(survives):
        notes = [note for key, note in (('fails', 'the first call fails'), ('no', 'the user says no'),
                                        ('budget', 'budget %s' % scenario.get('budget'))) if key in scenario]
        client = ', '.join(tt(q) for q in scenario['client']) + (' (' + ', '.join(notes) + ')' if notes else '')
        lines.append(f"{stack[0]} above {stack[1]}: client {' '.join(scenario['client'])} {notes}: world "
                     f"{world}: breaks {', '.join(broken)}")
        rows.append(f"\\ly{{{stack[0]}}} above \\ly{{{stack[1]}}} & {client} & "
                    f"{', '.join(tt(q) for q in world) or 'nothing'} & {', '.join(broken)} \\\\")
    tables['witnesses'] = rows
    claim('witnesses', len(rows) == len(before(TEN, survives)))
    nums['TenPairs'] = str(len(rows))

    # Section 6: variants of the eight layers
    variants = [
        ('the allow-list is closed under normalization',
         dict(allowed=ALLOWED - {'read b/../s'}, stream_allowed=STREAM_ALLOWED - {'A'}), DOWN),
        ('the formatter is outside the allow-list',
         dict(allowed=ALLOWED - {'fmt'}, stream_allowed=STREAM_ALLOWED - {'f'}), DOWN),
        ('a normal form can cost more', dict(costs={'read a': 2}, stream_cost={'s': 2}), DOWN),
        ('\\ly{Always} in the place of \\ly{Once}', {}, always),
    ]
    rows = [f"as in Table~\\ref{{tab:survive}} & {len(pairs)} & {all_four} & 0 \\\\"]
    hidden_all = {}
    for name, change, names in variants:
        with Variant(**change):
            table = survives_table()
            ps = before(names, table)
            n = count_extensions(names, ps)
            swap = lambda stack: tuple('Always' if x == 'Once' and 'Always' in names else x for x in stack)
            hidden, wrong = disagreements([swap(stack) for stack in FIVES], table)
        assert wrong == 0, name
        hidden_all[name] = hidden
        lines.append(f'variant, {name}: {len(ps)} pairs, {n} orders; on the stacks of five, {hidden} guarantees '
                     f'hold although the relation says that they can fail, and none fails against it')
        rows.append(f'{name} & {len(ps)} & {n} & {hidden} \\\\')
    tables['variants'] = rows
    claim('variants', [hidden_all[name] > 0 for name, _, _ in variants] == [False, True, False, False])
    nums['HiddenOutside'] = str(hidden_all['the formatter is outside the allow-list'])

    # Section 7: the correct orders differ in what they cost
    work = [random_scenario(rng) for _ in range(300)]
    orders = extensions(DOWN, pairs)
    seen, best = frontier(orders, work)
    rows = []
    for asked, waste in best:
        example = seen[(asked, waste)][0]
        rows.append(f"{asked} & {waste} & {len(seen[(asked, waste)])} & {', '.join(example)} \\\\")
        lines.append(f'{asked} questions, {waste} wasted: {len(seen[(asked, waste)])} orders, such as {example}')
    tables['frontier'] = rows
    most = max(a for a, _ in seen)
    lower = lambda p: max(p.index('Once'), p.index('Budget'))
    claim('frontier', len(best) > 1 and best[0][1] > 0 and best[-1][1] == 0 and all(
        (p.index('Budget') < p.index('Once')) == (i < len(best) - 1)
        and p.index('Guard') < lower(p) and p.index('Cache') < lower(p)
        for i, x in enumerate(best) for p in seen[x]))
    nums.update(Work='300', AskedLeast=str(best[0][0]), AskedMost=f'{most:,}', WasteMost=str(max(w for _, w in seen)),
                Frontier=spelled[len(best)], AskedNoWaste=str(best[-1][0]), WasteLeastAsked=str(best[0][1]))

    # a guarantee can hold although the theory says that it can fail: Once above Retry above a budget of one
    masked = ('Once', 'Retry', 'Budget')
    claim('masked', not predict(masked, survives)['covered'] and all(
        covered(Run(masked, **dict(random_scenario(rng), budget=1))) for _ in range(3000))
          and not covered(Run(masked, ('write a',), fails=(True,))))
    lines.append('Once above Retry above Budget: covered can fail, and with a budget of one it never does in 3000 runs')
    nums['MaskedRuns'] = '3,000'

    # Proposition 6.3: retries multiply
    rows = []
    for k in (1, 2, 3):
        for tries in (2, 3):
            run = Run(('Retry',) * k, ('write a',), fails=(True,) * 100, tries=tries)
            capped = Run(('Retry',) * k + ('Budget',), ('write a',), fails=(True,) * 100, tries=tries, budget=4)
            assert len(run.world.calls) == tries ** k and len(capped.world.calls) == min(4, tries ** k)
            rows.append(f'{k} & {tries} & {len(run.world.calls)} & {len(capped.world.calls)} \\\\')
            lines.append(f'{k} Retry layers of {tries} tries: {len(run.world.calls)} calls of the world, '
                         f'{len(capped.world.calls)} above a budget of 4')
    tables['retries'] = rows
    claim('retries-multiply', True)

    # every deliberate mistake is noticed
    caught = {name: catches(name, random.Random(2026), survives) for name in MUTANTS}
    _SURVIVES.clear()
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed: ' + ', '.join(MUTANTS))
    nums.update(Mutants=spelled[len(MUTANTS)], Layers=spelled[len(TEN)], Battery=spelled[len(BATTERY)],
                Lines=f"{round(len(open(os.path.join(here, 'layers.py')).readlines()), -2):,}", Seed='2026')

    paper = os.path.join(here, '..', 'paper.tex')
    if os.path.exists(paper):
        import re
        marked = set(re.findall(r'\\claim\{([a-z-]+)\}', open(paper).read()))
        assert marked == CLAIMS, (sorted(marked - CLAIMS), sorted(CLAIMS - marked))
    lines.append(f'{len(CLAIMS)} sentences of the paper checked: ' + ', '.join(sorted(CLAIMS)))

    os.makedirs(outdir, exist_ok=True)
    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by layers.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by layers.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
