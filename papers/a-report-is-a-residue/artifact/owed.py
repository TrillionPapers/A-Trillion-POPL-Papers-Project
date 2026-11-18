#!/usr/bin/env python3
"""Tests the claims of "A Report Is a Residue" on an implementation of its definitions.

The file has seven parts.

1. Regular expressions over letters, with shuffle: derivatives, and a second test of
   membership that uses no derivatives.
2. Obligations, rules, and the ledger; the same verdicts computed from the definition.
3. States, coverage, the shield, and the least request.
4. Two agents and the frame condition.
5. Code and its check.
6. Random systems.
7. The tests, the examples of the paper, and the session of Section 8.
   `python3 owed.py out` writes out/check.txt, out/numbers.tex and the tables of the paper.

A test is not a proof.  The proofs are in the paper.
"""
import heapq
import os
import random
import sys
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations_with_replacement, count

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked
LEDGER_MUTANTS = ('no-watch', 'self-trigger', 'never-break', 'no-retire', 'stale-report')
SHIELD_MUTANTS = ('plan-blind', 'separate', 'no-trigger-cover', 'need-complete')
MUTANTS = LEDGER_MUTANTS + SHIELD_MUTANTS + ('greedy-ask', 'half-frame', 'star-once', 'alt-first')


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. Regular expressions: ('0',) | ('1',) | ('sym', letters) | ('seq', r, s) | ('alt', (r, ...))
#    | ('star', r) | ('par', r, s).  The constructors keep every expression other than ZERO
#    nonempty, so that `r != ZERO` tests whether the language of r has a word.
# ---------------------------------------------------------------------------------------------

ZERO, ONE = ('0',), ('1',)


@lru_cache(maxsize=None)
def skey(r):
    if r[0] == 'sym':
        return ('sym', tuple(sorted(r[1])))
    if r[0] == 'alt':
        return ('alt',) + tuple(skey(q) for q in r[1])
    return (r[0],) + tuple(skey(q) for q in r[1:])


def sym(*letters):
    return ('sym', frozenset(letters)) if letters else ZERO


def seq2(r, s):
    if r == ZERO or s == ZERO:
        return ZERO
    if r == ONE:
        return s
    if s == ONE:
        return r
    if r[0] == 'seq':
        return ('seq', r[1], seq2(r[2], s))
    return ('seq', r, s)


def seq(*rs):
    out = ONE
    for r in reversed(rs):
        out = seq2(r, out)
    return out


def alt(*rs):
    parts, letters_ = set(), set()
    for r in rs:
        for q in (r[1] if r[0] == 'alt' else (r,)):
            if q[0] == 'sym':
                letters_ |= q[1]
            elif q != ZERO:
                parts.add(q)
    if letters_:
        parts.add(('sym', frozenset(letters_)))
    if not parts:
        return ZERO
    if len(parts) == 1:
        return next(iter(parts))
    return ('alt', tuple(sorted(parts, key=skey)))


def star(r):
    if r in (ZERO, ONE):
        return ONE
    return r if r[0] == 'star' else ('star', r)


def par2(r, s):
    if r == ZERO or s == ZERO:
        return ZERO
    if r == ONE:
        return s
    if s == ONE:
        return r
    return ('par',) + tuple(sorted((r, s), key=skey))


def par(*rs):
    out = ONE
    for r in rs:
        out = par2(out, r)
    return out


def opt(r):
    return alt(ONE, r)


def anything(sigma):
    return star(sym(*sigma))


@lru_cache(maxsize=None)
def nullable(r):
    k = r[0]
    if k in ('1', 'star'):
        return True
    if k in ('0', 'sym'):
        return False
    if k == 'alt':
        return any(nullable(q) for q in r[1])
    return nullable(r[1]) and nullable(r[2])


@lru_cache(maxsize=None)
def deriv(r, a):
    """What is left of r after the letter a."""
    k = r[0]
    if k in ('0', '1'):
        return ZERO
    if k == 'sym':
        return ONE if a in r[1] else ZERO
    if k == 'alt':
        return alt(*[deriv(q, a) for q in r[1]])
    if k == 'star':
        return seq2(deriv(r[1], a), r)
    if k == 'seq':
        d = seq2(deriv(r[1], a), r[2])
        return alt(d, deriv(r[2], a)) if nullable(r[1]) else d
    return alt(par2(deriv(r[1], a), r[2]), par2(r[1], deriv(r[2], a)))


@lru_cache(maxsize=None)
def letters(r):
    k = r[0]
    if k in ('0', '1'):
        return frozenset()
    if k == 'sym':
        return r[1]
    if k == 'alt':
        return frozenset().union(*[letters(q) for q in r[1]])
    if k == 'star':
        return letters(r[1])
    return letters(r[1]) | letters(r[2])


@lru_cache(maxsize=None)
def pref(r):
    """An expression for the beginnings of the words of r, built without derivatives."""
    k = r[0]
    if k in ('0', '1'):
        return r
    if k == 'sym':
        return alt(ONE, r)
    if k == 'alt':
        return alt(*[pref(q) for q in r[1]])
    if k == 'star':
        return seq2(r, pref(r[1]))
    if k == 'seq':
        return alt(pref(r[1]), seq2(r[1], pref(r[2])))
    return par2(pref(r[1]), pref(r[2]))


@lru_cache(maxsize=400000)
def member(r, w):
    """Whether the word w is in the language of r, by cutting w in every way.  The tests use
    it as a second opinion on everything that the derivatives compute."""
    k, n = r[0], len(w)
    if k == '0':
        return False
    if k == '1':
        return n == 0
    if k == 'sym':
        return n == 1 and w[0] in r[1]
    if k == 'alt':
        return any(member(q, w) for q in r[1])
    if k == 'seq':
        return any(member(r[1], w[:i]) and member(r[2], w[i:]) for i in range(n + 1))
    if k == 'star':
        return n == 0 or any(member(r[1], w[:i]) and member(r, w[i:]) for i in range(1, n + 1))
    for mask in range(1 << n):
        u = tuple(w[i] for i in range(n) if mask >> i & 1)
        v = tuple(w[i] for i in range(n) if not mask >> i & 1)
        if member(r[1], u) and member(r[2], v):
            return True
    return False


def show(r, level=0, name=str, signs=(' + ', ' || ', ' ', '*', '0', '1')):
    """The expression as text.  `name` prints a letter."""
    plus, shuffle, then, many, zero, one = signs
    k = r[0]
    if k == '0':
        s, p = zero, 3
    elif k == '1':
        s, p = one, 3
    elif k == 'sym':
        s, p = plus.join(name(a) for a in sorted(r[1])), 3 if len(r[1]) == 1 else 0
    elif k == 'alt':
        s, p = plus.join(show(q, 1, name, signs) for q in r[1]), 0
    elif k == 'par':
        s, p = shuffle.join(show(q, 2, name, signs) for q in r[1:]), 1
    elif k == 'seq':
        s, p = show(r[1], 3, name, signs) + then + show(r[2], 2, name, signs), 2
    else:
        s, p = show(r[1], 3, name, signs) + many, 3
    return '(' + s + ')' if p < level else s


# ---------------------------------------------------------------------------------------------
# 2. An obligation is a pair (r, W): perform a word of r, where only the letters of W count.
#    A watched letter that r does not expect breaks the obligation.
# ---------------------------------------------------------------------------------------------

MET, BROKEN, PENDING = 'met', 'broken', 'pending'


def ob(r, *also):
    """The obligation to perform a word of r; the letters `also` are watched and not expected."""
    assert r != ZERO and not nullable(r)
    return r, letters(r) | frozenset(also)


def ostep(o, a):
    """Section 3.2: what is left of the obligation after the letter a, or a verdict."""
    r, W = o
    if a not in W and MUTANT != 'no-watch':
        return o
    d = deriv(r, a)
    if nullable(d) and MUTANT != 'no-retire':
        return MET
    if d == ZERO:
        return o if MUTANT == 'never-break' else BROKEN
    return d, W


def verdict(o, w):
    """Definition 3.1 read off the language, with no derivative: the status of the obligation
    after the letters w, and the number of letters after which it was settled."""
    r, W = o
    for n in range(1, len(w) + 1):
        if w[n - 1] in W:
            u = tuple(a for a in w[:n] if a in W)
            if member(r, u):
                return MET, n
            if not member(pref(r), u):
                return BROKEN, n
    return PENDING, None


class Rules:
    """Standing instructions: the obligations that performing a letter creates."""

    def __init__(self, table):
        self.table = {a: tuple(os) for a, os in table.items() if os}

    def __call__(self, a):
        return self.table.get(a, ())


NONE = Rules({})


class Ledger:
    """Section 3: the open obligations with what is left of each, and the closed ones with
    their verdicts.  The ledger only watches; it refuses nothing."""

    def __init__(self, rules, owed=()):
        self.rules, self.now = rules, 0
        self.open = {(0, i): [None, o, o] for i, o in enumerate(owed)}
        self.closed = {}

    def act(self, a):
        self.now += 1
        fresh = {(self.now, i): [a, o, o] for i, o in enumerate(self.rules(a))}
        if MUTANT == 'self-trigger':
            self.open.update(fresh)
        for name in list(self.open):
            origin, first, o = self.open[name]
            left = ostep(o, a)
            if left in (MET, BROKEN):
                del self.open[name]
                self.closed[name] = (origin, first, left, self.now)
            else:
                self.open[name][2] = left
        self.open.update(fresh)

    def shape(self):
        return frozenset(o for _, _, o in self.open.values())

    def report(self):
        """What a successor must know: every open obligation, its origin, and what is left."""
        return [(name, origin, first if MUTANT == 'stale-report' else left)
                for name, (origin, first, left) in sorted(self.open.items())]

    def verdicts(self):
        out = {name: (first, v, t) for name, (_, first, v, t) in self.closed.items()}
        out.update({name: (first, PENDING, None) for name, (_, first, _) in self.open.items()})
        return out


# ---------------------------------------------------------------------------------------------
# 3. A state is a plan and the set of open obligations.  A step is refused when the plan
#    forbids the letter or an obligation breaks.  A state is covered when some word empties
#    its ledger.
# ---------------------------------------------------------------------------------------------

def succ(rules, s, a):
    """The rule Step of Section 4.1."""
    P, shape = s
    d = deriv(P, a)
    if d == ZERO:
        return None
    left = set()
    for o in shape:
        o2 = ostep(o, a)
        if o2 == BROKEN:
            return None
        if o2 != MET:
            left.add(o2)
    left.update(rules(a))
    return d, frozenset(left)


def run(rules, s, w):
    for a in w:
        if s is None:
            return None
        s = succ(rules, s, a)
    return s


def in_goal(rules, s, w):
    """The goal of Definition 4.1 read off the languages, with no derivative and no ledger: the
    plan allows w, and every obligation, open at the start or created on the way, is met."""
    P, shape = s
    if not member(pref(P), w):
        return False
    owed = [(o, 0) for o in shape] + [(o, n + 1) for n, a in enumerate(w) for o in rules(a)]
    return all(verdict(o, w[n:])[0] == MET for o, n in owed)


def brute(rules, sigma, s, depth):
    """A word of the goal of at most `depth` letters, found by trying words against the
    definition, or None."""
    P, shape = s

    def search(w):
        owed = [(o, 0) for o in shape] + [(o, n + 1) for n, a in enumerate(w) for o in rules(a)]
        vs = [verdict(o, w[n:])[0] for o, n in owed]
        if BROKEN in vs:
            return None
        if all(v == MET for v in vs):
            return w
        if len(w) < depth:
            for a in sigma:
                if member(pref(P), w + (a,)):
                    found = search(w + (a,))
                    if found is not None:
                        return found
        return None

    return search(())


class TooBig(Exception):
    pass


def reach(rules, sigma, s0, limit=4000):
    """The states that steps lead to from s0."""
    seen, todo = {s0}, [s0]
    while todo:
        s = todo.pop()
        for a in sigma:
            t = succ(rules, s, a)
            if t is not None and t not in seen:
                if len(seen) >= limit:
                    raise TooBig
                seen.add(t)
                todo.append(t)
    return seen


class Cover:
    """Definition 4.3: for every state, the length of a shortest word of its goal, or None when
    the state is not covered."""

    def __init__(self, rules, sigma, mut=None, limit=4000):
        self.rules = NONE if mut == 'no-trigger-cover' else rules
        self.sigma, self.mut, self.limit = tuple(sigma), mut, limit
        self.far = {}

    def done(self, s):
        return not s[1] and (self.mut != 'need-complete' or nullable(s[0]))

    def explore(self, s0):
        new, todo, back, heap, tie = {s0}, [s0], {}, [], count()
        while todo:
            s = todo.pop()
            if self.done(s):
                heapq.heappush(heap, (0, next(tie), s))
            for a in self.sigma:
                t = succ(self.rules, s, a)
                if t is None:
                    continue
                back.setdefault(t, []).append(s)
                if t in self.far:
                    if self.far[t] is not None:
                        heapq.heappush(heap, (self.far[t], next(tie), t))
                elif t not in new:
                    if len(new) >= self.limit:
                        raise TooBig
                    new.add(t)
                    todo.append(t)
        best = {}
        while heap:
            d, _, s = heapq.heappop(heap)
            if s in best:
                continue
            best[s] = d
            for p in back.get(s, ()):
                if p not in best:
                    heapq.heappush(heap, (d + 1, next(tie), p))
        for s in new:
            self.far[s] = best.get(s)

    def distance(self, s):
        if s not in self.far:
            self.explore(s)
        return self.far[s]

    def good(self, s):
        if self.mut == 'separate':
            return all(self.distance((s[0], frozenset([o]))) is not None for o in s[1])
        return self.distance(s) is not None

    def permits(self, rules, s, a):
        """The shield of Definition 4.5."""
        t = succ(rules, s, a)
        if t is None:
            return False
        return True if self.mut == 'plan-blind' else self.good(t)

    def completion(self, s):
        """A shortest word that empties the ledger of a covered state."""
        w = []
        while not self.done(s):
            d = self.distance(s)
            for a in self.sigma:
                t = succ(self.rules, s, a)
                if t is not None and self.distance(t) == d - 1:
                    w.append(a)
                    s = t
                    break
        return tuple(w)


def least_ask(rules, sigma, s, limit=4000):
    """Theorem 4.8: the fewest letters that, granted once each next to the plan, make the
    state covered; None when no grant does.  A letter that the plan allows may still be
    bought, because the plan's own use of it may be needed later."""
    free = anything(sigma)
    heap, tie, seen = [(0, 0, s, ())], count(1), set()
    while heap:
        cost, _, (P, shape), extra = heapq.heappop(heap)
        if (P, shape) in seen:
            continue
        seen.add((P, shape))
        if len(seen) > limit:
            raise TooBig
        if not shape:
            return extra
        for a in sigma:
            t = succ(rules, (P, shape), a)
            if t is not None:
                heapq.heappush(heap, (cost, next(tie), t, extra))
            if t is None or MUTANT != 'greedy-ask':
                u = succ(rules, (free, shape), a)
                if u is not None:
                    heapq.heappush(heap, (cost + 1, next(tie), (P, u[1]), extra + (a,)))
    return None


def differ(rules, sigma, s1, s2, limit=4000):
    """A word that is in the goal of one state and not of the other, or None."""
    seen, todo = {(s1, s2)}, deque([((), s1, s2)])
    while todo:
        w, x, y = todo.popleft()
        if (x is not None and not x[1]) != (y is not None and not y[1]):
            return w
        for a in sigma:
            x2 = succ(rules, x, a) if x is not None else None
            y2 = succ(rules, y, a) if y is not None else None
            if (x2 is not None or y2 is not None) and (x2, y2) not in seen:
                if len(seen) >= limit:
                    raise TooBig
                seen.add((x2, y2))
                todo.append((w + (a,), x2, y2))
    return None


# ---------------------------------------------------------------------------------------------
# 4. Two agents with a plan each act in one world: every open obligation sees every letter.
# ---------------------------------------------------------------------------------------------

def succ2(rules, g, i, a):
    """Agent i performs a.  g is ((P1, P2), (shape1, shape2))."""
    plans, shapes = list(g[0]), [set(), set()]
    plans[i] = deriv(plans[i], a)
    if plans[i] == ZERO:
        return None
    for j in (0, 1):
        for o in g[1][j]:
            o2 = ostep(o, a)
            if o2 == BROKEN:
                return None
            if o2 != MET:
                shapes[j].add(o2)
    shapes[i].update(rules(a))
    return tuple(plans), (frozenset(shapes[0]), frozenset(shapes[1]))


def good2(rules, sigma, g, limit=20000):
    """Whether the two agents together can still empty both ledgers."""
    seen, todo = {g}, [g]
    while todo:
        x = todo.pop()
        if not x[1][0] and not x[1][1]:
            return True
        for i in (0, 1):
            for a in sigma:
                y = succ2(rules, x, i, a)
                if y is not None and y not in seen:
                    if len(seen) >= limit:
                        raise TooBig
                    seen.add(y)
                    todo.append(y)
    return False


def watch(rules, s, full=True):
    """The letters watched by the obligations that the state has or, by its plan, can create."""
    out = set()
    for _, W in s[1]:
        out |= W
    if full:
        for a in letters(s[0]):
            for _, W in rules(a):
                out |= W
    return out


def separated(rules, s1, s2):
    """Definition 5.1: neither agent can perform a letter that the other's obligations watch."""
    full = MUTANT != 'half-frame'
    return not letters(s1[0]) & watch(rules, s2, full) and not letters(s2[0]) & watch(rules, s1, full)


# ---------------------------------------------------------------------------------------------
# 5. Code is a regular expression without shuffle, read as a program: at a choice and at the
#    end of each round of a loop the world decides, not the agent.
# ---------------------------------------------------------------------------------------------

class Refused(Exception):
    def __init__(self, word, letter):
        super().__init__(word, letter)
        self.word, self.letter = word, letter


def post(rules, starts, c):
    """Figure 2 as a function.  `starts` maps states to the words that led to them.  The result
    maps every state in which a run of c from a start can end to such a word.  Raises Refused
    when some run of c reaches a letter that is refused."""
    k = c[0]
    if k == '1':
        return dict(starts)
    if k == '0':
        return {}
    out = {}
    if k == 'sym':
        choice = sorted(c[1])
        for s, w in starts.items():
            for a in choice[:1] if MUTANT == 'alt-first' else choice:
                t = succ(rules, s, a)
                if t is None:
                    raise Refused(w, a)
                out.setdefault(t, w + (a,))
        return out
    if k == 'seq':
        return post(rules, post(rules, starts, c[1]), c[2])
    if k == 'alt':
        for q in c[1][:1] if MUTANT == 'alt-first' else c[1]:
            for t, w in post(rules, starts, q).items():
                out.setdefault(t, w)
        return out
    if k == 'star':
        out, frontier = dict(starts), dict(starts)
        while frontier:
            step = post(rules, frontier, c[1])
            frontier = {t: w for t, w in step.items() if t not in out}
            out.update(frontier)
            if MUTANT == 'star-once':
                break
        return out
    raise ValueError('code has no shuffle')


def words(c, n):
    """The words of c of at most n letters."""
    out, todo = [], [((), c)]
    while todo:
        w, r = todo.pop()
        if nullable(r):
            out.append(w)
        if len(w) < n:
            for a in sorted(letters(r)):
                d = deriv(r, a)
                if d != ZERO:
                    todo.append((w + (a,), d))
    return out


# ---------------------------------------------------------------------------------------------
# 6. Random systems over four letters.
# ---------------------------------------------------------------------------------------------

SIGMA = ('a', 'b', 'c', 'd')


class Gen:
    def __init__(self, rng, sigma=SIGMA):
        self.rng, self.sigma = rng, tuple(sigma)

    def flip(self, p):
        return self.rng.random() < p

    def below(self, n):
        return int(self.rng.random() * n)

    def pick(self, xs):
        return xs[self.below(len(xs))]

    def some(self, xs, lo, hi):
        pool, out = list(xs), []
        for _ in range(min(lo + self.below(hi - lo + 1), len(pool))):
            out.append(pool.pop(self.below(len(pool))))
        return tuple(sorted(out))

    def regex(self, ls, depth, shuffle=False):
        x = self.rng.random()
        if depth == 0 or x < 0.34:
            return sym(self.pick(ls))
        r, s = self.regex(ls, depth - 1, shuffle), self.regex(ls, depth - 1, shuffle)
        if x < 0.60:
            return seq(r, s)
        if x < 0.78:
            return alt(r, s)
        if x < 0.90:
            return star(r)
        return par(r, s) if shuffle else seq(r, s)

    def obligation(self, over=None):
        W = self.some(over or self.sigma, 1, 3)
        while True:
            r = self.regex(self.some(W, 1, len(W)), 2)
            if r != ZERO and not nullable(r):
                return r, frozenset(W)

    def rules(self, p=0.45):
        while True:
            table = {a: [self.obligation() for _ in range(1 + self.flip(0.2))]
                     for a in self.sigma if self.flip(p)}
            if table:
                return Rules(table)

    def plan(self, over=None):
        """A part that may be used without limit, next to a part that is used up."""
        ls = over or self.sigma
        if self.flip(0.3):
            return anything(ls)
        return par(anything(self.some(ls, 0, len(ls) - 1)), self.regex(ls, 3, shuffle=True))

    def owed(self, most=2):
        return [self.obligation() for _ in range(self.below(most + 1))]

    def walk(self, rules, s, most):
        """A state that some steps lead to from s, and the steps."""
        w = ()
        for _ in range(self.below(most + 1)):
            nexts = [(a, t) for a in self.sigma for t in [succ(rules, s, a)] if t is not None]
            if not nexts:
                break
            a, s = self.pick(nexts)
            w += (a,)
        return s, w


# ---------------------------------------------------------------------------------------------
# 7. The tests.  Each trial draws one random system, checks one claim on it, and counts.
# ---------------------------------------------------------------------------------------------

def trial_ledger(g, K):
    """Theorem 3.4: the ledger gives every obligation the verdict of the definition, at the
    same letter.  Proposition 3.6: a successor that starts from the report reaches the verdicts
    that the first ledger reaches."""
    rules, owed = g.rules(), g.owed()
    w = tuple(g.pick(g.sigma) for _ in range(1 + g.below(8)))
    cut, L, handed = g.below(len(w) + 1), Ledger(rules, owed), None
    for n, a in enumerate(w):
        if n == cut:
            handed = L.report()
        L.act(a)
    if cut == len(w):
        handed = L.report()
    got = L.verdicts()
    assert len(got) == len(owed) + sum(len(rules(a)) for a in w), 'an obligation was lost'
    for (start, _), (first, v, t) in got.items():
        v0, t0 = verdict(first, w[start:])
        assert (v, t) == (v0, t0 + start if t0 else None), 'the ledger disagrees with the definition'
        K[v] += 1
    S = Ledger(rules, [left for _, _, left in handed])
    for a in w[cut:]:
        S.act(a)
    for (start, i), (_, v, t) in S.verdicts().items():
        name = handed[i][0] if start == 0 else (start + cut, i)
        assert got[name][1:] == (v, t + cut if t else None), 'the successor disagrees'
    K['histories'] += 1
    K['obligations'] += len(got)
    K['handed over'] += len(handed)


def trial_cover(g, K):
    """Definition 4.3 against the languages: the shortest completion is in the goal, and on
    systems with few states a search by the definition agrees in both directions."""
    rules = g.rules()
    s, _ = g.walk(rules, (g.plan(), frozenset(g.owed())), 2)
    cov = Cover(rules, g.sigma)
    try:
        far, size = cov.distance(s), len(reach(rules, g.sigma, s))
    except TooBig:
        K['too big'] += 1
        return
    K['states'] += 1
    K['size ' + ('1' if size == 1 else '2-5' if size <= 5 else '6-20' if size <= 20 else 'over 20')] += 1
    K['largest'] = max(K['largest'], size)
    if far is not None:
        K['longest'] = max(K['longest'], far)
        w = cov.completion(s)
        assert len(w) == far and in_goal(rules, s, w), 'the completion is not in the goal'
        assert all(not in_goal(rules, s, w[:n]) for n in range(far)), 'a shorter word is in the goal'
        K['covered'] += 1
    if size <= 6:
        found = brute(rules, g.sigma, s, size)     # a shortest completion repeats no state
        assert (found is not None) == (far is not None), 'coverage disagrees with the definition'
        if far:
            assert brute(rules, g.sigma, s, far - 1) is None, 'a shorter word is in the goal'
        if found is not None:
            t = s
            for a in found:
                assert cov.permits(rules, t, a), 'the shield refuses the beginning of a goal word'
                t = succ(rules, t, a)
        K['small'] += 1
    if far is not None:
        # Lemma 4.4: fewer obligations or more authority keep a state covered
        for o in s[1]:
            assert cov.good((s[0], s[1] - {o})), 'dropping an obligation uncovers the state'
        more = par(s[0], g.regex(g.sigma, 2, shuffle=True))
        assert Cover(rules, g.sigma).good((more, s[1])), 'more authority uncovers the state'


def covered_start(g, tries=40):
    for _ in range(tries):
        rules, s = g.rules(), (g.plan(), frozenset(g.owed()))
        ref = Cover(rules, g.sigma)
        try:
            if ref.good(s):
                return rules, s, ref
        except TooBig:
            pass
    raise AssertionError('no covered start')


def trial_shield(g, K):
    """Theorem 4.6 on one shielded run: every state is covered, nothing breaks, the run is the
    beginning of a word of the goal, some letter is allowed unless the ledger is empty, and a
    letter is refused only when no word of the goal continues through it."""
    rules, s0, ref = covered_start(g)
    cov = Cover(rules, g.sigma, MUTANT if MUTANT in SHIELD_MUTANTS else None)
    L, s, h = Ledger(rules, list(s0[1])), s0, ()
    try:
        for _ in range(10):
            assert ref.good(s), 'the run reached a state that is not covered'
            assert in_goal(rules, s0, h + ref.completion(s)), 'the run is not the beginning of a goal word'
            allowed = [a for a in g.sigma if cov.permits(rules, s, a)]
            assert allowed or not s[1], 'the shield allows nothing and the ledger is not empty'
            for a in g.sigma:
                t = succ(rules, s, a)
                K['allowed' if a in allowed else 'refused: plan or break' if t is None
                  else 'refused: not covered'] += 1
                if a not in allowed and t is not None:
                    assert not ref.good(t), 'the shield refused a letter that leads to the goal'
                    if K['refused: not covered'] % 10 == 0:
                        assert brute(rules, g.sigma, t, 4) is None
            if not allowed or g.flip(0.12):
                break
            a = g.pick(allowed)
            L.act(a)
            s, h = succ(rules, s, a), h + (a,)
            assert L.shape() == s[1] and all(v != BROKEN for _, _, v, _ in L.closed.values())
        K['runs'] += 1
        K['steps'] += len(h)
        K['stops'] += 1
        K['stops with a report'] += bool(s[1])
        K['left to do'] += ref.distance(s)
        handed = (s[0], frozenset(left for _, _, left in L.report()))
        assert run(rules, handed, ref.completion(s))[1] == frozenset(), 'the report cannot be finished'
    except TooBig:
        K['too big'] += 1


def trial_ask(g, K):
    """Theorem 4.8: the least request makes the state covered, no smaller one does, and there
    is none exactly when the obligations cannot be met under any plan."""
    rules = g.rules()
    s = (g.plan(), frozenset(g.owed(3)))
    try:
        E = least_ask(rules, g.sigma, s)
        if E is None:
            assert not Cover(rules, g.sigma).good((anything(g.sigma), s[1])), 'a grant would do'
            K['no request helps'] += 1
            return
        assert Cover(rules, g.sigma).good((par(s[0], *[sym(a) for a in E]), s[1])), 'the request does not cover'
        if E:
            for F in combinations_with_replacement(g.sigma, len(E) - 1):
                assert not Cover(rules, g.sigma).good((par(s[0], *[sym(a) for a in F]), s[1])), \
                    'a smaller request covers'
        K['requests'] += 1
        K['request of %d' % min(len(E), 3)] += 1
    except TooBig:
        K['too big'] += 1


def trial_frame(g, K):
    """Theorem 5.2: for separated agents, the two are covered together exactly when each is
    covered alone, and the shield of the pair allows a letter exactly when the agent's own
    shield does."""
    disjoint = g.flip(0.7)
    A = (g.sigma[:2], g.sigma[2:]) if disjoint else (g.some(g.sigma, 2, 3), g.some(g.sigma, 2, 3))
    table = {}
    for i in (0, 1):
        for a in A[i]:
            if g.flip(0.35):
                table.setdefault(a, []).append(g.obligation(A[i] if g.flip(0.85) else None))
    rules = Rules(table)
    s = [(g.plan(A[i]), frozenset(g.obligation(A[i] if g.flip(0.85) else None)
                                  for _ in range(g.below(3)))) for i in (0, 1)]
    start = ((s[0][0], s[1][0]), (s[0][1], s[1][1]))
    cov = Cover(rules, g.sigma)
    try:
        alone = [cov.good(s[0]), cov.good(s[1])]
        same = good2(rules, g.sigma, start) == all(alone)
        if all(alone):
            for i in (0, 1):
                for a in g.sigma:
                    t = succ2(rules, start, i, a)
                    same &= cov.permits(rules, s[i], a) == (t is not None and good2(rules, g.sigma, t))
    except TooBig:
        K['too big'] += 1
        return
    K['alone, not together'] += all(alone) and not good2(rules, g.sigma, start)
    K['together, not alone'] += not all(alone) and good2(rules, g.sigma, start)
    if separated(rules, s[0], s[1]):
        assert same, 'separated agents interfere'
        K['separated'] += 1
        K['separated and covered'] += all(alone)
    else:
        K['not separated'] += 1
        K['not separated and different'] += not same


def trial_code(g, K):
    """Theorems 6.1 and 6.2: the check passes exactly when every run of the code is allowed, the states
    it reports are the states in which runs end, and when all of them are covered the shield
    stops no run and every state on the way is covered."""
    rules, s, cov = covered_start(g)
    c = g.regex(g.sigma, 3)
    try:
        try:
            ends = post(rules, {s: ()}, c)
        except Refused as e:
            t = run(rules, s, e.word)
            assert member(pref(c), e.word + (e.letter,)), 'the refused run is not a run of the code'
            assert t is not None and succ(rules, t, e.letter) is None, 'the refusal is not real'
            K['code refused'] += 1
            return
        ws = words(c, 5)
        for w in ws:
            t = run(rules, s, w)
            assert t is not None and t in ends, 'the check passed and a run is refused or ends elsewhere'
        for t, w in ends.items():
            assert member(c, w) and run(rules, s, w) == t, 'a reported end is not an end'
        K['code passed'] += 1
        K['code closed'] += all(not t[1] for t in ends)
        if all(cov.good(t) for t in ends):
            K['code safe'] += 1
            for w in ws:
                for n in range(len(w) + 1):
                    assert cov.good(run(rules, s, w[:n])), 'the code stops in a state that is not covered'
    except TooBig:
        K['too big'] += 1


def trial_equal(g, K):
    """Proposition 4.2: two states are told apart by some future exactly when their goals
    differ, and states with different ledgers can have the same goal."""
    rules, s0 = g.rules(), (g.plan(), frozenset(g.owed()))
    (s1, h1), (s2, _) = g.walk(rules, s0, 4), g.walk(rules, s0, 4)
    for _ in range(4):
        v = tuple(g.pick(g.sigma) for _ in range(g.below(5)))
        assert in_goal(rules, s1, v) == in_goal(rules, s0, h1 + v), 'the goal is not the quotient'
    try:
        w = differ(rules, g.sigma, s1, s2)
    except TooBig:
        K['too big'] += 1
        return
    if w is None:
        for _ in range(8):
            v = tuple(g.pick(g.sigma) for _ in range(g.below(6)))
            assert in_goal(rules, s1, v) == in_goal(rules, s2, v), 'equal goals differ on a word'
        K['same goal'] += 1
        K['same goal, other state'] += s1 != s2
    else:
        assert in_goal(rules, s1, w) != in_goal(rules, s2, w), 'the word does not tell the states apart'
        K['told apart'] += 1


TRIALS = [(trial_ledger, 4000), (trial_cover, 2500), (trial_shield, 1200), (trial_ask, 1200),
          (trial_frame, 2500), (trial_code, 2500), (trial_equal, 1500)]
CATCHES = {'no-watch': trial_ledger, 'self-trigger': trial_ledger, 'never-break': trial_ledger, 'no-retire': trial_ledger,
           'stale-report': trial_ledger, 'plan-blind': trial_shield, 'separate': trial_shield,
           'no-trigger-cover': trial_shield, 'need-complete': trial_shield,
           'greedy-ask': trial_ask, 'half-frame': trial_frame, 'star-once': trial_code,
           'alt-first': trial_code}


# ---------------------------------------------------------------------------------------------
# The examples of the paper.
# ---------------------------------------------------------------------------------------------

def chain(*ls):
    """`a, later b, later c`: the letters in this order; between them the other letters of the
    chain are ignored, so the obligation is never broken by its own letters."""
    return ob(seq(*[seq(star(sym(*(set(ls) - {a}))), sym(a)) for a in ls]))


def chain_names(*ls):
    """What is left of a chain after its first letters, by name."""
    o, out = chain(*ls), {}
    for i, a in enumerate(ls):
        out[o] = ls[i:]
        o = ostep(o, a)
    return out


CHAINS = chain_names('push', 'pull', 'look')


def describe(o, tex=True):
    """An obligation in the notation of the paper."""
    r, W = o
    name = (lambda a: '\\nm{%s}' % a.partition(':')[0]) if tex else (lambda a: a.partition(':')[0])
    if o in CHAINS:
        return (' \\later ' if tex else ' > ').join(name(a) for a in CHAINS[o])
    if r[0] == 'sym' and len(r[1]) == 1:
        rest = ', '.join(name(b) for b in sorted(W - r[1]))
        before = ' \\bef ' if tex else ' before '
        return name(next(iter(r[1]))) + (before + rest if rest else '')
    return show(r, 0, name)


def described(shape, tex=True):
    return sorted(describe(o, tex) for o in shape)


EX_SIGMA = ('edit', 'tex', 'commit', 'push', 'pull', 'look')
EX_RULES = Rules({'edit': [ob(sym('tex'), 'commit')], 'commit': [chain('push', 'pull', 'look')]})
EX_PLAN = par(anything(('edit', 'tex', 'commit', 'pull', 'look')), sym('push'))
EX_WALK = ('edit', 'commit', 'tex', 'commit', 'push', 'pull', 'look', 'edit', 'tex', 'commit')


def walk_example():
    """Table 1: the letters of EX_WALK offered to the shield one after the other."""
    cov, s, rows = Cover(EX_RULES, EX_SIGMA), (EX_PLAN, frozenset()), []
    for n, a in enumerate(EX_WALK, 1):
        t = succ(EX_RULES, s, a)
        if t is None:
            broken = [o for o in s[1] if ostep(o, a) == BROKEN]
            why = 'breaks ' + described(broken, False)[0] if broken else 'the plan forbids it'
            rows.append((n, a, 'refused', why, s))
        elif not cov.good(t):
            ask = least_ask(EX_RULES, EX_SIGMA, t)
            rows.append((n, a, 'refused', 'not covered; it would take ' + ', '.join(ask), s))
        else:
            s = t
            rows.append((n, a, 'allowed', '', s))
    return cov, rows


SHIP_SIGMA = ('edit', 'code', 'tex', 'run', 'commit', 'push', 'pull', 'look')
SHIP_RULES = Rules({'edit': [ob(sym('tex'), 'commit')], 'code': [ob(sym('run'), 'commit')],
                    'commit': [chain('push', 'pull', 'look')]})


def ship_code(fixed=False):
    """The script that shipped the papers of the session, as code: it compiles, runs the
    artifact, commits, pulls and pushes, and it exits at the first step that fails.  A step
    that fails performs no letter.  In the corrected script the pull cannot fail."""
    tail = seq(sym('pull'), sym('push'))
    return opt(seq(sym('tex'), opt(seq(sym('run'), opt(seq(sym('commit'), tail if fixed else opt(tail)))))))


def ship_exits(fixed):
    start = (anything(SHIP_SIGMA), frozenset(SHIP_RULES('edit') + SHIP_RULES('code')))
    ends = post(SHIP_RULES, {start: ()}, ship_code(fixed))
    return sorted(((w, t[1]) for t, w in ends.items()), key=lambda x: len(x[0]))


def residues(p):
    """An obligation that is met by a positive multiple of p letters `a` followed by `z`."""
    return ob(seq(*[sym('a')] * p, star(seq(*[sym('a')] * p)), sym('z')))


def size_of(r):
    """The number of letters written in an expression."""
    if r[0] in ('0', '1'):
        return 0
    if r[0] == 'sym':
        return len(r[1])
    return sum(size_of(q) for q in (r[1] if r[0] == 'alt' else r[1:]))


def rename(r, f):
    k = r[0]
    if k in ('0', '1'):
        return r
    if k == 'sym':
        return sym(*[f(a) for a in r[1]])
    if k == 'alt':
        return alt(*[rename(q, f) for q in r[1]])
    if k == 'star':
        return star(rename(r[1], f))
    return (seq2 if k == 'seq' else par2)(rename(r[1], f), rename(r[2], f))


def copies(k):
    """k copies of the example side by side, each with its own letters."""
    table, plans, sigma = {}, [], []
    for i in range(k):
        f = lambda a, i=i: a + str(i)
        for a, os in EX_RULES.table.items():
            table[f(a)] = [(rename(r, f), frozenset(f(b) for b in W)) for r, W in os]
        plans.append(rename(EX_PLAN, f))
        sigma += [f(a) for a in EX_SIGMA]
    return Rules(table), plans, tuple(sigma)


# ---------------------------------------------------------------------------------------------
# The session of Section 8.  session.txt is written by trace.py from the record of the session.
# ---------------------------------------------------------------------------------------------

class SessionRules:
    """The standing instructions of the project as rules, one family for every paper p."""
    registry = False

    def __call__(self, a):
        kind, _, p = a.partition(':')
        if kind == 'edit':
            return (ob(sym('tex:' + p), 'commit:' + p),)
        if kind == 'code':
            return (ob(sym('run:' + p), 'commit:' + p),)
        if kind == 'commit':
            return (chain('push', 'pull', 'look'),) if self.registry and p != '-' else (ob(sym('push')),)
        if kind == 'stash':
            return (ob(sym('pop')),)
        return ()


def replay(path):
    """Runs the ledger over the trace.  Returns the ledger and, for every mark, its kind, the
    number of letters before it, and the report at that point."""
    rules = SessionRules()
    L, marks, letters_ = Ledger(rules), [], Counter()
    for line in open(path):
        kind, _, p = line.strip().partition(' ')
        if kind in ('end', 'compact'):
            marks.append((kind, L.now, L.report()))
        elif kind == 'registry':
            rules.registry = True
        elif kind:
            L.act(kind + (':' + p if p else ''))
            letters_[kind] += 1
    return L, marks, letters_


def number_of(paper):
    """The number of a paper in the registry of the repository."""
    here = os.path.dirname(os.path.abspath(__file__))
    for line in open(os.path.join(here, '..', '..', 'REGISTRY')):
        n, name = line.split()
        if name == paper:
            return int(n)
    raise KeyError(paper)


def main(outdir):
    global MUTANT
    here = os.path.dirname(os.path.abspath(__file__))
    lines, nums, tables = [], {}, {}
    K = Counter()
    rng = random.Random(2026)
    for trial, n in TRIALS:
        g = Gen(rng)
        for _ in range(n):
            trial(g, K)

    # Section 7: the random systems
    assert K['met'] + K['broken'] + K[PENDING] == K['obligations']
    lines.append(f"ledger: {K['histories']} histories, {K['obligations']} obligations, of which {K['met']} met, "
                 f"{K['broken']} broken and {K[PENDING]} open; every verdict and its time agree with the "
                 f"definition; {K['handed over']} open obligations handed to a second ledger, which agrees")
    lines.append(f"coverage: {K['states']} states, {K['covered']} covered; sizes 1: {K['size 1']}, 2-5: "
                 f"{K['size 2-5']}, 6-20: {K['size 6-20']}, over 20: {K['size over 20']}, largest {K['largest']}; "
                 f"longest shortest completion {K['longest']}; searched by the definition: {K['small']}")
    refused = K['refused: plan or break'] + K['refused: not covered']
    lines.append(f"shield: {K['runs']} runs, {K['steps']} steps, {K['allowed'] + refused} letters offered, "
                 f"{K['allowed']} allowed, {K['refused: plan or break']} refused by the plan or a break, "
                 f"{K['refused: not covered']} refused for coverage; {K['stops with a report']} of "
                 f"{K['stops']} stops leave a report, {K['left to do']} letters left in all")
    lines.append(f"requests: {K['requests']} states with a least request (of size 0: {K['request of 0']}, "
                 f"1: {K['request of 1']}, 2: {K['request of 2']}, 3 or more: {K['request of 3']}), "
                 f"{K['no request helps']} that no request helps")
    lines.append(f"frame: {K['separated']} separated pairs ({K['separated and covered']} covered), all agree; "
                 f"{K['not separated']} other pairs, of which {K['not separated and different']} differ "
                 f"({K['alone, not together']} covered alone and not together, {K['together, not alone']} the reverse)")
    lines.append(f"code: {K['code passed'] + K['code refused']} pieces, {K['code refused']} refused, "
                 f"{K['code passed']} passed, of which {K['code safe']} end only in covered states and "
                 f"{K['code closed']} only with an empty ledger")
    lines.append(f"goals: {K['same goal'] + K['told apart']} pairs of states, {K['told apart']} told apart by a "
                 f"word, {K['same goal']} with one goal, of which {K['same goal, other state']} are different states")
    assert K['too big'] == 0, K['too big']
    for name in ('ledger-agrees', 'cover-agrees', 'shield-holds', 'ask-least', 'frame-holds', 'code-holds'):
        claim(name, True)                       # the trials above assert these and have passed
    claim('different-ledgers', K['same goal, other state'] > 0)
    ab = ('a', 'b')
    first, second = (sym('a'), frozenset([ob(sym('a'), 'b')])), (sym('b'), frozenset([ob(sym('b'), 'a')]))
    owes, pays = (sym('b'), frozenset([ob(sym('a'))])), (sym('a'), frozenset())
    claim('not-separated-differ', K['alone, not together'] > 0 and K['together, not alone'] > 0
          and Cover(NONE, ab).good(first) and Cover(NONE, ab).good(second)
          and not good2(NONE, ab, ((first[0], second[0]), (first[1], second[1])))
          and not Cover(NONE, ab).good(owes) and good2(NONE, ab, ((owes[0], pays[0]), (owes[1], pays[1]))))
    kept = (alt(sym('a'), seq(sym('b'), sym('b'))), frozenset([ob(seq(sym('a'), sym('b'), sym('b')))]))
    MUTANT = 'greedy-ask'
    greedy = least_ask(NONE, ab, kept)
    MUTANT = None
    claim('ask-example', least_ask(NONE, ab, kept) == ('a',) and len(greedy) == 2)
    total = sum(n for _, n in TRIALS)
    for trial, n in TRIALS:
        nums['Trials' + trial.__name__.partition('_')[2].capitalize()] = f'{n:,}'
    nums['Seed'] = '2026'
    nums['Lines'] = f"{round(len(open(os.path.join(here, 'owed.py')).readlines()), -2):,}"
    nums.update(Trials=f'{total:,}', Obligations=f"{K['obligations']:,}",
                Met=f"{K['met']:,}", Broken=f"{K['broken']:,}", Open=f"{K[PENDING]:,}",
                Handed=f"{K['handed over']:,}", States=f"{K['states']:,}", Covered=f"{K['covered']:,}",
                Small=f"{K['small']:,}", Largest=str(K['largest']), Longest=str(K['longest']),
                Runs=f"{K['runs']:,}", Offered=f"{K['allowed'] + refused:,}",
                Allowed=f"{K['allowed']:,}", RefusedPlan=f"{K['refused: plan or break']:,}",
                RefusedCover=f"{K['refused: not covered']:,}", StopsReport=str(K['stops with a report']),
                Requests=str(K['requests']), RequestsNone=str(K['request of 0']),
                RequestsSome=str(K['requests'] - K['request of 0']), NoRequest=str(K['no request helps']),
                Separated=f"{K['separated']:,}", NotSeparated=f"{K['not separated']:,}",
                Differ=str(K['not separated and different']), PiecesRefused=f"{K['code refused']:,}",
                PiecesPassed=f"{K['code passed']:,}", PiecesSafe=str(K['code safe']),
                PiecesClosed=str(K['code closed']), ToldApart=str(K['told apart']), SameGoal=f"{K['same goal']:,}",
                SameGoalOther=str(K['same goal, other state']))

    # every deliberate mistake is noticed
    tries = {}
    for name in MUTANTS:
        MUTANT, g, J = name, Gen(random.Random(2026)), Counter()
        for i in range(1, 20001):
            try:
                CATCHES[name](g, J)
            except AssertionError:
                tries[name] = i
                break
        MUTANT = None
    claim('all-noticed', set(tries) == set(MUTANTS))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed, after ' +
                 ', '.join(f'{m} {n}' for m, n in tries.items()) + ' trials')
    nums.update(Mutants=str(len(MUTANTS)), Slowest=f'{max(tries.values()):,}')
    for m, n in tries.items():
        nums['Try' + ''.join(part.capitalize() for part in m.split('-'))] = f'{n:,}'

    # Section 2: the walk of Table 1
    cov, rows = walk_example()
    out = []
    for n, a, verdict_, why, s in rows:
        left = ', '.join(described(s[1], False)) or '-'
        lines.append(f'walk {n}: {a} {verdict_}{" (" + why + ")" if why else ""}; open: {left}; '
                     f'letters left: {cov.distance(s)}')
        opened = ',\\ '.join(described(s[1])) or '\\text{--}'
        note = {'': ''}.get(why, why)
        note = note.replace('breaks tex before commit', 'it would break $\\nm{tex} \\bef \\nm{commit}$')
        note = note.replace('not covered; it would take push', 'the result is not covered; least request: $\\nm{push}$')
        out.append(f'{n} & $\\nm{{{a}}}$ & {verdict_}{": " + note if note else ""} & ${opened}$ & {cov.distance(s)} \\\\')
    tables['walk'] = out
    assert [r[2] for r in rows] == ['allowed', 'refused', 'allowed', 'allowed', 'allowed', 'allowed', 'allowed',
                                    'allowed', 'allowed', 'refused']
    claim('walk-refusals', rows[1][3] == 'breaks tex before commit' and rows[9][3] == 'not covered; it would take push'
          and sum(r[2] == 'refused' for r in rows) == 2)
    assert described(rows[3][4][1], False) == ['push > pull > look'] and cov.distance(rows[3][4]) == 3
    assert described(rows[5][4][1], False) == ['look'] and cov.distance(rows[5][4]) == 1
    assert not rows[6][4][1]
    start = (EX_PLAN, frozenset())
    states = reach(EX_RULES, EX_SIGMA, start)
    size, good = len(states), sum(cov.good(t) for t in states)
    lines.append(f'the example has {size} states that steps lead to from its start, {good} of them covered')
    nums.update(ExampleStates=str(size), ExampleCovered=str(good))

    # Section 5: copies of the example are separated, and the joint system multiplies
    sizes = []
    for k in (1, 2, 3):
        rules, plans, sigma = copies(k)
        states = [(P, frozenset()) for P in plans]
        assert all(separated(rules, states[i], states[j]) for i in range(k) for j in range(i))
        joint = len(reach(rules, sigma, (par(*plans), frozenset()), limit=200000))
        sizes.append(joint)
        lines.append(f'{k} copies of the example: {joint} states together, {k * size} apart')
    claim('copies-multiply', sizes[0] == size and sizes[1] == size ** 2 and sizes[2] == size ** 3)
    nums.update(CopiesTwo=f'{sizes[1]:,}', CopiesThree=f'{sizes[2]:,}', ApartThree=str(3 * size))

    # Section 6: the script that ships a paper
    out = []
    for fixed in (False, True):
        exits = ship_exits(fixed)
        for w, shape in exits:
            lines.append(f"ship{' (corrected)' if fixed else ''}: after {' '.join(w) or 'nothing'}: open "
                         f"{', '.join(described(shape, False)) or '-'}")
        if not fixed:
            for w, shape in exits:
                did = ',\\ '.join('\\nm{%s}' % a for a in w) or '\\text{nothing}'
                out.append(f'${did}$ & ${",\\ ".join(described(shape)) or "\\text{--}"}$ \\\\')
            claim('ship-one-exit', len(exits) == 5 and [w for w, shape in exits if any(
                describe(o, False).startswith('push') for o in shape)] == [('tex', 'run', 'commit')])
        else:
            claim('ship-corrected', len(exits) == 4 and not any(
                describe(o, False).startswith('push') for _, shape in exits for o in shape))
    tables['exits'] = out
    try:
        post(SHIP_RULES, {(anything(SHIP_SIGMA), frozenset(SHIP_RULES('code'))): ()},
             seq(sym('tex'), sym('commit'), sym('run'), sym('pull'), sym('push')))
        raise SystemExit('a script that commits before it runs the artifact passed the check')
    except Refused as e:
        claim('bad-script-refused', (e.word, e.letter) == (('tex',), 'commit'))
        lines.append('a script that commits before it runs the artifact is refused at ' + e.letter)
    nums.update(ShipExits='five', ShipExitsFixed='four')

    # Section 4: obligations whose shortest joint completion is long
    out, primes = [], (2, 3, 5, 7)
    for k in range(1, len(primes) + 1):
        obs = [residues(p) for p in primes[:k]]
        s = (anything(('a', 'z')), frozenset(obs))
        cov = Cover(NONE, ('a', 'z'))
        letters_, far, n = sum(size_of(o[0]) for o in obs), cov.distance(s), len(reach(NONE, ('a', 'z'), s))
        prod = 1
        for p in primes[:k]:
            prod *= p
        assert far == prod + 1
        lines.append(f'{k} obligations of {letters_} letters: shortest completion {far}, {n} states')
        out.append(f'{k} & {letters_} & {far} & {n} \\\\')
    tables['primes'] = out
    claim('primes-product', True)               # asserted for every row above
    nums.update(PrimesLetters=str(letters_), PrimesLength=str(far))

    # Section 8: the session
    L, marks, letters_ = replay(os.path.join(here, 'session.txt'))
    verdicts = Counter(v for _, _, v, _ in L.closed.values())
    by_rule = Counter(origin.partition(':')[0] for origin, _, _, _ in L.closed.values())
    claim('session-all-met', not L.open and set(verdicts) == {MET})
    waits = sorted(t - name[0] for name, (origin, _, _, t) in L.closed.items())
    chain_waits = sorted(t - name[0] for name, (origin, first, _, t) in L.closed.items() if first in CHAINS)
    ends = [m for m in marks if m[0] == 'end']
    compacts = [m for m in marks if m[0] == 'compact']
    stops = [m for m in marks if m[0] in ('end', 'compact')]
    with_report = [m for m in stops if m[2]]
    lines.append(f"session: {L.now} letters ({', '.join(f'{k} {letters_[k]}' for k in sorted(letters_))}), "
                 f"{len(ends)} ends of a turn, {len(compacts)} summaries")
    lines.append(f"session: {len(L.closed)} obligations ({', '.join(f'{k} {by_rule[k]}' for k in sorted(by_rule))}), "
                 f"all met, none broken, none open at the end; half are met within {waits[len(waits) // 2]} "
                 f'letters, the slowest after {waits[-1]}; of the {len(chain_waits)} that end with a look at the '
                 f'registry, half within {chain_waits[len(chain_waits) // 2]} and the slowest after {chain_waits[-1]}')
    out = []
    for kind, now, report in with_report:
        which = 1 + [m for m in stops if m[0] == kind].index((kind, now, report))
        what = '; '.join(f'{describe(left, False)} (from the commit of paper {number_of(origin.partition(":")[2])})'
                         for _, origin, left in report)
        lines.append(f"session: {'end of turn' if kind == 'end' else 'summary'} {which}, after {now} letters, "
                     f'leaves {len(report)} open: {what}')
        cells = ',\\ '.join(f'{describe(left)}\\ \\text{{(paper {number_of(origin.partition(":")[2])})}}'
                            for _, origin, left in report)
        out.append(f"{'end of turn' if kind == 'end' else 'summary'} {which} & {now} & ${cells}$ \\\\")
    tables['stops'] = out
    claim('session-two-stops', [m[0] for m in with_report] == ['end', 'compact']
          and [len(m[2]) for m in with_report] == [1, 3])
    claim('no-end-later', max(m[1] for m in ends) <= min(m[1] for m in compacts))
    trace = [line.strip() for line in open(os.path.join(here, 'session.txt'))]
    # the runs of the script that ships a paper: tex p, run p, commit p; all but one go on to pull
    shipped = [i for i in range(2, len(trace) - 1) if trace[i].startswith('commit ')
               and trace[i - 2:i] == ['tex ' + trace[i][7:], 'run ' + trace[i][7:]]]
    cut_short = [i for i in shipped if trace[i + 1] != 'pull']
    claim('session-tenth', [trace[i] for i in cut_short] == ['commit a-number-is-a-claim']
          and trace[cut_short[0] + 1:cut_short[0] + 5] == ['stash', 'pull', 'push', 'pop'])
    nums['SessionShipped'] = str(len(shipped))
    waits_after = [max(L.closed[name][3] for name, _, _ in report) - now for _, now, report in with_report]
    spelled = ['zero', 'one', 'two', 'three', 'four', 'five', 'six']
    nums.update(SessionLetters=str(L.now), SessionObligations=str(len(L.closed)),
                SessionEnds=str(len(ends)),
                SessionSummaries=spelled[len(compacts)], SessionStops=str(len(stops)),
                SessionWithReport=spelled[len(with_report)],
                SessionLeft=spelled[sum(len(m[2]) for m in with_report)],
                SessionHalf=str(waits[len(waits) // 2]), SessionSlowest=str(waits[-1]),
                SessionWaitEnd=spelled[waits_after[0]], SessionWaitSummary=str(waits_after[1]))
    assert letters_['stash'] == letters_['pop']
    for k in sorted(letters_):
        if k != 'pop':
            nums['Session' + k.capitalize() + 's'] = spelled[letters_[k]] if k == 'stash' else str(letters_[k])

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
        f.write('% written by owed.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by owed.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
