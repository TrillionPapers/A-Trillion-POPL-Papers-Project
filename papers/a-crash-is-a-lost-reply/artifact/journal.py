#!/usr/bin/env python3
"""Tests the claims of "A Crash Is a Lost Reply" on an implementation of its calculus.

The file has five parts.

1. Programs, and the type checker with its two labels, durable and volatile.
2. The machine: an attempt runs a program from its start against a journal, and the process may
   die at any point.  A run is a sequence of attempts.
3. The reference semantics: no journal and no crashes, but a `once` may lose its reply.  Also
   what it means that a world trace is the trace of a reference execution.
4. Random programs, random crashes, random deployments.
5. The tests.  `python3 journal.py out` writes out/check.txt and out/numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import random
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import count

VALUES = 4
CLASS = {'model': 'read', 'look': 'read', 'clock': 'read', 'put': 'idem', 'mail': 'once', 'pay': 'once'}
ACTIONS = sorted(CLASS)
D, V = 0, 1                     # the labels: durable below volatile


# ---------------------------------------------------------------------------------------------
# 1. Terms ('c', n) | ('v', x) | ('add', s, t); tests ('eq', s, t) | ('le', s, t).  Expressions:
#    ('tm', t) | ('let', x, e, e) | ('if', test, e, e) | ('iter', n, t, x, e)
#    | ('do', a, t) | ('once', a, t, x, e, e) | ('raw', a, t) | ('gate', v, e, e)
# ---------------------------------------------------------------------------------------------

def c(n):
    return ('c', n)


def v(x):
    return ('v', x)


def tval(t, env):
    if t[0] == 'c':
        return t[1]
    if t[0] == 'v':
        return env[t[1]]
    return (tval(t[1], env) + tval(t[2], env)) % VALUES


def holds(test, env):
    a, b = tval(test[1], env), tval(test[2], env)
    return a == b if test[0] == 'eq' else a <= b


BROKEN = None       # the name of a typing rule that is deliberately broken, for the last test

RULES = ('do-arg', 'do-pc', 'do-class', 'once-arg', 'once-pc', 'raw-label', 'raw-class', 'if-pc',
         'if-result', 'iter')


class Ill(Exception):
    pass


def need(ok, why):
    if not ok:
        raise Ill(why)


def tlab(t, G):
    if t[0] == 'c':
        return D
    if t[0] == 'v':
        need(t[1] in G, 'an unbound variable')
        return G[t[1]]
    return max(tlab(t[1], G), tlab(t[2], G))


def tc(e, G, pc):
    """The label of an expression under the labels G of its variables and the label pc of the
    tests that decide whether it runs."""
    k = e[0]
    if k == 'tm':
        return tlab(e[1], G)
    if k == 'let':
        return tc(e[3], {**G, e[1]: tc(e[2], G, pc)}, pc)
    if k == 'if':
        lt = max(tlab(e[1][1], G), tlab(e[1][2], G))
        inner = pc if BROKEN == 'if-pc' else max(pc, lt)
        l1, l2 = tc(e[2], G, inner), tc(e[3], G, inner)
        return max(l1, l2) if BROKEN == 'if-result' else max(lt, l1, l2)
    if k == 'iter':
        _, n, t, x, body = e
        lx = tlab(t, G)
        if tc(body, {**G, x: lx}, pc) > lx and BROKEN != 'iter':
            lx = V              # the state becomes volatile in the first turn
            tc(body, {**G, x: V}, pc)
        return lx
    if k == 'do':
        need(CLASS[e[1]] != 'once' or BROKEN == 'do-class', 'an action that must not be repeated')
        need(tlab(e[2], G) == D or BROKEN == 'do-arg', 'a request with a volatile argument')
        need(pc == D or BROKEN == 'do-pc', 'a request under volatile control')
        return D
    if k == 'once':
        _, a, t, x, e1, e2 = e
        need(tlab(t, G) == D or BROKEN == 'once-arg', 'a request with a volatile argument')
        need(pc == D or BROKEN == 'once-pc', 'a request under volatile control')
        return max(tc(e1, {**G, x: D}, pc), tc(e2, G, pc))
    if k == 'raw':
        tlab(e[2], G)
        need(CLASS[e[1]] == 'read' or BROKEN == 'raw-class', 'an effect outside the journal')
        return D if BROKEN == 'raw-label' else V
    if k == 'gate':
        return max(tc(e[2], G, pc), tc(e[3], G, pc))
    raise Ill('an expression of a program')


def verdict(e):
    """'accepted', or the reason for which the checker rejects."""
    try:
        tc(e, {}, D)
        return 'accepted'
    except Ill as reason:
        return str(reason)


def well_typed(e):
    return verdict(e) == 'accepted'


def strip(e, version):
    """The program as it was at a version: every gate above the version is its old branch."""
    if not isinstance(e, tuple):
        return e
    if e[0] == 'gate' and e[1] > version:
        return strip(e[3], version)
    return tuple(strip(part, version) for part in e)


# ---------------------------------------------------------------------------------------------
# 2. The machine.  Journal entries: ('epoch', v) | ('do', a, c) | ('once', a, c) | ('res', r)
#    | ('lost',).  World events: (journaled, a, c, r, position of the request in the journal).
# ---------------------------------------------------------------------------------------------

PROTO = None        # the name of a step of the protocol that is deliberately broken

PROTOCOL = ('late-req', 'once-retry', 'no-epoch', 'lenient', 'no-leftover')


class Crash(Exception):
    """The process dies.  The journal and the world stay as they are."""


class Mismatch(Exception):
    """The journal does not fit what the program does: the run is stuck."""


class World:
    """Replies from a random stream."""

    def __init__(self, seed):
        self.rng = random.Random(seed)

    def reply(self, att, a, arg, raw=False):
        return int(self.rng.random() * VALUES)


class Attempt:
    """One attempt.  `director(attempt, point)` says whether the process dies at a point; the
    points are 'sync', 'perform', and the kinds of journal entries just before they are
    written."""

    def __init__(self, J, W, cap, world, director):
        self.J, self.W, self.cap, self.world, self.director = J, W, cap, world, director
        self.cursor, self.cur, self.k, self.raws = 0, 0, 0, []

    def point(self, what):
        if self.director(self, what):
            raise Crash()

    def append(self, entry):
        self.point(entry[0])
        self.J.append(entry)
        self.cursor += 1

    def perform(self, a, arg, pos):
        self.point('perform')
        r = self.world.reply(self, a, arg)
        self.W.append((True, a, arg, r, pos))
        return r

    def sync(self):
        """Moves past the version marks under the cursor.  At the end of the journal, a newer
        deployed version starts here and is marked."""
        self.point('sync')
        if PROTO == 'no-epoch':
            self.cur = self.cap
            return
        while self.cursor < len(self.J) and self.J[self.cursor][0] == 'epoch':
            self.cur = self.J[self.cursor][1]
            self.cursor += 1
        if self.cursor == len(self.J) and self.cur < self.cap:
            self.append(('epoch', self.cap))
            self.cur = self.cap

    def request(self, kind, a, arg):
        """A journaled request; the answer is ('res', r) or ('lost',)."""
        self.sync()
        entry, pos = (kind, a, arg), self.cursor
        self.k += 1
        if pos < len(self.J):                           # the request was made before
            seen = self.J[pos]
            if not (seen[0] in ('do', 'once') if PROTO == 'lenient' else seen == entry):
                raise Mismatch()
            self.cursor += 1
            if self.cursor < len(self.J):
                answer = self.J[self.cursor]
                if not (answer[0] == 'res' or (answer[0] == 'lost' and kind == 'once')):
                    raise Mismatch()
                self.cursor += 1
                return answer
            # the attempt that wrote the request died before it wrote an answer
            if kind == 'once' and PROTO != 'once-retry':
                self.append(('lost',))
                return ('lost',)
            r = self.perform(a, arg, pos)
            self.append(('res', r))
            return ('res', r)
        if PROTO == 'late-req':
            r = self.perform(a, arg, pos)
            self.append(entry)
        else:
            self.append(entry)                          # the request is written before it is made
            r = self.perform(a, arg, pos)
        self.append(('res', r))
        return ('res', r)

    def finish(self):
        while self.cursor < len(self.J) and self.J[self.cursor][0] == 'epoch':
            self.cursor += 1
        if self.cursor < len(self.J) and PROTO != 'no-leftover':
            raise Mismatch()

    def ev(self, e, env):
        k = e[0]
        if k == 'tm':
            return tval(e[1], env)
        if k == 'let':
            return self.ev(e[3], {**env, e[1]: self.ev(e[2], env)})
        if k == 'if':
            return self.ev(e[2] if holds(e[1], env) else e[3], env)
        if k == 'iter':
            x = tval(e[2], env)
            for _ in range(e[1]):
                x = self.ev(e[4], {**env, e[3]: x})
            return x
        if k == 'do':
            return self.request('do', e[1], tval(e[2], env))[1]
        if k == 'once':
            answer = self.request('once', e[1], tval(e[2], env))
            if answer[0] == 'res':
                return self.ev(e[4], {**env, e[3]: answer[1]})
            return self.ev(e[5], env)
        if k == 'raw':
            arg = tval(e[2], env)
            r = self.world.reply(self, e[1], arg, raw=True)
            self.raws.append(r)
            self.W.append((False, e[1], arg, r, None))
            return r
        self.sync()
        return self.ev(e[2] if self.cur >= e[1] else e[3], env)


class Outcome:
    def __init__(self, value, J, W, crashes, raws, stuck):
        self.value, self.J, self.W, self.crashes, self.raws, self.stuck = value, J, W, crashes, raws, stuck


def run(text, cap, director, world):
    """A run: attempts until one ends.  `text(cap)` is the program that is deployed with a
    version, and `cap(j, J, last)` is the version of attempt j."""
    J, W, j, version = [], [], 0, 0
    while True:
        version = cap(j, J, version)
        att = Attempt(J, W, version, world, director)
        try:
            value = att.ev(text(version), {})
            att.finish()
            return Outcome(value, J, W, j, att.raws, False)
        except Crash:
            j += 1
        except Mismatch:
            return Outcome(None, J, W, j, att.raws, True)


# ---------------------------------------------------------------------------------------------
# 3. The reference semantics
# ---------------------------------------------------------------------------------------------

class Unfaithful(Exception):
    pass


class Reference:
    """Figure 2: an execution without a journal and without crashes.  It is given the answers
    to its requests, the version in force before each request, and the replies to its raw
    actions.  Events: ('do', a, c, r) | ('once', a, c, r) | ('lost', a, c) | ('raw', a, c, r)."""

    def __init__(self, answers, versions, raws):
        self.answers, self.versions, self.raws = answers, versions, list(raws)
        self.k, self.events = 0, []

    def answer(self, kind):
        if self.k >= len(self.answers):
            raise Unfaithful()
        return self.answers[self.k]

    def version(self):
        if self.k >= len(self.versions):
            raise Unfaithful()
        return self.versions[self.k]

    def raw(self):
        if not self.raws:
            raise Unfaithful()
        return self.raws.pop(0)

    def ev(self, e, env):
        k = e[0]
        if k == 'tm':
            return tval(e[1], env)
        if k == 'let':
            return self.ev(e[3], {**env, e[1]: self.ev(e[2], env)})
        if k == 'if':
            return self.ev(e[2] if holds(e[1], env) else e[3], env)
        if k == 'iter':
            x = tval(e[2], env)
            for _ in range(e[1]):
                x = self.ev(e[4], {**env, e[3]: x})
            return x
        if k in ('do', 'once'):
            arg, answer = tval(e[2], env), self.answer(k)
            self.k += 1
            if answer[0] == 'res':
                self.events.append((k, e[1], arg, answer[1]))
                return answer[1] if k == 'do' else self.ev(e[4], {**env, e[3]: answer[1]})
            if k == 'do':
                raise Unfaithful()
            self.events.append(('lost', e[1], arg))
            return self.ev(e[5], env)
        if k == 'raw':
            arg, r = tval(e[2], env), self.raw()
            self.events.append(('raw', e[1], arg, r))
            return r
        return self.ev(e[2] if self.version() >= e[1] else e[3], env)


class Free(Reference):
    """A reference execution that makes up its answers, versions, and replies as it goes."""

    def __init__(self, rng):
        super().__init__([], [1 + int(rng.random() * 2)], [])
        self.rng, self.replies = rng, []

    def answer(self, kind):
        while len(self.answers) <= self.k:
            if kind == 'once' and self.rng.random() < 0.3:
                self.answers.append(('lost',))
            else:
                self.answers.append(('res', int(self.rng.random() * VALUES)))
            self.versions.append(min(3, self.versions[-1] + (self.rng.random() < 0.2)))
        return self.answers[self.k]

    def raw(self):
        self.replies.append(int(self.rng.random() * VALUES))
        return self.replies[-1]


def well_formed(J):
    """Marks and pairs of a request and an answer, and at most one request without an answer,
    at the end.  Only a `once` is answered by `lost`."""
    i = 0
    while i < len(J):
        if J[i][0] == 'epoch':
            i += 1
        elif J[i][0] in ('do', 'once') and i + 1 == len(J):
            return True
        elif J[i][0] in ('do', 'once') and (J[i + 1][0] == 'res' or (J[i][0], J[i + 1][0]) == ('once', 'lost')):
            i += 2
        else:
            return False
    return True


def plain(J):
    """A journal without the version marks that no request follows."""
    return [entry for i, entry in enumerate(J)
            if entry[0] != 'epoch' or (i + 1 < len(J) and J[i + 1][0] != 'epoch')]


def decode(J):
    """The answers that a journal records, and the version in force before each request and
    after the last."""
    answers, versions, cur = [], [], 0
    for entry in J:
        if entry[0] == 'epoch':
            cur = entry[1]
        elif entry[0] in ('do', 'once'):
            versions.append(cur)
        else:
            answers.append(entry)
    return answers, versions + [cur]


def faithful(events, W, strong):
    """Definition 3.1: whether a world trace belongs to the trace of a reference execution, in
    which a `do` may be performed several times in a row and a lost `once` may have been
    performed or not.  The
    weak form looks at the journaled actions only.  The strong form adds that no action of
    class once is repeated and that every effect outside the journal happens once."""
    S = [w[:4] for w in W if w[0] or (strong and CLASS[w[1]] != 'read')]
    T = [ev for ev in events if ev[0] != 'raw' or (strong and CLASS[ev[1]] != 'read')]

    @lru_cache(maxsize=None)
    def go(i, j):
        if i == len(T):
            return j == len(S)
        ev = T[i]
        if ev[0] == 'raw':
            return j < len(S) and S[j] == (False,) + ev[1:] and go(i + 1, j + 1)
        if ev[0] == 'once':
            return j < len(S) and S[j] == (True,) + ev[1:] and go(i + 1, j + 1)
        if ev[0] == 'lost':
            return go(i + 1, j) or (j < len(S) and S[j][:3] == (True,) + ev[1:] and go(i + 1, j + 1))
        while j < len(S) and S[j][:3] == (True, ev[1], ev[2]):
            if S[j][3] == ev[3] and go(i + 1, j + 1):
                return True
            if strong and CLASS[ev[1]] == 'once':
                return False
            j += 1
        return False

    return go(0, 0)


def explained(e, out, strong):
    """Theorem 5.5 for one run that ended with a value."""
    answers, versions = decode(out.J)
    ref = Reference(answers, versions, out.raws)
    try:
        value = ref.ev(e, {})
    except Unfaithful:
        return False
    asked = [('once' if ev[0] == 'lost' else ev[0],) + ev[1:3] for ev in ref.events if ev[0] != 'raw']
    if PROTO != 'lenient' and asked != [entry for entry in out.J if entry[0] in ('do', 'once')]:
        return False
    return ref.k == len(answers) and not ref.raws and value == out.value and faithful(ref.events, out.W, strong)


def cost(out):
    """The number of repeated performances of `do` requests and the number of lost replies."""
    performed = {}
    for journaled, a, arg, r, pos in out.W:
        if journaled:
            performed[pos] = performed.get(pos, 0) + 1
    repeats = sum(n - 1 for pos, n in performed.items() if out.J[pos][0] == 'do')
    assert all(n == 1 for pos, n in performed.items() if out.J[pos][0] == 'once')
    return repeats, sum(entry[0] == 'lost' for entry in out.J)


# ---------------------------------------------------------------------------------------------
# 4. Random programs, crashes, and deployments
# ---------------------------------------------------------------------------------------------

class Gen:
    """Programs.  With wild = 0 every program follows the typing rules.  With wild > 0 each
    choice that a rule constrains ignores the rule with that probability."""

    def __init__(self, rng, wild=0.0):
        self.rng, self.wild, self.names, self.slipped = rng, wild, count(), 0

    def below(self, n):
        return int(self.rng.random() * n)

    def one(self, xs):
        return xs[self.below(len(xs))]

    def name(self):
        return 'x%d' % next(self.names)

    def slips(self):
        if self.wild > 0 and self.rng.random() < self.wild:
            self.slipped += 1
            return True
        return False

    def term(self, G, lab):
        """A term whose label is at most `lab`."""
        names = sorted(x for x, l in G.items() if l <= lab)
        r = self.rng.random()
        if names and r < 0.6:
            return v(self.one(names))
        if names and r < 0.75:
            return ('add', v(self.one(names)), c(1 + self.below(VALUES - 1)))
        return c(self.below(VALUES))

    def arg(self, G):
        return self.term(G, V if self.slips() else D)

    def step(self, G, pc):
        """One operation and the label of its result."""
        r = self.rng.random()
        if r < 0.5 and (pc == D or self.slips()):
            a = self.one(ACTIONS if self.slips() else [a for a in ACTIONS if CLASS[a] != 'once'])
            return ('do', a, self.arg(G)), D
        if r < 0.75:
            a = self.one(ACTIONS if self.slips() else [a for a in ACTIONS if CLASS[a] == 'read'])
            return ('raw', a, self.term(G, V)), V
        t = self.term(G, V)
        return ('tm', t), tlab(t, G)

    def pick(self, G):
        """A value that a test picks.  A slip forgets that the test may be volatile."""
        test = (self.one(['eq', 'le']), self.term(G, V), self.term(G, V))
        t1, t2 = self.term(G, V), self.term(G, V)
        lab = max(tlab(t1, G), tlab(t2, G))
        if not self.slips():
            lab = max(lab, tlab(test[1], G), tlab(test[2], G))
        return ('if', test, ('tm', t1), ('tm', t2)), lab

    def expr(self, depth, G, pc):
        """An expression and an upper bound of its label."""
        if depth == 0:
            return self.step(G, pc)
        k = self.one(['let'] * 6 + ['if', 'if', 'iter', 'gate', 'gate', 'once', 'once'])
        if k == 'once' and not (pc == D or self.slips()):
            k = 'let'
        if k == 'let':
            x, r = self.name(), self.rng.random()
            # what is bound is one operation, a value that a test picks, or a small expression
            e1, l1 = self.pick(G) if r < 0.1 else self.expr(1, G, pc) if r < 0.25 else self.step(G, pc)
            e2, l2 = self.expr(depth - 1, {**G, x: l1}, pc)
            return ('let', x, e1, e2), l2
        if k == 'if':
            lab = D if self.rng.random() < 0.6 else V
            test = (self.one(['eq', 'le']), self.term(G, lab), self.term(G, lab))
            lt = max(tlab(test[1], G), tlab(test[2], G))
            e1, l1 = self.expr(depth - 1, G, max(pc, lt))
            e2, l2 = self.expr(depth - 1, G, max(pc, lt))
            return ('if', test, e1, e2), max(lt, l1, l2)
        if k == 'iter':
            t, x = self.term(G, V), self.name()
            lx = max(tlab(t, G), D if self.rng.random() < 0.7 else V)
            body, lb = self.expr(depth - 1, {**G, x: lx}, pc)
            if lb > lx and not self.slips():
                lx = V
                body, lb = self.expr(depth - 1, {**G, x: V}, pc)
            return ('iter', 1 + self.below(3), t, x, body), max(lx, lb)
        if k == 'gate':
            e1, l1 = self.expr(depth - 1, G, pc)
            e2, l2 = self.expr(depth - 1, G, pc)
            return ('gate', 2 + self.below(2), e1, e2), max(l1, l2)
        x = self.name()
        e1, l1 = self.expr(depth - 1, {**G, x: D}, pc)
        e2, l2 = self.expr(depth - 1, G, pc)
        return ('once', self.one(ACTIONS), self.arg(G), x, e1, e2), max(l1, l2)

    def program(self):
        self.slipped = 0
        return self.expr(6, {}, D)[0]


class Crashes:
    """A director that lets the process die at random points, a bounded number of times.  With
    `replay` off it dies only before a request, an action, or an answer, and not where a
    version is looked up or marked."""

    def __init__(self, rng, budget, replay=True):
        self.rng, self.budget, self.replay = rng, budget, replay

    def __call__(self, att, what):
        if what in ('sync', 'epoch') and not self.replay:
            return False
        if self.budget > 0 and self.rng.random() < (0.02 if what == 'sync' else 0.15):
            self.budget -= 1
            return True
        return False


def never(att, what):
    return False


def deployments(rng):
    """Versions that never go down: each attempt runs the last version or the next one."""
    return lambda j, J, last: max(1, last) + (last < 3 and rng.random() < 0.3)


def random_run(e, rng, text=None, replay=True, cap=None):
    return run(text or (lambda cap: e), cap or deployments(rng), Crashes(rng, int(rng.random() * 5), replay),
               World(int(rng.random() * 2 ** 32)))


def size(e):
    return 1 + sum(size(part) for part in e if isinstance(part, tuple)) if isinstance(e, tuple) else 0


# ---------------------------------------------------------------------------------------------
# The programs of Section 2
# ---------------------------------------------------------------------------------------------

def booking(fare=('do', 'model', c(0))):
    """Pick a fare, pay it at most once, and file the receipt; if the reply is lost, look."""
    return ('let', 'f', fare,
            ('once', 'pay', v('f'), 'r', ('do', 'put', v('r')),
             ('let', 's', ('do', 'look', v('f')), ('do', 'put', v('s')))))


TABLE = [
    (booking(), 'accepted'),
    (('let', 'f', ('do', 'model', c(0)), ('do', 'pay', v('f'))), 'an action that must not be repeated'),
    (('let', 't', ('raw', 'clock', c(0)), ('do', 'put', v('t'))), 'a request with a volatile argument'),
    (('let', 't', ('raw', 'clock', c(0)), ('if', ('le', v('t'), c(1)), ('do', 'put', c(1)), ('tm', c(0)))),
     'a request under volatile control'),
    (('let', 't', ('do', 'clock', c(0)), ('if', ('le', v('t'), c(1)), ('do', 'put', v('t')), ('tm', c(0)))),
     'accepted'),
    (('let', 't', ('raw', 'clock', c(0)), ('let', 'u', ('raw', 'look', v('t')), ('do', 'put', c(1)))),
     'accepted'),
    (('raw', 'mail', c(1)), 'an effect outside the journal'),
    (booking(('gate', 2, ('do', 'model', c(1)), ('do', 'model', c(0)))), 'accepted'),
]


class Script(World):
    """A world whose replies are given: by the number of the request for journaled actions, and
    by their order within an attempt for raw ones."""

    def __init__(self, replies, raws=()):
        self.replies, self.raws = replies, raws

    def reply(self, att, a, arg, raw=False):
        return self.raws[len(att.raws)] if raw else self.replies[att.k - 1]


def dies_at(*points):
    """A director that kills the process at given (attempt, point, number of the request)."""
    state = {'attempt': 0}

    def director(att, what):
        if (state['attempt'], what, att.k) in points:
            state['attempt'] += 1
            return True
        return False

    return director


# ---------------------------------------------------------------------------------------------
# 5. The tests
# ---------------------------------------------------------------------------------------------

def realize(e, ref, rng):
    """Theorem 5.6: a run of the machine that does exactly what a reference execution does.
    The process dies where a reply is lost, and where a newer version starts."""
    performed = [rng.random() < 0.5 for _ in ref.answers]

    def director(att, what):
        j = att.k - 1
        if what == 'sync':
            return ref.versions[att.k] > att.cap
        if what == 'perform':
            return ref.answers[j][0] == 'lost' and not performed[j]
        return what == 'res' and ref.answers[j][0] == 'lost'

    def cap(j, J, last):
        return max(last, ref.versions[sum(entry[0] in ('do', 'once') for entry in J)])

    return run(lambda version: e, cap, director,
               Script([a[1] if a[0] == 'res' else 0 for a in ref.answers], ref.replies))


def refuted(e, rng, strong, runs=4):
    """Whether some run of the program gets stuck or ends with a trace that no reference
    execution explains."""
    for _ in range(runs):
        out = random_run(e, rng)
        if out.stuck or not explained(e, out, strong):
            return True
    return False


def expected_calls(n, q, journal):
    """The expected number of model calls of a task of n calls in a row, if the process dies
    after each call with probability q before the reply is stored.  Without a journal a
    restart begins again: E(i) = 1 + (1 - q) E(i + 1) + q E(0)."""
    if journal:
        return n / (1 - q)
    a, b = Fraction(0), Fraction(0)             # E(i) = a + b E(0), from i = n down to 0
    for _ in range(n):
        a, b = 1 + (1 - q) * a, (1 - q) * b + q
    return a / (1 - b)


def main(outdir):
    global BROKEN, PROTO
    rng = random.Random(2026)
    lines, nums = [], {}

    # Table 1 and the three runs of Section 2
    assert all(verdict(e) == expected for e, expected in TABLE)
    out = run(lambda cap: booking(), lambda j, J, last: 1, dies_at((0, 'res', 2)), Script([2, 3, 1, 0]))
    assert out.J == [('epoch', 1), ('do', 'model', 0), ('res', 2), ('once', 'pay', 2), ('lost',),
                     ('do', 'look', 2), ('res', 1), ('do', 'put', 1), ('res', 0)]
    assert [w[:4] for w in out.W] == [(True, 'model', 0, 2), (True, 'pay', 2, 3), (True, 'look', 2, 1),
                                      (True, 'put', 1, 0)]
    assert out.crashes == 1 and explained(booking(), out, True) and cost(out) == (0, 1)
    old, new = booking(), booking(('do', 'model', c(1)))
    out = run(lambda cap: old if cap == 1 else new, lambda j, J, last: j + 1, dies_at((0, 'once', 2)),
              Script([2, 3, 1, 0]))
    assert out.stuck and out.J == [('epoch', 1), ('do', 'model', 0), ('res', 2)]
    gated = TABLE[-1][0]
    assert strip(gated, 1) == old
    out = run(lambda cap: strip(gated, cap), lambda j, J, last: j + 1, dies_at((0, 'once', 2)),
              Script([2, 3, 1, 0]))
    assert not out.stuck and out.J[:5] == [('epoch', 1), ('do', 'model', 0), ('res', 2), ('epoch', 2),
                                           ('once', 'pay', 2)]
    lines.append('the checker gives the verdicts of Table 1, and the three runs of Section 2 end as the '
                 'paper says')

    # Theorems 5.3, 5.5 and 5.7 on programs that the checker accepts
    typed, wild, lucky, gen = [], [], 0, Gen(rng)
    while len(typed) < 2000:
        typed.append(gen.program())
    assert all(well_typed(e) for e in typed)
    gen = Gen(rng, wild=0.1)
    while len(wild) < 2000:
        e = gen.program()
        if well_typed(e):
            wild.append(e)
            lucky += gen.slipped > 0
    crashes = repeats = lost = requests = marks = 0
    for e in typed + wild:
        for _ in range(5):
            out = random_run(e, rng)
            assert not out.stuck and well_formed(out.J) and explained(e, out, True)
            r, l = cost(out)
            assert r + l <= out.crashes
            crashes, repeats, lost = crashes + out.crashes, repeats + r, lost + l
            requests += sum(entry[0] in ('do', 'once') for entry in out.J)
            marks += sum(entry[0] == 'epoch' for entry in out.J)
        # one text needs no order among the versions: here they go up and down
        out = random_run(e, rng, cap=lambda j, J, last: 1 + int(rng.random() * 3))
        assert not out.stuck and well_formed(out.J) and explained(e, out, True)
    lines.append(f'4000 programs that the checker accepts ({lucky} of them built with a rule ignored), five '
                 f'runs each with random crashes and deployments: no run gets stuck, every run is a '
                 f'reference execution up to repeated do requests, and repeats plus lost replies never '
                 f'exceed crashes; {crashes} crashes, {requests} requests, {repeats} repeats, {lost} lost '
                 f'replies, {marks} version marks')
    nums.update(Programs='4,000', Lucky=f'{lucky:,}', Runs='20,000', Crashes=f'{crashes:,}',
                Requests=f'{requests:,}', Repeats=f'{repeats:,}', Lost=f'{lost:,}', Marks=f'{marks:,}',
                MedianNodes=str(sorted(size(e) for e in typed + wild)[2000]))

    # Theorem 5.5 on programs of any kind, and what the journal does with the ones that are rejected
    rejected, gen = [], Gen(rng, wild=0.1)
    while len(rejected) < 2000:
        e = gen.program()
        if not well_typed(e):
            rejected.append(e)
    stuck = late = astray = quiet = 0
    for e in rejected:
        ever = False
        for _ in range(20):
            out = random_run(e, rng)
            assert well_formed(out.J)
            if out.stuck:
                ever, stuck = True, stuck + 1
                late += any(CLASS[w[1]] != 'read' for w in out.W)
            else:
                assert explained(e, out, False)
                if not explained(e, out, True):
                    ever, astray = True, astray + 1
        quiet += not ever
    lines.append(f'2000 programs that the checker rejects, twenty runs each: every run that ends is a '
                 f'reference execution up to repeated do requests and effects outside the journal; {stuck} '
                 f'of the 40000 runs get stuck, {late} of them after an effect; {astray} runs end with an '
                 f'effect too many; {quiet} programs show nothing in twenty runs')
    nums.update(Rejected='2,000', RejectedRuns='40,000', Stuck=f'{stuck:,}', Late=f'{late:,}',
                Astray=f'{astray:,}', BadPercent=f'{100 * (stuck + astray) / 40000:.0f}',
                LatePercent=f'{100 * late / stuck:.0f}', Quiet=f'{quiet:,}',
                QuietPercent=f'{100 * quiet / len(rejected):.0f}')

    # Theorem 5.6: every reference execution is a run
    losses = starts = 0
    for e in typed[:1000] + wild[:1000]:
        ref = Free(rng)
        value = ref.ev(e, {})
        out = realize(e, ref, rng)
        answers, versions = decode(out.J)
        assert not out.stuck and out.value == value and answers == ref.answers[:ref.k]
        assert explained(e, out, True) and cost(out)[0] == 0
        assert all(versions[k] == ref.versions[k] or k == ref.k for k in range(ref.k + 1))
        losses += sum(a[0] == 'lost' for a in answers)
        starts += sum(entry[0] == 'epoch' for entry in out.J)
    lines.append(f'2000 reference executions with {losses} lost replies and {starts} starts of a version: '
                 f'for each there is a run of the machine with the same value, answers, and world trace')
    nums.update(References='2,000', RefLost=f'{losses:,}')

    # Theorem 5.9: old texts with their versions against the newest text
    for e in typed[:1000] + wild[:1000]:
        seed = int(rng.random() * 2 ** 32)
        outs = []
        for text in (lambda cap: strip(e, cap), lambda cap: e):
            r = random.Random(seed)
            # the two texts have different numbers of gates, so the process may not die where
            # a version is looked up or marked: then both runs die at the same places
            outs.append(random_run(e, r, text, replay=False))
        assert outs[0].value == outs[1].value and plain(outs[0].J) == plain(outs[1].J)
        assert [w[:4] for w in outs[0].W] == [w[:4] for w in outs[1].W]
        assert well_typed(strip(e, 1)) and well_typed(strip(e, 2))
    lines.append('2000 programs with gates: a run in which every attempt uses the text of its version has '
                 'the value, the world trace, and, up to version marks that no request follows, the journal '
                 'of the run in which every attempt uses the newest text')
    # a deployment that is taken back gets stuck
    back = run(lambda cap: strip(gated, cap), lambda j, J, last: 2 - j if j < 2 else 1,
               dies_at((0, 'once', 2)), Script([2, 3, 1, 0]))
    assert back.stuck and back.J[:2] == [('epoch', 2), ('do', 'model', 1)]

    # every typing rule is needed
    tries = {}
    for rule in RULES:
        BROKEN = rule
        gen = Gen(rng, wild=0.15)
        for i in range(1, 300001):
            e = gen.program()
            if well_typed(e) and refuted(e, rng, True):
                tries[rule] = i
                break
        BROKEN = None
    assert set(tries) == set(RULES), tries
    assert max(tries, key=tries.get) == 'if-result'     # the paper says which rule is the slowest
    lines.append(f'{len(RULES)} checkers with one broken rule each: every one accepts a program with a run '
                 'that gets stuck or that no reference execution explains, after '
                 + ', '.join(f'{rule} {n}' for rule, n in tries.items()) + ' programs')
    nums.update(Rules=str(len(RULES)), Slowest=f'{max(tries.values()):,}')
    for rule, n in tries.items():
        nums['Try' + ''.join(part.capitalize() for part in rule.split('-'))] = f'{n:,}'

    # every step of the protocol is needed
    steps = {}
    for step in PROTOCOL:
        PROTO = step
        gen = Gen(rng) if step in ('late-req', 'once-retry', 'no-epoch') else Gen(rng, wild=0.15)
        for i in range(1, 300001):
            e = gen.program()
            strong = step in ('late-req', 'once-retry', 'no-epoch')
            bad = False
            for _ in range(4):
                out = random_run(e, rng)
                bad = bad or (out.stuck if strong else not out.stuck and not explained(e, out, False))
                bad = bad or (strong and not out.stuck and not explained(e, out, True))
            if bad:
                steps[step] = i
                break
        PROTO = None
    assert set(steps) == set(PROTOCOL), steps
    lines.append(f'{len(PROTOCOL)} machines with one broken step each: every one has a run that the '
                 'theorems exclude, after ' + ', '.join(f'{s} {n}' for s, n in steps.items()) + ' programs')
    nums.update(Steps=str(len(PROTOCOL)))
    for step, n in steps.items():
        nums['Step' + ''.join(part.capitalize() for part in step.split('-'))] = f'{n:,}'

    # Section 6.1: the cost of a long task with and without a journal
    q = Fraction(1, 100)
    for n in (1, 2, 5, 10, 100, 1000):
        assert expected_calls(n, q, False) == ((1 - q) ** -n - 1) / q
    chain = ('tm', c(0))
    for i in range(20):
        chain = ('let', 'x%d' % i, ('do', 'model', c(0)), chain)
    total, sims = 0, 4000
    for _ in range(sims):
        r = random.Random(int(rng.random() * 2 ** 32))
        out = run(lambda cap: chain, lambda j, J, last: 1,
                  lambda att, what: what == 'res' and r.random() < 0.1, World(1))
        total += sum(w[0] for w in out.W)
    assert abs(total / sims - 20 / 0.9) < 0.3
    lines.append(f'the closed form for a task without a journal agrees with its recurrence, and a chain of '
                 f'20 model calls with a crash after one call in ten makes {total / sims:.2f} calls on '
                 f'average over {sims} runs, against 20 / 0.9 = {20 / 0.9:.2f}')
    for letter, n in zip('abc', (10, 100, 1000)):
        for name, journal in (('Scratch', False), ('Journal', True)):
            calls = float(expected_calls(n, q, journal))
            nums[name + letter] = f'{calls:,.1f}' if calls < 1000 else f'{calls:,.0f}'
    nums['ChainCalls'] = f'{total / sims:.2f}'

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by journal.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
