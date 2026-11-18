#!/usr/bin/env python3
"""Tests the claims of "What an Agent Loop Costs" against an implementation of its semantics.

The file has four parts.

1. The cost semantics of Figure 2.  A string is a tuple of tokens, the cache is the set of the
   breakpoints sent so far, and a provider may bill at the reduced price any part of a prompt
   that is at least as long as the longest breakpoint that the prompt begins with.
2. The typing rules of Figure 3 for closed programs.  A closed program has numbers for all its
   indices, so the checker unrolls every loop and needs no invariant: the type that it computes
   for turn i is the invariant at i.
3. The programs of Section 6 with their closed forms.
4. The tests.  `python3 cost.py out` writes out/check.txt and out/numbers.tex.  The paper reads
   its numbers from the committed copy of numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import math
import random
import sys
from fractions import Fraction as Q
from itertools import count


# ---------------------------------------------------------------------------------------------
# Programs.  Values:  ('lit', tokens) | ('var', x) | ('pair', v1, v2)
# Expressions:        ('val', v) | ('cat', v1, v2) | ('tail', n, v) | ('recv', n) | ('hear', n)
#                     | ('call', v1, v2, n) | ('let', x, e1, e2) | ('split', x, y, v, e)
#                     | ('or', e1, e2) | ('iter', n, v, x, body)
# The body of a loop is a function from the turn number to an expression.
# A call returns the triple (v1, v1 v2, answer), represented as the pair (v1, (v1 v2, answer)).
# ---------------------------------------------------------------------------------------------

def var(x):
    return ('var', x)


def lit(n, base):
    """A literal of n tokens that occur in no other literal with a different base."""
    return ('lit', tuple(range(base, base - n, -1)))


def call3(s, p, a, v1, v2, n, body):
    """let (s, p, a) = call(v1; v2, n) in body"""
    return ('let', '%z', ('call', v1, v2, n),
            ('split', s, '%r', var('%z'), ('split', p, a, var('%r'), body)))


# ---------------------------------------------------------------------------------------------
# 1. The cost semantics
# ---------------------------------------------------------------------------------------------

class Pair:
    __slots__ = ('fst', 'snd')

    def __init__(self, fst, snd):
        self.fst, self.snd = fst, snd


class Run:
    """One evaluation.  In mode 'worst' every message and every answer has the maximal length and
    consists of new tokens, the provider bills at the reduced price only what it must, and a wait
    empties the cache.  In mode 'random' all of these are drawn at random."""

    def __init__(self, rho, omega, mode, rng):
        self.rho, self.omega, self.mode, self.rng = rho, omega, mode, rng
        self.cache = set()
        self.cost = Q(0)
        self.peak = 0
        self.fresh = count(1)

    def below(self, n):
        return int(self.rng.random() * (n + 1))

    def string(self, n):
        if self.mode == 'worst':
            return tuple(next(self.fresh) for _ in range(n))
        # mostly the token 0, so that different prompts often begin alike
        return tuple(0 if self.rng.random() < 0.8 else next(self.fresh) for _ in range(self.below(n)))

    def hit(self, w):
        least = max((len(u) for u in self.cache if len(u) <= len(w) and w[:len(u)] == u), default=0)
        return least if self.mode == 'worst' else least + self.below(len(w) - least)

    def wait(self):
        if self.mode == 'worst':
            self.cache = set()
        else:
            self.cache = {u for u in self.cache if self.rng.random() < 0.5}

    def left(self):
        return self.rng.random() < 0.5


def value(v, env):
    if v[0] == 'lit':
        return v[1]
    if v[0] == 'var':
        return env[v[1]]
    return Pair(value(v[1], env), value(v[2], env))


def ev(e, env, run):
    k = e[0]
    if k == 'val':
        return value(e[1], env)
    if k == 'cat':
        return value(e[1], env) + value(e[2], env)
    if k == 'tail':
        w = value(e[2], env)
        return w[len(w) - min(e[1], len(w)):]
    if k == 'recv':
        return run.string(e[1])
    if k == 'hear':
        run.wait()
        return run.string(e[1])
    if k == 'call':
        w1, w2 = value(e[1], env), value(e[2], env)
        w = w1 + w2
        a = run.string(e[3])
        hit = run.hit(w)
        run.cost += run.rho * hit + (len(w) - hit) + run.omega * len(a)
        run.peak = max(run.peak, len(w) + e[3])
        run.cache |= {w1, w}
        return Pair(w1, Pair(w, a))
    if k == 'let':
        return ev(e[3], {**env, e[1]: ev(e[2], env, run)}, run)
    if k == 'split':
        p = value(e[3], env)
        return ev(e[4], {**env, e[1]: p.fst, e[2]: p.snd}, run)
    if k == 'or':
        return ev(e[1] if run.left() else e[2], env, run)
    if k == 'iter':
        acc = value(e[2], env)
        for i in range(e[1]):
            acc = ev(e[4](i), {**env, e[3]: acc}, run)
        return acc
    raise ValueError(k)


# ---------------------------------------------------------------------------------------------
# 2. The typing rules for closed programs.  Types: ('str', P, R) | ('prod', A, B)
# ---------------------------------------------------------------------------------------------

def forget(A):
    if A[0] == 'str':
        return ('str', 0, A[1] + A[2])
    return ('prod', forget(A[1]), forget(A[2]))


def join(A, B):
    if A[0] == 'prod':
        return ('prod', join(A[1], B[1]), join(A[2], B[2]))
    return ('str', max(A[1], B[1]), max(A[2], B[2]))


def total(A):
    return A[1] + A[2] if A[0] == 'str' else total(A[1]) + total(A[2])


def hears(e):
    k = e[0]
    if k == 'hear':
        return True
    if k == 'let':
        return hears(e[2]) or hears(e[3])
    if k == 'split':
        return hears(e[4])
    if k == 'or':
        return hears(e[1]) or hears(e[2])
    if k == 'iter':
        return e[1] > 0 and hears(e[4](0))
    return False


def vtype(v, tenv):
    if v[0] == 'lit':
        return ('str', 0, len(v[1]))
    if v[0] == 'var':
        return tenv[v[1]]
    return ('prod', vtype(v[1], tenv), vtype(v[2], tenv))


class Check:
    def __init__(self, rho, omega):
        self.rho, self.omega = rho, omega
        self.peak = 0      # the largest prompt-plus-answer bound of a call
        self.big = 0       # the largest size bound of a string

    def ty(self, e, tenv):
        """The type, the cost, and whether the expression may wait."""
        k = e[0]
        if k == 'val':
            return vtype(e[1], tenv), Q(0), 0
        if k == 'cat':
            A, B = vtype(e[1], tenv), vtype(e[2], tenv)
            self.big = max(self.big, total(A) + total(B))
            return ('str', A[1], A[2] + B[1] + B[2]), Q(0), 0
        if k == 'tail':
            assert vtype(e[2], tenv)[0] == 'str'
            return ('str', 0, e[1]), Q(0), 0
        if k == 'recv':
            return ('str', 0, e[1]), Q(0), 0
        if k == 'hear':
            return ('str', 0, e[1]), Q(0), 1
        if k == 'call':
            A, B = vtype(e[1], tenv), vtype(e[2], tenv)
            n = total(A) + total(B)
            self.peak = max(self.peak, n + e[3])
            self.big = max(self.big, n)
            cost = self.rho * A[1] + A[2] + B[1] + B[2] + self.omega * e[3]
            return ('prod', ('str', total(A), 0), ('prod', ('str', n, 0), ('str', 0, e[3]))), cost, 0
        if k == 'let':
            A, c1, f1 = self.ty(e[2], tenv)
            if f1:
                tenv = {x: forget(T) for x, T in tenv.items()}
            B, c2, f2 = self.ty(e[3], {**tenv, e[1]: A})
            return B, c1 + c2, f1 | f2
        if k == 'split':
            A = vtype(e[3], tenv)
            return self.ty(e[4], {**tenv, e[1]: A[1], e[2]: A[2]})
        if k == 'or':
            A, c1, f1 = self.ty(e[1], tenv)
            B, c2, f2 = self.ty(e[2], tenv)
            return join(A, B), max(c1, c2), f1 | f2
        if k == 'iter':
            A, cost, f = vtype(e[2], tenv), Q(0), int(hears(e))
            if f:
                tenv = {x: forget(T) for x, T in tenv.items()}
            for i in range(e[1]):
                A, c, _ = self.ty(e[4](i), {**tenv, e[3]: A})
                cost += c
            return A, cost, f
        raise ValueError(k)


def inhabits(v, A, cache):
    """Whether the value is in the interpretation of the type at the cache."""
    if A[0] == 'prod':
        return isinstance(v, Pair) and inhabits(v.fst, A[1], cache) and inhabits(v.snd, A[2], cache)
    if isinstance(v, Pair):
        return False
    return any(len(v) - len(u) <= A[2]
               for u in cache | {()} if len(u) <= min(A[1], len(v)) and v[:len(u)] == u)


# ---------------------------------------------------------------------------------------------
# 3. The programs of Section 6 and their closed forms
# ---------------------------------------------------------------------------------------------

def tri(n):
    return n * (n - 1) // 2


def turn(y, q, m, recv='recv'):
    """let u = recv q in let (_, p, a) = call(y; u, m) in p ++ a"""
    return ('let', 'u', (recv, q), call3('_', 'p', 'a', y, var('u'), m, ('cat', var('p'), var('a'))))


def plain(N, h, q, m):
    """One turn on a new context of h tokens, then N more turns."""
    return ('let', 'x', turn(lit(h, -1), q, m),
            ('iter', N, var('x'), 'y', lambda i: turn(var('y'), q, m)))


def plain_cost(N, h, q, m, rho, omega):
    d = q + m
    return (h + q + N * d) + (N + 1) * omega * m + rho * (N * (h + q) + d * tri(N))


def session(n, j, h, q, m):
    """n blocks: a turn that waits for a person, then j - 1 turns that do not."""
    return ('iter', n, lit(h, -1), 'y', lambda b: (
        'let', 'x', turn(var('y'), q, m, recv='hear'),
        ('iter', j - 1, var('x'), 'z', lambda i: turn(var('z'), q, m))))


def session_cost(n, j, h, q, m, rho, omega):
    d = q + m
    return ((1 + rho * (j - 1)) * (n * h + j * d * tri(n))
            + n * (q + (j - 1) * d + j * omega * m + rho * ((j - 1) * q + d * tri(j - 1))))


def block(sigma, z, p, q, m, s, g, before=False):
    """A block of p turns that ends with a summary; returns the system prompt and the summary."""
    kappa = lit(g, -500000)
    summary = (kappa, var('y')) if before else (var('y'), kappa)
    return ('let', 'u', ('recv', q), ('let', 'k', ('cat', z, var('u')),
            call3('sg', 'c', 'a', sigma, var('k'), m,
                  ('let', 'x', ('cat', var('c'), var('a')),
                   ('let', 'y', ('iter', p - 1, var('x'), 'y', lambda i: turn(var('y'), q, m)),
                    call3('_', '_', 'zz', summary[0], summary[1], s,
                          ('val', ('pair', var('sg'), var('zz')))))))))


def compaction(n, p, h, q, m, s, g, before=False):
    """One block from a new system prompt, then n more blocks."""
    return ('let', 'st', block(lit(h, -1), lit(s, -300000), p, q, m, s, g, before),
            ('iter', n, var('st'), 'st', lambda b: (
                'split', 'sig', 'zed', var('st'), block(var('sig'), var('zed'), p, q, m, s, g, before))))


def block_cost(p, h, q, m, s, g, rho, omega):
    d = q + m
    return s + p * d + g + omega * (p * m + s) + rho * (h + p * (h + s + q) + d * tri(p))


def compaction_cost(n, p, h, q, m, s, g, rho, omega, before=False):
    extra = (1 - rho) * (h + s + q + (p - 1) * (q + m)) if before else 0
    return (n + 1) * (block_cost(p, h, q, m, s, g, rho, omega) + extra) + (1 - rho) * h


def wturn(sigma, x, b, q, m):
    """A turn that keeps the system prompt and the last b tokens of the history."""
    return ('let', 'u', ('recv', q), ('let', 'k', ('cat', x, var('u')),
            call3('sg', '_', 'a', sigma, var('k'), m,
                  ('let', 'k2', ('cat', var('k'), var('a')),
                   ('let', 'x2', ('tail', b, var('k2')), ('val', ('pair', var('sg'), var('x2'))))))))


def window(N, b, h, q, m):
    return ('let', 'st', wturn(lit(h, -1), lit(b, -300000), b, q, m),
            ('iter', N, var('st'), 'st', lambda i: (
                'split', 'sig', 'win', var('st'), wturn(var('sig'), var('win'), b, q, m))))


def window_cost(N, b, h, q, m, rho, omega):
    return (h + b + q + omega * m) + N * (rho * h + b + q + omega * m)


def sblock(sigma, x, p, b, q, m):
    """A block of p turns on a context that only grows, after which the window slides."""
    inner = ('split', 'y', 'k', var('st'), ('let', 'u', ('recv', q),
             call3('_', 'c', 'a', var('y'), var('u'), m,
                   ('let', 'y2', ('cat', var('c'), var('a')),
                    ('let', 'k1', ('cat', var('k'), var('u')), ('let', 'k2', ('cat', var('k1'), var('a')),
                     ('val', ('pair', var('y2'), var('k2')))))))))
    return ('let', 'u', ('recv', q), ('let', 'k', ('cat', x, var('u')),
            call3('sg', 'c', 'a', sigma, var('k'), m,
                  ('let', 'y', ('cat', var('c'), var('a')), ('let', 'k2', ('cat', var('k'), var('a')),
                   ('let', 'st', ('iter', p - 1, ('pair', var('y'), var('k2')), 'st', lambda i: inner),
                    ('split', 'y', 'k', var('st'), ('let', 'x2', ('tail', b, var('k')),
                     ('val', ('pair', var('sg'), var('x2')))))))))))


def stepped(n, p, b, h, q, m):
    """One block from a new system prompt and a full window, then n more blocks."""
    return ('let', 'st', sblock(lit(h, -1), lit(b, -300000), p, b, q, m),
            ('iter', n, var('st'), 'st', lambda j: (
                'split', 'sig', 'win', var('st'), sblock(var('sig'), var('win'), p, b, q, m))))


def sblock_cost(p, b, h, q, m, rho, omega):
    d = q + m
    return b + q + (p - 1) * d + p * omega * m + rho * (h + (p - 1) * (h + b + q) + d * tri(p - 1))


def stepped_cost(n, p, b, h, q, m, rho, omega):
    return (n + 1) * sblock_cost(p, b, h, q, m, rho, omega) + (1 - rho) * h


def clock(T, h, q, m):
    """Every prompt begins with a new token."""
    return ('iter', T, lit(h, -1), 'y', lambda i: (
        'let', 't', ('recv', 1), ('let', 'u', ('recv', q), ('let', 'k', ('cat', var('y'), var('u')),
        call3('_', '_', 'a', var('t'), var('k'), m, ('cat', var('k'), var('a')))))))


def clock_cost(T, h, q, m, rho, omega):
    return T * (1 + h + q + omega * m) + (q + m) * tri(T)


def agent(tau, fans, k, par):
    """An agent for the task tau.  With no fan-outs it does k turns itself; otherwise it gives
    fans[0] tasks to agents one level down.  It ends with a report."""
    h, q, m, t, r, g = par
    sigma, kappa = lit(h, -1), lit(g, -500000)
    if not fans:
        first = ('let', 'u', ('recv', q), ('let', 'k', ('cat', tau, var('u')),
                 call3('_', 'p', 'a', sigma, var('k'), m, ('cat', var('p'), var('a')))))
        return ('let', 'x', first,
                ('let', 'y', ('iter', k - 1, var('x'), 'y', lambda i: turn(var('y'), q, m)),
                 call3('_', '_', 'rep', var('y'), kappa, r, ('val', var('rep')))))
    child = agent(var('a'), fans[1:], k, par)
    body = ('split', 'y', 'v', var('st'), call3('_', 'p', 'a', var('y'), var('v'), t,
            ('let', 'v2', child, ('let', 'c', ('cat', var('p'), var('a')),
             ('val', ('pair', var('c'), var('v2')))))))
    return call3('_', 'p', 'a', sigma, tau, t,
                 ('let', 'v', child, ('let', 'x', ('cat', var('p'), var('a')),
                  ('let', 'st', ('iter', fans[0] - 1, ('pair', var('x'), var('v')), 'st', lambda i: body),
                   ('split', 'y', 'v', var('st'), ('let', 'k', ('cat', var('v'), kappa),
                    call3('_', '_', 'rep', var('y'), var('k'), r, ('val', var('rep')))))))))


def leaf_cost(k, par, rho, omega):
    h, q, m, t, r, g = par
    return (h + t + k * (q + m) + g) + omega * (k * m + r) + rho * (k * (h + t + q) + (q + m) * tri(k))


def manager_cost(J, par, rho, omega):
    h, q, m, t, r, g = par
    return (h + t + J * (t + r) + g) + omega * (J * t + r) + rho * (J * (h + t) + (t + r) * tri(J))


def agent_cost(fans, k, par, rho, omega):
    if not fans:
        return leaf_cost(k, par, rho, omega)
    return manager_cost(fans[0], par, rho, omega) + fans[0] * agent_cost(fans[1:], k, par, rho, omega)


# ---------------------------------------------------------------------------------------------
# 4. The tests
# ---------------------------------------------------------------------------------------------

PRICES = [(Q(1), Q(1)), (Q(2, 25), Q(4)), (Q(1, 10), Q(5)), (Q(0), Q(3))]


def measure(e, rho, omega, mode, rng):
    run = Run(rho, omega, mode, rng)
    v = ev(e, {}, run)
    return run, v


def agree(e, expected, rho, omega, rng, attained=True):
    """The checker computes the closed form, and the worst evaluation costs exactly that much."""
    chk = Check(rho, omega)
    A, bound, _ = chk.ty(e, {})
    assert bound == expected, (bound, expected)
    run, v = measure(e, rho, omega, 'worst', rng)
    assert inhabits(v, A, run.cache) and run.peak <= chk.peak
    assert run.cost == bound if attained else run.cost <= bound, (run.cost, bound)
    return run.cost


def closed_forms(rng):
    cases = 0
    for rho, omega in PRICES:
        for h in (0, 7, 40):
            for q, m in ((1, 1), (3, 2), (2, 9)):
                for N in range(0, 13):
                    agree(plain(N, h, q, m), plain_cost(N, h, q, m, rho, omega), rho, omega, rng)
                    agree(clock(N, h, q, m), clock_cost(N, h, q, m, rho, omega), rho, omega, rng)
                    cases += 2
                for n in range(0, 5):
                    for j in (1, 2, 5):
                        agree(session(n, j, h, q, m), session_cost(n, j, h, q, m, rho, omega), rho, omega, rng)
                        cases += 1
                for b in (4, 15):
                    for N in (0, 1, 6):
                        agree(window(N, b, h, q, m), window_cost(N, b, h, q, m, rho, omega), rho, omega, rng)
                        cases += 1
                        for p in (1, 2, 4):
                            agree(stepped(N, p, b, h, q, m), stepped_cost(N, p, b, h, q, m, rho, omega),
                                  rho, omega, rng)
                            cases += 1
                for s, g in ((3, 0), (10, 2)):
                    for p in (1, 2, 5):
                        for n in (0, 1, 3):
                            agree(compaction(n, p, h, q, m, s, g),
                                  compaction_cost(n, p, h, q, m, s, g, rho, omega), rho, omega, rng)
                            # With the instruction first, the worst evaluation still finds the
                            # instruction itself in the cache from the second block on.  An empty
                            # instruction changes nothing, and there the rule for calls is loose.
                            bound = compaction_cost(n, p, h, q, m, s, g, rho, omega, before=True)
                            cost = agree(compaction(n, p, h, q, m, s, g, before=True), bound,
                                         rho, omega, rng, attained=False)
                            if g > 0:
                                assert cost == bound - (1 - rho) * g * n
                            else:
                                assert cost == compaction_cost(n, p, h, q, m, s, g, rho, omega)
                            cases += 2
                for t, r, g in ((2, 3, 0), (5, 1, 2)):
                    par = (h, q, m, t, r, g)
                    for fans, k in (((), 1), ((), 4), ((1,), 1), ((3,), 2), ((2, 3), 2), ((2, 2, 2), 1)):
                        # all agents begin with the same system prompt, and every agent after
                        # the first finds it in the cache
                        bound = agent_cost(fans, k, par, rho, omega)
                        cost = agree(agent(lit(t, -700000), fans, k, par), bound, rho, omega, rng,
                                     attained=False)
                        agents, width = 1, 1
                        for J in fans:
                            width *= J
                            agents += width
                        assert cost == bound - (1 - rho) * h * (agents - 1)
                        cases += 1
    return cases


class Gen:
    """Random closed programs that evaluate to a string."""

    def __init__(self, rng, exact):
        self.rng, self.exact, self.names = rng, exact, count()

    def below(self, n):
        return int(self.rng.random() * (n + 1))

    def name(self):
        return 'v%d' % next(self.names)

    def atom(self, scope):
        if scope and self.rng.random() < 0.75:
            return var(scope[self.below(len(scope) - 1)])
        return ('lit', tuple(0 if self.rng.random() < 0.7 else 7 for _ in range(self.below(3))))

    def expr(self, depth, scope):
        r = self.rng.random()
        if depth == 0 or r < 0.15:
            r = self.rng.random()
            if r < 0.3:
                return ('val', self.atom(scope))
            if r < 0.6:
                return ('cat', self.atom(scope), self.atom(scope))
            if r < 0.7 and not self.exact:
                return ('tail', self.below(6), self.atom(scope))
            if r < 0.85:
                return ('recv', self.below(4))
            return ('hear', self.below(4))
        if r < 0.45:
            x = self.name()
            return ('let', x, self.expr(depth - 1, scope), self.expr(depth - 1, scope + [x]))
        if r < 0.70:
            s, p, a = self.name(), self.name(), self.name()
            return call3(s, p, a, self.atom(scope), self.atom(scope), self.below(4),
                         self.expr(depth - 1, scope + [s, p, a]))
        if r < 0.82 and not self.exact:
            return ('or', self.expr(depth - 1, scope), self.expr(depth - 1, scope))
        n, x, u = self.below(3), self.name(), self.name()
        if self.rng.random() < 0.5:
            body = self.expr(depth - 1, scope + [x, u])
            return ('iter', n, self.atom(scope), x, lambda i: ('let', u, ('recv', i % 3), body))
        y, z, y2, z2, st = (self.name() for _ in range(5))
        b1 = self.expr(depth - 1, scope + [y, z, u])
        b2 = self.expr(depth - 1, scope + [y, z, u, y2])
        body = ('split', y, z, var(x),
                ('let', y2, b1, ('let', z2, b2, ('val', ('pair', var(y2), var(z2))))))
        loop = ('iter', n, ('pair', self.atom(scope), self.atom(scope)), x,
                lambda i: ('let', u, ('recv', i % 3), body))
        return ('let', st, loop, ('split', y, z, var(st), ('cat', var(y), var(z))))


def random_programs(rng, wanted, exact):
    """Theorem 5.5 and Corollary 5.7 on random programs; with exact, Proposition 5.8."""
    gen, done, runs = Gen(rng, exact), 0, 0
    while done < wanted:
        e = gen.expr(4, [])
        sizes = Check(Q(1), Q(1))
        sizes.ty(e, {})
        if sizes.big > 2000:
            continue
        done += 1
        if exact:
            chk = Check(Q(1), Q(3))
            A, bound, _ = chk.ty(e, {})
            run, v = measure(e, Q(1), Q(3), 'worst', rng)
            assert run.cost == bound and len(v) == total(A), (run.cost, bound)
            runs += 1
            continue
        for rho, omega in PRICES:
            chk = Check(rho, omega)
            A, bound, _ = chk.ty(e, {})
            for mode in ('worst', 'random', 'random', 'random'):
                run, v = measure(e, rho, omega, mode, rng)
                assert run.cost <= bound, (run.cost, bound)
                assert inhabits(v, A, run.cache)
                assert run.peak <= chk.peak
                runs += 1
    return runs


def grid(top, ratio):
    out, x = [], 1.0
    while x <= top:
        if not out or int(x) > out[-1]:
            out.append(int(x))
        x *= ratio
    return out


def hierarchy(par, rho, omega):
    """The least overhead over a grid of fan-outs, and the exponents fitted to it.  The overhead
    of a hierarchy is its cost minus what its turns cost in isolation."""
    h, q, m, t, r, g = par
    alone = (q + m) + omega * m + rho * (h + t + q)

    def over(level, T, memo={}):
        if (level, T) not in memo:
            if level == 0:
                memo[level, T] = float(leaf_cost(T, par, rho, omega)) - alone * T
            else:
                memo[level, T] = min(
                    -(-T // n) * over(level - 1, n) + float(manager_cost(-(-T // n), par, rho, omega))
                    for n in grid(T, 1.02))
        return memo[level, T]
    lo, hi = 10 ** 12, 10 ** 15
    return [math.log(over(level, hi) / over(level, lo)) / math.log(hi / lo) for level in (0, 1, 2)]


def fmt(x, digits=0):
    return f'{float(x):,.{digits}f}'


def numbers():
    """The numbers of the examples in the paper."""
    rho, omega = Q(2, 25), Q(4)
    h, q, m, s, g, W, b = 10000, 500, 500, 2000, 100, 200000, 20000
    d = q + m
    out = {}

    # the plain loop
    def parts(T):
        N = T - 1
        return h + q + N * d, T * omega * m, rho * (N * (h + q) + d * tri(N))
    cross = next(T for T in count(1) if parts(T)[2] >= parts(T)[0] + parts(T)[1])
    out['Cross'] = fmt(cross)
    for T, name in ((100, 'Hundred'), (200, 'TwoHundred')):
        out['Cost' + name] = fmt(sum(parts(T)) / 10 ** 6, 2)
        out['Bare' + name] = fmt(plain_cost(T - 1, h, q, m, 1, omega) / 10 ** 6, 2)
    out['Double'] = fmt(sum(parts(200)) / sum(parts(100)), 1)
    out['RentShare'] = fmt(100 * parts(200)[2] / sum(parts(200)))

    # a person every j turns
    for j, name in ((1, 'One'), (5, 'Five'), (20, 'Twenty')):
        out['Rho' + name] = fmt(rho + (1 - rho) / j, 2)
    out['Question'] = fmt((1 - rho) * 100000)

    # compaction
    E = (1 + omega) * s + g + rho * h
    star = math.sqrt(2 * E / (rho * d))
    per_turn = lambda p: block_cost(p, h, q, m, s, g, rho, omega) / p
    best = min(range(1, 2000), key=per_turn)
    assert abs(best - star) <= 1
    full = (W - h - 2 * s - g) // d
    out['E'], out['Pstar'], out['Pbest'] = fmt(E), fmt(star, 1), fmt(best)
    out['PerTurnBest'], out['Pfull'], out['PerTurnFull'] = fmt(per_turn(best)), fmt(full), fmt(per_turn(full))
    out['CompShare'] = fmt(100 * per_turn(best) / per_turn(full))
    E1 = (1 + omega) * s + g + h
    out['PstarBare'] = fmt(math.sqrt(2 * E1 / d), 1)

    # the sliding window
    win = rho * h + b + q + omega * m
    first = next(i for i in count(1) if rho * (h + q + (i - 1) * d) + d + omega * m > win)
    out['WinTurn'], out['WinContext'], out['WinCost'] = fmt(first), fmt(h + first * d), fmt(win)
    out['WinLimit'] = fmt((b - m) / rho)
    Ew = (1 - rho) * (b - m)
    wstar = math.sqrt(2 * Ew / (rho * d))
    wper = lambda p: sblock_cost(p, b, h, q, m, rho, omega) / p
    wbest = min(range(1, 2000), key=wper)
    assert abs(wbest - wstar) <= 1
    out['StepE'], out['StepStar'], out['StepBest'] = fmt(Ew), fmt(wstar, 1), fmt(wbest)
    out['StepPerTurn'] = fmt(wper(wbest))

    # the instruction of the summary before the history
    extra = (1 - rho) * (h + s + q + (best - 1) * d)
    out['FirstExtra'] = fmt(extra)
    out['FirstShare'] = fmt(100 * extra / block_cost(best, h, q, m, s, g, rho, omega))

    # delegation
    slopes = hierarchy((50, 20, 20, 20, 20, 5), 0.08, 4.0)
    for name, slope, law in zip(('Zero', 'One', 'Two'), slopes, (2, 4 / 3, 8 / 7)):
        assert abs(slope - law) < 0.01, (slope, law)
        out['Slope' + name] = fmt(slope, 3)

    # five strategies side by side, in millions of units
    t, r = 1000, 2000
    par = (h, q, m, t, r, g)
    for T, name in ((100, 'Hundred'), (1000, 'Thousand'), (10000, 'TenK')):
        blocks = lambda p: -(-T // p)
        comp = lambda p: blocks(p) * block_cost(p, h, q, m, s, g, rho, omega) + (1 - rho) * h
        dele = lambda k: agent_cost((blocks(k),), k, par, rho, omega)
        step = lambda p: blocks(p) * sblock_cost(p, b, h, q, m, rho, omega) + (1 - rho) * h
        p, k = min(range(1, full + 1), key=comp), min(range(1, T + 1), key=dele)
        row = {'Bare': plain_cost(T - 1, h, q, m, 1, omega), 'Plain': plain_cost(T - 1, h, q, m, rho, omega),
               'Win': window_cost(T - 1, b, h, q, m, rho, omega), 'Comp': comp(p), 'Del': dele(k),
               'Step': min(step(p) for p in range(1, T + 1))}
        for key, c in row.items():
            out['Tab' + key + name] = fmt(c / 10 ** 6, 2)
        out['TabP' + name], out['TabK' + name] = fmt(p), fmt(k)
    out['Feasible'] = fmt((W - h - q - m) // d + 1)
    return out


def main(outdir):
    rng = random.Random(2026)
    lines = []
    cases = closed_forms(rng)
    lines.append(f'closed forms of Section 6: {cases} cases agree with the checker and with the semantics')
    runs = random_programs(rng, 3000, exact=False)
    lines.append(f'Theorem 5.5 and Corollary 5.7: 3000 random programs, {runs} evaluations within the bounds')
    runs = random_programs(rng, 1000, exact=True)
    lines.append(f'Proposition 5.8: {runs} random programs attain their bounds')
    for p_case in ((2000, 500, 500, 100, 10000), (8000, 300, 200, 0, 0), (500, 50, 950, 20, 3000)):
        s, q, m, g, h = p_case
        for rho, omega in PRICES[:3]:
            star = math.sqrt(2 * ((1 + omega) * s + g + rho * h) / (rho * (q + m)))
            best = min(range(1, 3000), key=lambda p: block_cost(p, h, q, m, s, g, rho, omega) / p)
            assert abs(best - star) <= 1, (best, star)
    lines.append('best period of compaction: within one turn of the square-root law in 9 cases')
    nums = numbers()
    lines.append('fitted exponents of delegation: ' + ', '.join(nums['Slope' + n] for n in ('Zero', 'One', 'Two')))
    nums['Cases'], nums['Programs'], nums['Exact'] = fmt(cases), fmt(3000), fmt(1000)
    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by cost.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
