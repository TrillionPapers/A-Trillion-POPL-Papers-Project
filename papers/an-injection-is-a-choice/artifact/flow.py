#!/usr/bin/env python3
"""Tests the claims of "An Injection Is a Choice" on an implementation of its two semantics.

The file has five parts.

1. Terms, predicates, and entailment.  The theory of the paper is parametric in the set of
   values; here the values are 0..4, so that entailment is decided by enumeration.
2. The type checker of Figure 3, in an algorithmic form that computes the least labels.
3. The real semantics of Figure 2 and the opaque semantics of Figure 4.  Each evaluation
   returns its value, its events and a log of its decisions, and each can be guided by the
   log of an evaluation in the other semantics.
4. A generator of random well-typed programs, and the programs of Sections 2 and 6.
5. The tests.  `python3 flow.py out` writes out/check.txt and out/numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import math
import random
import sys
from itertools import count, product

T, E, U = 0, 1, 2
STAR = '*'
V = range(5)
FUN = {'add': lambda a, b: min(a + b, 4), 'min': min, 'max': max}


# ---------------------------------------------------------------------------------------------
# 1. Terms ('c', n) | ('v', x) | ('f', name, args) and predicates
#    ('true',) | ('le', s, t) | ('eq', s, t) | ('not', p) | ('and', p, q) | ('or', p, q)
# ---------------------------------------------------------------------------------------------

def c(n):
    return ('c', n)


def v(x):
    return ('v', x)


def le(s, t):
    return ('le', s, t)


def eq(s, t):
    return ('eq', s, t)


def conj(p, q):
    return ('and', p, q)


def add(s, t):
    return ('f', 'add', (s, t))


TRUE = ('true',)
NU = v('nu')

# an action has an arity, a label for the results that the world returns, and a policy over
# the payload p0, p1
ACTIONS = {
    'read': (0, T, TRUE),
    'fetch': (1, U, le(v('p0'), c(2))),
    'pay': (1, T, le(v('p0'), c(3))),
    'send': (2, T, conj(eq(v('p0'), c(1)), le(v('p1'), c(2)))),
    'log': (1, T, TRUE),
    'file': (1, T, TRUE),
}


def fvt(t):
    if t[0] == 'c':
        return set()
    if t[0] == 'v':
        return {t[1]}
    return set().union(*[fvt(s) for s in t[2]])


def fvp(p):
    k = p[0]
    if k == 'true':
        return set()
    if k in ('le', 'eq'):
        return fvt(p[1]) | fvt(p[2])
    if k == 'not':
        return fvp(p[1])
    return fvp(p[1]) | fvp(p[2])


def subt(t, s):
    if t[0] == 'c':
        return t
    if t[0] == 'v':
        return s.get(t[1], t)
    return ('f', t[1], tuple(subt(a, s) for a in t[2]))


def subp(p, s):
    k = p[0]
    if k == 'true':
        return p
    if k in ('le', 'eq'):
        return (k, subt(p[1], s), subt(p[2], s))
    if k == 'not':
        return ('not', subp(p[1], s))
    return (k, subp(p[1], s), subp(p[2], s))


def tval(t, env):
    """The value of a term; STAR if it mentions an opaque value."""
    if t[0] == 'c':
        return t[1]
    if t[0] == 'v':
        return env[t[1]]
    args = [tval(s, env) for s in t[2]]
    return STAR if STAR in args else FUN[t[1]](*args)


def pval(p, env):
    """The truth of a predicate; STAR if it mentions an opaque value."""
    k = p[0]
    if k == 'true':
        return True
    if k in ('le', 'eq'):
        a, b = tval(p[1], env), tval(p[2], env)
        if STAR in (a, b):
            return STAR
        return a <= b if k == 'le' else a == b
    if k == 'not':
        r = pval(p[1], env)
        return STAR if r is STAR else not r
    a, b = pval(p[1], env), pval(p[2], env)
    if STAR in (a, b):
        return STAR
    return (a and b) if k == 'and' else (a or b)


CACHE = {}


def entails(Phi, goal):
    """Whether every assignment of values that satisfies Phi satisfies the goal.  Only
    hypotheses that share variables with the goal are used, and only while at most six
    variables are involved; dropping hypotheses is sound."""
    key = (tuple(Phi), goal)
    if key not in CACHE:
        names, hyps, rest, grew = set(fvp(goal)), [], list(Phi), True
        while grew:
            grew = False
            for h in rest[:]:
                if (not fvp(h) or fvp(h) & names) and len(names | fvp(h)) <= 6:
                    hyps.append(h)
                    names |= fvp(h)
                    rest.remove(h)
                    grew = True
        names = sorted(names)
        CACHE[key] = all(
            pval(goal, env) or not all(pval(h, env) for h in hyps)
            for env in (dict(zip(names, vals)) for vals in product(V, repeat=len(names))))
    return CACHE[key]


# ---------------------------------------------------------------------------------------------
# 2. Expressions and the type checker
#    ('term', t) | ('oracle', ts) | ('act', a, ts) | ('grd', a, ts) | ('ask', a, ts, x, e1, e2)
#    | ('let', x, e1, e2) | ('if', p, e1, e2) | ('check', t, x, p, e1, e2)
#    | ('iter', n, t, x, inv, body)
# ---------------------------------------------------------------------------------------------

class Ill(Exception):
    pass


def need(ok, why):
    if not ok:
        raise Ill(why)


def post(e):
    """What the checker records about the result of e, as a predicate over nu."""
    if e[0] == 'term':
        return eq(NU, e[1])
    if e[0] == 'iter':
        return e[4]
    return TRUE


def policy(a, ts):
    return subp(ACTIONS[a][2], {'p%d' % i: t for i, t in enumerate(ts)})


BROKEN = None       # the name of a rule that is deliberately broken, for the last test


def tc(e, G, Phi, pc, want=TRUE):
    """The least label of e at the program counter pc, or Ill.  The result satisfies want."""
    k = e[0]
    lab = lambda t: max([G[x] for x in fvt(t)], default=T)
    labs = lambda ts: max([lab(t) for t in ts], default=T)
    if k == 'term':
        need(entails(Phi, subp(want, {'nu': e[1]})), 'postcondition')
        return lab(e[1])
    if k == 'oracle':
        need(entails(Phi, want), 'postcondition')
        return T if BROKEN == 'oracle' else labs(e[1])
    if k == 'act':
        need(entails(Phi, want), 'postcondition')
        need(BROKEN == 'act' or max(labs(e[2]), pc) == T, 'a trusted action under influence')
        return ACTIONS[e[1]][1]
    if k == 'grd':
        need(entails(Phi, want), 'postcondition')
        need(BROKEN == 'grd' or max(labs(e[2]), pc) <= E, 'a guarded action on untrusted data')
        need(BROKEN == 'policy' or entails(Phi, policy(e[1], e[2])), 'policy')
        return ACTIONS[e[1]][1] if BROKEN == 'grd-result' else max(ACTIONS[e[1]][1], labs(e[2]))
    if k == 'ask':
        _, a, ts, x, e1, e2 = e
        l = labs(ts)
        inner = pc if BROKEN == 'ask-pc' else max(pc, l)
        lx = max(ACTIONS[a][1], l)
        l1 = tc(e1, {**G, x: lx}, Phi, inner, want)
        l2 = tc(e2, G, Phi, inner, want)
        return max(l1, l2) if BROKEN == 'ask-join' else max(l1, l2, l)
    if k == 'let':
        _, x, e1, e2 = e
        l1 = T if BROKEN == 'let' else tc(e1, G, Phi, pc)
        return tc(e2, {**G, x: l1}, Phi + [subp(post(e1), {'nu': v(x)})], pc, want)
    if k == 'if':
        _, p, e1, e2 = e
        l = max([G[x] for x in fvp(p)], default=T)
        inner = pc if BROKEN == 'if-pc' else max(pc, l)
        l1 = tc(e1, G, Phi + [p], inner, want)
        l2 = tc(e2, G, Phi + [('not', p)], inner, want)
        return max(l1, l2) if BROKEN == 'if-join' else max(l1, l2, l)
    if k == 'check':
        _, t, x, p, e1, e2 = e
        lp = max([G[y] for y in fvp(p) if y != x], default=T)
        lx = T if BROKEN == 'check-value' else min(lab(t), E)
        ld = lx if BROKEN == 'check-parameters' else max(lx, lp)
        inner = pc if BROKEN == 'check-pc' else max(pc, ld)
        l1 = tc(e1, {**G, x: lx}, Phi + [p, eq(v(x), t)], inner, want)
        l2 = tc(e2, G, Phi, inner, want)
        return max(l1, l2) if BROKEN == 'check-join' else max(l1, l2, ld)
    if k == 'iter':
        _, n, t, x, inv, body = e
        need(entails(Phi, subp(inv, {'nu': t})), 'invariant at the start')
        l = lab(t)
        while True:
            lb = tc(body, {**G, x: l}, Phi + [subp(inv, {'nu': v(x)})], pc, inv)
            if lb <= l or BROKEN == 'iter':
                break
            l = lb
        need(entails(Phi + [inv], want), 'postcondition')
        return l
    raise ValueError(k)


RULES = ('oracle', 'act', 'grd', 'policy', 'grd-result', 'ask-pc', 'ask-join', 'let',
         'if-pc', 'if-join', 'check-value', 'check-parameters', 'check-pc', 'check-join', 'iter')


# ---------------------------------------------------------------------------------------------
# 3. The two semantics
# ---------------------------------------------------------------------------------------------

class Mismatch(Exception):
    """A guided evaluation could not follow its guide: the theorem under test is false."""


def same(ok):
    if not ok:
        raise Mismatch()


class Rand:
    """Random decisions."""

    def __init__(self, rng):
        self.rng = rng

    def value(self, key):
        return int(self.rng.random() * len(V))

    def coin(self, key):
        return self.rng.random() < 0.6

    def option(self, n):
        return int(self.rng.random() * n)


class Fixed:
    """A model, a world and a person that answer as a function of the request, and a list of
    choices for the checks of opaque values.  Beyond the list every choice is the first one;
    the numbers of options are recorded."""

    def __init__(self, choices):
        self.choices, self.seen = list(choices), []

    def value(self, key):
        return sum(x for x in key if isinstance(x, int)) % len(V)

    def coin(self, key):
        return True

    def option(self, n):
        i = len(self.seen)
        self.seen.append(n)
        return self.choices[i] if i < len(self.choices) else 0


def source(e, x):
    """Whether e produces a value that the world or the model chooses freely."""
    return e[0] == 'oracle' or (e[0] in ('act', 'grd') and ACTIONS[e[1]][1] == U)


def rev(e, env, src, guide=None, force=None):
    """The real semantics.  The guide is the log of an opaque evaluation; force is a value
    that the next answer of the model or of the outside world must have."""
    k = e[0]
    g = guide if guide is not None and guide[0] != 'skip' else None
    if k == 'term':
        return tval(e[1], env), [], ('term',)
    if k == 'oracle':
        args = tuple(tval(t, env) for t in e[1])
        ans = force if force is not None else g[1] if g and g[1] is not STAR else src.value(args)
        return ans, [], ('oracle', ans)
    if k in ('act', 'grd'):
        args = tuple(tval(t, env) for t in e[2])
        res = force if force is not None else g[1] if g and g[1] is not STAR else src.value(args)
        return res, [(k, e[1], args)], (k, res)
    if k == 'ask':
        _, a, ts, x, e1, e2 = e
        args = tuple(tval(t, env) for t in ts)
        yes = g[1] if g else src.coin(args)
        if yes:
            res = g[2] if g and g[2] is not STAR else src.value(args)
            val, ev, sub = rev(e1, {**env, x: res}, src, g[3] if g else None)
            return val, [('ok', a, args)] + ev, ('ask', True, res, sub)
        val, ev, sub = rev(e2, env, src, g[3] if g else None)
        return val, [('no', a, args)] + ev, ('ask', False, None, sub)
    if k == 'let':
        _, x, e1, e2 = e
        g2 = g[2] if g else None
        forced = None
        if g2 and g2[0] in ('choose', 'refuse') and e2[0] == 'check' and e2[1] == v(x) and source(e1, x):
            forced = g2[1]
        v1, ev1, l1 = rev(e1, env, src, g[1] if g else None, forced)
        v2, ev2, l2 = rev(e2, {**env, x: v1}, src, g2)
        return v2, ev1 + ev2, ('let', l1, l2)
    if k == 'if':
        b = pval(e[1], env)
        same(g is None or g[1] == b)
        val, ev, sub = rev(e[2] if b else e[3], env, src, g[2] if g else None)
        return val, ev, ('if', b, sub)
    if k == 'check':
        _, t, x, p, e1, e2 = e
        cand = tval(t, env)
        ok = pval(p, {**env, x: cand})
        if g:
            same(g[0] == 'check' and g[1] == ok or g[0] == 'choose' and ok and g[1] == cand
                 or g[0] == 'refuse' and not ok)
        sub = None if g is None else g[3] if g[0] == 'check' else g[2]
        val, ev, sub = rev(e1, {**env, x: cand}, src, sub) if ok else rev(e2, env, src, sub)
        return val, ev, ('check', ok, cand, sub)
    if k == 'iter':
        _, n, t, x, inv, body = e
        acc, events, subs = tval(t, env), [], []
        for i in range(n):
            acc, ev, sub = rev(body, {**env, x: acc}, src, g[1][i] if g else None)
            events += ev
            subs.append(sub)
        return acc, events, ('iter', subs)
    raise ValueError(k)


SKIP = (STAR, [], ('skip',))


def aev(e, env, kappa, src, guide=None):
    """The opaque semantics at the level kappa.  The guide is the log of a real evaluation."""
    k = e[0]
    g = guide
    if k == 'term':
        return tval(e[1], env), [], ('term',)
    if k == 'oracle':
        args = tuple(tval(t, env) for t in e[1])
        ans = STAR if STAR in args else g[1] if g else src.value(args)
        return ans, [], ('oracle', ans)
    if k in ('act', 'grd'):
        args = tuple(tval(t, env) for t in e[2])
        if STAR in args:
            same(k == 'grd' and kappa == E)
            return SKIP
        res = STAR if ACTIONS[e[1]][1] == U else g[1] if g else src.value(args)
        return res, [(k, e[1], args)], (k, res)
    if k == 'ask':
        _, a, ts, x, e1, e2 = e
        args = tuple(tval(t, env) for t in ts)
        if STAR in args:
            return SKIP
        yes = g[1] if g else src.coin(args)
        if yes:
            res = STAR if ACTIONS[a][1] == U else g[2] if g else src.value(args)
            val, ev, sub = aev(e1, {**env, x: res}, kappa, src, g[3] if g else None)
            return val, [('ok', a, args)] + ev, ('ask', True, res, sub)
        val, ev, sub = aev(e2, env, kappa, src, g[3] if g else None)
        return val, [('no', a, args)] + ev, ('ask', False, None, sub)
    if k == 'let':
        _, x, e1, e2 = e
        v1, ev1, l1 = aev(e1, env, kappa, src, g[1] if g else None)
        v2, ev2, l2 = aev(e2, {**env, x: v1}, kappa, src, g[2] if g else None)
        return v2, ev1 + ev2, ('let', l1, l2)
    if k == 'if':
        b = pval(e[1], env)
        if b is STAR:
            return SKIP
        same(g is None or g[1] == b)
        val, ev, sub = aev(e[2] if b else e[3], env, kappa, src, g[2] if g else None)
        return val, ev, ('if', b, sub)
    if k == 'check':
        _, t, x, p, e1, e2 = e
        cand = tval(t, env)
        if any(env[y] is STAR for y in fvp(p) if y != x):
            return SKIP
        if cand is not STAR:
            ok = pval(p, {**env, x: cand})
            same(g is None or g[1] == ok)
            sub = g[3] if g else None
            val, ev, sub = (aev(e1, {**env, x: cand}, kappa, src, sub) if ok
                            else aev(e2, env, kappa, src, sub))
            return val, ev, ('check', ok, cand, sub)
        if kappa == E:
            return SKIP
        accept = [w for w in V if pval(p, {**env, x: w})]
        reject = [w for w in V if not pval(p, {**env, x: w})]
        if g:
            choice = g[2]
            same(choice in (accept if g[1] else reject))
            ok = g[1]
        else:
            i = src.option(len(accept) + (1 if reject else 0))
            ok = i < len(accept)
            choice = accept[i] if ok else reject[0]
        sub = g[3] if g else None
        if ok:
            val, ev, sub = aev(e1, {**env, x: choice}, kappa, src, sub)
            return val, ev, ('choose', choice, sub)
        val, ev, sub = aev(e2, env, kappa, src, sub)
        return val, ev, ('refuse', choice, sub)
    if k == 'iter':
        _, n, t, x, inv, body = e
        acc, events, subs = tval(t, env), [], []
        for i in range(n):
            acc, ev, sub = aev(body, {**env, x: acc}, kappa, src, g[1][i] if g else None)
            events += ev
            subs.append(sub)
        return acc, events, ('iter', subs)
    raise ValueError(k)


def visible(events, kappa):
    """The trusted actions, and at the level U also the guarded ones."""
    return [ev for ev in events if ev[0] == 'act' or (ev[0] == 'grd' and kappa == U)]


# ---------------------------------------------------------------------------------------------
# 4. Random programs, and the programs of the paper
# ---------------------------------------------------------------------------------------------

class Gen:
    """Random closed programs that the checker accepts.  With paired=True every check is
    applied to a value that the model has just produced."""

    def __init__(self, rng, paired):
        self.rng, self.paired, self.names = rng, paired, count()

    def below(self, n):
        return int(self.rng.random() * n)

    def one(self, xs):
        return xs[self.below(len(xs))]

    def name(self):
        return 'x%d' % next(self.names)

    def term(self, G, most=U):
        pool = [v(x) for x in G if G[x] <= most]
        r = self.rng.random()
        if pool and r < 0.6:
            return self.one(pool)
        if pool and r < 0.75:
            return ('f', self.one(['add', 'min', 'max']), (self.one(pool), self.term(G, most)))
        return c(self.below(len(V)))

    def pred(self, G, most=U):
        r = self.rng.random()
        if r < 0.5:
            return le(self.term(G, most), c(self.below(len(V))))
        if r < 0.8:
            return eq(self.term(G, most), self.term(G, most))
        return ('not', le(self.term(G, most), self.term(G, most)))

    def guard(self, x, G):
        """A predicate for a check of x; its other variables are not untrusted."""
        r = self.rng.random()
        if r < 0.4:
            return le(v(x), c(self.below(len(V))))
        if r < 0.6:
            return conj(le(c(self.below(3)), v(x)), le(v(x), c(2 + self.below(3))))
        if r < 0.8:
            return le(v(x), self.term(G))
        return eq(v(x), self.term(G))

    def expr(self, depth, G, Phi, pc):
        r = self.rng.random()
        if depth == 0 or r < 0.12:
            return self.leaf(G, Phi, pc)
        if r < 0.40:
            x, e1 = self.name(), self.expr(depth - 1, G, Phi, pc)
            l1 = tc(e1, G, Phi, pc)
            e2 = self.expr(depth - 1, {**G, x: l1}, Phi + [subp(post(e1), {'nu': v(x)})], pc)
            return ('let', x, e1, e2)
        if r < 0.52:
            p = self.pred(G)
            l = max(pc, max([G[y] for y in fvp(p)], default=T))
            return ('if', p, self.expr(depth - 1, G, Phi + [p], l),
                    self.expr(depth - 1, G, Phi + [('not', p)], l))
        if r < 0.80:
            return self.check(depth, G, Phi, pc)
        if r < 0.90:
            a = self.one(['pay', 'send', 'log', 'fetch'])
            ts = tuple(self.term(G) for _ in range(ACTIONS[a][0]))
            l = max([G[y] for t in ts for y in fvt(t)], default=T)
            x = self.name()
            return ('ask', a, ts, x,
                    self.expr(depth - 1, {**G, x: max(ACTIONS[a][1], l)}, Phi, max(pc, l)),
                    self.expr(depth - 1, G, Phi, max(pc, l)))
        n, t, x = self.below(4), self.term(G), self.name()
        l = max([G[y] for y in fvt(t)], default=T)
        body = self.expr(depth - 1, {**G, x: l}, Phi, pc)
        if tc(body, {**G, x: l}, Phi, pc) > l:
            body = self.expr(depth - 1, {**G, x: U}, Phi, pc)
        return ('iter', n, t, x, TRUE, body)

    def check(self, depth, G, Phi, pc):
        x = self.name()
        if self.paired:
            y = self.name()
            made = ('oracle', tuple(self.term(G) for _ in range(1 + self.below(2))))
            G = {**G, y: tc(made, G, Phi, pc)}
            t = v(y)
        else:
            t = self.term(G)
        p = self.guard(x, G)
        lx = min(max([G[z] for z in fvt(t)], default=T), E)
        ld = max(lx, max([G[z] for z in fvp(p) if z != x], default=T))
        e = ('check', t, x, p,
             self.expr(depth - 1, {**G, x: lx}, Phi + [p, eq(v(x), t)], max(pc, ld)),
             self.expr(depth - 1, G, Phi, max(pc, ld)))
        return ('let', y, made, e) if self.paired else e

    def leaf(self, G, Phi, pc):
        r = self.rng.random()
        if r < 0.2:
            return ('term', self.term(G))
        if r < 0.4:
            return ('oracle', tuple(self.term(G) for _ in range(1 + self.below(2))))
        a = self.one(['read', 'fetch', 'pay', 'send', 'log'])
        if pc == T and r < 0.7:
            return ('act', a, tuple(self.term(G, T) for _ in range(ACTIONS[a][0])))
        if pc <= E:
            for _ in range(6):
                ts = tuple(self.term(G, E) for _ in range(ACTIONS[a][0]))
                if entails(Phi, policy(a, ts)):
                    return ('grd', a, ts)
        return ('term', self.term(G))


class Wild(Gen):
    """Random closed programs made without regard to the typing rules.  The tests keep those
    that the checker accepts, so a checker with a broken rule lets wrong programs through."""

    def expr(self, depth, G, Phi=None, pc=None):
        r = self.rng.random()
        if depth == 0 or r < 0.15:
            r = self.rng.random()
            if r < 0.2:
                return ('term', self.term(G))
            if r < 0.4:
                return ('oracle', tuple(self.term(G) for _ in range(1 + self.below(2))))
            a = self.one(['read', 'fetch', 'pay', 'send', 'log', 'log'])
            return ('act' if r < 0.6 else 'grd', a, tuple(self.term(G) for _ in range(ACTIONS[a][0])))
        if r < 0.42:
            x = self.name()
            return ('let', x, self.expr(depth - 1, G), self.expr(depth - 1, {**G, x: U}))
        if r < 0.54:
            return ('if', self.pred(G), self.expr(depth - 1, G), self.expr(depth - 1, G))
        if r < 0.80:
            x, G1 = self.name(), G
            if self.paired:
                y = self.name()
                made, t, G1 = ('oracle', tuple(self.term(G) for _ in range(1 + self.below(2)))), v(y), {**G, y: U}
            else:
                t = self.term(G)
            p = self.guard(x, G1)
            # half of the time the checked value is used at once in a guarded action
            then = (('grd', self.one(['pay', 'fetch', 'log']), (v(x),)) if self.rng.random() < 0.5
                    else self.expr(depth - 1, {**G1, x: U}))
            e = ('check', t, x, p, then, self.expr(depth - 1, G1))
            return ('let', y, made, e) if self.paired else e
        if r < 0.90:
            a = self.one(['pay', 'send', 'log', 'fetch'])
            x = self.name()
            return ('ask', a, tuple(self.term(G) for _ in range(ACTIONS[a][0])), x,
                    self.expr(depth - 1, {**G, x: U}), self.expr(depth - 1, G))
        x = self.name()
        return ('iter', self.below(4), self.term(G), x, TRUE, self.expr(depth - 1, {**G, x: U}))


def let(x, e1, e2):
    return ('let', x, e1, e2)


def term(t):
    return ('term', t)


ASK_PAY = ('ask', 'pay', (v('p'),), 'r', term(v('r')), term(c(0)))


def invoice(kind):
    """An agent that reads an invoice and pays it; the variants of Section 2."""
    body = {
        'plain': ('act', 'pay', (v('p'),)),
        'ask': ASK_PAY,
        'judge': let('j', ('oracle', (v('p'),)),
                     ('if', eq(v('j'), c(1)), ('grd', 'pay', (v('p'),)), term(c(0)))),
        'check': ('check', v('p'), 'x', le(v('x'), c(3)), ('grd', 'pay', (v('x'),)), ASK_PAY),
        'limit-from-page': let('lim', ('oracle', (v('m'),)),
                               ('check', v('p'), 'x', le(v('x'), v('lim')),
                                ('grd', 'pay', (v('x'),)), term(c(0)))),
        'limit-from-user': let('lim', ('act', 'read', ()),
                               ('check', v('p'), 'x', le(v('x'), v('lim')),
                                ('if', le(v('lim'), c(3)), ('grd', 'pay', (v('x'),)), ASK_PAY),
                                term(c(0)))),
    }[kind]
    return let('m', ('act', 'fetch', (c(0),)), let('p', ('oracle', (v('m'),)), body))


def payments(n, budget):
    """n invoices; with a budget the total of the payments stays within 3."""
    ok = conj(le(v('x'), c(3)), le(add(v('s'), v('x')), c(3))) if budget else le(v('x'), c(3))
    body = let('m', ('act', 'fetch', (c(0),)), let('p', ('oracle', (v('m'),)),
               ('check', v('p'), 'x', ok,
                let('r', ('grd', 'pay', (v('x'),)), term(add(v('s'), v('x')))), term(v('s')))))
    return ('iter', n, c(0), 's', le(NU, c(3)) if budget else TRUE, body)


def routing():
    """The model picks one of three routes; the check admits nothing else."""
    route = lambda i: ('grd', 'file', (c(i),))
    return let('m', ('act', 'fetch', (c(0),)), let('k', ('oracle', (v('m'),)),
               ('check', v('k'), 'x', conj(le(c(1), v('x')), le(v('x'), c(3))),
                ('if', eq(v('x'), c(1)), route(1), ('if', eq(v('x'), c(2)), route(2), route(3))),
                term(c(0)))))


# ---------------------------------------------------------------------------------------------
# 5. The tests
# ---------------------------------------------------------------------------------------------

def well_typed(e):
    try:
        tc(e, {}, [], T)
        return True
    except Ill:
        return False


def related(real, opaque, label, kappa):
    return opaque == real or (opaque is STAR and label >= kappa)


def examine(e, label, src, paired):
    """One evaluation of a well-typed program and the checks of the theorems on it."""
    if paired:
        # Theorem 5.6: an opaque evaluation is matched by a real one
        a, aevents, alog = aev(e, {}, U, src)
        val, events, _ = rev(e, {}, src, alog)
        assert visible(events, U) == visible(aevents, U) and related(val, a, label, U)
        return
    val, events, log = rev(e, {}, src)
    # Theorem 5.1: guarded actions are within their policies
    for kind, a, args in events:
        assert kind != 'grd' or pval(policy(a, [c(w) for w in args]), {})
    # Theorem 5.4: a real evaluation is matched by an opaque one, at both levels
    for kappa in (E, U):
        a, aevents, _ = aev(e, {}, kappa, src, log)
        assert visible(aevents, kappa) == visible(events, kappa)
        assert related(val, a, label, kappa)


def random_programs(rng, wanted, paired, wild):
    gen, src, runs, done = (Wild if wild else Gen)(rng, paired), Rand(rng), 0, 0
    while done < wanted:
        e = gen.expr(5, {}, [], T)
        try:
            label = tc(e, {}, [], T)
        except Ill:
            assert wild
            continue
        done += 1
        for _ in range(4):
            examine(e, label, src, paired)
            runs += 1
    return runs


def probe():
    """The result of a guarded action on an endorsed value, used in a trusted action.  The
    random search rarely builds this flow, so the last test tries it first."""
    return let('m', ('act', 'fetch', (c(0),)), let('k', ('oracle', (v('m'),)),
               let('y', ('check', v('k'), 'x', le(v('x'), c(4)), term(v('x')), term(c(0))),
                   let('r', ('grd', 'file', (v('y'),)), ('act', 'log', (v('r'),))))))


def caught(rule, rng, limit=60000):
    """The number of programs tried until the tests find one that a checker with this rule
    broken accepts and that violates a theorem; None if there is none within the limit."""
    global BROKEN
    BROKEN = rule
    CACHE.clear()
    gen, src = Wild(rng, False), Rand(rng)
    try:
        for i in range(limit):
            e = probe() if i == 0 else gen.expr(4, {})
            try:
                label = tc(e, {}, [], T)
            except Ill:
                continue
            try:
                for _ in range(4):
                    examine(e, label, src, False)
            except (AssertionError, Mismatch):
                return i + 1
        return None
    finally:
        BROKEN = None
        CACHE.clear()


def traces(e):
    """The clean traces of the opaque semantics when the model, the world and the person are
    fixed functions, with the largest number of choices on a path and the largest bound."""
    found, todo, depth, bound = set(), [[]], 0, 1
    while todo:
        prefix = todo.pop()
        src = Fixed(prefix)
        _, events, _ = aev(e, {}, U, src)
        found.add(tuple(visible(events, U)))
        depth = max(depth, len(src.seen))
        bound = max(bound, math.prod(src.seen))
        for i in range(len(prefix), len(src.seen)):
            for j in range(1, src.seen[i]):
                todo.append(src.choices[:i] + [0] * (i - len(prefix)) + [j])
    return found, depth, bound


def paid(events):
    return sum(args[0] for kind, a, args in events if kind == 'grd' and a == 'pay')


def fmt(x):
    return f'{x:,}'


def main(outdir):
    rng = random.Random(2026)
    lines, nums = [], {}

    verdicts = {kind: well_typed(invoice(kind)) for kind in
                ('plain', 'ask', 'judge', 'check', 'limit-from-page', 'limit-from-user')}
    assert verdicts == {'plain': False, 'ask': True, 'judge': False, 'check': True,
                        'limit-from-page': False, 'limit-from-user': True}
    assert well_typed(routing()) and well_typed(payments(4, True)) and well_typed(payments(4, False))
    assert not well_typed(probe())
    lines.append('the checker accepts and rejects the programs of Sections 2 and 6 as the paper says')

    runs = (random_programs(rng, 3000, paired=False, wild=False)
            + random_programs(rng, 3000, paired=False, wild=True))
    lines.append(f'Theorems 5.1 and 5.4: 6000 random programs, {runs} evaluations, '
                 f'each matched at both levels')
    nums['Programs'], nums['Runs'] = fmt(6000), fmt(runs)
    runs = (random_programs(rng, 3000, paired=True, wild=False)
            + random_programs(rng, 3000, paired=True, wild=True))
    lines.append(f'Theorem 5.6: 6000 random programs, {runs} opaque evaluations, each matched')
    nums['Paired'], nums['PairedRuns'] = fmt(6000), fmt(runs)
    tries = {rule: caught(rule, rng) for rule in RULES}
    assert all(tries.values()), tries
    lines.append(f'{len(RULES)} checkers with one broken rule each: the tests reject every one, after '
                 + ', '.join(f'{rule} {n}' for rule, n in tries.items()) + ' programs')
    nums['Rules'], nums['Slowest'] = fmt(len(RULES)), fmt(max(tries.values()))

    # the budget: the worst totals over all choices, and by Theorem 5.6 they are attainable
    for budget, name in ((True, 'With'), (False, 'Without')):
        e = payments(4, budget)
        found, depth, bound = traces(e)
        worst = max(paid(tr) for tr in found)
        assert worst == (3 if budget else 12)
        src = Rand(rng)
        assert all(paid(rev(e, {}, src)[1]) <= worst for _ in range(2000))
        nums['Total' + name], nums['Traces' + name], nums['Bound' + name] = fmt(worst), fmt(len(found)), fmt(bound)
    lines.append(f"four invoices: the payments total at most {nums['TotalWith']} with the budget "
                 f"and {nums['TotalWithout']} without it")

    found, depth, bound = traces(routing())
    assert len(found) == 4 == bound and depth == 1
    nums['Routes'] = fmt(len(found))
    found, depth, bound = traces(invoice('check'))
    nums['InvoiceTraces'], nums['InvoiceBound'] = fmt(len(found)), fmt(bound)
    assert len(found) <= bound
    lines.append(f"clean traces under attack: routing {nums['Routes']}, one invoice "
                 f"{nums['InvoiceTraces']}, four invoices with a budget {nums['TracesWith']} "
                 f"of at most {nums['BoundWith']}")

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by flow.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
