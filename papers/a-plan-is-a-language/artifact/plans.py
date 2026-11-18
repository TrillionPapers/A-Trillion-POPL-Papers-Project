#!/usr/bin/env python3
"""Tests the claims of "A Plan Is a Language" on an implementation of its calculus.

The file has six parts.

1. Terms and predicates over the values 0..3.
2. Regular expressions over the letters (action, payload), with shuffle: derivatives, and the
   test whether the authority of some expressions, interleaved, lies within that of another.
3. Plans, which are such expressions with variables, and the type checker of Figures 3 and 4.
4. The semantics of Figure 2 in two forms: with named tokens and a ledger, and without both.
5. Random plans and programs.
6. The tests.  `python3 plans.py out` writes out/check.txt and out/numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import random
import sys
from functools import lru_cache
from itertools import count, product

V = range(4)
ACTIONS = ('edit', 'test', 'push')
LETTERS = [(a, n) for a in ACTIONS for n in V]


# ---------------------------------------------------------------------------------------------
# 1. Terms ('c', n) | ('v', x) | ('add', s, t); predicates ('true',) | ('le', s, t)
#    | ('eq', s, t) | ('not', p) | ('and', p, q).  The payload of a letter is the variable 'p'.
# ---------------------------------------------------------------------------------------------

TRUE = ('true',)


def c(n):
    return ('c', n)


def v(x):
    return ('v', x)


def le(s, t):
    return ('le', s, t)


def eq(s, t):
    return ('eq', s, t)


def var(y):
    return ('var', y)


def fvt(t):
    if t[0] == 'c':
        return frozenset()
    if t[0] == 'v':
        return frozenset([t[1]])
    return fvt(t[1]) | fvt(t[2])


def fvp(p):
    if p[0] == 'true':
        return frozenset()
    if p[0] == 'not':
        return fvp(p[1])
    if p[0] == 'and':
        return fvp(p[1]) | fvp(p[2])
    return fvt(p[1]) | fvt(p[2])


def tval(t, env):
    if t[0] == 'c':
        return t[1]
    if t[0] == 'v':
        return env[t[1]]
    return min(tval(t[1], env) + tval(t[2], env), V[-1])


def pval(p, env):
    if p[0] == 'true':
        return True
    if p[0] == 'not':
        return not pval(p[1], env)
    if p[0] == 'and':
        return pval(p[1], env) and pval(p[2], env)
    a, b = tval(p[1], env), tval(p[2], env)
    return a <= b if p[0] == 'le' else a == b


MODELS = {}


def models(Phi, names):
    """The assignments to `names`, and to the variables that share a fact with them, that
    satisfy these facts.  To leave a fact out is sound."""
    key = (tuple(Phi), frozenset(names))
    if key not in MODELS:
        names, hyps, rest, grew = set(names), [], list(Phi), True
        while grew:
            grew = False
            for h in rest[:]:
                if (not fvp(h) or fvp(h) & names) and len(names | fvp(h)) <= 6:
                    hyps.append(h)
                    names |= fvp(h)
                    rest.remove(h)
                    grew = True
        names = sorted(names)
        MODELS[key] = [env for env in (dict(zip(names, vals)) for vals in product(V, repeat=len(names)))
                       if all(pval(h, env) for h in hyps)]
    return MODELS[key]


# ---------------------------------------------------------------------------------------------
# 2. Regular expressions: ('0',) | ('1',) | ('sym', letters) | ('seq', r, s) | ('alt', {r})
#    | ('star', r) | ('par', r, s)
# ---------------------------------------------------------------------------------------------

ZERO, ONE = ('0',), ('1',)


def sym(letters):
    return ('sym', frozenset(letters)) if letters else ZERO


def seq(r, s):
    if r == ZERO or s == ZERO:
        return ZERO
    if r == ONE:
        return s
    if s == ONE:
        return r
    if r[0] == 'seq':
        return seq(r[1], seq(r[2], s))
    return ('seq', r, s)


def alt(*rs):
    parts, letters = set(), set()
    for r in rs:
        for q in (r[1] if r[0] == 'alt' else [r]):
            if q[0] == 'sym':
                letters |= q[1]
            elif q != ZERO:
                parts.add(q)
    if letters:
        parts.add(('sym', frozenset(letters)))
    if not parts:
        return ZERO
    return next(iter(parts)) if len(parts) == 1 else ('alt', frozenset(parts))


def star(r):
    if r in (ZERO, ONE):
        return ONE
    return r if r[0] == 'star' else ('star', r)


def par(r, s):
    if r == ZERO or s == ZERO:
        return ZERO
    if r == ONE:
        return s
    if s == ONE:
        return r
    return ('par',) + tuple(sorted((r, s), key=repr))


@lru_cache(maxsize=None)
def nullable(r):
    k = r[0]
    if k in ('1', 'star'):
        return True
    if k in ('0', 'sym'):
        return False
    if k in ('seq', 'par'):
        return nullable(r[1]) and nullable(r[2])
    return any(nullable(q) for q in r[1])


@lru_cache(maxsize=None)
def deriv(r, letter):
    """What is left of r after a letter."""
    k = r[0]
    if k in ('0', '1'):
        return ZERO
    if k == 'sym':
        return ONE if letter in r[1] else ZERO
    if k == 'seq':
        d = seq(deriv(r[1], letter), r[2])
        return alt(d, deriv(r[2], letter)) if nullable(r[1]) else d
    if k == 'alt':
        return alt(*[deriv(q, letter) for q in r[1]])
    if k == 'star':
        return seq(deriv(r[1], letter), r)
    return alt(par(deriv(r[1], letter), r[2]), par(r[1], deriv(r[2], letter)))


@lru_cache(maxsize=None)
def alive(r):
    """Whether r has a word at all."""
    k = r[0]
    if k == '0':
        return False
    if k in ('1', 'star', 'sym'):
        return True
    if k in ('seq', 'par'):
        return alive(r[1]) and alive(r[2])
    return any(alive(q) for q in r[1])


def beyond(parts, whole, limit=3000):
    """The authority of r is the set of the prefixes of its words, with the empty word.  Returns
    a word that is an interleaving of words from the authorities of `parts` and that is not in
    the authority of `whole`; None if there is none.  A search that grows too large returns
    the empty word, which errs on the side of refusing."""
    start = (frozenset([tuple(parts)]), whole)
    seen, work = {start}, [(start, ())]
    while work:
        (states, r), word = work.pop()
        for letter in LETTERS:
            nxt = set()
            for state in states:
                for i, q in enumerate(state):
                    d = deriv(q, letter)
                    if alive(d):
                        nxt.add(state[:i] + (d,) + state[i + 1:])
            if not nxt:
                continue
            d = deriv(r, letter)
            if not alive(d):
                return word + (letter,)
            pair = (frozenset(nxt), d)
            if pair not in seen:
                if len(seen) >= limit:
                    return ()
                seen.add(pair)
                work.append((pair, word + (letter,)))
    return None


def within(parts, whole):
    return beyond(parts, whole) is None


def inside(r, word):
    """Whether a word is in the authority of r."""
    for letter in word:
        r = deriv(r, letter)
    return not word or alive(r)


# ---------------------------------------------------------------------------------------------
# 3. Plans: ('zero',) | ('eps',) | ('letter', a, phi) | ('seq', P, Q) | ('alt', P, Q)
#    | ('star', P) | ('par', P, Q) | ('der', P, a, t), the last for what is left of P after the
#    action a with payload t.  Types: BASE | UNIT | ('prod', A, B) | ('sum', A, B) | ('plan', P).
#    Operands: ('var', y) | ('tm', t) | ('unit',) | ('pair', w, w) | ('inl', w, B)
#    | ('inr', w, A) | ('as', w, A).  Expressions:
#    ('ret', w) | ('letb', x, e, e) | ('letr', y, e, e) | ('letp', y, y, w, e)
#    | ('case', w, y, e, y, e) | ('if', p, e, e) | ('model',) | ('ask', P)
#    | ('act', a, t, w, x, y, e) | ('split', w, P, P) | ('run', A, B, t, w) | ('iter', n, A, w, y, e)
# ---------------------------------------------------------------------------------------------

BASE, UNIT, EPS = ('base',), ('unit',), ('eps',)


def letter(a, phi=TRUE):
    return ('letter', a, phi)


def fvplan(P):
    k = P[0]
    if k in ('zero', 'eps'):
        return frozenset()
    if k == 'letter':
        return fvp(P[2]) - {'p'}
    if k == 'star':
        return fvplan(P[1])
    if k == 'der':
        return fvplan(P[1]) | fvt(P[3])
    return fvplan(P[1]) | fvplan(P[2])


def fvty(A):
    if A[0] in ('prod', 'sum'):
        return fvty(A[1]) | fvty(A[2])
    return fvplan(A[1]) if A[0] == 'plan' else frozenset()


CLOSED = {}


def close(P, env):
    """The regular expression of a plan under values for its variables."""
    key = (P, tuple(sorted((x, env[x]) for x in fvplan(P))))
    if key not in CLOSED:
        k = P[0]
        if k == 'zero':
            r = ZERO
        elif k == 'eps':
            r = ONE
        elif k == 'letter':
            r = sym((P[1], n) for n in V if pval(P[2], {**env, 'p': n}))
        elif k == 'star':
            r = star(close(P[1], env))
        elif k == 'der':
            r = deriv(close(P[1], env), (P[2], tval(P[3], env)))
        else:
            r = {'seq': seq, 'alt': alt, 'par': par}[k](close(P[1], env), close(P[2], env))
        CLOSED[key] = r
    return CLOSED[key]


BROKEN = None       # the name of a rule that is deliberately broken, for the last test

RULES = ('contraction', 'branch', 'loop', 'shadow', 'act', 'residual', 'split', 'narrow', 'if-fact', 'run')


class Ill(Exception):
    pass


def need(ok, why):
    if not ok:
        raise Ill(why)


def allowed(Phi, P, a, t):
    """Whether the facts entail that the plan has a word that begins with this action."""
    return all(alive(deriv(close(P, env), (a, tval(t, env)))) for env in models(Phi, fvplan(P) | fvt(t)))


def contained(Phi, parts, whole):
    """Whether the facts entail that the parts, interleaved, stay within the whole."""
    names = fvplan(whole).union(*[fvplan(Q) for Q in parts])
    return all(within([close(Q, env) for Q in parts], close(whole, env)) for env in models(Phi, names))


def subtype(Phi, A, B):
    """Whether a value of type A may be used where B is expected."""
    if A[0] != B[0]:
        return False
    if A[0] in ('prod', 'sum'):
        return subtype(Phi, A[1], B[1]) and subtype(Phi, A[2], B[2])
    if A[0] == 'plan':
        # a token for a plan serves for every plan that it contains
        return BROKEN == 'narrow' or contained(Phi, [B[1]], A[1])
    return True


def without(D, used):
    return {y: A for y, A in D.items() if y not in used}


def wtype(w, Phi, G, D):
    """The type of an operand and the resources it uses."""
    k = w[0]
    if k == 'var':
        need(w[1] in D, 'a resource that is not available')
        return D[w[1]], {w[1]}
    if k == 'tm':
        need(fvt(w[1]) <= G, 'an unbound base variable')
        return BASE, set()
    if k == 'unit':
        return UNIT, set()
    if k == 'pair':
        A, u1 = wtype(w[1], Phi, G, D)
        B, u2 = wtype(w[2], Phi, G, D if BROKEN == 'contraction' else without(D, u1))
        return ('prod', A, B), u1 | u2
    if k == 'inl':
        A, u = wtype(w[1], Phi, G, D)
        return ('sum', A, w[2]), u
    if k == 'inr':
        B, u = wtype(w[1], Phi, G, D)
        return ('sum', w[2], B), u
    if k == 'as':
        A, u = wtype(w[1], Phi, G, D)
        need(fvty(w[2]) <= G, 'an unbound base variable')
        need(subtype(Phi, A, w[2]), 'a plan that the token does not contain')
        return w[2], u
    raise Ill('an operand of a program')


def join(Phi, A, B):
    if subtype(Phi, A, B):
        return B
    need(subtype(Phi, B, A), 'branches of different types')
    return A


def tc(e, Phi, G, D):
    """The type of an expression and the resources it uses."""
    k = e[0]
    rest = (lambda used: D) if BROKEN == 'contraction' else (lambda used: without(D, used))
    if k == 'ret':
        return wtype(e[1], Phi, G, D)
    if k == 'letb':
        _, x, e1, e2 = e
        need(BROKEN == 'shadow' or x not in G, 'a base variable that is bound twice')
        A, u1 = tc(e1, Phi, G, D)
        need(A == BASE, 'a base binding of a resource')
        B, u2 = tc(e2, Phi, G | {x}, rest(u1))
        need(x not in fvty(B), 'a type that mentions a local variable')
        return B, u1 | u2
    if k == 'letr':
        _, y, e1, e2 = e
        A, u1 = tc(e1, Phi, G, D)
        B, u2 = tc(e2, Phi, G, {**rest(u1), y: A})
        return B, u1 | (u2 - {y})
    if k == 'letp':
        _, y1, y2, w, e1 = e
        A, u1 = wtype(w, Phi, G, D)
        need(A[0] == 'prod', 'a pair pattern on another type')
        B, u2 = tc(e1, Phi, G, {**rest(u1), y1: A[1], y2: A[2]})
        return B, u1 | (u2 - {y1, y2})
    if k == 'case':
        _, w, y1, e1, y2, e2 = e
        A, u = wtype(w, Phi, G, D)
        need(A[0] == 'sum', 'a case on another type')
        B1, u1 = tc(e1, Phi, G, {**rest(u), y1: A[1]})
        B2, u2 = tc(e2, Phi, G, {**rest(u), y2: A[2]})
        u1, u2 = u1 - {y1}, u2 - {y2}
        return join(Phi, B1, B2), u | (u1 & u2 if BROKEN == 'branch' else u1 | u2)
    if k == 'if':
        _, p, e1, e2 = e
        need(fvp(p) <= G, 'an unbound base variable')
        B1, u1 = tc(e1, Phi + [p], G, D)
        B2, u2 = tc(e2, Phi + [p if BROKEN == 'if-fact' else ('not', p)], G, D)
        return join(Phi, B1, B2), u1 & u2 if BROKEN == 'branch' else u1 | u2
    if k == 'model':
        return BASE, set()
    if k == 'ask':
        need(fvplan(e[1]) <= G, 'an unbound base variable')
        return ('sum', ('plan', e[1]), UNIT), set()
    if k == 'act':
        _, a, t, w, x, y, body = e
        need(fvt(t) <= G, 'an unbound base variable')
        need(BROKEN == 'shadow' or x not in G, 'a base variable that is bound twice')
        A, u = wtype(w, Phi, G, D)
        need(A[0] == 'plan', 'an action without a plan')
        need(BROKEN == 'act' or allowed(Phi, A[1], a, t), 'an action that the plan does not allow')
        left = A[1] if BROKEN == 'residual' else ('der', A[1], a, t)
        B, u2 = tc(body, Phi, G | {x}, {**rest(u), y: ('plan', left)})
        need(x not in fvty(B), 'a type that mentions a local variable')
        return B, u | (u2 - {y})
    if k == 'split':
        _, w, P1, P2 = e
        need(fvplan(P1) | fvplan(P2) <= G, 'an unbound base variable')
        A, u = wtype(w, Phi, G, D)
        need(A[0] == 'plan', 'a split of another type')
        need(BROKEN == 'split' or contained(Phi, [P1, P2], A[1]), 'parts that go beyond the plan')
        return ('prod', ('plan', P1), ('plan', P2)), u
    if k == 'run':
        _, A, B, t, w = e
        need(fvt(t) <= G and not fvty(A) and not fvty(B), 'an open type for code')
        A1, u = wtype(w, Phi, G, D)
        need(subtype(Phi, A1, A), 'the argument of the code')
        return ('sum', B, A), u
    if k == 'iter':
        _, n, A, w, y, body = e
        need(fvty(A) <= G, 'an unbound base variable')
        A1, u = wtype(w, Phi, G, D)
        need(subtype(Phi, A1, A), 'the start of a loop')
        B, ub = tc(body, Phi, G, {**(rest(u) if BROKEN == 'loop' else {}), y: A})
        need(subtype(Phi, B, A), 'the state of a loop')
        return A, u | (ub - {y})
    raise Ill('an expression of a program')


def has_run(e):
    return isinstance(e, tuple) and (e[:1] == ('run',) or any(has_run(part) for part in e))


def accepts_code(code, A, B):
    """The check that `run` performs before it runs code that the model wrote."""
    if has_run(code):
        return False
    if BROKEN == 'run':
        return True
    try:
        B1, _ = tc(code, [], frozenset(), {'arg': A})
        return subtype([], B1, B)
    except Ill:
        return False


def verdict(e, D=None, want=BASE):
    """'accepted', or the reason for which the checker rejects."""
    try:
        A, _ = tc(e, [], frozenset(), D or {})
        return 'accepted' if subtype([], A, want) else 'a result of another type'
    except Ill as reason:
        return str(reason)


def well_typed(e):
    return verdict(e) == 'accepted'


# ---------------------------------------------------------------------------------------------
# 4. Semantics.  Events: ('grant', n, r) | ('deny',) | ('act', n, a, c) | ('split', n, n2, r1, r2)
# ---------------------------------------------------------------------------------------------

class Blocked(Exception):
    """The ledger refuses a step."""


class Stuck(Exception):
    """A value has the wrong shape.  No program that the checker accepts does this."""


def shaped(value, *tags):
    if not (isinstance(value, tuple) and value[0] in tags):
        raise Stuck()
    return value


class Ledger:
    """What is left of the plan of each token."""

    def __init__(self):
        self.entry = {}

    def grant(self, n, r):
        self.entry[n] = r

    def act(self, n, a, payload):
        left = deriv(self.entry[n], (a, payload)) if n in self.entry else ZERO
        if not alive(left):
            raise Blocked()
        self.entry[n] = left

    def split(self, n, n2, r1, r2):
        if n not in self.entry or n2 in self.entry or not within([r1, r2], self.entry[n]):
            raise Blocked()
        self.entry[n2], self.entry[n] = r1, r2

    def replay(self, trace):
        for ev in trace:
            if ev[0] == 'grant':
                self.grant(*ev[1:])
            elif ev[0] == 'act':
                self.act(*ev[1:])
            elif ev[0] == 'split':
                self.split(*ev[1:])


def least(value, A, env, ledger):
    """Fills the least ledger in which the value has the type A (Section 5.4)."""
    if A[0] == 'prod':
        least(value[1], A[1], env, ledger)
        least(value[2], A[2], env, ledger)
    elif A[0] == 'sum':
        least(value[1], A[1] if value[0] == 'inl' else A[2], env, ledger)
    elif A[0] == 'plan':
        ledger.grant(value[1], close(A[1], env))
    return ledger


def explained(trace):
    """Definition 5.4, without the ledger: the actions under a grant, in the order of the trace
    and whichever part of the plan they were made with, form a word in the authority of the
    plan that was granted."""
    root, left = {}, {}
    for ev in trace:
        if ev[0] == 'grant':
            if ev[1] in root:
                return False
            root[ev[1]], left[ev[1]] = ev[1], ev[2]
        elif ev[0] == 'split':
            if ev[1] not in root or ev[2] in root:
                return False
            root[ev[2]] = root[ev[1]]
        elif ev[0] == 'act':
            if ev[1] not in root:
                return False
            g = root[ev[1]]
            left[g] = deriv(left[g], (ev[2], ev[3]))
            if not alive(left[g]):
                return False
    return True


def erase(trace):
    """A trace without the names of the tokens; a split leaves nothing."""
    return [ev[:1] + ev[2:] for ev in trace if ev[0] != 'split']


def unname(value):
    if not isinstance(value, tuple):
        return value
    return ('tok', None) if value[0] == 'tok' else tuple(unname(part) for part in value)


def tokens(value):
    if not isinstance(value, tuple):
        return set()
    return {value[1]} if value[0] == 'tok' else set().union(*[tokens(part) for part in value])


def names_of(ev):
    return set() if ev[0] == 'deny' else {ev[1], ev[2]} if ev[0] == 'split' else {ev[1]}


class Source:
    """The model, the world and the person, from a random stream."""

    def __init__(self, seed):
        self.rng = random.Random(seed)

    def value(self):
        return int(self.rng.random() * len(V))

    def grants(self):
        return self.rng.random() < 0.8

    def code(self, A, B):
        """Code that the model writes for an argument of type A and a result of type B: half
        of the time written for these types, otherwise for a larger plan or with a rule
        ignored."""
        r = self.rng.random()
        if r < 0.5:
            return Gen(self.rng, code=True).expr(3, [], frozenset(), {'arg': A}, B)
        if r < 0.8:
            wide = ('plan', ('star', ('alt', letter('edit'), ('alt', letter('test'), letter('push')))))
            return Gen(self.rng, code=True).expr(3, [], frozenset(), {'arg': wide}, B)
        return Gen(self.rng, wild=0.3, code=True).expr(3, [], frozenset(), {'arg': A}, B)


class Run:
    """One execution.  With a ledger, tokens have names and every step is checked; with `check`
    the statements of Theorems 5.2 and 5.7 are checked where code runs and where a loop turns.
    Without a ledger, tokens are erased."""

    def __init__(self, src, ledger, check=False):
        self.src, self.trace, self.names = src, [], count()
        self.ledger = Ledger() if ledger else None
        self.check = check and ledger and not BROKEN
        self.asked = self.written = self.accepted = self.lent = 0

    def operand(self, w, eb, er):
        k = w[0]
        if k == 'var':
            return er[w[1]]
        if k == 'tm':
            return tval(w[1], eb)
        if k == 'unit':
            return ('unit',)
        if k == 'pair':
            return ('pair', self.operand(w[1], eb, er), self.operand(w[2], eb, er))
        if k == 'as':
            return self.operand(w[1], eb, er)
        return (k, self.operand(w[1], eb, er))

    def confined(self, value, A, env, thunk):
        """Runs a part of the program whose only resource is `value`, of the type A."""
        if not self.check:
            return thunk()
        own, before, start = tokens(value), dict(self.ledger.entry), len(self.trace)
        result = thunk()
        fresh = set(self.ledger.entry) - set(before)
        assert tokens(result) <= own | fresh
        assert all(self.ledger.entry[n] == ent for n, ent in before.items() if n not in own)
        assert all(names_of(ev) <= own | fresh for ev in self.trace[start:])
        least(value, A, env, Ledger()).replay(self.trace[start:])
        return result

    def returned(self, given, P, back, Q, start):
        """Corollary 5.8: if the token that code gives back comes from the token that it was
        given, then what the code did with that token, followed by any word that the type of
        the result allows, stays within the plan of the argument.  Returns whether it applies."""
        under, left = {given}, P
        for ev in self.trace[start:]:
            if ev[0] == 'split' and ev[1] in under:
                under.add(ev[2])
            elif ev[0] == 'act' and ev[1] in under:
                left = deriv(left, (ev[2], ev[3]))
        if back not in under:
            return 0                        # the code asked the person for a new token
        assert alive(left) or left == P
        assert within([Q], left)
        return 1

    def ev(self, e, eb, er):
        k = e[0]
        if k == 'ret':
            return self.operand(e[1], eb, er)
        if k == 'letb':
            return self.ev(e[3], {**eb, e[1]: self.ev(e[2], eb, er)}, er)
        if k == 'letr':
            return self.ev(e[3], eb, {**er, e[1]: self.ev(e[2], eb, er)})
        if k == 'letp':
            p = shaped(self.operand(e[3], eb, er), 'pair')
            return self.ev(e[4], eb, {**er, e[1]: p[1], e[2]: p[2]})
        if k == 'case':
            s = shaped(self.operand(e[1], eb, er), 'inl', 'inr')
            if s[0] == 'inl':
                return self.ev(e[3], eb, {**er, e[2]: s[1]})
            return self.ev(e[5], eb, {**er, e[4]: s[1]})
        if k == 'if':
            return self.ev(e[2] if pval(e[1], eb) else e[3], eb, er)
        if k == 'model':
            return self.src.value()
        if k == 'ask':
            self.asked += 1
            if not self.src.grants():
                self.trace.append(('deny',))
                return ('inr', ('unit',))
            r = close(e[1], eb)
            if self.ledger is None:
                self.trace.append(('grant', r))
                return ('inl', ('tok', None))
            n = next(self.names)
            self.trace.append(('grant', n, r))
            self.ledger.grant(n, r)
            return ('inl', ('tok', n))
        if k == 'act':
            _, a, t, w, x, y, body = e
            payload, value = tval(t, eb), shaped(self.operand(w, eb, er), 'tok')
            if self.ledger is None:
                self.trace.append(('act', a, payload))
            else:
                self.ledger.act(value[1], a, payload)
                self.trace.append(('act', value[1], a, payload))
            return self.ev(body, {**eb, x: self.src.value()}, {**er, y: value})
        if k == 'split':
            value = shaped(self.operand(e[1], eb, er), 'tok')
            if self.ledger is None:
                return ('pair', value, value)
            n, n2, r1, r2 = value[1], next(self.names), close(e[2], eb), close(e[3], eb)
            self.ledger.split(n, n2, r1, r2)
            self.trace.append(('split', n, n2, r1, r2))
            return ('pair', ('tok', n2), value)
        if k == 'run':
            _, A, B, t, w = e
            value, code = self.operand(w, eb, er), self.src.code(A, B)
            self.written += 1
            if not accepts_code(code, A, B):
                return ('inr', value)
            self.accepted += 1
            start = len(self.trace)
            result = self.confined(value, A, {}, lambda: self.ev(code, {}, {'arg': value}))
            if self.check and A[0] == 'plan' and B[0] == 'plan':
                self.lent += self.returned(value[1], close(A[1], {}), result[1], close(B[1], {}), start)
            return ('inl', result)
        _, n, A, w, y, body = e
        state = self.operand(w, eb, er)
        for _ in range(n):
            state = self.confined(state, A, eb, lambda: self.ev(body, eb, {**er, y: state}))
        return state


# ---------------------------------------------------------------------------------------------
# 5. Random plans and programs
# ---------------------------------------------------------------------------------------------

class Gen:
    """Programs.  With wild = 0 every program follows the typing rules.  With wild > 0 each
    choice that a rule constrains ignores the rule with that probability."""

    def __init__(self, rng, wild=0.0, code=False):
        self.rng, self.wild, self.code, self.names, self.slipped = rng, wild, code, count(), 0

    def below(self, n):
        return int(self.rng.random() * n)

    def one(self, xs):
        return xs[self.below(len(xs))]

    def name(self, prefix):
        return '%s%d' % (prefix, next(self.names))

    def slips(self):
        if self.wild > 0 and self.rng.random() < self.wild:
            self.slipped += 1
            return True
        return False

    def term(self, G):
        if G and self.rng.random() < 0.5:
            return v(self.one(sorted(G)))
        return c(self.below(len(V)))

    def shown(self, G):
        r = self.rng.random()
        if r < 0.3:
            return TRUE
        if r < 0.6:
            return le(v('p'), self.term(G))
        return eq(v('p'), self.term(G))

    def plan(self, G, depth=2):
        r = self.rng.random()
        if depth == 0 or r < 0.3:
            return letter(self.one(ACTIONS), self.shown(G))
        if r < 0.45:
            return ('star', self.plan(G, depth - 1))
        if r < 0.8:
            return ('seq', self.plan(G, depth - 1), self.plan(G, depth - 1))
        if r < 0.92:
            return ('alt', self.plan(G, depth - 1), self.plan(G, depth - 1))
        return ('par', self.plan(G, depth - 1), self.plan(G, depth - 1))

    def step(self, Phi, G, P):
        """An action and a payload that the plan allows under the facts, if the search finds one."""
        choices = [(a, t) for a in ACTIONS for t in [c(n) for n in V] + [v(x) for x in sorted(G)]]
        for i in range(len(choices) - 1, 0, -1):
            j = self.below(i + 1)
            choices[i], choices[j] = choices[j], choices[i]
        if self.slips():
            return choices[0]
        for a, t in choices:
            if allowed(Phi, P, a, t):
                return a, t
        return None

    def narrowed(self, Phi, G, P, closed):
        """A plan that the token contains, if the search finds one."""
        tries = [self.plan(set() if closed else G, 1) for _ in range(4)]
        tries += [P] if not (closed and fvplan(P)) else []
        if self.slips():
            return tries[0]
        for Q in tries:
            if contained(Phi, [Q], P):
                return Q
        return None

    def expr(self, depth, Phi, G, D, want=BASE):
        plans = sorted(y for y, A in D.items() if A[0] == 'plan')
        options = ['ret']
        if depth > 0:
            options += ['model', 'if', 'ask', 'seq', 'loop'] + (['act'] * 4 + ['split', 'narrow'] if plans else [])
            options += ['run', 'lend'] if plans and not self.code else []
        k = self.one(options)

        def again(Phi=Phi, G=G, D=D):
            return self.expr(depth - 1, Phi, G, dict(D), want)

        if k == 'ret':
            if want == BASE:
                return ('ret', ('tm', self.term(G)))
            fit = [y for y in plans if subtype(Phi, D[y], want)]
            return ('ret', var(self.one(fit or plans))) if plans else ('ret', ('tm', c(0)))
        if k == 'model':
            x = self.one(sorted(G)) if G and self.slips() else self.name('x')
            return ('letb', x, ('model',), again(G=G | {x}))
        if k == 'if':
            p = (self.one(['le', 'eq']), self.term(G), self.term(G))
            return ('if', p, again(Phi=Phi + [p]), again(Phi=Phi + [('not', p)]))
        if k == 'seq':
            first = {y: A for y, A in sorted(D.items()) if self.rng.random() < 0.5}
            x, e1 = self.name('x'), self.expr(depth - 1, Phi, G, dict(first))
            return ('letb', x, e1, again(G=G | {x}, D=D if self.slips() else without(D, first)))
        if k == 'ask':
            P, r, y, u = self.plan(G), self.name('r'), self.name('y'), self.name('u')
            return ('letr', r, ('ask', P), ('case', var(r), y, again(D={**D, y: ('plan', P)}), u, again()))
        if k == 'loop':
            # a loop whose state is a token for a starred plan: every turn takes one more step.
            # The token is one that the program holds and whose plan contains the starred plan,
            # or it is asked for.
            L = letter(self.one(ACTIONS), self.shown(G))
            Q, st, x, y2, out = ('star', L), self.name('s'), self.name('x'), self.name('y'), self.name('s')
            found = self.step(Phi, G, Q)
            if found is None:
                return again()
            held = [y for y in plans if contained(Phi, [Q], D[y][1])]
            y = self.one(held) if held else self.name('y')
            outer = without(D, {y})
            body = ('act', found[0], found[1], var(st), x, y2, ('ret', var(y2)))
            tokens_ = sorted(z for z in outer if outer[z][0] == 'plan')
            if tokens_ and self.slips():    # the body also takes a step with a token from outside
                z = self.one(tokens_)
                step = self.step(Phi, G, outer[z][1]) or ('edit', c(0))
                body = ('act', step[0], step[1], var(z), self.name('x'), self.name('y'), body)
            loop = ('letr', out, ('iter', 1 + self.below(3), ('plan', Q), var(y), st, body),
                    again(D={**outer, out: ('plan', Q)}))
            if held:
                return loop
            r, u = self.name('r'), self.name('u')
            return ('letr', r, ('ask', Q), ('case', var(r), y, loop, u, again()))
        y = self.one(plans)
        P = D[y][1]
        if k == 'act':
            found = self.step(Phi, G, P)
            if found is None:
                return again()
            x, y2 = self.name('x'), self.name('y')
            kept = D if self.slips() else without(D, {y})
            return ('act', found[0], found[1], var(y), x, y2,
                    again(G=G | {x}, D={**kept, y2: ('plan', ('der', P, found[0], found[1]))}))
        if k == 'narrow':
            Q = self.narrowed(Phi, G, P, False)
            if Q is None:
                return again()
            y2 = self.name('y')
            return ('letr', y2, ('ret', ('as', var(y), ('plan', Q))), again(D={**without(D, {y}), y2: ('plan', Q)}))
        if k == 'split':
            if self.slips():
                P1, P2 = self.plan(G, 1), self.plan(G, 1)
            elif P[0] == 'par':
                P1, P2 = P[1], P[2]
            elif P[0] == 'star':
                P1, P2 = P, P
            else:
                P1, P2 = P, EPS
            if not self.wild and not contained(Phi, [P1, P2], P):
                return again()
            pr, y1, y2 = self.name('r'), self.name('y'), self.name('y')
            parts = {**without(D, {y}), y1: ('plan', P1), y2: ('plan', P2)}
            return ('letr', pr, ('split', var(y), P1, P2), ('letp', y1, y2, var(pr), again(D=parts)))
        Q = self.narrowed(Phi, G, P, True)
        if Q is None:
            return again()
        A, r, y1, y2 = ('plan', Q), self.name('r'), self.name('y'), self.name('y')
        if k == 'lend':                     # the code gives back a token that is as good as the one it got
            return ('letr', r, ('run', A, A, self.term(G), var(y)),
                    ('case', var(r), y1, again(D={**without(D, {y}), y1: A}), y2, again(D={**without(D, {y}), y2: A})))
        return ('letr', r, ('run', A, BASE, self.term(G), var(y)),
                ('case', var(r), y1, again(D=without(D, {y})), y2, again(D={**without(D, {y}), y2: A})))


# ---------------------------------------------------------------------------------------------
# The programs of Section 2: edit files up to number 2 as often as needed, test, push to 1
# ---------------------------------------------------------------------------------------------

EDITS = ('star', letter('edit', le(v('p'), c(2))))
RELEASE = ('seq', EDITS, ('seq', letter('test'), letter('push', eq(v('p'), c(1)))))


def release(kind):
    last = ('ret', ('tm', c(0)))
    push = ('act', 'push', c(2 if kind == 'another-branch' else 1), var('y3'), 'x3', 'y4',
            ('act', 'push', c(1), var('y4'), 'x4', 'y5', last) if kind == 'twice' else
            ('act', 'edit', c(0), var('y4'), 'x4', 'y5', last) if kind == 'edit-after' else last)
    test = ('act', 'test', c(0), var('y2'), 'x2', 'y3', push)
    edit = ('letb', 'm', ('model',),
            ('if', le(v('m'), c(2)), ('act', 'edit', v('m'), var('y'), 'x1', 'y2', test),
             ('ret', ('tm', c(0)))) if kind != 'unchecked' else ('act', 'edit', v('m'), var('y'), 'x1', 'y2', test))
    return ('letr', 'r', ('ask', RELEASE), ('case', var('r'), 'y', edit, 'u', ('ret', ('tm', c(0)))))


def lending(kind):
    """The edits go to code that the model writes; the token comes back for the rest."""
    lent = ('plan', RELEASE)
    after = ('act', 'test', c(0), var('back'), 'x2', 'y3', ('act', 'push', c(1), var('y3'), 'x3', 'y4', ('ret', ('tm', c(0)))))
    if kind == 'split':
        return ('letr', 'r', ('ask', RELEASE), ('case', var('r'), 'y',
                ('letr', 'pr', ('split', var('y'), EDITS, ('seq', letter('test'), letter('push', eq(v('p'), c(1))))),
                 ('ret', ('tm', c(0)))), 'u', ('ret', ('tm', c(0)))))
    return ('letr', 'r', ('ask', RELEASE), ('case', var('r'), 'y',
            ('letr', 'out', ('run', lent, lent, c(0), var('y')), ('case', var('out'), 'back', after, 'back', after)),
            'u', ('ret', ('tm', c(0)))))


CODE = {
    'edits': ('act', 'edit', c(1), var('arg'), 'x', 'y', ('act', 'edit', c(2), var('y'), 'x2', 'y2', ('ret', var('y2')))),
    'tests': ('act', 'test', c(0), var('arg'), 'x', 'y', ('ret', var('y'))),
    'keeps': ('act', 'edit', c(1), var('arg'), 'x', 'y', ('ret', ('tm', c(0)))),
}


def holding(P, use):
    """A program that asks for a plan and, if it is granted, goes on with the token `y`."""
    return ('letr', 'r', ('ask', P), ('case', var('r'), 'y', use, 'u', ('ret', ('tm', c(0)))))


def steps(word, token='y', last=None, tag=''):
    """The actions of a word, one after the other, under a token."""
    return follows(word, token, last or (lambda y: ('ret', ('tm', c(0)))), tag)


# Section 6: three plans.  A push only after a test since the last edit; at most two pushes,
# among any edits and tests; two helpers with their own files.
ANY = ('alt', letter('edit'), letter('test'))
ROUNDS = ('star', ('seq', ('star', letter('edit')), ('seq', letter('test'), letter('push'))))
TWICE = ('par', ('star', ANY), ('seq', ('alt', letter('push'), EPS), ('alt', letter('push'), EPS)))
LOW, HIGH = ('star', letter('edit', le(v('p'), c(1)))), ('star', ('alt', letter('edit', eq(v('p'), c(2))), letter('test')))
HELPERS = ('par', LOW, HIGH)


def budget(total):
    """The budget of an earlier paper as a regular expression: payments that sum to at most
    `total`."""
    more = alt(ONE, *[seq(sym([('push', n)]), budget(total - n)) for n in V if 1 <= n <= total])
    return seq(star(sym([('push', 0)])), more)


# ---------------------------------------------------------------------------------------------
# 6. The tests
# ---------------------------------------------------------------------------------------------

def narrowings(e):
    return (e[:1] == ('as',)) + sum(narrowings(part) for part in e if isinstance(part, tuple)) if isinstance(e, tuple) else 0


def brute(r, word):
    """Whether a word is in the language of r, by the definition."""
    k = r[0]
    if k == '0':
        return False
    if k == '1':
        return not word
    if k == 'sym':
        return len(word) == 1 and word[0] in r[1]
    if k == 'alt':
        return any(brute(q, word) for q in r[1])
    if k == 'seq':
        return any(brute(r[1], word[:i]) and brute(r[2], word[i:]) for i in range(len(word) + 1))
    if k == 'star':
        return not word or any(brute(r[1], word[:i]) and brute(r, word[i:]) for i in range(1, len(word) + 1))
    for mask in product((0, 1), repeat=len(word)):
        left = tuple(l for l, m in zip(word, mask) if m)
        right = tuple(l for l, m in zip(word, mask) if not m)
        if brute(r[1], left) and brute(r[2], right):
            return True
    return False


def execute(e, seed):
    """One execution with the ledger and one without it, on the same choices."""
    led = Run(Source(seed), True, check=True)
    value = led.ev(e, {}, {})
    bare = Run(Source(seed), False)
    assert bare.ev(e, {}, {}) == unname(value) and bare.trace == erase(led.trace)
    assert explained(led.trace)
    return led


def refused(e, rng, runs=3):
    """Whether the ledger refuses a step in one of some executions."""
    for _ in range(runs):
        try:
            execute(e, int(rng.random() * 2 ** 32))
        except Blocked:
            return True
        except Stuck:
            pass
    return False


def follows(word, token, done, tag=''):
    """A program that makes the actions of a word with a token and then goes on with `done`."""
    names = count()
    for a, n in reversed(word):
        i = '%s%d' % (tag, next(names))
        done = (lambda rest, a=a, n=n, i=i: lambda y: ('act', a, c(n), var(y), 'x' + i, 'y' + i, rest('y' + i)))(done)
    return done(token)


def main(outdir):
    global BROKEN
    rng = random.Random(2026)
    gen = Gen(rng)
    lines, nums = [], {}

    # derivatives against the definition of a language, on words of up to three letters
    small = [('edit', 0), ('test', 0), ('push', 1)]
    words = [w for n in range(4) for w in product(small, repeat=n)]
    checked = 0
    for _ in range(150):
        r = close(gen.plan(set(), 3), {})
        for w in words:
            d = r
            for l in w:
                d = deriv(d, l)
            assert nullable(d) == brute(r, w)
            assert inside(r, w) == (not w or any(brute(r, w + rest) for rest in words) or alive(d))
        checked += len(words)
    lines.append(f'150 random plans: membership by derivatives agrees with the definition on {checked} words')

    # Table 1 of the paper
    table = [(release('follows'), 'accepted'),
             (release('unchecked'), 'an action that the plan does not allow'),
             (release('twice'), 'an action that the plan does not allow'),
             (release('edit-after'), 'an action that the plan does not allow'),
             (release('another-branch'), 'an action that the plan does not allow'),
             (lending('lend'), 'accepted'),
             (lending('split'), 'parts that go beyond the plan')]
    assert all(verdict(e) == expected for e, expected in table), [verdict(e) for e, _ in table]
    lent = ('plan', RELEASE)
    assert accepts_code(CODE['edits'], lent, lent) and not accepts_code(CODE['tests'], lent, lent)
    assert not accepts_code(CODE['keeps'], lent, lent)
    assert verdict(CODE['tests'], {'arg': lent}, lent) == 'a result of another type'
    lines.append('the checker gives the verdicts of Table 1 on the programs and the code of Section 2')

    # the trace of Table 2: the token is lent to the code that edits twice
    led = Run(Source(0), True, check=True)
    led.src.grants, led.src.code = (lambda: True), (lambda A, B: CODE['edits'])
    led.ev(lending('lend'), {}, {})
    rest = [('edit', 1), ('edit', 2), ('test', 0), ('push', 1)]
    assert led.trace == [('grant', 0, close(RELEASE, {}))] + [('act', 0) + l for l in rest]
    left = close(RELEASE, {})
    for i, l in enumerate(rest):
        left = deriv(left, l)
        assert within([left], close([RELEASE, RELEASE, letter('push', eq(v('p'), c(1))), EPS][i], {}))
        assert within([close([RELEASE, RELEASE, letter('push', eq(v('p'), c(1))), EPS][i], {})], left)

    # the plans of Section 6, each with a program that keeps it and one that does not
    E, T, U = ('edit', 0), ('test', 0), ('push', 0)
    refusal = 'an action that the plan does not allow'
    assert verdict(holding(ROUNDS, steps([E, T, U, E, E, T, U]))) == 'accepted'
    assert verdict(holding(ROUNDS, steps([E, T, U, E, U]))) == refusal
    assert verdict(holding(TWICE, steps([E, U, T, E, U, E]))) == 'accepted'
    assert verdict(holding(TWICE, steps([U, E, U, T, U]))) == refusal
    both = lambda first, second: holding(HELPERS, ('letr', 'pr', ('split', var('y'), LOW, HIGH), ('letp', 'h1', 'h2', var('pr'),
                                         steps(first, 'h1', lambda y: steps(second, 'h2', None, 'b'), 'a'))))
    assert verdict(both([('edit', 0), ('edit', 1)], [('edit', 2), T])) == 'accepted'
    assert verdict(both([('edit', 0), ('edit', 2)], [T])) == refusal
    assert verdict(holding(ROUNDS, ('letr', 'pr', ('split', var('y'), ('star', letter('edit')), ROUNDS), ('ret', ('tm', c(0)))))) \
        == 'parts that go beyond the plan'
    lines.append('the three plans of Section 6: the checker accepts the programs that keep them and rejects the '
                 'ones that do not')

    # Theorems 5.2, 5.3, 5.6 and 5.7 on programs that the checker accepts
    typed = [gen.expr(6, [], frozenset(), {}) for _ in range(3000)]
    assert all(well_typed(e) for e in typed)
    wild, lucky, wgen = [], 0, Gen(rng, wild=0.1)
    while len(wild) < 3000:
        wgen.slipped = 0
        e = wgen.expr(6, [], frozenset(), {})
        if well_typed(e):
            wild.append(e)
            lucky += wgen.slipped > 0
    acts = grants = asks = splits = written = accepted = lent = 0
    for e in typed + wild:
        for _ in range(3):
            led = execute(e, int(rng.random() * 2 ** 32))
            acts += sum(ev[0] == 'act' for ev in led.trace)
            grants += sum(ev[0] == 'grant' for ev in led.trace)
            splits += sum(ev[0] == 'split' for ev in led.trace)
            asks, written, accepted = asks + led.asked, written + led.written, accepted + led.accepted
            lent += led.lent
    lines.append(f'6000 programs that the checker accepts ({lucky} of them built with a rule ignored), three '
                 f'executions each: the ledger refuses no step, the execution without tokens gives the same '
                 f'trace and value, every trace is explained, and no part goes beyond the least ledger of what '
                 f'it was given; {asks} requests, {grants} grants, {acts} actions, {splits} splits, {written} '
                 f'pieces of code written by the model, {accepted} of them accepted, {lent} of which give '
                 f'back the token that they were lent')
    nums.update(Programs='6,000', Lucky=f'{lucky:,}', Runs='18,000', Asks=f'{asks:,}', Grants=f'{grants:,}',
                Acts=f'{acts:,}', Splits=f'{splits:,}', Written=f'{written:,}', Accepted=f'{accepted:,}',
                Lent=f'{lent:,}', Typed='3,000', Slip='0.1', SlipBroken='0.15', EnginePlans='150',
                EngineWords=f'{checked:,}', Narrowings=f'{sum(narrowings(e) for e in typed + wild):,}',
                Questions=f'{sum(str(e).count("('ask'") for e in typed + wild):,}')

    # Theorem 5.9: narrowing is containment, in both directions
    yes = no = 0
    for _ in range(2000):
        P, Q = gen.plan(set(), 2), gen.plan(set(), 2)
        word = beyond([close(Q, {})], close(P, {}))

        def program(w):
            use = follows(w, 'z', lambda y: ('ret', ('tm', c(0))))
            return ('letr', 'r', ('ask', P), ('case', var('r'), 'y',
                    ('letr', 'z', ('ret', ('as', var('y'), ('plan', Q))), use), 'u', ('ret', ('tm', c(0)))))

        if word is None:
            yes += 1
            w, r = (), close(Q, {})         # a random walk in the authority of Q
            for _ in range(4):
                nxt = [l for l in LETTERS if alive(deriv(r, l))]
                if not nxt:
                    break
                l = gen.one(nxt)
                w, r = w + (l,), deriv(r, l)
            assert well_typed(program(w)) and not refused(program(w), rng)
        else:
            no += 1
            assert inside(close(Q, {}), word) and not inside(close(P, {}), word)
            assert not well_typed(program(word))
            BROKEN = 'narrow'
            assert well_typed(program(word))
            led = Run(Source(1), True)
            led.src.grants = lambda: True
            try:
                led.ev(program(word), {}, {})
                assert False
            except Blocked:
                pass
            BROKEN = None
    lines.append(f'2000 pairs of plans: in {yes} the first contains the second, and a walk in the second runs '
                 f'under a token for the first; in {no} it does not, and the word that the search returns is '
                 f'refused by the ledger once the checker lets the narrowing through')
    nums.update(Pairs='2,000', PairsYes=f'{yes:,}', PairsNo=f'{no:,}')

    # Proposition 5.10: approvals and budgets of the earlier paper are plans
    for total in V:
        for n in V:
            left = deriv(budget(total), ('push', n))
            assert alive(left) == (n <= total)
            if n <= total:
                assert within([left], budget(total - n)) and within([budget(total - n)], left)
        for part in range(total + 1):
            assert within([budget(part), budget(total - part)], budget(total))
            assert total == V[-1] or not within([budget(part), budget(total - part + 1)], budget(total))
    lines.append('budgets as plans: paying takes the derivative, and two budgets interleaved stay within a '
                 'budget exactly if their amounts sum to at most its amount')

    # every rule is needed
    tries = {}
    for rule in RULES:
        BROKEN = rule
        MODELS.clear()
        wgen = Gen(rng, wild=0.15)
        for i in range(1, 200001):
            e = wgen.expr(6, [], frozenset(), {})
            if well_typed(e) and refused(e, rng):
                tries[rule] = i
                break
        BROKEN = None
    assert set(tries) == set(RULES), tries
    lines.append(f'{len(RULES)} checkers with one broken rule each: every one accepts a program that the '
                 'ledger refuses, after ' + ', '.join(f'{rule} {n}' for rule, n in tries.items()) + ' programs')
    assert max(tries, key=tries.get) == 'branch'        # the paper says which rule is the slowest
    nums.update(Rules=str(len(RULES)), Slowest=f'{max(tries.values()):,}')
    for rule, n in tries.items():
        nums['Try' + ''.join(part.capitalize() for part in rule.split('-'))] = f'{n:,}'

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by plans.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
