#!/usr/bin/env python3
"""Tests the claims of "Consent as a Linear Resource" on an implementation of its calculus.

The file has five parts.

1. Terms, predicates, types, and entailment.  Base values are 0..5 with saturating
   arithmetic, so that entailment is decided by enumeration.
2. The type checker of Figure 3: resources that are used at most once, approvals indexed by a
   predicate on the payload, and budgets indexed by an amount.
3. The semantics of Figure 2 in two forms: with tokens that have names and a ledger that
   checks every action, and with tokens erased and no ledger.  Also the definition of an
   explained trace, written without the ledger.
4. Random programs: a generator that follows the typing rules, and that can be told to
   ignore a side condition now and then.
5. The tests.  `python3 consent.py out` writes out/check.txt and out/numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import random
import sys
from itertools import count, product

V = range(6)
TOP = 5


# ---------------------------------------------------------------------------------------------
# 1. Terms ('c', n) | ('v', x) | ('add', s, t) | ('sub', s, t); predicates
#    ('true',) | ('le', s, t) | ('eq', s, t) | ('not', p) | ('and', p, q); types
#    BASE | UNIT | ('prod', A, B) | ('sum', A, B) | ('ex', x, A) | ('ok', a, phi) | ('bud', a, t)
#    The payload of an approval is the variable 'p' of its predicate.
# ---------------------------------------------------------------------------------------------

BASE, UNIT, TRUE = ('base',), ('unit',), ('true',)
ACTIONS = ('pay', 'send', 'delete')


def c(n):
    return ('c', n)


def v(x):
    return ('v', x)


def le(s, t):
    return ('le', s, t)


def eq(s, t):
    return ('eq', s, t)


def sub(s, t):
    return ('sub', s, t)


def var(y):
    return ('var', y)


def fvt(t):
    if t[0] == 'c':
        return set()
    if t[0] == 'v':
        return {t[1]}
    return fvt(t[1]) | fvt(t[2])


def fvp(p):
    if p[0] == 'true':
        return set()
    if p[0] == 'not':
        return fvp(p[1])
    if p[0] == 'and':
        return fvp(p[1]) | fvp(p[2])
    return fvt(p[1]) | fvt(p[2])


def fvty(A):
    k = A[0]
    if k in ('base', 'unit'):
        return set()
    if k in ('prod', 'sum'):
        return fvty(A[1]) | fvty(A[2])
    if k == 'ex':
        return fvty(A[2]) - {A[1]}
    if k == 'ok':
        return fvp(A[2]) - {'p'}
    return fvt(A[2])


def subt(t, s):
    if t[0] == 'c':
        return t
    if t[0] == 'v':
        return s.get(t[1], t)
    return (t[0], subt(t[1], s), subt(t[2], s))


def subp(p, s):
    if p[0] == 'true':
        return p
    if p[0] == 'not':
        return ('not', subp(p[1], s))
    if p[0] == 'and':
        return ('and', subp(p[1], s), subp(p[2], s))
    return (p[0], subt(p[1], s), subt(p[2], s))


def subty(A, s):
    k = A[0]
    if k in ('base', 'unit'):
        return A
    if k in ('prod', 'sum'):
        return (k, subty(A[1], s), subty(A[2], s))
    if k == 'ex':
        return ('ex', A[1], subty(A[2], {x: t for x, t in s.items() if x != A[1]}))
    if k == 'ok':
        return ('ok', A[1], subp(A[2], {x: t for x, t in s.items() if x != 'p'}))
    return ('bud', A[1], subt(A[2], s))


def tval(t, env):
    if t[0] == 'c':
        return t[1]
    if t[0] == 'v':
        return env[t[1]]
    a, b = tval(t[1], env), tval(t[2], env)
    return min(a + b, TOP) if t[0] == 'add' else max(a - b, 0)


def pval(p, env):
    if p[0] == 'true':
        return True
    if p[0] == 'not':
        return not pval(p[1], env)
    if p[0] == 'and':
        return pval(p[1], env) and pval(p[2], env)
    a, b = tval(p[1], env), tval(p[2], env)
    return a <= b if p[0] == 'le' else a == b


CACHE = {}


def entails(Phi, goal):
    """Whether every assignment that satisfies Phi satisfies the goal.  Only hypotheses that
    share variables with the goal are used, and only while at most six variables are involved;
    to leave a hypothesis out is sound."""
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
# 2. The type checker.  Operands:
#    ('var', y) | ('tm', t) | ('unit',) | ('pair', w, w) | ('inl', w, B) | ('inr', w, A)
#    | ('pack', t, w, x, A)
#    Expressions:
#    ('ret', w) | ('letb', x, e, e) | ('letr', y, e, e) | ('letp', y, y, w, e)
#    | ('case', w, y, e, y, e) | ('unpack', x, y, w, e) | ('if', p, e, e) | ('model',)
#    | ('ask', a, p) | ('askb', a, t) | ('act', a, t, w) | ('spend', a, t, w) | ('split', w, t)
#    | ('run', A, B, t, w) | ('iter', n, A, w, y, e)
# ---------------------------------------------------------------------------------------------

BROKEN = None       # the name of a rule that is deliberately broken, for the last test

RULES = ('contraction', 'branch', 'loop', 'shadow', 'act', 'action', 'spend', 'split',
         'attenuate', 'attenuate-budget', 'if-fact', 'run')


class Ill(Exception):
    pass


def need(ok, why):
    if not ok:
        raise Ill(why)


def subtype(Phi, A, B, depth=0):
    """Whether a value of type A may be used where B is expected."""
    if A[0] != B[0]:
        return False
    k = A[0]
    if k in ('base', 'unit'):
        return True
    if k in ('prod', 'sum'):
        return subtype(Phi, A[1], B[1], depth) and subtype(Phi, A[2], B[2], depth)
    if k == 'ex':
        z = v('_%d' % depth)        # no variable of a program starts with an underscore
        return subtype(Phi, subty(A[2], {A[1]: z}), subty(B[2], {B[1]: z}), depth + 1)
    if A[1] != B[1]:
        return False
    if k == 'ok':
        # an approval for the payloads of A serves where only some of them are named
        return BROKEN == 'attenuate' or entails(Phi + [B[2]], A[2])
    return BROKEN == 'attenuate-budget' or entails(Phi, le(B[2], A[2]))


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
    if k == 'pack':
        _, t, w1, x, A = w
        need(fvt(t) <= G, 'an unbound base variable')
        A1, u = wtype(w1, Phi, G, D)
        need(subtype(Phi, A1, subty(A, {x: t})), 'the packed value')
        return ('ex', x, A), u
    raise Ill('an operand of a program')


def join(Phi, A, B):
    if subtype(Phi, A, B):
        return B
    need(subtype(Phi, B, A), 'branches of different types')
    return A


def tc(e, Phi, G, D):
    """The type of an expression and the resources it uses.  A resource is used at most once:
    what one part has used is not available to the parts after it."""
    k = e[0]
    rest = (lambda used: D) if BROKEN == 'contraction' else (lambda used: without(D, used))
    if k == 'ret':
        return wtype(e[1], Phi, G, D)
    if k == 'letb':
        _, x, e1, e2 = e
        # the facts speak about the variables by name, so no name is bound twice
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
        # the broken rule counts a resource as used only if both branches use it
        return join(Phi, B1, B2), u | (u1 & u2 if BROKEN == 'branch' else u1 | u2)
    if k == 'unpack':
        _, x, y, w, e1 = e
        need(BROKEN == 'shadow' or x not in G, 'a base variable that is bound twice')
        A, u1 = wtype(w, Phi, G, D)
        need(A[0] == 'ex', 'an unpack of another type')
        B, u2 = tc(e1, Phi, G | {x}, {**rest(u1), y: subty(A[2], {A[1]: v(x)})})
        need(x not in fvty(B), 'a type that mentions a local variable')
        return B, u1 | (u2 - {y})
    if k == 'if':
        _, p, e1, e2 = e
        need(fvp(p) <= G, 'an unbound base variable')
        B1, u1 = tc(e1, Phi + [p], G, D)
        B2, u2 = tc(e2, Phi + [p if BROKEN == 'if-fact' else ('not', p)], G, D)
        return join(Phi, B1, B2), u1 & u2 if BROKEN == 'branch' else u1 | u2
    if k == 'model':
        return BASE, set()
    if k == 'ask':
        need(fvp(e[2]) <= G | {'p'}, 'an unbound base variable')
        return ('sum', ('ok', e[1], e[2]), UNIT), set()
    if k == 'askb':
        need(fvt(e[2]) <= G, 'an unbound base variable')
        return ('sum', ('bud', e[1], e[2]), UNIT), set()
    if k == 'act':
        _, a, t, w = e
        need(fvt(t) <= G, 'an unbound base variable')
        A, u = wtype(w, Phi, G, D)
        need(A[0] == 'ok' and (A[1] == a or BROKEN == 'action'), 'an action without its approval')
        need(BROKEN == 'act' or entails(Phi, subp(A[2], {'p': t})), 'a payload outside the approval')
        return BASE, u
    if k == 'spend':
        _, a, t, w = e
        need(fvt(t) <= G, 'an unbound base variable')
        A, u = wtype(w, Phi, G, D)
        need(A[0] == 'bud' and (A[1] == a or BROKEN == 'action'), 'an action without its budget')
        need(BROKEN == 'spend' or entails(Phi, le(t, A[2])), 'a payload above the budget')
        return ('bud', A[1], sub(A[2], t)), u
    if k == 'split':
        _, w, t = e
        need(fvt(t) <= G, 'an unbound base variable')
        A, u = wtype(w, Phi, G, D)
        need(A[0] == 'bud', 'a split of another type')
        need(BROKEN == 'split' or entails(Phi, le(t, A[2])), 'a part above the budget')
        return ('prod', ('bud', A[1], t), ('bud', A[1], sub(A[2], t))), u
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
        # the body runs many times, so it may use no resource but its state
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
        B1, _ = tc(code, [], set(), {'arg': A})
        return subtype([], B1, B)
    except Ill:
        return False


def well_typed(e):
    try:
        A, _ = tc(e, [], set(), {})
        return A == BASE
    except Ill:
        return False


def verdict(e, D=None):
    """'accepted', or the reason for which the checker rejects."""
    try:
        tc(e, [], set(), D or {})
        return 'accepted'
    except Ill as reason:
        return str(reason)


# ---------------------------------------------------------------------------------------------
# 3. Semantics
# ---------------------------------------------------------------------------------------------

class Blocked(Exception):
    """The ledger refuses a step."""


class Stuck(Exception):
    """A value has the wrong shape.  No program of the generator does this."""


class Ledger:
    """What each token still permits.  The rules of Figure 2 ask it before every action."""

    def __init__(self):
        self.entry = {}

    def grant(self, n, a, phi):
        self.entry[n] = ('ok', a, phi)

    def grant_budget(self, n, a, amount):
        self.entry[n] = ('bud', a, amount)

    def act(self, n, a, payload):
        ent = self.entry.get(n)
        if ent and ent[0] == 'ok' and ent[1] == a and pval(ent[2], {'p': payload}):
            self.entry[n] = ('gone',)
        elif ent and ent[0] == 'bud' and ent[1] == a and payload <= ent[2]:
            self.entry[n] = ('bud', a, ent[2] - payload)
        else:
            raise Blocked()

    def split(self, n, n2, amount):
        ent = self.entry.get(n)
        if not (ent and ent[0] == 'bud' and amount <= ent[2]) or n2 in self.entry:
            raise Blocked()
        self.entry[n] = ('bud', ent[1], ent[2] - amount)
        self.entry[n2] = ('bud', ent[1], amount)

    def replay(self, trace):
        for ev in trace:
            if ev[0] == 'grant':
                self.grant(*ev[1:])
            elif ev[0] == 'budget':
                self.grant_budget(*ev[1:])
            elif ev[0] == 'act':
                self.act(*ev[1:])
            elif ev[0] == 'split':
                self.split(*ev[1:])


def least(value, A, ledger):
    """Fills the least ledger in which the value has the closed type A (Definition 5.9)."""
    k = A[0]
    if k == 'prod':
        least(value[1], A[1], ledger)
        least(value[2], A[2], ledger)
    elif k == 'sum':
        least(value[1], A[1] if value[0] == 'inl' else A[2], ledger)
    elif k == 'ex':
        least(value[2], subty(A[2], {A[1]: c(value[1])}), ledger)
    elif k == 'ok':
        ledger.grant(value[1], A[1], A[2])
    elif k == 'bud':
        ledger.grant_budget(value[1], A[1], tval(A[2], {}))
    return ledger


def explained(trace):
    """Definition 5.6, written without the ledger: every action belongs to a grant that was
    made before it; an approval has at most one action, of its kind, with a payload that
    satisfies what the person was shown; the actions under a budget and under the parts split
    from it are of its kind and sum to at most its amount."""
    approval, budget, origin, used, total = {}, {}, {}, set(), {}
    for ev in trace:
        if ev[0] == 'grant':
            _, n, a, phi = ev
            if n in approval or n in origin:
                return False
            approval[n] = (a, phi)
        elif ev[0] == 'budget':
            _, n, a, amount = ev
            if n in approval or n in origin:
                return False
            budget[n], origin[n], total[n] = (a, amount), n, 0
        elif ev[0] == 'split':
            _, n, n2, amount = ev
            if n not in origin or n2 in approval or n2 in origin:
                return False
            origin[n2] = origin[n]
        elif ev[0] == 'act':
            _, n, a, payload = ev
            if n in approval:
                if n in used or approval[n][0] != a or not pval(approval[n][1], {'p': payload}):
                    return False
                used.add(n)
            elif n in origin:
                g = origin[n]
                total[g] += payload
                if budget[g][0] != a or total[g] > budget[g][1]:
                    return False
            else:
                return False
    return True


def erase(trace):
    """A trace without the names of the tokens; a split leaves nothing."""
    return [ev if ev[0] == 'deny' else (ev[0],) + ev[2:] for ev in trace if ev[0] != 'split']


def unname(value):
    if not isinstance(value, tuple):
        return value
    if value[0] == 'tok':
        return ('tok', None)
    return tuple(unname(part) for part in value)


def tokens(value):
    if not isinstance(value, tuple):
        return set()
    if value[0] == 'tok':
        return {value[1]}
    return set().union(*[tokens(part) for part in value])


def names_of(ev):
    return set() if ev[0] == 'deny' else {ev[1], ev[2]} if ev[0] == 'split' else {ev[1]}


class Source:
    """The model, the world and the person, from a random stream."""

    def __init__(self, seed):
        self.rng = random.Random(seed)

    def value(self):
        return int(self.rng.random() * len(V))

    def grants(self):
        return self.rng.random() < 0.75

    def code(self, A):
        """Code that the model writes for an argument of type A: half of the time written for
        that type, otherwise written for more than was given or with a rule ignored."""
        r = self.rng.random()
        if r < 0.5:
            return Gen(self.rng, code=True).expr(3, [], set(), {'arg': A})
        if r < 0.8:
            wider = ('bud', A[1], c(TOP)) if A[0] == 'bud' else ('ok', A[1], TRUE)
            return Gen(self.rng, code=True).expr(3, [], set(), {'arg': wider})
        return Gen(self.rng, wild=0.3, code=True).expr(3, [], set(), {'arg': A})


class Run:
    """One execution.  With a ledger, tokens have names, every action is checked, and the
    statements of Theorem 5.3 and Theorem 5.10 are checked where code runs and where a loop
    turns.  Without a ledger, tokens are erased and nothing is checked."""

    def __init__(self, src, ledger, check=False):
        self.src, self.trace, self.names = src, [], count()
        self.ledger = Ledger() if ledger else None
        self.check = check and ledger and not BROKEN    # only for programs that the checker accepts
        self.asked = self.written = self.accepted = 0

    def token(self, value):
        if not (isinstance(value, tuple) and value[0] == 'tok'):
            raise Stuck()
        return value[1]

    def shaped(self, value, tags):
        if not (isinstance(value, tuple) and value[0] in tags):
            raise Stuck()
        return value

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
        if k in ('inl', 'inr'):
            return (k, self.operand(w[1], eb, er))
        return ('pack', tval(w[1], eb), self.operand(w[2], eb, er))

    def granted(self, kind, a, what):
        if self.ledger is None:
            self.trace.append((kind, a, what))
            return ('inl', ('tok', None))
        n = next(self.names)
        self.trace.append((kind, n, a, what))
        if kind == 'grant':
            self.ledger.grant(n, a, what)
        else:
            self.ledger.grant_budget(n, a, what)
        return ('inl', ('tok', n))

    def action(self, value, a, payload):
        n = self.token(value)
        if self.ledger is None:
            self.trace.append(('act', a, payload))
        else:
            self.ledger.act(n, a, payload)
            self.trace.append(('act', n, a, payload))

    def confined(self, value, A, thunk):
        """Runs a part of the program whose only resource is `value`, of the closed type A.
        Checks the frame of Theorem 5.3, and Theorem 5.10: the least ledger for the value
        has the steps of what the part does."""
        if not self.check:
            return thunk()
        own, before, start = tokens(value), dict(self.ledger.entry), len(self.trace)
        result = thunk()
        fresh = set(self.ledger.entry) - set(before)
        assert tokens(result) <= own | fresh
        assert all(self.ledger.entry[n] == ent for n, ent in before.items() if n not in own)
        assert all(names_of(ev) <= own | fresh for ev in self.trace[start:])
        least(value, A, Ledger()).replay(self.trace[start:])
        return result

    def ev(self, e, eb, er):
        k = e[0]
        if k == 'ret':
            return self.operand(e[1], eb, er)
        if k == 'letb':
            c1 = self.ev(e[2], eb, er)
            if not isinstance(c1, int):
                raise Stuck()
            return self.ev(e[3], {**eb, e[1]: c1}, er)
        if k == 'letr':
            return self.ev(e[3], eb, {**er, e[1]: self.ev(e[2], eb, er)})
        if k == 'letp':
            p = self.shaped(self.operand(e[3], eb, er), ('pair',))
            return self.ev(e[4], eb, {**er, e[1]: p[1], e[2]: p[2]})
        if k == 'case':
            s = self.shaped(self.operand(e[1], eb, er), ('inl', 'inr'))
            if s[0] == 'inl':
                return self.ev(e[3], eb, {**er, e[2]: s[1]})
            return self.ev(e[5], eb, {**er, e[4]: s[1]})
        if k == 'unpack':
            p = self.shaped(self.operand(e[3], eb, er), ('pack',))
            return self.ev(e[4], {**eb, e[1]: p[1]}, {**er, e[2]: p[2]})
        if k == 'if':
            return self.ev(e[2] if pval(e[1], eb) else e[3], eb, er)
        if k == 'model':
            return self.src.value()
        if k in ('ask', 'askb'):
            self.asked += 1
            if not self.src.grants():
                self.trace.append(('deny', e[1]))
                return ('inr', ('unit',))
            if k == 'ask':
                return self.granted('grant', e[1], subp(e[2], {x: c(n) for x, n in eb.items()}))
            return self.granted('budget', e[1], tval(e[2], eb))
        if k in ('act', 'spend'):
            payload, value = tval(e[2], eb), self.operand(e[3], eb, er)
            self.action(value, e[1], payload)
            return self.src.value() if k == 'act' else value
        if k == 'split':
            value, amount = self.operand(e[1], eb, er), tval(e[2], eb)
            n = self.token(value)
            if self.ledger is None:
                return ('pair', value, value)
            n2 = next(self.names)
            self.ledger.split(n, n2, amount)
            self.trace.append(('split', n, n2, amount))
            return ('pair', ('tok', n2), value)
        if k == 'run':
            _, A, B, t, w = e
            value, code = self.operand(w, eb, er), self.src.code(A)
            self.written += 1
            if not accepts_code(code, A, B):
                return ('inr', value)
            self.accepted += 1
            return ('inl', self.confined(value, A, lambda: self.ev(code, {}, {'arg': value})))
        if k == 'iter':
            _, n, A, w, y, body = e
            state, A = self.operand(w, eb, er), subty(A, {x: c(m) for x, m in eb.items()})
            for _ in range(n):
                state = self.confined(state, A, lambda: self.ev(body, eb, {**er, y: state}))
            return state
        raise Stuck()


# ---------------------------------------------------------------------------------------------
# 4. Random programs
# ---------------------------------------------------------------------------------------------

class Gen:
    """Programs of type Base.  With wild = 0 every program follows the typing rules.  With
    wild > 0 each choice that a rule constrains ignores the rule with that probability."""

    def __init__(self, rng, wild=0.0, code=False, rebind=True):
        self.rng, self.wild, self.code, self.names, self.slipped = rng, wild, code, count(), 0
        self.rebind = rebind        # whether a wild choice may bind a base variable twice

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
        r = self.rng.random()
        if G and r < 0.5:
            return v(self.one(sorted(G)))
        if G and r < 0.6:
            return (self.one(['add', 'sub']), v(self.one(sorted(G))), c(1 + self.below(2)))
        return c(self.below(len(V)))

    def pred(self, G):
        return (self.one(['le', 'eq']), self.term(G), self.term(G))

    def shown(self, G):
        """A predicate on the payload p, as a person is shown it."""
        r = self.rng.random()
        if r < 0.5:
            return eq(v('p'), self.term(G))
        if r < 0.8:
            return le(v('p'), self.term(G))
        return ('and', le(c(self.below(3)), v('p')), le(v('p'), c(2 + self.below(4))))

    def fitting(self, Phi, G, goal):
        """A term t for which the facts entail goal(t), if the search finds one."""
        candidates = [c(n) for n in V] + [v(x) for x in sorted(G)]
        h = goal(v('p'))
        if h[0] in ('eq', 'le') and h[1] == v('p') and 'p' not in fvt(h[2]):
            candidates.append(h[2])
        for i in range(len(candidates) - 1, 0, -1):
            j = self.below(i + 1)
            candidates[i], candidates[j] = candidates[j], candidates[i]
        for t in candidates:
            if entails(Phi, goal(t)):
                return t
        return None

    def intruded(self, body, Phi, G, outer):
        """With wild > 0: a loop body that also uses a resource from outside the loop."""
        if not outer or not self.slips():
            return body
        y = self.one(sorted(outer))
        if outer[y][0] == 'ok':
            t = self.fitting(Phi, G, lambda t: subp(outer[y][2], {'p': t})) or self.term(G)
            return ('letb', self.name('x'), ('act', outer[y][1], t, var(y)), body)
        t = self.fitting(Phi, G, lambda t: ('and', le(c(1), t), le(t, outer[y][2]))) or self.term(G)
        return ('letr', self.name('y'), ('spend', outer[y][1], t, var(y)), body)

    def delegated(self, A, y, G, D, again):
        r, y1, y2 = self.name('r'), self.name('y'), self.name('y')
        return ('letr', r, ('run', A, BASE, self.term(G), var(y)),
                ('case', var(r), y1, again(D=without(D, {y})), y2, again(D={**without(D, {y}), y2: A})))

    def expr(self, depth, Phi, G, D):
        oks = sorted(y for y, A in D.items() if A[0] == 'ok')
        buds = sorted(y for y, A in D.items() if A[0] == 'bud')
        options = ['ret']
        if depth > 0:
            options += ['model', 'if', 'ask', 'askb', 'seq']
            if oks:
                options += ['act'] * 3 + ['retry'] + ([] if self.code else ['runok'])
            if buds:
                options += ['spend'] * 2 + ['guard', 'split', 'loop'] + ([] if self.code else ['run'])
        k = self.one(options)

        def again(Phi=Phi, G=G, D=D):
            return self.expr(depth - 1, Phi, G, dict(D))

        if k == 'ret':
            return ('ret', ('tm', self.term(G)))
        if k == 'model':
            x = self.one(sorted(G)) if G and self.rebind and self.slips() else self.name('x')
            return ('letb', x, ('model',), again(G=G | {x}))
        if k == 'if':
            p = self.pred(G)
            return ('if', p, again(Phi=Phi + [p]), again(Phi=Phi + [('not', p)]))
        if k == 'seq':
            first = {y: A for y, A in sorted(D.items()) if self.rng.random() < 0.5}
            x, e1 = self.name('x'), self.expr(depth - 1, Phi, G, dict(first))
            return ('letb', x, e1, again(G=G | {x}, D=D if self.slips() else without(D, first)))
        if k in ('ask', 'askb'):
            a, r, y, u = self.one(ACTIONS), self.name('r'), self.name('y'), self.name('u')
            if k == 'ask':
                p = self.shown(G)
                first, A = ('ask', a, p), ('ok', a, p)
            else:
                t = self.term(G)
                first, A = ('askb', a, t), ('bud', a, t)
            return ('letr', r, first, ('case', var(r), y, again(D={**D, y: A}), u, again()))
        if k in ('act', 'retry', 'runok'):
            y = self.one(oks)
            a, phi = D[y][1], D[y][2]
        if k == 'act':
            t = self.term(G) if self.slips() else self.fitting(Phi, G, lambda t: subp(phi, {'p': t}))
            if t is None:
                return again()
            a2, x = self.one(ACTIONS) if self.slips() else a, self.name('x')
            return ('letb', x, ('act', a2, t, var(y)),
                    again(G=G | {x}, D=D if self.slips() else without(D, {y})))
        if k == 'retry':
            # the model gets some tries to name a payload that the approval covers
            st, t, u, m, z, out, t2, u2 = (self.name(s) for s in 'stumzotu')
            used = ('inr', ('unit',), D[y])
            hit = ('letb', z, ('act', a, v(m), var(t)), ('ret', used))
            body = ('case', var(st), t,
                    ('letb', m, ('model',), ('if', subp(phi, {'p': v(m)}), hit, ('ret', ('inl', var(t), UNIT)))),
                    u, ('ret', used))
            body = self.intruded(body, Phi, G, without(D, {y}))
            loop = ('iter', 1 + self.below(3), ('sum', D[y], UNIT), ('inl', var(y), UNIT), st, body)
            return ('letr', out, loop, ('case', var(out), t2, again(D={**without(D, {y}), t2: D[y]}),
                                        u2, again(D=without(D, {y}))))
        if k == 'runok':
            if self.slips():
                psi = self.shown(set())
            else:
                fits = [eq(v('p'), c(n)) for n in V if entails(Phi, subp(phi, {'p': c(n)}))]
                fits += [] if fvp(phi) - {'p'} else [phi]
                if not fits:
                    return again()
                psi = self.one(fits)
            return self.delegated(('ok', a, psi), y, G, D, again)
        y = self.one(buds)
        a, b = D[y][1], D[y][2]
        if k == 'run':
            fits = list(V) if self.slips() else [m for m in V if entails(Phi, le(c(m), b))]
            return self.delegated(('bud', a, c(self.one(fits))), y, G, D, again)
        if k == 'guard':
            x, y2 = self.name('x'), self.name('y')
            spent = ('letr', y2, ('spend', a, v(x), var(y)),
                     self.expr(depth - 1, Phi + [le(v(x), b)], G | {x},
                               {**without(D, {y}), y2: ('bud', a, sub(b, v(x)))}))
            other = again(G=G | {x})
            branches = (other, spent) if self.slips() else (spent, other)
            return ('letb', x, ('model',), ('if', le(v(x), b)) + branches)
        if k == 'loop':
            # a loop whose state is a budget of an amount that changes
            q, st, x, m, y1, y2 = (self.name(s) for s in 'qsxmyy')
            A = ('ex', q, ('bud', a, v(q)))
            keep = ('ret', ('pack', v(x), var(y1), q, ('bud', a, v(q))))
            pay = ('letr', y2, ('spend', a, v(m), var(y1)),
                   ('ret', ('pack', sub(v(x), v(m)), var(y2), q, ('bud', a, v(q)))))
            body = ('unpack', x, y1, var(st), ('letb', m, ('model',), ('if', le(v(m), v(x)), pay, keep)))
            body = self.intruded(body, Phi, G, without(D, {y}))
            out, x2, y3 = self.name('s'), self.name('x'), self.name('y')
            after = self.expr(depth - 1, Phi, G | {x2}, {**without(D, {y}), y3: ('bud', a, v(x2))})
            return ('letr', out, ('iter', 1 + self.below(3), A, ('pack', b, var(y), q, ('bud', a, v(q))), st, body),
                    ('unpack', x2, y3, var(out), after))
        t = self.term(G) if self.slips() else self.fitting(Phi, G, lambda t: le(t, b))
        if t is None:
            return again()
        if k == 'spend':
            a2, y2 = self.one(ACTIONS) if self.slips() else a, self.name('y')
            left = D if self.slips() else without(D, {y})
            return ('letr', y2, ('spend', a2, t, var(y)), again(D={**left, y2: ('bud', a, sub(b, t))}))
        pr, y1, y2 = self.name('r'), self.name('y'), self.name('y')
        parts = {**without(D, {y}), y1: ('bud', a, t), y2: ('bud', a, sub(b, t))}
        return ('letr', pr, ('split', var(y), t), ('letp', y1, y2, var(pr), again(D=parts)))


# ---------------------------------------------------------------------------------------------
# The programs of Section 2
# ---------------------------------------------------------------------------------------------

def invoice(kind):
    """A payment that is asked for and then made."""
    m, r, t, u = 'm', 'r', 't', 'u'
    paid = {
        'shown': ('letb', 'z', ('act', 'pay', v(m), var(t)), ('ret', ('tm', v('z')))),
        'asked-again': ('letb', 'm2', ('model',),
                        ('letb', 'z', ('act', 'pay', v('m2'), var(t)), ('ret', ('tm', v('z'))))),
        'twice': ('letb', 'z', ('act', 'pay', v(m), var(t)),
                  ('letb', 'z2', ('act', 'pay', v(m), var(t)), ('ret', ('tm', v('z2'))))),
        'other-action': ('letb', 'z', ('act', 'delete', v(m), var(t)), ('ret', ('tm', v('z')))),
    }[kind]
    return ('letb', m, ('model',), ('letr', r, ('ask', 'pay', eq(v('p'), v(m))),
            ('case', var(r), t, paid, u, ('ret', ('tm', c(0))))))


LEFT = ('ex', 'q', ('bud', 'pay', v('q')))      # a budget of some amount that is left


def packed(t, w):
    return ('ret', ('pack', t, w, 'q', ('bud', 'pay', v('q'))))


def invoices(kind):
    """Three payments under one budget."""
    pay = ('letr', 'b2', ('spend', 'pay', v('m'), var('b1')),
           packed(v('n') if kind == 'miscounted' else sub(v('n'), v('m')), var('b2')))
    step = pay if kind == 'unguarded' else ('if', le(v('m'), v('n')), pay, packed(v('n'), var('b1')))
    body = ('unpack', 'n', 'b1', var('st'), ('letb', 'm', ('model',), step))
    loop = ('iter', 3, LEFT, ('pack', c(5), var('b'), 'q', ('bud', 'pay', v('q'))), 'st', body)
    return ('letr', 'r', ('askb', 'pay', c(5)),
            ('case', var('r'), 'b', ('letr', 's', loop, ('ret', ('tm', c(0)))), 'u', ('ret', ('tm', c(0)))))


def delegation(kind):
    """A part of a budget goes to code that the model writes."""
    part = 4 if kind == 'more-than-the-part' else 2
    after = ('letr', 'b3', ('spend', 'pay', c(3), var('b1' if kind == 'part-again' else 'b2')),
             ('ret', ('tm', c(0))))
    rest = ('letr', 'out', ('run', ('bud', 'pay', c(part)), BASE, c(1), var('b1')),
            ('case', var('out'), 'z', after, 'back', ('ret', ('tm', c(0)))))
    return ('letr', 'r', ('askb', 'pay', c(5)),
            ('case', var('r'), 'b',
             ('letr', 'pr', ('split', var('b'), c(2)), ('letp', 'b1', 'b2', var('pr'), rest)),
             'u', ('ret', ('tm', c(0)))))


CODE = {
    # code for an argument `arg`, with the type of its result
    'frugal': (('letb', 'm', ('model',),
                ('if', le(v('m'), c(2)),
                 ('letr', 'y', ('spend', 'pay', v('m'), var('arg')), ('ret', ('tm', v('m')))),
                 ('ret', ('tm', c(0))))), BASE),
    'greedy': (('letr', 'y', ('spend', 'pay', c(3), var('arg')), ('ret', ('tm', c(0)))), BASE),
    'returns-the-rest': (('letb', 'm', ('model',),
                          ('if', le(v('m'), c(2)),
                           ('letr', 'y', ('spend', 'pay', v('m'), var('arg')), packed(sub(c(2), v('m')), var('y'))),
                           packed(c(2), var('arg')))), LEFT),
}


# ---------------------------------------------------------------------------------------------
# 5. The tests
# ---------------------------------------------------------------------------------------------

def size(e):
    """The number of nodes of a syntax tree, with its terms, predicates and types."""
    return 1 + sum(size(part) for part in e if isinstance(part, tuple)) if isinstance(e, tuple) else 0


def has_twice(e, bound):
    """Whether an expression binds a base variable that is already bound."""
    if not isinstance(e, tuple) or not e:
        return False
    if e[0] in ('letb', 'unpack'):
        if e[1] in bound:
            return True
        return any(has_twice(part, bound) for part in e[2:-1]) or has_twice(e[-1], bound | {e[1]})
    return any(has_twice(part, bound) for part in e[1:])


def execute(e, seed):
    """One execution with the ledger and one without it, on the same choices of the model,
    the world and the person.  Raises Blocked if the ledger refuses a step."""
    led = Run(Source(seed), True, check=True)
    value = led.ev(e, {}, {})
    bare = Run(Source(seed), False)
    assert bare.ev(e, {}, {}) == unname(value) and bare.trace == erase(led.trace)
    assert explained(led.trace)
    return led


def refused(e, rng, runs=3):
    """Whether the ledger refuses a step of the program in one of some executions."""
    for _ in range(runs):
        try:
            execute(e, int(rng.random() * 2 ** 32))
        except Blocked:
            return True
    return False


def main(outdir):
    global BROKEN
    rng = random.Random(2026)
    lines, nums = [], {}

    # Table 1 of the paper
    part = ('bud', 'pay', c(2))
    table = [(invoice('shown'), 'accepted'),
             (invoice('asked-again'), 'a payload outside the approval'),
             (invoice('twice'), 'a resource that is not available'),
             (invoice('other-action'), 'an action without its approval'),
             (invoices('guarded'), 'accepted'),
             (invoices('unguarded'), 'a payload above the budget'),
             (invoices('miscounted'), 'the packed value'),
             (delegation('part'), 'accepted'),
             (delegation('more-than-the-part'), 'the argument of the code'),
             (delegation('part-again'), 'a resource that is not available')]
    assert all(verdict(e) == expected for e, expected in table)
    assert verdict(CODE['frugal'][0], {'arg': part}) == 'accepted'
    assert verdict(CODE['greedy'][0], {'arg': part}) == 'a payload above the budget'
    assert accepts_code(CODE['frugal'][0], part, BASE) and not accepts_code(CODE['greedy'][0], part, BASE)
    assert accepts_code(CODE['returns-the-rest'][0], part, LEFT)
    lines.append('the checker gives the verdicts of Table 1 on the programs and the code of Section 2')

    # Theorems 5.3, 5.5, 5.8 and 5.10 on programs that the checker accepts
    typed, gen = [], Gen(rng)
    while len(typed) < 3000:
        typed.append(gen.expr(5, [], set(), {}))
    assert all(well_typed(e) for e in typed)
    wild, lucky, gen = [], 0, Gen(rng, wild=0.1)
    while len(wild) < 3000:
        gen.slipped = 0
        e = gen.expr(5, [], set(), {})
        if well_typed(e):
            wild.append(e)
            lucky += gen.slipped > 0
    acts = grants = asks = written = accepted = 0
    for e in typed + wild:
        for _ in range(3):
            led = execute(e, int(rng.random() * 2 ** 32))
            acts += sum(ev[0] == 'act' for ev in led.trace)
            grants += sum(ev[0] in ('grant', 'budget') for ev in led.trace)
            asks, written, accepted = asks + led.asked, written + led.written, accepted + led.accepted
    lines.append(f'6000 programs that the checker accepts ({lucky} of them built with a rule ignored), three '
                 f'executions each: the ledger refuses no step, the execution without tokens gives the same '
                 f'trace and value, every trace is explained, and no part goes beyond the least ledger of what '
                 f'it was given; {asks} requests, {grants} grants, {acts} actions, {written} pieces of code '
                 f'written by the model, {accepted} of them accepted')
    nums.update(Programs='6,000', Lucky=f'{lucky:,}', Runs='18,000', Asks=f'{asks:,}', Grants=f'{grants:,}',
                Acts=f'{acts:,}', Written=f'{written:,}', Accepted=f'{accepted:,}',
                MedianNodes=str(sorted(size(e) for e in typed + wild)[3000]))

    # Lemma 5.7 on programs that the checker rejects, and what the ledger alone would do.  No
    # variable is bound twice here: that is rejected for the checker's sake, not for consent.
    rejected, gen = [], Gen(rng, wild=0.1, rebind=False)
    while len(rejected) < 3000:
        e = gen.expr(5, [], set(), {})
        if not well_typed(e):
            rejected.append(e)
    stopped = late = quiet = 0
    assert not any(has_twice(e, set()) for e in rejected)
    for e in rejected:
        blocked = False
        for _ in range(20):
            led = Run(Source(int(rng.random() * 2 ** 32)), True)
            try:
                led.ev(e, {}, {})
            except Blocked:
                blocked = True
                stopped += 1
                late += any(ev[0] == 'act' for ev in led.trace)
            assert explained(led.trace)
        quiet += not blocked
    lines.append(f'3000 programs that the checker rejects, twenty executions each: every trace that the ledger '
                 f'lets through is explained; the ledger stops {stopped} of the 60000 executions, {late} of '
                 f'them after an action has been done; {quiet} programs are never stopped')
    nums.update(Rejected='3,000', RejectedRuns='60,000', Stopped=f'{stopped:,}', Late=f'{late:,}',
                StoppedPercent=f'{100 * stopped / 60000:.0f}', LatePercent=f'{100 * late / stopped:.0f}',
                Quiet=f'{quiet:,}', QuietPercent=f'{100 * quiet / len(rejected):.0f}')

    # every rule is needed: a checker without it accepts a program that the ledger refuses
    tries = {}
    for rule in RULES:
        BROKEN = rule
        CACHE.clear()
        gen = Gen(rng, wild=0.15)
        for i in range(1, 100001):
            e = gen.expr(5, [], set(), {})
            if well_typed(e) and refused(e, rng):
                tries[rule] = i
                break
        BROKEN = None
        CACHE.clear()
    assert set(tries) == set(RULES), tries
    assert max(tries, key=tries.get) == 'branch'        # the paper says which rule is the slowest
    lines.append(f'{len(RULES)} checkers with one broken rule each: every one accepts a program that the '
                 'ledger refuses, after ' + ', '.join(f'{rule} {n}' for rule, n in tries.items()) + ' programs')
    nums.update(Rules=str(len(RULES)), Slowest=f'{max(tries.values()):,}')
    for rule, n in tries.items():
        nums['Try' + ''.join(part.capitalize() for part in rule.split('-'))] = f'{n:,}'

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by consent.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
