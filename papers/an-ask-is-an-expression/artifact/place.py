#!/usr/bin/env python3
"""Tests the claims of "An Ask Is an Expression" on an implementation of its analyses.

The file has seven parts.

1. Programs with actions that need an approval and actions that make one stale, and their
   flow graphs.
2. The four analyses of lazy code motion, read for approvals, and the placements they give.
3. Exact checks of a placement that do not use the analyses: whether every use is covered,
   whether an ask can be in vain, which of two placements asks more on some path, and whether
   one holds approvals where the other does not.
4. Probabilities: how often a node is visited, and what a placement costs on average.
5. Asking in vain on purpose: the cheapest placement as a minimum cut.
6. Several kinds of approval: how few interruptions serve them all.
7. The tests.  `python3 place.py out` writes out/check.txt, out/numbers.tex and the tables.

A test is not a proof.  The proofs are in the paper and in the work that it builds on.
"""
import os
import random
import sys
from fractions import Fraction
from itertools import combinations, product

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. A program is a list of statements.  A statement is an action, a choice, or a loop:
#      ('act', label, {kind: role})     role 'u' needs a valid approval of that kind,
#                                       'k' makes approvals of that kind stale,
#                                       'uk' needs one and then makes it stale
#      ('if', probability, then, else)
#      ('while', probability of another round, body)
#    The flow graph has one node for every action and a node without effect on every edge
#    that leads to a node with several predecessors, so that an ask can be put on that edge.
# ---------------------------------------------------------------------------------------------

class Graph:
    def __init__(self, prog, split=True):
        self.succ, self.pred, self.role, self.label, self.prob = [], [], [], [], {}
        self.split = split and MUTANT != 'no-split'
        self.start = self.node('start')
        last = self.seq(prog, self.start)
        self.end = self.node('end')
        self.edge(last, self.end)
        self.kinds = sorted({k for r in self.role for k in r})

    def node(self, label, role=None):
        self.succ.append([])
        self.pred.append([])
        self.role.append(dict(role or {}))
        self.label.append(label)
        return len(self.succ) - 1

    def edge(self, m, n, p=Fraction(1)):
        self.succ[m].append(n)
        self.pred[n].append(m)
        self.prob[(m, n)] = p

    def into_join(self, m, n, p=Fraction(1)):
        """An edge to a node that has several predecessors gets a node of its own."""
        if self.split or n in self.succ[m]:
            mid = self.node(f'{self.label[m]}>{self.label[n]}')
            self.edge(m, mid, p)
            self.edge(mid, n)
        else:
            self.edge(m, n, p)

    def seq(self, prog, cur):
        for st in prog:
            if st[0] == 'act':
                n = self.node(st[1], st[2])
                self.edge(cur, n)
                cur = n
            elif st[0] == 'if':
                branch, join = self.node('if'), self.node('fi')
                self.edge(cur, branch)
                for p, part in ((st[1], st[2]), (1 - st[1], st[3])):
                    if part:
                        first = self.node(part[0][1], part[0][2]) if part[0][0] == 'act' else self.node('then')
                        self.edge(branch, first, p)
                        last = self.seq(part[1:] if part[0][0] == 'act' else part, first)
                        self.into_join(last, join)
                    else:
                        self.into_join(branch, join, p)
                cur = join
            else:
                head = self.node('while')
                self.into_join(cur, head)
                first = self.node('do')
                self.edge(head, first, st[1])
                self.into_join(self.seq(st[2], first), head)
                after = self.node('done')
                self.edge(head, after, 1 - st[1])
                cur = after
        return cur

    def nodes(self):
        return range(len(self.succ))

    def needs(self, kind):
        return [('u' in r.get(kind, '')) for r in self.role]

    def kills(self, kind):
        return [('k' in r.get(kind, '')) for r in self.role]


def act(label, **roles):
    return ('act', label, roles)


def random_program(rng, size, kinds, depth=0):
    """A random program with about `size` actions."""
    prog = []
    while size > 0:
        r = rng.random()
        if depth < 2 and size >= 2 and r < 0.22:
            half = 1 + int(rng.random() * (size - 1))
            p = Fraction(1 + int(rng.random() * 7), 8)
            prog.append(('if', p, random_program(rng, half, kinds, depth + 1),
                         random_program(rng, int(rng.random() * (size - half + 1)), kinds, depth + 1)))
            size -= half + 1
        elif depth < 2 and size >= 2 and r < 0.36:
            body = 1 + int(rng.random() * (size - 1))
            p = Fraction(1 + int(rng.random() * 6), 8)
            prog.append(('while', p, random_program(rng, body, kinds, depth + 1)))
            size -= body + 1
        else:
            kind = kinds[int(rng.random() * len(kinds))]
            r = rng.random()
            role = 'u' if r < 0.5 else 'k' if r < 0.8 else 'uk' if r < 0.9 else ''
            prog.append(('act', role or 'skip', {kind: role} if role else {}))
            size -= 1
    return prog


# ---------------------------------------------------------------------------------------------
# 2. The analyses of Knoop, Ruething and Steffen for one kind of approval.  `needs` plays the
#    part of a computation of the expression and `kills` that of a change to its operands.
# ---------------------------------------------------------------------------------------------

def fixpoint(g, start, step):
    val = [start] * len(g.succ)
    changed = True
    while changed:
        changed = False
        for n in g.nodes():
            new = step(n, val)
            if new != val[n]:
                val[n], changed = new, True
    return val


def analyses(g, kind):
    needs, kills = g.needs(kind), g.kills(kind)
    if MUTANT == 'stale':
        kills = [False] * len(kills)             # forgets that an approval can go stale
    # an ask here is used on every path before the approval goes stale
    dsafe = fixpoint(g, True, lambda n, v: needs[n] or (
        not kills[n] and n != g.end and all(v[m] for m in g.succ[n])))
    # on some path no earlier node could hold the ask
    some = all if MUTANT == 'every-path' else any
    earliest = fixpoint(g, False, lambda n, v: n == g.start or bool(g.pred[n]) and some(
        kills[m] or (not dsafe[m] and v[m]) for m in g.pred[n]))
    first = [dsafe[n] and earliest[n] for n in g.nodes()]
    # the ask can be put off until here on every path
    through = (lambda m: True) if MUTANT == 'past-use' else (lambda m: not needs[m])
    delay = fixpoint(g, True, lambda n, v: first[n] or (
        n != g.start and bool(g.pred[n]) and all(through(m) and v[m] for m in g.pred[n])))
    latest = [delay[n] and (needs[n] or not all(delay[m] for m in g.succ[n]) or MUTANT == 'too-often')
              for n in g.nodes()]
    return dict(needs=needs, kills=kills, dsafe=dsafe, earliest=earliest, first=first, delay=delay, latest=latest)


def placements(g, kind):
    """The four placements that the paper compares, as sets of nodes at whose entry to ask."""
    a = analyses(g, kind)
    naive = {n for n in g.nodes() if a['needs'][n]}
    eager = {g.start} | {m for n in g.nodes() if a['kills'][n] for m in g.succ[n]}
    return dict(naive=naive, eager=eager, earliest={n for n in g.nodes() if a['first'][n]},
                lazy={n for n in g.nodes() if a['latest'][n]})


# ---------------------------------------------------------------------------------------------
# 3. Exact checks.  None of them uses the analyses of part 2.  Inside a node the order is:
#    the ask, if one is placed there; the use; the change that makes approvals stale.
# ---------------------------------------------------------------------------------------------

def safe(g, kind, asks):
    """On every path, every action that needs an approval finds a valid one."""
    needs, kills = g.needs(kind), g.kills(kind)
    seen, todo = {(g.start, False)}, [(g.start, False)]
    while todo:
        n, valid = todo.pop()
        valid = valid or n in asks
        if needs[n] and not valid:
            return False
        valid = valid and not kills[n]
        for m in g.succ[n]:
            if (m, valid) not in seen:
                seen.add((m, valid))
                todo.append((m, valid))
    return True


def vain(g, kind, n):
    """An ask at this node is in vain on some path: the approval goes stale, or the program
    ends, before any action uses it."""
    needs, kills = g.needs(kind), g.kills(kind)
    seen, todo = {n}, [n]
    while todo:
        x = todo.pop()
        if needs[x]:
            continue
        if kills[x] or x == g.end:
            return True
        for m in g.succ[x]:
            if m not in seen:
                seen.add(m)
                todo.append(m)
    return False


def frugal(g, kind, asks):
    return not any(vain(g, kind, n) for n in asks)


def asks_more(g, a, b):
    """Some path from start to end on which placement a asks more often than placement b."""
    weight = [(n in a) - (n in b) for n in g.nodes()]
    best = [None] * len(g.succ)
    best[g.start] = weight[g.start]
    for _ in range(len(g.succ) + 1):
        changed = False
        for m in g.nodes():
            if best[m] is None:
                continue
            for n in g.succ[m]:
                if best[n] is None or best[m] + weight[n] > best[n]:
                    best[n], changed = best[m] + weight[n], True
        if not changed:
            return best[g.end] > 0
    return True                                     # a loop on which a asks more


def holds_more(g, kind, a, b):
    """Some path and some position on it into which placement a carries an approval that is
    used later, and placement b does not.  An approval is carried into a position if it was
    asked for earlier and has not gone stale; it is used later if an action that needs it
    follows before a change and before another ask of the same placement."""
    needs, kills = g.needs(kind), g.kills(kind)

    def used_but(n, carried_b):
        seen, todo = set(), [(n, False)]
        while todo:
            x, saw_b = todo.pop()
            if x in a:
                continue
            saw_b = saw_b or x in b
            if needs[x]:
                if not carried_b or saw_b:
                    return True
                continue
            if kills[x]:
                continue
            for m in g.succ[x]:
                if (m, saw_b) not in seen:
                    seen.add((m, saw_b))
                    todo.append((m, saw_b))
        return False

    seen, todo = {(g.start, False, False)}, [(g.start, False, False)]
    while todo:
        n, ca, cb = todo.pop()
        if ca and used_but(n, cb):
            return True
        ca, cb = (ca or n in a) and not kills[n], (cb or n in b) and not kills[n]
        for m in g.succ[n]:
            if (m, ca, cb) not in seen:
                seen.add((m, ca, cb))
                todo.append((m, ca, cb))
    return False


def all_placements(g, kind, among):
    """Every safe placement within the given nodes."""
    among = sorted(among)
    for size in range(len(among) + 1):
        for chosen in combinations(among, size):
            if safe(g, kind, set(chosen)):
                yield set(chosen)


# ---------------------------------------------------------------------------------------------
# 4. Probabilities.  Every branch has a probability; the numbers of visits and the costs of a
#    placement are expectations, computed exactly with fractions.
# ---------------------------------------------------------------------------------------------

def solve(rows, rhs):
    """Solves a sparse system: rows[i] maps a column to its coefficient."""
    n = len(rows)
    for i in range(n):
        pivot = rows[i][i]
        for r in range(i + 1, n):
            c = rows[r].get(i)
            if c:
                f = c / pivot
                for col, val in rows[i].items():
                    new = rows[r].get(col, 0) - f * val
                    if new:
                        rows[r][col] = new
                    else:
                        rows[r].pop(col, None)
                rhs[r] -= f * rhs[i]
    x = [Fraction(0)] * n
    for i in reversed(range(n)):
        x[i] = (rhs[i] - sum(val * x[col] for col, val in rows[i].items() if col != i)) / rows[i][i]
    return x


def visits(g):
    """How often each node is entered in one run, on average."""
    rows = [{n: Fraction(1)} for n in g.nodes()]
    for (m, n), p in g.prob.items():
        rows[n][m] = rows[n].get(m, 0) - p
    return solve(rows, [Fraction(int(n == g.start)) for n in g.nodes()])


def reach(g, value):
    """For every node the probability of an event that `value` decides where it can: it
    returns 0 or 1 for a node that settles the matter and None for a node to pass through."""
    rows, rhs = [], []
    for n in g.nodes():
        v = value(n)
        rows.append({n: Fraction(1)})
        rhs.append(Fraction(v or 0))
        if v is None:
            for m in g.succ[n]:
                rows[n][m] = rows[n].get(m, 0) - g.prob[(n, m)]
    return solve(rows, rhs)


def costs(g, kind, asks, freq=None):
    """What a placement costs in one run, on average: asks, asks in vain, positions into which
    an approval is carried and later used (held), positions into which a valid approval is
    carried when it is dropped wherever no path can use it any more (kept), and positions
    into which a valid approval is carried at all."""
    needs, kills = g.needs(kind), g.kills(kind)
    freq = freq or visits(g)
    settle = lambda n: 1 if needs[n] else 0 if kills[n] or n == g.end else None
    used = reach(g, settle)                                       # a fresh ask here is used
    later = reach(g, lambda n: 0 if n in asks else settle(n))     # a carried approval is used
    # how often a node is entered with a valid approval: states (node, carried)
    index = {(n, c): 2 * n + c for n in g.nodes() for c in (0, 1)}
    rows = [{i: Fraction(1)} for i in range(len(index))]
    for n in g.nodes():
        for c in (0, 1):
            after = int((c or n in asks) and not kills[n])
            for m in g.succ[n]:
                row = rows[index[(m, after)]]
                row[index[(n, c)]] = row.get(index[(n, c)], 0) - g.prob[(n, m)]
    rhs = [Fraction(0)] * len(index)
    rhs[index[(g.start, 0)]] = Fraction(1)
    carried = solve(rows, rhs)
    return dict(asks=sum(freq[n] for n in asks),
                vain=sum(freq[n] * (1 - used[n]) for n in asks),
                held=sum(carried[index[(n, 1)]] * later[n] for n in g.nodes()),
                kept=sum(carried[index[(n, 1)]] for n in g.nodes() if later[n] > 0),
                carried=sum(carried[index[(n, 1)]] for n in g.nodes()))


# ---------------------------------------------------------------------------------------------
# 5. Asking in vain on purpose.  Every path from a point where no approval is valid (the start,
#    or just after a change) to the first action that needs one must pass an ask.  The
#    cheapest set of nodes that meets all these paths is a minimum cut, with the number of
#    visits as the price of a node.
# ---------------------------------------------------------------------------------------------

def min_cut(g, kind, freq=None):
    needs, kills = g.needs(kind), g.kills(kind)
    freq = freq or visits(g)
    big = sum(freq) + 1
    cap = {'source': {}, 'sink': {}}

    def arc(a, b, c):
        cap.setdefault(a, {})[b] = cap.get(a, {}).get(b, 0) + c
        cap.setdefault(b, {}).setdefault(a, Fraction(0))

    for n in g.nodes():
        arc(('in', n), ('out', n), Fraction(1) if MUTANT == 'unit-price' else freq[n])
        if n == g.start:
            arc('source', ('in', n), big)
        if needs[n]:
            arc(('out', n), 'sink', big)
        for m in g.succ[n]:
            if kills[n]:
                arc('source', ('in', m), big)
            elif not needs[n]:
                arc(('out', n), ('in', m), big)
    value = Fraction(0)
    while True:
        back, todo = {'source': None}, ['source']
        for a in todo:
            for b, c in cap[a].items():
                if c > 0 and b not in back:
                    back[b] = a
                    todo.append(b)
        if 'sink' not in back:
            break
        path, b = [], 'sink'
        while back[b] is not None:
            path.append((back[b], b))
            b = back[b]
        push = min(cap[a][b] for a, b in path)
        for a, b in path:
            cap[a][b] -= push
            cap[b][a] += push
        value += push
    # the cut nearest to the uses: the nodes whose way out still reaches the sink
    side, todo = {'sink'}, ['sink']
    for b in todo:
        for a in cap[b]:
            if cap[a][b] > 0 and a not in side:
                side.add(a)
                todo.append(a)
    return value, {n for n in g.nodes() if ('out', n) in side and ('in', n) not in side}


def rotate(prog):
    """Turns every loop `while c do B` into `if c then (B; while c do B)`, so that there is a
    place that is passed exactly when the loop runs at least once."""
    out = []
    for st in prog:
        if st[0] == 'if':
            out.append(('if', st[1], rotate(st[2]), rotate(st[3])))
        elif st[0] == 'while':
            body = rotate(st[2])
            out.append(('if', st[1], body + [('while', st[1], body)], []))
        else:
            out.append(st)
    return out


# ---------------------------------------------------------------------------------------------
# 6. Several kinds of approval.  An interruption is a node at which some kind is asked for.
# ---------------------------------------------------------------------------------------------

def intervals(g, kind):
    """In a program without branches: for every ask of the lazy placement, the positions
    from the earliest to the latest at which it can be put."""
    a = analyses(g, kind)
    out, first = [], None
    for n in g.nodes():                       # the nodes of a straight line are in order
        if a['first'][n]:
            first = n
        if a['latest'][n]:
            out.append((first, n))
    return out


def held_on_line(g, kind, asks):
    """In a program without branches: the number of positions at which an approval is held."""
    needs, kills = g.needs(kind), g.kills(kind)
    total, asked, used = 0, None, None
    for n in g.nodes():
        if n in asks:
            total += used - asked if used is not None else 0
            asked, used = n, None
        if needs[n] and asked is not None:
            used = n
        if kills[n]:
            total += used - asked if used is not None else 0
            asked, used = None, None
    return total + (used - asked if used is not None else 0)


def pierce(spans):
    """The fewest points that meet every interval: always take the end of the interval that
    ends first among those not yet met."""
    points = []
    for lo, hi in sorted(spans, key=lambda s: s[1]):
        if not points or points[-1] < lo:
            points.append(lo if MUTANT == 'left-end' else hi)
    return points


def fewest_points(spans):
    """The same number by trying every choice."""
    return min(len(set(choice)) for choice in product(*[range(lo, hi + 1) for lo, hi in spans])) if spans else 0


def cover_program(vertices, edges):
    """The flow graph of Theorem 6.2 for a graph.  One kind is needed at the very beginning.
    Every edge {u, v} has a kind of its own, which goes stale at a node of its own, then
    passes the shared node of u and the shared node of v, and is needed at a node of its own."""
    g = Graph([])
    g.succ, g.pred, g.role, g.label, g.prob = [], [], [], [], {}
    g.start, g.end = g.node('start'), g.node('end')
    first = g.node('use', {'first': 'u'})
    g.edge(g.start, first)
    shared = {v: g.node(f'x{v}') for v in vertices}
    for u, v in edges:
        kind = f'{u}-{v}'
        stale, use = g.node('stale', {kind: 'k'}), g.node('use', {kind: 'u'})
        for a, b in ((first, stale), (stale, shared[u]), (shared[u], shared[v]), (shared[v], use), (use, g.end)):
            if b not in g.succ[a]:
                g.edge(a, b)
    g.kinds = sorted({k for r in g.role for k in r})
    return g, shared


def fewest_nodes(g, limit):
    """The least number of nodes, up to the limit, that hold a safe placement of every kind."""
    for size in range(limit + 1):
        for chosen in combinations(g.nodes(), size):
            if all(safe(g, kind, set(chosen)) for kind in g.kinds):
                return size
    return None


def vertex_cover(vertices, edges):
    return min(size for size in range(len(vertices) + 1) for chosen in combinations(vertices, size)
               if all(u in chosen or v in chosen for u, v in edges))


# ---------------------------------------------------------------------------------------------
# 7. The tests.
# ---------------------------------------------------------------------------------------------

HALF, QUARTER = Fraction(1, 2), Fraction(1, 4)

# A release: edit until the tests pass, commit, pull, perhaps resolve conflicts and commit
# again, then tag and push.  The approval of the diff goes stale with every edit, and the
# approval of the history with every commit and every pull.
RELEASE = [act('edit', diff='k'),
           ('while', HALF, [act('test'), act('edit', diff='k')]),
           act('test'),
           act('commit', diff='u', history='k'),
           act('pull', history='k'),
           ('if', QUARTER, [act('resolve', diff='k'), act('commit', diff='u', history='k')], []),
           act('tag', history='u'),
           act('push', history='u')]

# A deployment: one round for every host.  Nothing makes these approvals stale.
DEPLOY = [act('build'),
          ('while', Fraction(3, 4), [act('copy', deploy='u'), act('restart', restart='u')]),
          act('report')]

# A cleanup: every deletion needs an approval of its own.
CLEANUP = [act('list'),
           ('while', Fraction(2, 3), [act('delete', delete='uk')]),
           act('report')]

CASES = [('release', RELEASE), ('deployment', DEPLOY), ('cleanup', CLEANUP)]


def total(g, name, freq, key):
    """A cost of one of the placements, summed over the kinds of the program."""
    out = Fraction(0)
    for kind in g.kinds:
        asks = min_cut(g, kind, freq)[1] if name == 'cut' else placements(g, kind)[name]
        out += costs(g, kind, asks, freq)[key]
    return out


def exhaustive(rng, counts):
    """Theorems 4.3 and 4.4 and Lemma 4.2 on one small random program, against every safe
    placement that never asks in vain."""
    g = Graph(random_program(rng, 2 + int(rng.random() * 5), ['p']))
    if len(g.succ) > 16:
        return
    p, a = placements(g, 'p'), analyses(g, 'p')
    for name in p:
        assert safe(g, 'p', p[name]), f'the {name} placement leaves an action without a valid approval'
    for name in ('naive', 'earliest', 'lazy'):
        assert frugal(g, 'p', p[name]), f'the {name} placement asks in vain'
    points = [n for n in g.nodes() if not vain(g, 'p', n)]
    assert points == [n for n in g.nodes() if a['dsafe'][n]], 'an ask is in vain exactly where it is not anticipated'
    assert not asks_more(g, p['lazy'], p['earliest']), 'the lazy placement asks more often than the earliest'
    assert not asks_more(g, p['earliest'], p['lazy']), 'the earliest placement asks more often than the lazy'
    for other in all_placements(g, 'p', points):
        counts['placements'] += 1
        assert not asks_more(g, p['earliest'], other), 'a placement asks less often than the earliest on some path'
        if not asks_more(g, other, p['lazy']):
            counts['optimal'] += 1
            assert not holds_more(g, 'p', p['lazy'], other), 'the lazy placement holds an approval where another does not'
    counts['graphs'] += 1
    counts['nodes'] += len(g.succ)


def cheapest(rng, counts):
    """Theorem 5.2 on one small random program, against every safe placement."""
    g = Graph(random_program(rng, 2 + int(rng.random() * 5), ['p']))
    if len(g.succ) > 14:
        return
    freq = visits(g)
    value, cut = min_cut(g, 'p', freq)
    assert safe(g, 'p', cut), 'the cut leaves an action without a valid approval'
    best = min(sum(freq[n] for n in other) for other in all_placements(g, 'p', g.nodes()))
    assert sum(freq[n] for n in cut) == best, 'the cut is not the cheapest safe placement'
    lazy = sum(freq[n] for n in placements(g, 'p')['lazy'])
    counts['cuts'] += 1
    counts['cheaper'] += best < lazy


def line(rng, counts):
    """Theorem 6.1 on one random program without branches and with three kinds."""
    kinds = ['p', 'q', 'r']
    prog = []
    for _ in range(3 + int(rng.random() * 7)):
        kind = kinds[int(rng.random() * 3)]
        prog.append(('act', 'a', {kind: ('u', 'u', 'k', 'uk')[int(rng.random() * 4)]}))
    g = Graph(prog)
    spans = {kind: intervals(g, kind) for kind in g.kinds}
    points = pierce([s for kind in spans for s in spans[kind]])
    assert len(points) == fewest_points([s for kind in spans for s in spans[kind]]), 'fewer interruptions are possible'
    assert fewest_nodes(g, len(points)) == len(points), 'a smaller set of nodes is safe for every kind'
    for kind in g.kinds:
        p = placements(g, kind)
        chosen = {next(x for x in points if lo <= x <= hi) for lo, hi in spans[kind]}
        assert safe(g, kind, chosen), 'the chosen interruptions leave an action without a valid approval'
        assert frugal(g, kind, chosen) and not asks_more(g, chosen, p['lazy']), 'the chosen interruptions ask too often'
        assert held_on_line(g, kind, p['lazy']) == costs(g, kind, p['lazy'])['held'], 'two counts of held positions differ'
        for name, asks in (('lazy', p['lazy']), ('earliest', p['earliest']), ('greedy', chosen)):
            counts[f'held-{name}'] += held_on_line(g, kind, asks)
    counts['lines'] += 1
    counts['line-greedy'] += len(points)
    counts['line-lazy'] += len({n for kind in g.kinds for n in placements(g, kind)['lazy']})
    counts['line-earliest'] += len({n for kind in g.kinds for n in placements(g, kind)['earliest']})


FIELDS = ('graphs', 'nodes', 'placements', 'optimal', 'cuts', 'cheaper', 'lines', 'line-greedy', 'line-lazy',
          'line-earliest', 'held-lazy', 'held-earliest', 'held-greedy')
MUTANTS = ('no-split', 'stale', 'every-path', 'past-use', 'too-often', 'unit-price', 'left-end')


def catches(name):
    """The check that notices the mistake, or None."""
    global MUTANT
    MUTANT = name
    rng, counts = random.Random(2026), dict.fromkeys(FIELDS, 0)
    try:
        for _ in range(150):
            exhaustive(rng, counts)
            cheapest(rng, counts)
            line(rng, counts)
        return None
    except AssertionError as failed:
        return str(failed) or 'a check without a name'
    finally:
        MUTANT = None


def number(x):
    return f'{float(x):.2f}'


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten']
    counts = dict.fromkeys(FIELDS, 0)

    # Section 2: the release
    g = Graph(RELEASE)
    freq = visits(g)
    where = {kind: {name: sorted(g.label[n] for n in nodes) for name, nodes in placements(g, kind).items()}
             for kind in g.kinds}
    asks = {name: total(g, name, freq, 'asks') for name in ('naive', 'eager', 'earliest', 'lazy', 'cut')}
    held = {name: total(g, name, freq, 'held') for name in ('naive', 'eager', 'earliest', 'lazy', 'cut')}
    claim('example', where['diff']['naive'] == where['diff']['lazy'] == ['commit', 'commit']
          and where['history']['naive'] == ['push', 'tag'] and where['history']['lazy'] == ['tag']
          and where['diff']['earliest'] == ['commit', 'done'] and where['history']['earliest'] == ['commit>fi', 'if>fi']
          and where['diff']['eager'] == ['commit', 'edit>while', 'edit>while', 'start']
          and where['history']['eager'] == ['commit>fi', 'if', 'pull', 'start']
          and asks['naive'] == Fraction(13, 4) and asks['lazy'] == asks['earliest'] == Fraction(9, 4)
          and asks['eager'] > asks['naive'] and held['lazy'] < held['earliest'] < held['eager']
          and held['naive'] == 0 and all(safe(g, kind, placements(g, kind)['lazy']) for kind in g.kinds))
    for kind in g.kinds:
        lines.append(f'release, {kind}: ' + '; '.join(f"{name} at {', '.join(where[kind][name])}" for name in where[kind]))
    lines.append('release, asks in one run: ' + ', '.join(f'{name} {asks[name]}' for name in asks))
    lines.append('release, positions with a held approval: ' + ', '.join(f'{name} {held[name]}' for name in held))
    nums.update(ReleaseNaive=number(asks['naive']), ReleaseLazy=number(asks['lazy']), ReleaseEager=number(asks['eager']),
                ReleaseHeldNaive=number(held['naive']), ReleaseHeldLazy=number(held['lazy']), ReleaseHeldEarliest=number(held['earliest']),
                ReleaseHeldEager=number(held['eager']))

    # Section 7: every placement of small programs (Theorems 4.3 and 4.4)
    for _ in range(1500):
        exhaustive(rng, counts)
    claim('frugal', counts['graphs'] > 1000)
    claim('earliest', counts['placements'] > 100000)
    claim('lazy', counts['optimal'] > 1000)
    lines.append(f"{counts['graphs']} small programs with {counts['nodes']} nodes in all: an ask is in vain exactly "
                 f"where the analysis says so; {counts['placements']} safe placements that never ask in vain, none asks "
                 f"less often than the earliest on any path; {counts['optimal']} of them ask as rarely as the lazy one, "
                 f"and the lazy one holds an approval nowhere that they do not")
    nums.update(Graphs=f"{counts['graphs']:,}", Placements=f"{counts['placements']:,}", Optimal=f"{counts['optimal']:,}",
                Seed='2026')

    # Corollary 4.5: approvals that are used up
    same = 0
    for _ in range(300):
        prog = random_program(rng, 3 + int(rng.random() * 6), ['p'])
        once = [(st if st[0] != 'act' else ('act', st[1], {k: 'uk' for k in st[2]})) for st in prog]
        fix = lambda p: [('act', s[1], {k: 'uk' for k in s[2]}) if s[0] == 'act' else
                         ('if', s[1], fix(s[2]), fix(s[3])) if s[0] == 'if' else ('while', s[1], fix(s[2])) for s in p]
        g = Graph(fix(once))
        p = placements(g, 'p')
        same += p['lazy'] == p['naive']
    claim('one-shot', same == 300)
    lines.append(f'{same} programs in which every use makes the approval stale: the lazy placement asks at the uses')
    nums.update(OneShot=str(same))

    # Table 4: what the placements cost on average
    names = ('naive', 'eager', 'earliest', 'lazy', 'cut')
    keys = ('asks', 'vain', 'held', 'kept', 'carried')
    sums = {name: dict.fromkeys(keys, Fraction(0)) for name in names}
    programs, order = 0, True
    while programs < 200:
        g = Graph(random_program(rng, 6 + int(rng.random() * 7), ['p']))
        if len(g.succ) > 40:
            continue
        freq = visits(g)
        p = placements(g, 'p')
        p['cut'] = min_cut(g, 'p', freq)[1]
        cost = {name: costs(g, 'p', p[name], freq) for name in names}
        order = order and (cost['lazy']['asks'] == cost['earliest']['asks'] <= cost['naive']['asks']
                           and cost['cut']['asks'] <= cost['lazy']['asks']
                           and cost['lazy']['held'] <= cost['earliest']['held'] <= cost['eager']['held']
                           and cost['naive']['vain'] == cost['earliest']['vain'] == cost['lazy']['vain'] == 0
                           and cost['naive']['held'] == 0 and safe(g, 'p', p['cut'])
                           and all(c['held'] <= c['kept'] <= c['carried'] for c in cost.values()))
        for name in names:
            for key in keys:
                sums[name][key] += cost[name][key]
        programs += 1
    mean = {name: {key: sums[name][key] / programs for key in keys} for name in names}
    shown = dict(naive='at every use', eager='whenever none is valid', earliest='earliest', lazy='lazy',
                 cut='cheapest, also in vain')
    tables['costs'] = [f"{shown[name]} & " + ' & '.join(number(mean[name][key]) for key in keys) + ' \\\\' for name in names]
    claim('costs', order and mean['lazy']['asks'] < mean['naive']['asks'] and mean['cut']['asks'] < mean['lazy']['asks']
          and mean['cut']['vain'] > 0 and mean['eager']['vain'] > mean['cut']['vain']
          and mean['lazy']['held'] < mean['cut']['held'] < mean['eager']['held'])
    for name in names:
        lines.append(f'{programs} programs, {name}: ' + ', '.join(f'{key} {number(mean[name][key])}' for key in keys))
    nums.update(Programs=str(programs))

    # Theorem 5.2 against every safe placement
    for _ in range(600):
        cheapest(rng, counts)
    claim('cut', counts['cuts'] > 400 and counts['cheaper'] > 0)
    lines.append(f"{counts['cuts']} small programs: the minimum cut is the cheapest of all safe placements; it is cheaper "
                 f"than the lazy placement for {counts['cheaper']} of them")
    nums.update(Cuts=str(counts['cuts']), Cheaper=str(counts['cheaper']))

    # Table 3: a loop
    rows, facts = [], True
    for eighths in (1, 2, 4, 6, 7):
        p = Fraction(eighths, 8)
        prog = [('while', p, [act('use', p='u')])]
        plain, turned = Graph(prog), Graph(rotate(prog))
        row = [costs(plain, 'p', placements(plain, 'p')['naive'])['asks'],
               costs(plain, 'p', placements(plain, 'p')['lazy'])['asks'], min_cut(plain, 'p')[0],
               costs(turned, 'p', placements(turned, 'p')['lazy'])['asks'], min_cut(turned, 'p')[0]]
        facts = facts and row[0] == row[1] == p / (1 - p) and row[2] == min(1, p / (1 - p)) and row[3] == row[4] == p
        rows.append(f"{p.numerator}/{p.denominator} & " + ' & '.join(number(x) for x in row) + ' \\\\')
        lines.append(f'a loop that goes on with probability {p}: ' + ', '.join(str(x) for x in row))
    tables['loop'] = rows
    claim('loop', facts)

    # Table 5: three workflows
    rows, case = [], {}
    for name, prog in CASES:
        g, turned = Graph(prog), Graph(rotate(prog))
        freq, freq2 = visits(g), visits(turned)
        row = [total(g, 'naive', freq, 'asks'), total(g, 'eager', freq, 'asks'), total(g, 'lazy', freq, 'asks'),
               total(turned, 'lazy', freq2, 'asks'), total(g, 'cut', freq, 'asks'),
               total(g, 'eager', freq, 'held'), total(g, 'earliest', freq, 'held'), total(g, 'lazy', freq, 'held')]
        case[name] = row
        assert all(safe(h, kind, placements(h, kind)[which]) for h in (g, turned) for kind in h.kinds
                   for which in ('naive', 'eager', 'earliest', 'lazy'))
        rows.append(f'{name} & ' + ' & '.join(number(x) for x in row) + ' \\\\')
        lines.append(f'{name}: ' + ', '.join(str(x) for x in row))
    tables['cases'] = rows
    claim('cases', case['release'][2] < case['release'][0] and case['deployment'][2] == case['deployment'][0]
          and case['deployment'][3] < case['deployment'][4] < case['deployment'][2]
          and len(set(case['cleanup'][:1] + case['cleanup'][2:5])) == 1
          and all(r[7] <= r[6] <= r[5] for r in case.values()))
    nums.update(DeployNaive=number(case['deployment'][0]), DeployTurned=number(case['deployment'][3]),
                DeployCut=number(case['deployment'][4]))

    # Theorem 6.1: programs without branches
    for _ in range(500):
        line(rng, counts)
    claim('line', counts['lines'] == 500 and counts['line-greedy'] < counts['line-earliest'] < counts['line-lazy']
          and counts['held-lazy'] < counts['held-greedy'] < counts['held-earliest'])
    lines.append(f"{counts['lines']} programs without branches and with three kinds: the greedy choice needs the fewest "
                 f"interruptions; on average {number(Fraction(counts['line-greedy'], counts['lines']))}, where the lazy "
                 f"placements need {number(Fraction(counts['line-lazy'], counts['lines']))} and the earliest "
                 f"{number(Fraction(counts['line-earliest'], counts['lines']))}")
    nums.update(Lines=str(counts['lines']), LineGreedy=number(Fraction(counts['line-greedy'], counts['lines'])),
                LineLazy=number(Fraction(counts['line-lazy'], counts['lines'])),
                LineEarliest=number(Fraction(counts['line-earliest'], counts['lines'])),
                HeldLazy=number(Fraction(counts['held-lazy'], counts['lines'])),
                HeldEarliest=number(Fraction(counts['held-earliest'], counts['lines'])),
                HeldGreedy=number(Fraction(counts['held-greedy'], counts['lines'])))
    lines.append(f"  positions with a held approval: lazy {number(Fraction(counts['held-lazy'], counts['lines']))}, "
                 f"earliest {number(Fraction(counts['held-earliest'], counts['lines']))}, greedy "
                 f"{number(Fraction(counts['held-greedy'], counts['lines']))}")

    # Section 6 on programs with branches and two kinds: how many interruptions in one run
    sums, done, strict = dict.fromkeys(('lazy', 'earliest', 'best'), Fraction(0)), 0, 0
    while done < 150:
        g = Graph(random_program(rng, 3 + int(rng.random() * 4), ['p', 'q']))
        if len(g.succ) > 14 or len(g.kinds) < 2:
            continue
        freq = visits(g)
        p = {kind: placements(g, kind) for kind in g.kinds}
        options = {kind: [o for o in all_placements(g, kind, [n for n in g.nodes() if not vain(g, kind, n)])
                          if not asks_more(g, o, p[kind]['lazy'])] for kind in g.kinds}
        price = lambda sets: sum(freq[n] for n in set().union(*sets))
        best = min(price(choice) for choice in product(*options.values()))
        lazy, earliest = price([p[k]['lazy'] for k in g.kinds]), price([p[k]['earliest'] for k in g.kinds])
        assert best <= lazy and best <= earliest
        strict += best < min(lazy, earliest)
        for name, value in (('lazy', lazy), ('earliest', earliest), ('best', best)):
            sums[name] += value
        done += 1
    claim('kinds', sums['best'] < sums['earliest'] < sums['lazy'] and strict > 0)
    lines.append(f'{done} programs with branches and two kinds, interruptions in one run: lazy '
                 f"{number(sums['lazy'] / done)}, earliest {number(sums['earliest'] / done)}, the best choice of "
                 f"placements that ask as rarely {number(sums['best'] / done)}; the best is better than both for {strict}")
    nums.update(Branching=str(done), KindsLazy=number(sums['lazy'] / done), KindsEarliest=number(sums['earliest'] / done),
                KindsBest=number(sums['best'] / done), KindsStrict=str(strict))

    # Theorem 6.2: the reduction from vertex cover
    covers = 0
    while covers < 60:
        nv = 3 + int(rng.random() * 3)
        edges = [(u, v) for u in range(nv) for v in range(u + 1, nv) if rng.random() < 0.45]
        if not edges or len(edges) > 6:
            continue
        g, _ = cover_program(range(nv), edges)
        assert fewest_nodes(g, vertex_cover(range(nv), edges) + 1) == vertex_cover(range(nv), edges) + 1, edges
        covers += 1
    claim('hard', covers == 60)
    lines.append(f'{covers} random graphs: the least number of interruptions for the program of the reduction is the '
                 f'size of the least vertex cover and one more')
    nums.update(Covers=str(covers))

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)],
                Size=f"{round(len(open(os.path.join(here, 'place.py')).readlines()), -2):,}")

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
        f.write('% written by place.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by place.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
