#!/usr/bin/env python3
"""Tests the claims of "A Compaction Is a Collection" on an implementation of its model.

The file has six parts.

1. Items, how each can be had again, and what a compaction costs.  These definitions are the
   only thing that is trusted: every algorithm is compared with a search over all sets of
   items that uses them.
2. Safety as a cut (Lemma 3.1), the rule of keeping what cannot be had again (Theorem 3.2),
   and garbage (Proposition 3.3).
3. The cheapest compaction for a known need as a minimum cut (Theorem 4.1), with a maximum
   flow written out.
4. Where it gets hard: several ways to have an item again (Theorem 5.1) and the case in
   which no item is used twice (Proposition 5.2), a window with a hard bound and its
   relaxation by a price (Proposition 5.3), and what happens to the kept items as holding
   gets dearer (Proposition 5.4).
5. Not knowing the need: the rule of holding an idle item until the hold paid equals its
   fetch (Theorem 6.1), and needs that have chances (Proposition 6.2).
6. The tests.  `python3 compact.py out` writes out/check.txt, out/numbers.tex and the table.

A test is not a proof.  The proofs are in the paper.
"""
import math
import os
import random
import sys
from itertools import combinations

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked
NEVER = math.inf    # the price of what cannot be had again


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


def subsets(items):
    items = list(items)
    for size in range(len(items) + 1):
        for chosen in combinations(items, size):
            yield frozenset(chosen)


# ---------------------------------------------------------------------------------------------
# 1. A context is a list of items.  Item i costs hold[i] to keep.  ways[i] lists the ways to
#    have it again when it has been dropped: each way is (the items that must then be at hand,
#    the price).  An item with no way cannot be had again.  The items a way names come before
#    the item, so nothing depends on itself.
# ---------------------------------------------------------------------------------------------

def at_hand(context, keep):
    """Every item that can be had from the kept ones, by any ways."""
    have = set(keep)
    changed = True
    while changed:
        changed = False
        for i, ways in enumerate(context['ways']):
            if i not in have and any(set(parents) <= have for parents, _ in ways):
                have.add(i)
                changed = True
    return have


def safe(context, keep, need):
    return set(need) <= at_hand(context, keep)


def price(context, keep, need):
    """What the compaction costs: the hold of what is kept, and the least total price of having
    again whatever of the need is not kept.  NEVER if the need cannot be met."""
    hold = sum(context['hold'][i] for i in keep)
    best = {}

    def again(wanted, have):
        """The least price of making all wanted items at hand, given the set at hand."""
        wanted = frozenset(wanted) - have
        if not wanted:
            return 0
        key = (wanted, have)
        if key not in best:
            i = max(wanted)                             # the latest item: nothing wanted depends on it
            least = NEVER
            for parents, cost in context['ways'][i]:
                rest = again((wanted - {i}) | set(parents), have)
                if rest < NEVER:                        # i is had last, after everything else
                    least = min(least, cost + rest)
            best[key] = least
        return best[key]

    return hold + again(need, frozenset(keep))


def cheapest_by_force(context, need, allowed=None):
    """The least price over all sets of kept items, and one set that has it."""
    least, which = NEVER, None
    for keep in subsets(range(len(context['hold']))):
        if allowed is None or allowed(keep):
            cost = price(context, keep, need)
            if cost < least:
                least, which = cost, keep
    return least, which


# ---------------------------------------------------------------------------------------------
# 2. Safety, for contexts in which every item has at most one way.
# ---------------------------------------------------------------------------------------------

def separated(context, keep, need):
    """Lemma 3.1: whether every chain from a needed item down through the items its way names
    to an item that cannot be had again meets a kept item."""
    def reaches(i):                                     # a chain from i to such an item without a kept item
        if i in keep:
            return False
        if not context['ways'][i]:
            return MUTANT != 'no-roots'
        return any(reaches(p) for p in context['ways'][i][0][0])
    return not any(reaches(i) for i in need)


def marked(context, keep, need):
    """Proposition 3.3: the items that a walk from the need reaches.  The walk goes on from an
    item to the items that its way names only if the item is not kept.  A kept item that is
    not marked is garbage."""
    seen, todo = set(), list(need)
    while todo:
        i = todo.pop()
        if i not in seen:
            seen.add(i)
            if (i not in keep or MUTANT == 'walk-on') and context['ways'][i]:
                todo += list(context['ways'][i][0][0])
    return seen


def pinned(context):
    """Theorem 3.2: the items that cannot be had again."""
    return {i for i, ways in enumerate(context['ways']) if not ways}


# ---------------------------------------------------------------------------------------------
# 3. The cheapest compaction as a minimum cut, for contexts with at most one way per item.
#    Every item has two nodes: `at hand` and `had again`.  On the side of the source, the first
#    says that the item is at hand and the second that it is had again and not kept.
# ---------------------------------------------------------------------------------------------

def maximum_flow(capacity, source, sink):
    """The value of a maximum flow and the nodes on the side of the source of a minimum cut, by
    shortest augmenting paths."""
    flow, total = {}, 0
    nodes = {a for a, _ in capacity} | {b for _, b in capacity}
    room = lambda a, b: capacity.get((a, b), 0) - flow.get((a, b), 0) + flow.get((b, a), 0)
    while True:
        before, front = {source: None}, [source]
        while front and sink not in before:
            a = front.pop(0)
            for b in nodes:
                if b not in before and room(a, b) > 0:
                    before[b] = a
                    front.append(b)
        if sink not in before:
            return total, set(before)
        path, b = [], sink
        while before[b] is not None:
            path.append((before[b], b))
            b = before[b]
        push = min(room(a, b) for a, b in path)
        for a, b in path:
            back = min(push, flow.get((b, a), 0))
            flow[b, a] = flow.get((b, a), 0) - back
            flow[a, b] = flow.get((a, b), 0) + push - back
        total += push


def cheapest_by_cut(context, need):
    """Theorem 4.1: the least price and a set of kept items that has it."""
    n = len(context['hold'])
    huge = 1 + sum(context['hold']) + sum(cost for ways in context['ways'] for _, cost in ways)
    capacity = {}
    for i in range(n):
        capacity[('hand', i), ('again', i)] = context['hold'][i]
        capacity[('again', i), 'sink'] = context['ways'][i][0][1] if context['ways'][i] else huge
        if context['ways'][i] and MUTANT != 'no-parents':
            for p in context['ways'][i][0][0]:
                capacity[('again', i), ('hand', p)] = huge
        if i in need:
            capacity['source', ('hand', i)] = huge
    value, side = maximum_flow(capacity, 'source', 'sink')
    keep = frozenset(i for i in range(n) if ('hand', i) in side and ('again', i) not in side)
    return (NEVER if value >= huge else value), keep


# ---------------------------------------------------------------------------------------------
# 4. Where it gets hard.
# ---------------------------------------------------------------------------------------------

def from_cover(sets, elements):
    """Theorem 5.1: a context whose cheapest compaction keeps a least cover.  Item j < len(sets)
    is a set and cannot be had again.  The other items are the elements: each can be had again
    for nothing from any one set that contains it, and is too dear to keep."""
    dear = len(sets) + 1
    hold = [1] * len(sets) + [dear] * len(elements)
    ways = [[] for _ in sets] + [[((j,), 0) for j, members in enumerate(sets) if e in members] for e in elements]
    return dict(hold=hold, ways=ways), set(range(len(sets), len(sets) + len(elements)))


def least_cover(sets, elements):
    for size in range(len(sets) + 1):
        for chosen in combinations(range(len(sets)), size):
            if set(elements) <= set().union(*[sets[j] for j in chosen]) if chosen else not elements:
                return size
    return None


def cheapest_unshared(context, need):
    """Proposition 5.2: the least price when no item is used twice, that is, when every item is
    needed or is a premise of one way of one item, and not both.  Each item then costs the
    least of its hold and its ways with the premises counted the same way."""
    def least(i):
        return min([context['hold'][i]] + [cost + sum(least(p) for p in parents) for parents, cost in context['ways'][i]])
    return sum(least(i) for i in need)


def holding(context, keep):
    return sum(context['hold'][i] for i in keep)


# ---------------------------------------------------------------------------------------------
# 5. Not knowing the need.  An item that is fetched from outside has a hold per step and a
#    fetch.  It is used at some steps.  Between two uses it is idle, and a rule says for how
#    many idle steps it is held before it is dropped.
# ---------------------------------------------------------------------------------------------

def expected_price(context, keep, chance):
    """Proposition 6.2: the expected price of a compaction when item i is needed with the
    chance chance[i], independently of the others.  An item outside the kept ones is had again
    exactly if some needed item reaches it by a chain of premises through items that are not
    kept; the items from which it is reached so are its `users`."""
    n = len(context['hold'])
    users = {i: {i} for i in range(n) if i not in keep}
    for a in sorted(users, reverse=True):               # a later item names earlier ones
        if context['ways'][a]:
            for p in context['ways'][a][0][0]:
                if p not in keep:
                    users[p] |= users[a]
    total = sum(context['hold'][i] for i in keep)
    for i, above in users.items():
        missing = 1.0
        for a in above:
            missing *= 1 - chance[a]
        if missing < 1:
            if not context['ways'][i]:
                return NEVER
            share = min(1, sum(chance[a] for a in above)) if MUTANT == 'add-chances' else 1 - missing
            total += context['ways'][i][0][1] * share
    return total


def break_even(hold, fetch):
    """Theorem 6.1: hold an idle item as long as the hold paid since its last use stays below
    its fetch."""
    return math.ceil(fetch / hold) if MUTANT == 'one-more' else math.ceil(fetch / hold) - 1


def paid(hold, fetch, gaps, patience):
    """What a rule pays that holds for `patience` idle steps: `gaps` are the idle steps between
    uses, and the last one, after the last use, never ends."""
    total = 0
    for gap in gaps[:-1]:
        total += gap * hold if gap <= patience else patience * hold + fetch
    return total + patience * hold


def least_paid(hold, fetch, gaps):
    """What is paid with the uses known: for every gap the cheaper of holding through it and
    fetching again, and nothing after the last use."""
    return sum(min(gap * hold, fetch) for gap in gaps[:-1])


# ---------------------------------------------------------------------------------------------
# 6. The tests.
# ---------------------------------------------------------------------------------------------

MUTANTS = ('no-roots', 'walk-on', 'no-parents', 'greedy', 'one-more', 'add-chances')


def random_context(rng, n, several=False):
    hold, ways = [], []
    for i in range(n):
        hold.append(rng.randrange(1, 10))
        kinds = []
        for _ in range(rng.choice((1, 2, 2)) if several else 1):
            if rng.random() < 0.25:
                continue                                # this way does not exist
            parents = tuple(sorted(rng.sample(range(i), rng.randrange(0, min(i, 3) + 1)))) if i else ()
            kinds.append((parents, rng.randrange(1, 12)))
        ways.append(kinds)
    return dict(hold=hold, ways=ways)


def keep_by_rule(context, need):
    """A plausible wrong rule, for the planted mistake 'greedy': keep a needed item exactly if
    holding it is cheaper than its own way, and otherwise have it again."""
    keep, todo = set(), list(need)
    while todo:
        i = todo.pop()
        if i in keep:
            continue
        if not context['ways'][i] or context['hold'][i] <= context['ways'][i][0][1]:
            keep.add(i)
        else:
            todo += list(context['ways'][i][0][0])
    return frozenset(keep)


def check_single(rng, counts):
    """Lemma 3.1, Theorems 3.2 and 4.1 and Propositions 5.2 and 5.3 on one random context."""
    n = rng.randrange(2, 9)
    context = random_context(rng, n)
    need = frozenset(i for i in range(n) if rng.random() < 0.4) or frozenset({n - 1})
    for keep in subsets(range(n)):
        assert safe(context, keep, need) == separated(context, keep, need), 'safety is not the cut of Lemma 3.1'
        assert safe(context, keep, need) == (price(context, keep, need) < NEVER)
        if safe(context, keep, need):                   # Proposition 3.3: garbage is what the walk does not reach
            live = marked(context, keep, need)
            for j in keep:
                saved = price(context, keep, need) - price(context, keep - {j}, need)
                assert (saved == context['hold'][j]) == (j not in live), 'garbage is not what the walk from the need misses'
                counts['garbage'] += j not in live
    for _ in range(4):                                  # what cannot be had again, kept: safe for every need
        other = frozenset(i for i in range(n) if rng.random() < 0.5)
        extra = frozenset(i for i in range(n) if rng.random() < 0.3)
        assert safe(context, pinned(context) | extra, other), 'a compaction that keeps what cannot be had again is not safe'
    least, _ = cheapest_by_force(context, need)
    value, keep = cheapest_by_cut(context, need)
    if MUTANT == 'greedy':
        keep = keep_by_rule(context, need)
        value = price(context, keep, need)
    assert value == least, 'the minimum cut is not the cheapest compaction'
    assert price(context, keep, need) == least, 'the kept items of the cut do not have the least price'
    assert keep <= marked(context, keep, need), 'the cheapest compaction keeps garbage'
    counts['contexts'] += 1
    counts['sets'] += 2 ** n
    counts['kept'] += len(keep)
    counts['again'] += len(need - keep)
    counts['pins dropped'] += bool(pinned(context) - keep)
    # Proposition 5.3: the cheapest for a price of space is the cheapest for a window of its own size
    size = [rng.randrange(1, 8) for _ in range(n)]
    for rate in (0, 1, 3):
        priced = dict(hold=[rate * s for s in size], ways=context['ways'])
        cost, chosen = cheapest_by_force(priced, need)
        if cost < NEVER:
            used = sum(size[i] for i in chosen)
            free = dict(hold=[0] * n, ways=context['ways'])
            bounded, _ = cheapest_by_force(free, need, lambda keep: sum(size[i] for i in keep) <= used)
            assert bounded == price(free, chosen, need), 'a window of the same size has a cheaper compaction'
            counts['windows'] += 1
    # Proposition 5.4: as holding gets dearer, the kept items do not form a chain, but less is held
    held, seen = None, []
    for rate in (1, 2, 4, 8, 16):
        priced = dict(hold=[rate * h for h in context['hold']], ways=context['ways'])
        cost, _ = cheapest_by_force(priced, need)
        if cost == NEVER:
            break
        best = [keep for keep in subsets(range(n)) if price(priced, keep, need) == cost]
        assert held is None or max(holding(context, keep) for keep in best) <= held, 'more is held when holding is dearer'
        held = min(holding(context, keep) for keep in best)
        seen.append(best)
    if len(seen) > 1:
        counts['ladders'] += 1
        chain = any(True for _ in nested(seen))
        counts['not nested'] += not chain


def nested(levels):
    """The ways to pick one cheapest set per price of holding so that every set contains the next."""
    def pick(i, above):
        if i == len(levels):
            yield ()
            return
        for keep in levels[i]:
            if above is None or keep <= above:
                for rest in pick(i + 1, keep):
                    yield (keep,) + rest
    return pick(0, None)


def check_several(rng, counts):
    """Theorem 5.1: least covers as compactions, and that the cut is no longer the answer."""
    m, k = rng.randrange(2, 6), rng.randrange(2, 6)
    elements = list(range(k))
    sets = [set(e for e in elements if rng.random() < 0.45) for _ in range(m)]
    context, need = from_cover(sets, elements)
    cover = least_cover(sets, elements)
    least, keep = cheapest_by_force(context, need)
    if cover is None:
        counts['no cover'] += 1
    else:
        assert least == cover and len(keep) == cover, 'the cheapest compaction is not a least cover'
        counts['covers'] += 1
    # random contexts with several ways: the search still answers; count where one way is not enough
    n = rng.randrange(2, 8)
    context = random_context(rng, n, several=True)
    need = frozenset(i for i in range(n) if rng.random() < 0.4) or frozenset({n - 1})
    least, _ = cheapest_by_force(context, need)
    first = dict(hold=context['hold'], ways=[ways[:1] for ways in context['ways']])
    counts['several'] += 1
    counts['first way dearer'] += cheapest_by_force(first, need)[0] > least


def check_unshared(rng, counts):
    """Proposition 5.2 on one random context in which no item is used twice."""
    n = rng.randrange(2, 9)
    free, hold, ways = [], [], []
    for i in range(n):
        hold.append(rng.randrange(1, 10))
        kinds = []
        for _ in range(rng.randrange(0, 3)):
            rng.shuffle(free)
            parents = tuple(sorted(free[:rng.randrange(0, min(len(free), 2) + 1)]))
            free = free[len(parents):]
            kinds.append((parents, rng.randrange(1, 12)))
        ways.append(kinds)
        free.append(i)
    context, need = dict(hold=hold, ways=ways), frozenset(free)
    assert cheapest_unshared(context, need) == cheapest_by_force(context, need)[0], 'the item-by-item rule fails although nothing is used twice'
    counts['unshared'] += 1
    counts['with choice'] += any(len(kinds) > 1 for kinds in ways)


RULES = ('the need', 'the newer half', 'what cannot be had again', 'item by item', 'the cut', 'the cut and what cannot be had again')


def check_rules(rng, totals):
    """What six rules pay on one random session, and whether they are safe."""
    n = rng.randrange(6, 13)
    size, ways = [], []
    for i in range(n):
        kind = rng.choice(('said', 'fetched', 'fetched', 'derived', 'derived')) if i else 'said'
        if kind == 'said':
            size.append(rng.randrange(20, 80))
            ways.append([])
        elif kind == 'fetched':
            size.append(rng.randrange(300, 3000))
            ways.append([((), size[-1] + 200)])
        else:
            size.append(rng.randrange(40, 200))
            ways.append([(tuple(sorted(rng.sample(range(i), rng.randrange(1, min(i, 3) + 1)))), rng.randrange(300, 1500))])
    rate = rng.choice((0.5, 1, 2, 4))
    context = dict(hold=[round(rate * s) for s in size], ways=ways)
    need = frozenset(i for i in range(n) if rng.random() < 0.15 + 0.4 * i / n) or frozenset({n - 1})
    least, best = cheapest_by_cut(context, need)
    keeps = {'the need': need, 'the newer half': frozenset(range(n // 2, n)), 'what cannot be had again': frozenset(pinned(context)),
             'item by item': keep_by_rule(context, need), 'the cut': best,
             'the cut and what cannot be had again': best | pinned(context)}
    other = frozenset(i for i in range(n) if rng.random() < 0.5)       # a need that nobody expected
    for rule, keep in keeps.items():
        cost = price(context, keep, need)
        row = totals.setdefault(rule, dict(paid=0, least=0, unsafe=0, surprised=0))
        if cost == NEVER:
            row['unsafe'] += 1
        else:
            row['paid'] += cost
            row['least'] += least
        row['surprised'] += not safe(context, keep, other)
    assert keeps['the cut and what cannot be had again'] >= best and price(context, best, need) == least
    extra = price(context, best | pinned(context), need) - least
    assert 0 <= extra <= sum(context['hold'][i] for i in pinned(context) - best), 'keeping what cannot be had again costs more than its holds'
    totals['sessions'] = totals.get('sessions', 0) + 1


def check_chances(rng, counts):
    """Proposition 6.2 on one random context with chances."""
    n = rng.randrange(2, 7)
    context = random_context(rng, n)
    chance = [rng.choice((0, 0.1, 0.5, 0.9, 1)) for _ in range(n)]
    needs = []
    for need in subsets(range(n)):
        weight = 1.0
        for i in range(n):
            weight *= chance[i] if i in need else 1 - chance[i]
        if weight:
            needs.append((need, weight))
    best = NEVER
    for keep in subsets(range(n)):
        by_needs = sum(weight * price(context, keep, need) for need, weight in needs)
        mine = expected_price(context, keep, chance)
        assert (mine == NEVER) == (by_needs == NEVER) and (mine == NEVER or abs(mine - by_needs) < 1e-6), 'the expected price is not the mean over the needs'
        best = min(best, mine)
    likely = frozenset(i for i in range(n) if chance[i] >= 0.5)
    possible = frozenset(i for i in range(n) if chance[i] > 0)
    for name, need in (('likely', likely), ('possible', possible)):
        keep = cheapest_by_cut(context, need)[1] | (pinned(context) & at_least(context, possible))
        cost = expected_price(context, keep, chance)
        assert cost < NEVER, 'a cut with what cannot be had again fails for a possible need'
        counts[name + ' paid'] += cost
        counts[name + ' dearer'] += cost > best + 1e-6
    counts['chances'] += 1
    counts['chances least'] += best
    if all(not ways or not ways[0][0] for ways in context['ways']):     # no premises: item by item
        rule = frozenset(i for i in range(n) if chance[i] > 0 and (not context['ways'][i] or context['hold'][i] < chance[i] * context['ways'][i][0][1]))
        assert abs(expected_price(context, rule, chance) - best) < 1e-6, 'without premises the rule by chances is not the cheapest'
        counts['flat'] += 1


def at_least(context, need):
    """The items that some chain of premises from the need reaches."""
    seen, todo = set(), list(need)
    while todo:
        i = todo.pop()
        if i not in seen:
            seen.add(i)
            if context['ways'][i]:
                todo += list(context['ways'][i][0][0])
    return seen


def check_online(rng, counts):
    """Theorem 6.1 on one random item and one random sequence of uses."""
    hold, fetch = rng.randrange(1, 6), rng.randrange(1, 40)
    gaps = [rng.randrange(0, 30) for _ in range(rng.randrange(1, 12))] + [None]
    patience = break_even(hold, fetch)
    mine, best = paid(hold, fetch, gaps, patience), least_paid(hold, fetch, gaps)
    assert mine <= 2 * best + fetch, 'the rule pays more than twice the least and one fetch'
    for gap in gaps[:-1]:
        one, least = paid(hold, fetch, [gap, None], patience) - patience * hold, min(gap * hold, fetch)
        assert one <= 2 * least and (fetch % hold or one * fetch <= (2 * fetch - hold) * least), 'in one gap the rule pays more than the bound'
    # every patience is beaten by a use just after it lets go
    for other in range(0, 3 * math.ceil(fetch / hold) + 2):
        cost = other * hold + fetch
        least = min((other + 1) * hold, fetch)
        assert cost * fetch >= (2 * fetch - hold) * least, 'some patience beats the bound from below'
    counts['sequences'] += 1
    counts['paid'] += mine
    counts['least'] += best


FIELDS = ('chances', 'chances least', 'likely paid', 'likely dearer', 'possible paid', 'possible dearer', 'flat', 'unshared', 'with choice', 'contexts', 'sets', 'garbage', 'kept', 'again', 'pins dropped', 'windows', 'ladders', 'not nested', 'covers', 'no cover',
          'several', 'first way dearer', 'sequences', 'paid', 'least')

# The example of Section 2: a session in which a test is being fixed.
EXAMPLE = [
    # name, tokens, the items its way names, the price of the way (None: cannot be had again)
    ('the instruction of the user', 40, (), None),
    ('the file parser.py', 3000, (), 3200),
    ('the file lexer.py', 2500, (), 2700),
    ('the output of the failing test', 1200, (), 3000),
    ('the result of a search', 300, (), 500),
    ('the finding: where the bug is', 60, (1, 3), 1500),
    ('the decision: the interface stays', 30, (), None),
    ('the plan for the rest', 120, (0, 5, 6), 800),
]
EXAMPLE_NEED = {2, 5, 6, 7}
EXAMPLE_RATES = (0.5, 3, 20)


def catches(name):
    """The check that notices the mistake, or None."""
    global MUTANT
    MUTANT = name
    rng = random.Random(2026)
    counts = dict.fromkeys(FIELDS, 0)
    try:
        for _ in range(150):
            check_single(rng, counts)
            check_online(rng, counts)
            check_chances(rng, counts)
        return None
    except AssertionError as failed:
        return str(failed) or 'a check without a name'
    finally:
        MUTANT = None


def percent(part, whole):
    return f'{100 * part / whole:.0f}'


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten', 'eleven', 'twelve']

    # Section 2: the example, for three prices of holding a token
    ways = [[(parents, cost)] if cost is not None else [] for _, _, parents, cost in EXAMPLE]
    chosen = {}
    for rate in EXAMPLE_RATES:
        context = dict(hold=[round(rate * tokens) for _, tokens, _, _ in EXAMPLE], ways=ways)
        least, keep = cheapest_by_cut(context, EXAMPLE_NEED)
        assert least == cheapest_by_force(context, EXAMPLE_NEED)[0]
        only = [k for k in subsets(range(len(EXAMPLE))) if price(context, k, EXAMPLE_NEED) == least]
        assert only == [keep], 'the example has several cheapest compactions'
        hand = at_hand(context, keep)
        again = set()
        todo = list(EXAMPLE_NEED - keep)
        while todo:
            i = todo.pop()
            if i not in keep and i not in again:
                again.add(i)
                todo += list(ways[i][0][0])
        chosen[rate] = (keep, again, least, price(context, pinned(context) | keep, EXAMPLE_NEED))
    tables['example'] = []
    for i, (name, tokens, parents, cost) in enumerate(EXAMPLE):
        how = 'cannot be had again' if cost is None else f"{cost:,}" + (', from ' + ' and '.join(str(p + 1) for p in parents) if parents else '')
        marks = ' & '.join('kept' if i in chosen[rate][0] else 'again' if i in chosen[rate][1] else '' for rate in EXAMPLE_RATES)
        tables['example'].append(f"{i + 1} & {name} & {tokens:,} & {how} & {marks} \\\\")
    cheap, dear, dearest = (chosen[rate] for rate in EXAMPLE_RATES)
    claim('example', cheap[0] == {2, 5, 6, 7} and not cheap[1] and dear[0] == {5, 6, 7} and dear[1] == {2}
          and dearest[0] == {0, 5, 6} and dearest[1] == {2, 7})
    claim('example-instruction', 0 not in cheap[0] and 0 not in dear[0] and 0 in dearest[0]
          and not dearest[0] <= dear[0] and cheap[3] - cheap[2] == 20 and dear[3] - dear[2] == 120)
    lines.append('the example: ' + '; '.join(f"at {rate} per token kept {sorted(i + 1 for i in keep)}, had again {sorted(i + 1 for i in again)}, "
                                             f"price {least}" for rate, (keep, again, least, _) in chosen.items()))
    nums.update(RateLow='$\\frac{1}{2}$', RateMiddle=str(EXAMPLE_RATES[1]), RateHigh=str(EXAMPLE_RATES[2]))
    nums.update(ExampleCheap=f"{cheap[2]:,}", ExampleDear=f"{dear[2]:,}", ExampleDearest=f"{dearest[2]:,}",
                ExamplePinCheap=str(cheap[3] - cheap[2]), ExamplePinDear=str(dear[3] - dear[2]))

    # random contexts with one way per item
    counts = dict.fromkeys(FIELDS, 0)
    for _ in range(2000):
        check_single(rng, counts)
    claim('single', counts['contexts'] == 2000 and counts['garbage'] > 1000 and counts['again'] > 500 and counts['pins dropped'] > 100 and counts['windows'] > 1000)
    claim('ladder', counts['not nested'] > 0 and counts['ladders'] > 1000)
    lines.append(f"{counts['contexts']} random contexts of two to eight items, {counts['sets']} sets of kept items: a set is safe exactly "
                 f"if it cuts every chain from the need to what cannot be had again; keeping what cannot be had again is safe for "
                 f"every need; a kept item is garbage exactly if the walk from the need misses it ({counts['garbage']} cases); the minimum cut has the least price; the cheapest compactions keep {counts['kept']} items and have "
                 f"{counts['again']} needed items again; {counts['pins dropped']} of them drop an item that cannot be had again")
    lines.append(f"{counts['windows']} cheapest compactions for a price of space: none is beaten in a window of its own size; "
                 f"of {counts['ladders']} contexts with holding made dearer step by step, less is held at every step, and in "
                 f"{counts['not nested']} no choice of cheapest sets is a chain")
    nums.update(Garbage=f"{counts['garbage']:,}", Kept=f"{counts['kept']:,}", Again=f"{counts['again']:,}")
    nums.update(Contexts=f"{counts['contexts']:,}", Sets=f"{counts['sets']:,}", PinsDropped=f"{counts['pins dropped']:,}",
                Windows=f"{counts['windows']:,}", Ladders=f"{counts['ladders']:,}", NotNested=f"{counts['not nested']:,}")

    # several ways
    for _ in range(600):
        check_several(rng, counts)
    claim('several', counts['covers'] > 300 and counts['first way dearer'] > 0)
    lines.append(f"{counts['covers']} random families of sets with a cover: the cheapest compaction of the context of Theorem 5.1 keeps "
                 f"a least cover; of {counts['several']} random contexts with several ways, the first way alone is dearer in "
                 f"{counts['first way dearer']}")
    nums.update(Covers=f"{counts['covers']:,}", Several=f"{counts['several']:,}", FirstDearer=f"{counts['first way dearer']:,}")

    # nothing used twice
    for _ in range(1500):
        check_unshared(rng, counts)
    claim('unshared', counts['unshared'] == 1500 and counts['with choice'] > 500)
    lines.append(f"{counts['unshared']} random contexts in which no item is used twice, {counts['with choice']} with an item that has "
                 f"two ways: the item-by-item rule has the least price")
    nums.update(Unshared=f"{counts['unshared']:,}", WithChoice=f"{counts['with choice']:,}")

    # rules of thumb on random sessions
    totals = {}
    for _ in range(2000):
        check_rules(rng, totals)
    tables['rules'] = []
    for rule in RULES:
        row = totals[rule]
        ratio = f"{row['paid'] / row['least']:.2f}" if row['least'] else '--'
        tables['rules'].append(f"keep {rule} & {percent(row['unsafe'], totals['sessions'])} & {ratio} & "
                               f"{percent(row['surprised'], totals['sessions'])} \\\\")
        lines.append(f"the rule 'keep {rule}': unsafe for the need in {row['unsafe']} of {totals['sessions']} sessions, pays "
                     f"{ratio} times the least where it is safe, unsafe for another need in {row['surprised']}")
    claim('rules', totals['the cut']['paid'] == totals['the cut']['least'] and totals['the newer half']['unsafe'] > 0
          and all(totals[rule]['unsafe'] == 0 for rule in RULES if rule != 'the newer half')
          and totals['the cut and what cannot be had again']['surprised'] == 0 == totals['what cannot be had again']['surprised']
          and totals['the cut']['surprised'] > 0
          and totals['the cut and what cannot be had again']['paid'] < 1.1 * totals['the cut']['paid']
          and totals['the need']['paid'] > 1.1 * totals['the cut']['paid'])
    nums.update(Sessions=f"{totals['sessions']:,}",
                RuleNeed=f"{totals['the need']['paid'] / totals['the need']['least']:.2f}",
                RulePins=f"{totals['what cannot be had again']['paid'] / totals['what cannot be had again']['least']:.2f}",
                RuleOwn=f"{totals['item by item']['paid'] / totals['item by item']['least']:.2f}",
                RuleBoth=f"{totals['the cut and what cannot be had again']['paid'] / totals['the cut and what cannot be had again']['least']:.2f}",
                RuleNewestUnsafe=percent(totals['the newer half']['unsafe'], totals['sessions']),
                RuleCutSurprised=percent(totals['the cut']['surprised'], totals['sessions']))

    # not knowing the need
    for _ in range(5000):
        check_online(rng, counts)
    worst = max((break_even(1, fetch) + fetch) / min(break_even(1, fetch) + 1, fetch) for fetch in range(1, 200))
    claim('online', counts['sequences'] == 5000 and counts['paid'] <= 2 * counts['least'] + 5000 * 40 and 1.99 < worst < 2
          and counts['paid'] > counts['least'])
    lines.append(f"{counts['sequences']} random sequences of uses: the rule pays {counts['paid']} where knowing the uses pays "
                 f"{counts['least']}, never more than twice that and one fetch; its worst gap costs up to {worst:.3f} times the least")
    nums.update(Sequences=f"{counts['sequences']:,}", OnlineRatio=f"{counts['paid'] / counts['least']:.2f}")

    # needs with chances
    for _ in range(1500):
        check_chances(rng, counts)
    claim('chances', counts['chances'] == 1500 and counts['flat'] > 20 and counts['likely dearer'] > 0 and counts['possible dearer'] > 0)
    lines.append(f"{counts['chances']} random contexts with chances: the expected price is the mean over all needs; without premises "
                 f"({counts['flat']} contexts) the rule by chances is the cheapest; the cut for the likely need is dearer than the "
                 f"cheapest in {counts['likely dearer']} contexts and pays {counts['likely paid'] / counts['chances least']:.2f} times "
                 f"the least in total, the cut for the possible need in {counts['possible dearer']} and {counts['possible paid'] / counts['chances least']:.2f} times")
    nums.update(Chances=f"{counts['chances']:,}", Flat=str(counts['flat']), LikelyDearer=f"{counts['likely dearer']:,}",
                LikelyRatio=f"{counts['likely paid'] / counts['chances least']:.2f}", PossibleDearer=f"{counts['possible dearer']:,}",
                PossibleRatio=f"{counts['possible paid'] / counts['chances least']:.2f}")

    # Theorem 6.1 with the price of a held token: for how many idle steps a file is worth holding
    tables['patience'] = []
    for tokens in (300, 3000, 30000):
        cells = [str(break_even(share * tokens, tokens + 200)) for share in (1 / 10, 1 / 20, 1 / 40)]
        tables['patience'].append(f"{tokens:,} & " + ' & '.join(cells) + ' \\\\')
    claim('patience', break_even(300, 3200) == 10 and break_even(75, 3200) == 42 and break_even(7.5, 500) == 66)
    lines.append('the patience of the break-even rule for files of 300, 3000 and 30000 tokens: ' + '; '.join(row.replace(' \\\\', '') for row in tables['patience']))

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)],
                Size=f"{round(len(open(os.path.join(here, 'compact.py')).readlines()), -2):,}")

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
        f.write('% written by compact.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by compact.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
