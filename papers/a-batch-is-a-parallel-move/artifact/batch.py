#!/usr/bin/env python3
"""Tests the claims of "A Batch Is a Parallel Move" on an implementation of its model.

The file has five parts.

1. Calls with footprints, and what a batch does: in the listed order, in any order, and at
   once.  A call is run symbolically: what it writes and returns is a term that records the
   call and everything that it read.  Two runs that give the same terms give the same state
   and results whatever the calls compute, and two runs that give different terms differ for
   some calls with these footprints.  These runs are the only thing that is trusted.
2. Independent calls (Theorem 3.1), the orders that give the meaning at once (Theorem 3.2),
   and the listed order (Corollary 3.3).
3. Rounds (Theorem 4.1), and calls that start as soon as they may (Theorem 4.2).
4. Snapshots: for a harness that picks the order (Theorem 5.1), the hardness of the fewest
   keys (Theorem 5.2), moves (Proposition 5.3), and a harness that runs everything at the
   same time (Proposition 5.4).  Calls that fail (Proposition 6.1) and footprints that are
   declared too large (Proposition 6.2).  Batches in stages, of which the listed order and
   the meaning at once are the two ends (Theorem 7.1 and Corollary 7.2).
5. The tests.  `python3 batch.py out` writes out/check.txt, out/numbers.tex and the tables.

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


def subsets(items):
    items = list(items)
    for size in range(len(items) + 1):
        for chosen in combinations(items, size):
            yield frozenset(chosen)


# ---------------------------------------------------------------------------------------------
# 1. A call is (reads, writes): two sets of keys.  A batch is a list of calls.  A state gives
#    every key a value.  An outcome is the state after the batch and the result of every call.
# ---------------------------------------------------------------------------------------------

def keys_of(batch):
    return sorted({key for reads, writes in batch for key in reads | writes})


def run_one(batch, i, view, state, results, failed=frozenset()):
    """Call i reads its keys in `view` and writes its keys in `state`.  A call that fails writes
    nothing and returns that it failed."""
    reads, writes = batch[i]
    if i in failed:
        results[i] = ('failed', i)
        return
    seen = tuple((key, view[key]) for key in sorted(reads))
    for key in writes:
        state[key] = ('written', i, key, seen)
    results[i] = ('result', i, seen)


def outcome(state, results):
    return tuple(sorted(state.items())), tuple(sorted(results.items()))


def in_order(batch, order, snapshot=frozenset(), failed=frozenset()):
    """The outcome of running the calls one at a time in this order.  A key of `snapshot` is
    read as it was before the batch."""
    old = {key: ('old', key) for key in keys_of(batch)}
    state, results = dict(old), {}
    for i in order:
        view = {key: old[key] if key in snapshot else state[key] for key in state}
        run_one(batch, i, view, state, results, failed)
    return outcome(state, results)


def at_once(batch, failed=frozenset()):
    """The meaning at once: every call reads the state before the batch, and then all writes
    are made.  None if two calls write the same key."""
    written = [key for _, writes in batch for key in writes]
    if len(written) != len(set(written)) and MUTANT != 'last-writer':
        return None
    old = {key: ('old', key) for key in keys_of(batch)}
    state, results = dict(old), {}
    for i in range(len(batch)):
        run_one(batch, i, old, state, results, failed)
    return outcome(state, results)


def torn(result):
    """Whether two calls of an outcome have read different values of one key."""
    seen = {}
    for _, term in result[1]:
        if term[0] == 'result':
            for key, value in term[2]:
                if seen.setdefault(key, value) != value:
                    return True
    return False


# ---------------------------------------------------------------------------------------------
# 2. Footprints.
# ---------------------------------------------------------------------------------------------

def independent(batch):
    """Theorem 3.1: no call reads or writes a key that another call writes."""
    return all(not (batch[c][1] & (batch[d][0] | batch[d][1])) for c in range(len(batch)) for d in range(len(batch)) if c != d)


def write_disjoint(batch):
    return all(not (batch[c][1] & batch[d][1]) for c in range(len(batch)) for d in range(c))


def before(batch, snapshot=frozenset()):
    """Theorem 3.2: the pairs (c, d) such that call c reads a key that call d writes, and so
    must run before it.  Keys of the snapshot do not count."""
    pairs = {(c, d) for c in range(len(batch)) for d in range(len(batch))
             if (c != d or MUTANT == 'own-key') and (batch[c][0] & batch[d][1]) - snapshot}
    return {(d, c) for c, d in pairs} if MUTANT == 'writer-first' else pairs


def respects(order, pairs):
    place = {c: i for i, c in enumerate(order)}
    return all(place[c] < place[d] for c, d in pairs)


def sorted_by(n, pairs):
    """An order of 0..n-1 that respects the pairs, or None if they have a cycle."""
    order = []
    while len(order) < n:
        ready = [c for c in range(n) if c not in order and all(a in order for a, b in pairs if b == c)]
        if not ready:
            return None
        order.append(ready[0])
    return order


def listed_is_at_once(batch):
    """Corollary 3.3: no call reads a key that a call listed before it writes."""
    return write_disjoint(batch) and not any(batch[c][0] & batch[d][1] for c in range(len(batch)) for d in range(c))


# ---------------------------------------------------------------------------------------------
# 3. Rounds.  The calls of a round run at the same time, in whatever order; the rounds follow
#    one another.
# ---------------------------------------------------------------------------------------------

def longest_time(n, pairs, time):
    """For every call the largest total time of a chain that ends in it."""
    heavy = {}
    for c in sorted_by(n, pairs):
        heavy[c] = time[c] + max([heavy[a] for a, b in pairs if b == c], default=0)
    return heavy


def longest_chain(n, pairs):
    """Theorem 4.1: the number of calls on a longest chain c1 before c2 before ..., or None if
    the pairs have a cycle."""
    order = sorted_by(n, pairs)
    if order is None:
        return None
    depth = {}
    for c in order:
        depth[c] = 1 + max([depth[a] for a, b in pairs if b == c], default=0)
    return max(depth.values(), default=0)


def as_soon(n, pairs, time):
    """Theorem 4.2: when every call starts and ends if it starts as soon as the calls that must
    run before it have ended.  time[c] is how long call c takes."""
    span = {}
    for c in sorted_by(n, pairs):
        start = max([span[a][1] for a, b in pairs if b == c], default=0)
        span[c] = (start, start + (1 if MUTANT == 'unit-time' else time[c]))
    return span


def in_rounds(n, pairs, time):
    """How long the plan in rounds of Theorem 4.1 takes: every round as long as its slowest call."""
    depth = {}
    for c in sorted_by(n, pairs):
        depth[c] = 1 + max([depth[a] for a, b in pairs if b == c], default=0)
    return sum(max(time[c] for c in range(n) if depth[c] == level) for level in set(depth.values()))


def rounds_by_force(batch, wanted=None):
    """The fewest rounds such that every way of running them gives the wanted outcome (the
    meaning at once, if none is named), by trying every division into rounds; None if no
    division does."""
    n, wanted = len(batch), wanted or at_once(batch)
    for count in range(1, n + 1):
        for rounds in product(range(count), repeat=n):
            if len(set(rounds)) != count:
                continue
            groups = [[c for c in range(n) if rounds[c] == r] for r in range(count)]
            orders = [sum(parts, ()) for parts in product(*[list(permutations(group)) for group in groups])]
            if all(in_order(batch, order) == wanted for order in orders):
                return count
    return None


def in_stages(batch, stage):
    """The meaning in stages: stage[i] is the stage of call i.  The calls of a stage run at once
    on the state that the stages before it left.  None if two calls of one stage write one key."""
    state, results = {key: ('old', key) for key in keys_of(batch)}, {}
    for number in sorted(set(stage)):
        calls = [i for i in range(len(batch)) if stage[i] == number]
        written = [key for i in calls for key in batch[i][1]]
        if len(written) != len(set(written)):
            return None
        view = dict(state)
        for i in calls:
            run_one(batch, i, view, state, results)
    return outcome(state, results)


def leads(batch, stage):
    """Theorem 7.1: the pairs (c, d) such that c must run before d.  In one stage: c reads a key
    that d writes.  From an earlier stage to a later one: the two calls conflict, that is, one
    of them writes a key that the other reads or writes."""
    pairs = set()
    for c in range(len(batch)):
        for d in range(len(batch)):
            if c != d and stage[c] == stage[d] and batch[c][0] & batch[d][1]:
                pairs.add((c, d))
            if stage[c] < stage[d] and (batch[c][1] & (batch[d][0] | batch[d][1])
                                         or (batch[c][0] & batch[d][1] and MUTANT != 'late-reader')):
                pairs.add((c, d))
    return pairs


# ---------------------------------------------------------------------------------------------
# 4. Snapshots.
# ---------------------------------------------------------------------------------------------

def fewest_snapshot(batch):
    """Theorem 5.1: a smallest set of keys with which some order gives the meaning at once."""
    for snapshot in subsets(keys_of(batch)):            # by size
        if sorted_by(len(batch), before(batch, snapshot)) is not None:
            return snapshot
    return None


def fewest_snapshot_by_force(batch):
    wanted = at_once(batch)
    for snapshot in subsets(keys_of(batch)):
        if any(in_order(batch, order, snapshot) == wanted for order in permutations(range(len(batch)))):
            return len(snapshot)
    return None


def shared(batch):
    """Proposition 5.4: the keys that one call reads and another writes."""
    return frozenset(key for c in range(len(batch)) for d in range(len(batch)) if c != d for key in batch[c][0] & batch[d][1])


def cheapest_for_moves(batch, weight):
    """Proposition 5.3 with prices: for every cycle the cheapest of its keys.  Every call reads
    at most one key that another writes."""
    n = len(batch)
    writer = {key: c for c in range(n) for key in batch[c][1]}
    source = {c: key for c in range(n) for key in batch[c][0] if key in writer and writer[key] != c}
    total, seen = 0, set()
    for start in range(n):
        path, c = [], start
        while c in source and c not in seen:
            seen.add(c)
            path.append(c)
            c = writer[source[c]]
        if c in path:
            total += min(weight[source[d]] for d in path[path.index(c):])
    return total


def cycles(n, pairs):
    """The number of cycles when every call is before at most one other."""
    after = dict(pairs)
    assert len(after) == len(pairs), 'a call is before two others'
    found, seen = 0, set()
    for start in range(n):
        path, c = [], start
        while c is not None and c not in seen:
            seen.add(c)
            path.append(c)
            c = after.get(c)
        found += c in path
    return 1 if MUTANT == 'one-cycle' and found else found


def from_graph(n, edges):
    """Theorem 5.2: a batch for a directed graph.  Call v writes the key of v and reads the keys
    of the vertices that its edges lead to.  A set of keys is a snapshot with which the batch
    has an order exactly if the vertices of the keys meet every cycle of the graph."""
    return [(frozenset(f'k{u}' for v2, u in edges if v2 == v), frozenset({f'k{v}'})) for v in range(n)]


def fewest_feedback(n, edges):
    for chosen in subsets(range(n)):
        left = {(a, b) for a, b in edges if a not in chosen and b not in chosen}
        if sorted_by(n, left) is not None:
            return len(chosen)


# ---------------------------------------------------------------------------------------------
# 5. The tests.
# ---------------------------------------------------------------------------------------------

MUTANTS = ('last-writer', 'own-key', 'writer-first', 'same-round', 'unit-time', 'one-cycle', 'some-shared', 'late-reader')


def random_batch(rng, n, keys, disjoint):
    while True:
        batch = []
        for _ in range(n):
            reads = frozenset(key for key in keys if rng.random() < 0.35)
            writes = frozenset(key for key in keys if rng.random() < 0.25)
            batch.append((reads, writes))
        if not disjoint or write_disjoint(batch):
            return batch


def check_batch(rng, counts):
    """Theorems 3.1, 3.2, 4.1, 5.1 and Propositions 5.3 and 5.4 on one random batch."""
    n = rng.randrange(2, 5)
    keys = 'abcd'[:rng.randrange(2, 5)]
    batch = random_batch(rng, n, keys, disjoint=rng.random() < 0.8)
    wanted = at_once(batch)
    orders = list(permutations(range(n)))
    results = {order: in_order(batch, order) for order in orders}
    kind = None
    # Theorem 3.1
    same = wanted is not None and all(result == wanted for result in results.values())
    assert same == independent(batch), 'every order gives the meaning at once without the calls being independent, or the reverse'
    if not write_disjoint(batch):
        assert wanted is None, 'two calls write one key and the batch has a meaning at once'
        assert len({result[0] for result in results.values()}) > 1, 'two calls write one key and every order leaves the same state'
        counts['two writers'] += 1
        return
    # Theorem 3.2 and Corollary 3.3
    pairs = before(batch)
    for order in orders:
        assert (results[order] == wanted) == respects(order, pairs), 'an order gives the meaning at once without respecting the pairs, or the reverse'
    assert (results[tuple(range(n))] == wanted) == listed_is_at_once(batch), 'the listed order'
    found = sorted_by(n, pairs)
    assert (found is None) == (not any(result == wanted for result in results.values())), 'sorting the pairs'
    # Theorem 4.1
    least = rounds_by_force(batch)
    chain = longest_chain(n, pairs)
    if MUTANT == 'same-round' and chain:
        chain = max(1, chain - 1)
    assert least == chain, 'the fewest rounds are not the longest chain'
    # Theorem 4.2: start every call as soon as it may
    if found is not None:
        time = [rng.randrange(1, 10) for _ in range(n)]
        span = as_soon(n, pairs, time)
        overlap_free = [order for order in orders if all(order.index(c) < order.index(d) for c in range(n) for d in range(n)
                                                         if c != d and span[c][1] <= span[d][0])]
        assert overlap_free and all(results[order] == wanted for order in overlap_free), 'starting as soon as possible does not give the meaning at once'
        end = max(finish for _, finish in span.values())
        heaviest = max(longest_time(n, pairs, time).values())
        assert end == heaviest, 'starting as soon as possible does not end with the heaviest chain'
        assert end <= in_rounds(n, pairs, time), 'rounds are faster than starting as soon as possible'
        counts['soon'] += end
        counts['slow'] += in_rounds(n, pairs, time)
        counts['one by one'] += sum(time)
        counts['timed'] += 1
    # Theorem 5.1 and Proposition 5.4
    snapshot = fewest_snapshot(batch)
    assert len(snapshot) == fewest_snapshot_by_force(batch), 'the fewest keys of a snapshot'
    order = sorted_by(n, before(batch, snapshot))
    assert in_order(batch, order, snapshot) == wanted, 'the order with the snapshot does not give the meaning at once'
    every = shared(batch)
    for chosen in subsets(keys_of(batch)):
        all_orders = all(in_order(batch, order, chosen) == wanted for order in orders)
        enough = bool(chosen & every) or not every if MUTANT == 'some-shared' else every <= chosen
        assert all_orders == enough, 'a snapshot under which every order works, or does not'
    # Proposition 5.3
    if all(len({key for d in range(n) if d != c for key in batch[c][0] & batch[d][1]}) <= 1 for c in range(n)):
        assert len(snapshot) == cycles(n, pairs), 'the fewest keys are not the number of cycles'
        weight = {key: rng.randrange(1, 10) for key in keys_of(batch)}
        cheapest = min(sum(weight[key] for key in chosen) for chosen in subsets(keys_of(batch))
                       if sorted_by(n, before(batch, chosen)) is not None)
        assert cheapest == cheapest_for_moves(batch, weight), 'the cheapest snapshot of moves is not the cheapest key of every cycle'
        counts['moves'] += 1
        counts['move cycles'] += cycles(n, pairs)
    # one state: at once, no two calls see different values of a key; in some order they may
    assert not torn(wanted), 'two calls of the meaning at once read different values of one key'
    counts['torn'] += any(torn(result) for result in results.values())
    # Proposition 6.1: a call that fails changes nothing for the others
    failed = frozenset(c for c in range(n) if rng.random() < 0.3)
    partly = at_once(batch, failed)
    for order in orders:
        if respects(order, pairs):
            assert in_order(batch, order, failed=failed) == partly, 'a failure changes what an order gives'
    for c in range(n):
        if c not in failed:
            assert dict(partly[1])[c] == dict(wanted[1])[c], 'a failure changes the result of another call'
            assert all(dict(partly[0])[key] == dict(wanted[0])[key] for key in batch[c][1]), 'a failure changes what another call writes'
    if failed and not listed_is_at_once(batch):
        listed, hurt = in_order(batch, tuple(range(n))), in_order(batch, tuple(range(n)), failed=failed)
        counts['spread'] += any(dict(hurt[1])[c] != dict(listed[1])[c] for c in range(n) if c not in failed)
        counts['listed and failed'] += 1
    # Proposition 6.2: footprints that are declared too large are safe
    wider = [(reads | frozenset(k for k in keys if rng.random() < 0.2), writes | frozenset(k for k in keys if rng.random() < 0.1))
             for reads, writes in batch]
    if write_disjoint(wider):
        declared = before(wider)
        for order in orders:
            assert not respects(order, declared) or results[order] == wanted, 'an order for larger footprints fails for the true ones'
        if sorted_by(n, declared) is not None:
            assert longest_chain(n, declared) >= chain, 'larger footprints need fewer rounds'
        assert len(fewest_snapshot(wider)) >= len(snapshot), 'larger footprints need fewer keys in the snapshot'
        counts['wider'] += 1
    kind = ('independent' if independent(batch) else 'listed' if listed_is_at_once(batch) else 'reorder' if found is not None else 'cycle')
    counts[kind] += 1
    counts['batches'] += 1
    counts['orders'] += len(orders)
    counts['rounds'] += least or 0
    counts['snapshot keys'] += len(snapshot)
    counts['shared keys'] += len(every)


def check_stages(rng, counts):
    """Theorem 7.1 and Corollary 7.2 on one random batch in stages."""
    n = rng.randrange(2, 5)
    keys = 'abc'[:rng.randrange(2, 4)]
    while True:
        batch = random_batch(rng, n, keys, disjoint=False)
        stage = [rng.randrange(3) for _ in range(n)]
        wanted = in_stages(batch, stage)
        if wanted is not None:
            break
    pairs = leads(batch, stage)
    orders = list(permutations(range(n)))
    once = write_disjoint(batch)                        # no key is written by two calls of the whole batch
    more = False
    for order in orders:
        gives = in_order(batch, order) == wanted
        assert gives or not respects(order, pairs), 'an order respects the pairs and does not give the meaning in stages'
        assert respects(order, pairs) or not gives or not once, 'an order gives the meaning in stages without respecting the pairs'
        more = more or (gives and not respects(order, pairs))
    least, chain = rounds_by_force(batch, wanted), longest_chain(n, pairs)
    if chain is None:
        assert least is None or not once, 'a batch in stages with a cycle has a plan'
    else:
        assert least <= chain and (least == chain or not once), 'the fewest rounds of a batch in stages'
    counts['more orders'] += more
    if len(set(stage)) == 1:
        assert wanted == at_once(batch) and pairs == before(batch), 'one stage is not the meaning at once'
    # Corollary 7.2: every call a stage of its own is the listed order
    alone = list(range(n))
    listed = in_order(batch, tuple(range(n)))
    assert in_stages(batch, alone) == listed, 'one call per stage is not the listed order'
    conflicts = leads(batch, alone)
    for order in orders:
        gives = in_order(batch, order) == listed
        assert (gives or not respects(order, conflicts)) and (respects(order, conflicts) or not gives or not once), 'the listed order and its conflicts'
    least = longest_chain(n, conflicts)
    assert rounds_by_force(batch, listed) <= least, 'the rounds of the listed order'
    counts['staged'] += 1
    counts['staged rounds'] += longest_chain(n, pairs) or 0
    counts['listed rounds'] += least
    counts['listed calls'] += n


def check_graph(rng, counts):
    """Theorem 5.2 on one random directed graph."""
    n = rng.randrange(2, 6)
    edges = {(a, b) for a in range(n) for b in range(n) if a != b and rng.random() < 0.3}
    batch = from_graph(n, edges)
    assert before(batch) == edges, 'the batch of a graph has other pairs than the edges'
    assert len(fewest_snapshot(batch)) == fewest_feedback(n, edges), 'the fewest keys are not a least set that meets every cycle'
    counts['graphs'] += 1
    counts['with cycle'] += fewest_feedback(n, edges) > 0


FIELDS = ('soon', 'slow', 'one by one', 'timed', 'more orders', 'staged', 'staged rounds', 'listed rounds', 'listed calls', 'torn', 'spread', 'listed and failed', 'wider', 'batches', 'orders', 'two writers', 'independent', 'listed', 'reorder', 'cycle', 'rounds', 'snapshot keys', 'shared keys',
          'moves', 'move cycles', 'graphs', 'with cycle')


def catches(name):
    """The check that notices the mistake, or None."""
    global MUTANT
    MUTANT = name
    rng = random.Random(2026)
    counts = dict.fromkeys(FIELDS, 0)
    try:
        for _ in range(300):
            check_batch(rng, counts)
            check_stages(rng, counts)
        swaps = [call('a', 'b'), call('b', 'a'), call('c', 'd'), call('d', 'c')]
        assert len(fewest_snapshot(swaps)) == cycles(4, before(swaps)), 'the fewest keys are not the number of cycles'
        return None
    except AssertionError as failed:
        return str(failed) or 'a check without a name'
    finally:
        MUTANT = None


def percent(part, whole):
    return f'{100 * part / whole:.0f}'


def call(reads, writes):
    return frozenset(reads.split()), frozenset(writes.split())


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten', 'eleven', 'twelve']

    # Section 2: three batches
    reads = [call('a.py', ''), call('b.py', ''), call('c.py', '')]
    claim('reads', independent(reads) and len({in_order(reads, order) for order in permutations(range(3))}) == 1
          and in_order(reads, (0, 1, 2)) == at_once(reads) and longest_chain(3, before(reads)) == 1)
    lines.append('three reads: every order gives the same outcome, one round')

    format_and_test = [call('lexer.py', 'lexer.py'), call('lexer.py tests', '')]
    two = {order: in_order(format_and_test, order) for order in permutations(range(2))}
    claim('format', two[0, 1] != two[1, 0] and at_once(format_and_test) == two[1, 0] and not listed_is_at_once(format_and_test)
          and before(format_and_test) == {(1, 0)} and longest_chain(2, before(format_and_test)) == 2)
    lines.append('format a file and run the tests: the two orders differ; the meaning at once is the one with the tests first')

    rotate = [call('a', 'b'), call('b', 'c'), call('c', 'a')]
    claim('rotate', write_disjoint(rotate) and sorted_by(3, before(rotate)) is None
          and not any(in_order(rotate, order) == at_once(rotate) for order in permutations(range(3)))
          and len(fewest_snapshot(rotate)) == 1 == cycles(3, before(rotate)) and shared(rotate) == {'a', 'b', 'c'}
          and in_order(rotate, sorted_by(3, before(rotate, frozenset('a'))), frozenset('a')) == at_once(rotate))
    content = {'a': 'A', 'b': 'B', 'c': 'C'}             # the three moves as listed, with real contents
    for source, target in (('a', 'b'), ('b', 'c'), ('c', 'a')):
        content[target] = content[source]
    claim('rotate-listed', content == {'a': 'A', 'b': 'A', 'c': 'A'})
    lines.append('three files moved in a circle: no order gives the meaning at once; a snapshot of one file is enough')

    four = [call('a', ''), call('x', 'a'), call('b', ''), call('y', 'b')]       # a reader and a writer of a, the same for b
    pairs = before(four)
    time = [1, 10, 10, 1]
    span = as_soon(4, pairs, time)
    claim('time-example', pairs == {(0, 1), (2, 3)} and in_rounds(4, pairs, time) == 20
          and max(finish for _, finish in span.values()) == 11 and sum(time) == 22)
    lines.append('two readers and two writers with the times 1, 10, 10, 1: rounds take 20, starting as soon as possible 11')

    staged = [call('lexer.py', 'lexer.py'), call('lexer.py tests', ''), call('lexer.py', '')]      # format; then test and read
    stage = [0, 1, 1]
    claim('stages-example', in_stages(staged, stage) == in_order(staged, (0, 1, 2)) != at_once(staged)
          and leads(staged, stage) == {(0, 1), (0, 2)} and longest_chain(3, leads(staged, stage)) == 2
          and longest_chain(3, before(staged)) == 2 and before(staged) == {(1, 0), (2, 0)})
    lines.append('format in a first stage, test and read in a second: two rounds, the formatter first; at once: two rounds, the formatter last')

    # random batches
    counts = dict.fromkeys(FIELDS, 0)
    for _ in range(10000):
        check_batch(rng, counts)
    total = counts['batches']
    claim('batches', total > 2500 and counts['two writers'] > 200 and all(counts[kind] > 100 for kind in ('independent', 'listed', 'reorder', 'cycle')))
    claim('moves', counts['moves'] > 500 and counts['move cycles'] > 50)
    claim('time', counts['timed'] > 5000 and counts['soon'] < counts['slow'] < counts['one by one'])
    claim('failures', counts['spread'] > 100 and counts['listed and failed'] > counts['spread'])
    claim('footprints', counts['wider'] > 1000)
    claim('torn', counts['torn'] > 100)
    tables['kinds'] = [
        f"independent & every order, and at the same time & {percent(counts['independent'], total)} \\\\",
        f"readers listed before writers & the listed order & {percent(counts['listed'], total)} \\\\",
        f"a reader listed after a writer & another order & {percent(counts['reorder'], total)} \\\\",
        f"a cycle of readers and writers & no order; a snapshot & {percent(counts['cycle'], total)} \\\\",
    ]
    lines.append(f"{total + counts['two writers']} random batches of two to four calls, {counts['two writers']} with two writers of one key "
                 f"(no meaning at once); of the other {total}, with {counts['orders']} orders run: {counts['independent']} independent, "
                 f"{counts['listed']} for which the listed order gives the meaning at once, {counts['reorder']} for which only another "
                 f"order does, {counts['cycle']} for which none does; an order gives the meaning at once exactly if every reader of a "
                 f"key runs before its writer; the fewest rounds are the longest chain ({counts['rounds']} rounds in all); the "
                 f"fewest keys of a snapshot are found ({counts['snapshot keys']} in all, where {counts['shared keys']} keys are "
                 f"shared); every order works exactly under a snapshot of all shared keys")
    lines.append(f"{counts['moves']} batches in which every call is before at most one other, with {counts['move cycles']} cycles: "
                 f"the fewest keys are the number of cycles")
    lines.append(f"in {counts['torn']} batches some order lets two calls read different values of one key, and at once none does; "
                 f"a failed call changes nothing for the others at once or in an order that gives it; in the listed order of "
                 f"{counts['listed and failed']} batches where that order is not the meaning at once, a failure changes the result of "
                 f"another call in {counts['spread']}; for {counts['wider']} batches with larger footprints declared, every order, "
                 f"number of rounds and snapshot that fits the declared footprints fits the true ones")
    lines.append(f"{counts['timed']} batches with an order and random times: starting every call as soon as it may gives the "
                 f"meaning at once and ends with the heaviest chain; in all it takes {counts['soon']}, the plan in rounds "
                 f"{counts['slow']}, one call at a time {counts['one by one']}")
    nums.update(Timed=f"{counts['timed']:,}", SoonOverRounds=percent(counts['slow'] - counts['soon'], counts['slow']),
                SoonOverSerial=percent(counts['one by one'] - counts['soon'], counts['one by one']))
    nums.update(Torn=f"{counts['torn']:,}", Spread=f"{counts['spread']:,}", ListedFailed=f"{counts['listed and failed']:,}",
                Wider=f"{counts['wider']:,}")
    nums.update(Batches=f"{total:,}", All=f"{total + counts['two writers']:,}", TwoWriters=f"{counts['two writers']:,}",
                Orders=f"{counts['orders']:,}", Cycle=f"{counts['cycle']:,}", SnapshotKeys=f"{counts['snapshot keys']:,}",
                SharedKeys=f"{counts['shared keys']:,}", Moves=f"{counts['moves']:,}", MoveCycles=f"{counts['move cycles']:,}",
                Saved=percent(counts['shared keys'] - counts['snapshot keys'], counts['shared keys']))

    # Theorem 7.1: batches in stages
    for _ in range(4000):
        check_stages(rng, counts)
    claim('stages', counts['staged'] == 4000 and counts['listed rounds'] < counts['listed calls'] and counts['more orders'] > 0)
    lines.append(f"{counts['staged']} random batches in up to three stages: every order that respects the pairs of Theorem 7.1 gives "
                 f"the meaning in stages, and where no key is written twice no other order does and the fewest rounds are the "
                 f"longest chain; in {counts['more orders']} batches with a key written twice some other order gives it too; with "
                 f"every call a stage of its own the meaning is the listed order, which runs in {counts['listed rounds']} rounds "
                 f"for {counts['listed calls']} calls")
    nums.update(MoreOrders=f"{counts['more orders']:,}", Staged=f"{counts['staged']:,}", ListedRounds=f"{counts['listed rounds']:,}", ListedCalls=f"{counts['listed calls']:,}",
                ListedSaved=percent(counts['listed calls'] - counts['listed rounds'], counts['listed calls']))

    # Theorem 5.2
    for _ in range(1500):
        check_graph(rng, counts)
    claim('graphs', counts['graphs'] == 1500 and counts['with cycle'] > 300)
    lines.append(f"{counts['graphs']} random graphs, {counts['with cycle']} with a cycle: the fewest keys of a snapshot of the batch of "
                 f"Theorem 5.2 are the fewest vertices that meet every cycle")
    nums.update(Graphs=f"{counts['graphs']:,}", WithCycle=f"{counts['with cycle']:,}")

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)],
                Size=f"{round(len(open(os.path.join(here, 'batch.py')).readlines()), -2):,}")

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
        f.write('% written by batch.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by batch.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
