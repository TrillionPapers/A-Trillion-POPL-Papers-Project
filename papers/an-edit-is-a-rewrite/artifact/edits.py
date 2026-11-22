#!/usr/bin/env python3
"""Tests the claims of "An Edit Is a Rewrite" on an implementation of its analyses.

The file has six parts.

1. Texts and edits, as a harness has them: an edit names a string and its replacement, and it
   is made only if the string occurs exactly once.  Nothing else in the file is trusted: every
   analysis is compared with running the edits.
2. Batches: the place of every edit in the snapshot, the text with some of the edits made at
   their places (the parallel meaning), and that text cut into what is old and what is new.
3. Spurious occurrences: what each of them touches (Lemma 4.1), and the constraints that they
   put on an order (Theorem 4.2).
4. Orders: every order that works, by trying; the sets of edits that can be made, by subsets;
   an order built from its end (Theorem 5.1); the graph of a separated batch (Theorem 5.2); a
   batch for every instance of a hard ordering problem (Theorem 5.3); context and merging
   (Propositions 5.4 and 5.5).
5. A snapshot that is no longer current: four rules for a harness (Theorem 6.1).
6. The tests.  `python3 edits.py out` writes out/check.txt, out/numbers.tex and the tables.

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
# 1. A text is a string.  An edit is (old, new).  It is made if old occurs exactly once.
# ---------------------------------------------------------------------------------------------

def occurrences(word, text):
    return [i for i in range(len(text) - len(word) + 1) if text.startswith(word, i)]


def apply(edit, text):
    """The text after the edit, or None if the harness refuses it."""
    old, new = edit
    found = occurrences(old, text)
    if len(found) != 1:
        return None
    return text[:found[0]] + new + text[found[0] + len(old):]


def run(order, batch, text):
    """The text after the edits of the batch in this order, or None if one is refused."""
    for k in order:
        text = apply(batch[k], text)
        if text is None:
            return None
    return text


# ---------------------------------------------------------------------------------------------
# 2. A batch is a list of edits that were written for one text, the snapshot.  It is valid if
#    every old string occurs exactly once in the snapshot and the places do not overlap.
# ---------------------------------------------------------------------------------------------

def places(batch, snapshot):
    """(start, end) of every edit's old string in the snapshot, or None if the batch is not
    valid."""
    found = []
    for old, _ in batch:
        at = occurrences(old, snapshot)
        if len(at) != 1:
            return None
        found.append((at[0], at[0] + len(old)))
    if MUTANT != 'overlap-ok':
        for a in range(len(found)):
            for b in range(a):
                if found[a][0] < found[b][1] and found[b][0] < found[a][1]:
                    return None
    return found


def layout(batch, snapshot, where, made):
    """The text in which the edits of `made` have been made at their places, as segments
    (kind, edit, text): a 'gap' of the snapshot between two places, the 'old' string of an edit
    that has not been made, the 'new' string of one that has."""
    segments, at = [], 0
    for k in sorted(range(len(batch)), key=lambda k: where[k][0]):
        if where[k][0] > at:
            segments.append(('gap', None, snapshot[at:where[k][0]]))
        segments.append(('new', k, batch[k][1]) if k in made else ('old', k, batch[k][0]))
        at = where[k][1]
    if at < len(snapshot):
        segments.append(('gap', None, snapshot[at:]))
    return segments


def par(batch, snapshot, where, made=None):
    """The parallel meaning: the snapshot with the edits of `made` (all, if none are named)
    made at once, each at its place."""
    made = set(range(len(batch))) if made is None else made
    if MUTANT == 'unsorted':                            # the places are not moved by other edits
        text = snapshot
        for k in sorted(made):
            text = text[:where[k][0]] + batch[k][1] + text[where[k][1]:]
        return text
    return ''.join(text for _, _, text in layout(batch, snapshot, where, made))


def clean(batch, snapshot, where, k, made):
    """Whether edit k is made when its turn comes after the edits of `made`: its old string
    occurs once in the text that they leave."""
    text = snapshot if MUTANT == 'snapshot-clean' else par(batch, snapshot, where, made)
    return len(occurrences(batch[k][0], text)) == 1


def subsets(items):
    items = list(items)
    for size in range(len(items) + 1):
        for chosen in combinations(items, size):
            yield frozenset(chosen)


# ---------------------------------------------------------------------------------------------
# 3. An occurrence of an old string that is not its place in the snapshot is spurious.  It
#    touches the edits whose new string it overlaps, or across whose deletion it reaches, and it
#    cuts the edits not yet made whose old string it overlaps in part.
# ---------------------------------------------------------------------------------------------

def touching(segments, start, end):
    """(touched, cut, whole): the edits made that the stretch from start to end touches, the
    edits not made whose old string it overlaps in part, and those whose old string lies in it
    whole."""
    touched, cut, whole, at = set(), set(), set(), 0
    for kind, k, text in segments:
        a, b = at, at + len(text)
        at = b
        if kind == 'new':
            if a < end and start < b and not (a == b and MUTANT == 'empty-touch'):   # a == b: a deletion inside
                touched.add(k)
        elif kind == 'old' and a < end and start < b:
            (whole if start <= a and b <= end else cut).add(k)
    return touched, cut, whole


def spurious(batch, snapshot, where, k, made):
    """What every spurious occurrence of the old string of edit k touches, cuts and contains,
    in the text that the edits of `made` leave."""
    segments = layout(batch, snapshot, where, made)
    text = ''.join(part for _, _, part in segments)
    found = []
    for start in occurrences(batch[k][0], text):
        touched, cut, whole = touching(segments, start, start + len(batch[k][0]))
        if whole == {k} and not touched and not cut:
            continue                                    # the place of edit k itself
        found.append((frozenset(touched), frozenset(cut - {k}), frozenset(whole)))
    return found


def constraints(batch, snapshot, where, k):
    """Theorem 4.2: every pair (touched, cut) of a spurious occurrence of the old string of
    edit k, over all sets of other edits.  Edit k is refused after the edits of a set exactly
    if the set contains the touched edits of some pair and none of its cut edits."""
    others = [j for j in range(len(batch)) if j != k]
    return {(touched, cut) for made in subsets(others)
            for touched, cut, _ in spurious(batch, snapshot, where, k, made)}


def allowed(found, made):
    return not any(touched <= made and (MUTANT == 'no-negative' or not cut & made) for touched, cut in found)


# ---------------------------------------------------------------------------------------------
# 4. Orders.
# ---------------------------------------------------------------------------------------------

def working_orders(batch, text):
    """Every order in which the harness makes all edits, by trying.  This is the definition."""
    return [order for order in permutations(range(len(batch))) if run(order, batch, text) is not None]


def reachable(batch, snapshot, where):
    """The sets of edits that can be made in some order, by subsets."""
    reach, frontier = {frozenset()}, [frozenset()]
    while frontier:
        made = frontier.pop()
        for k in range(len(batch)):
            if k not in made and clean(batch, snapshot, where, k, made) and made | {k} not in reach:
                reach.add(made | {k})
                frontier.append(made | {k})
    return reach


def from_the_end(batch, snapshot, where, choose=min):
    """Theorem 5.1: an order built from its end.  The last edit is one that is made after all
    the others, and so on.  None if at some point no edit can be last."""
    left, order = set(range(len(batch))), []
    if MUTANT == 'forward':                             # from the front: any edit that is made now
        while left:
            ready = [k for k in left if clean(batch, snapshot, where, k, set(range(len(batch))) - left)]
            if not ready:
                return None
            order.append(choose(ready))
            left.remove(order[-1])
        return order
    while left:
        ready = [k for k in left if clean(batch, snapshot, where, k, left - {k})]
        if not ready:
            return None
        order.append(choose(ready))
        left.remove(order[-1])
    return order[::-1]


def monotone(batch, snapshot, where):
    """Whether an edit that is made after some edits is also made after fewer of them."""
    for k in range(len(batch)):
        for made in subsets(j for j in range(len(batch)) if j != k):
            if clean(batch, snapshot, where, k, made) and not all(clean(batch, snapshot, where, k, made - {j}) for j in made):
                return False
    return True


def separated(batch, snapshot, where):
    """Whether no stretch as long as an old string reaches from one place to the next."""
    longest = max(len(old) for old, _ in batch)
    spans = sorted(where)
    return MUTANT == 'no-joint' or all(b[0] - a[1] >= longest - 1 for a, b in zip(spans, spans[1:]))


def spoils(batch, snapshot, where, j, k):
    """Whether edit j, made alone, leaves the old string of edit k with a second occurrence."""
    return len(occurrences(batch[k][0], par(batch, snapshot, where, {j}))) > 1


def before(batch, snapshot, where):
    """The pairs (k, j) of Theorem 5.2: edit k must be made before edit j, which spoils it."""
    n = len(batch)
    pairs = {(k, j) for j in range(n) for k in range(n) if j != k and spoils(batch, snapshot, where, j, k)}
    return {(j, k) for k, j in pairs} if MUTANT == 'edge-reversed' else pairs


def as_batch(m, pairs, triples):
    """Theorem 5.3.  The elements are 0..m-1.  A pair (p, q) asks that p comes before q, and a
    triple (a, k, b) forbids that a comes before k and k before b.  No element is in two
    triples.  Returns a text and a valid batch, edit x for element x, such that an order of
    the edits works exactly if it does what the pairs and triples ask.

    The new string of q holds a copy of the old string of p, so p is refused once q is made.
    The places of a and b stand side by side, the new string of a ends with a letter X, and
    the old string of k is X and the first letter of the old string of b: it occurs a second
    time when a is made and b is not."""
    count = [0]

    def letter():
        count[0] += 1
        return chr(0x4E00 + count[0])                  # as many different letters as are needed

    role = {}
    for t, (a, k, b) in enumerate(triples):
        role[a], role[k], role[b] = ('a', t), ('k', t), ('b', t)
    first = [letter() for _ in triples]                 # the first letter of the old string of b
    mark = [letter() for _ in triples]                  # the last letter of the new string of a
    old = {}
    for x in range(m):
        kind, t = role.get(x, ('free', None))
        old[x] = mark[t] + first[t] if kind == 'k' else first[t] + letter() if kind == 'b' else letter() + letter()
    batch = []
    for x in range(m):
        new = letter() + ''.join(old[p] + letter() for p, q in pairs if q == x)
        batch.append((old[x], new + mark[role[x][1]] if x in role and role[x][0] == 'a' else new))
    parts = [part for a, k, b in triples
             for part in ((old[a], old[b], old[k]) if MUTANT == 'triple-apart' else (old[a] + old[b], old[k]))]
    parts += [old[x] for x in range(m) if x not in role]
    return letter() + ''.join(part + letter() for part in parts), batch


def with_context(batch, snapshot, where, k, left, right):
    """Proposition 5.4: edit k with the letters before and after its place added to both of
    its strings, `left` letters before and `right` after."""
    a, b = where[k]
    before, after = snapshot[a - left:a], snapshot[b:b + right]
    return [(before + old + after, before + new + after) if i == k else (old, new) for i, (old, new) in enumerate(batch)]


def room(batch, snapshot, where):
    """For every edit, how many letters of the snapshot stand before its place and after it up
    to the next place or the end of the text."""
    order = sorted(range(len(batch)), key=lambda i: where[i])
    ends = [0] + [where[i][1] for i in order]
    starts = [where[i][0] for i in order] + [len(snapshot)]
    return {k: (starts[i] - ends[i], starts[i + 1] - ends[i + 1]) for i, k in enumerate(order)}, order


def repair(batch, snapshot, where, most):
    """The least number of letters of context, at most `most`, with which the batch has an
    order that works, and the batch with that context; or None.  Two edits may not take the
    same letter of the gap between them."""
    n = len(batch)
    space, order = room(batch, snapshot, where)
    texts = {made: par(batch, snapshot, where, made) for made in subsets(range(n))}
    seen = {}

    def clean_after(k, left, right):                    # the sets after which edit k with this context is clean
        if (k, left, right) not in seen:
            word = snapshot[where[k][0] - left:where[k][1] + right]
            seen[k, left, right] = {made for made in texts if k not in made and len(occurrences(word, texts[made])) == 1}
        return seen[k, left, right]

    def choices(i, budget, taken):                      # the ways to give the edits from the i-th on their context
        if i == n:
            if budget == 0:
                yield {}
            return
        k = order[i]
        for left in range(min(budget, space[k][0] - taken) + 1):
            for right in range(min(budget - left, space[k][1]) + 1):
                for rest in choices(i + 1, budget - left - right, right):
                    yield {k: (left, right), **rest}

    for budget in range(most + 1):
        for chosen in choices(0, budget, 0):
            reach, frontier = {frozenset()}, [frozenset()]
            while frontier:
                made = frontier.pop()
                for k in range(n):
                    if k not in made and made in clean_after(k, *chosen[k]) and made | {k} not in reach:
                        reach.add(made | {k})
                        frontier.append(made | {k})
            if frozenset(range(n)) in reach:
                wider = batch
                for k, (left, right) in chosen.items():
                    wider = with_context(wider, snapshot, where, k, left, right)
                return budget, wider
    return None


def merged(batch, snapshot, where, j, k):
    """Proposition 5.5: the batch in which two edits whose places are neighbours are one edit,
    from the start of the first place to the end of the second."""
    first, second = sorted((j, k), key=lambda i: where[i])
    (a, b), (c, d) = where[first], where[second]
    one = (snapshot[a:d], batch[first][1] + snapshot[b:c] + batch[second][1])
    return [edit for i, edit in enumerate(batch) if i not in (j, k)] + [one]


def sorted_by(n, pairs):
    """An order of 0..n-1 in which a comes before b for every pair (a, b), or None if the pairs
    have a cycle."""
    waiting = {b: {a for a, c in pairs if c == b} for b in range(n)}
    order = []
    while len(order) < n:
        ready = [k for k in range(n) if k not in order and not waiting[k] - set(order)]
        if not ready:
            return None
        order.append(min(ready))
    return order


# ---------------------------------------------------------------------------------------------
# 5. An edit that was written for a snapshot, and a text in which a batch has been made since.
# ---------------------------------------------------------------------------------------------

def stale(batch, snapshot, where, edit):
    """What four rules of a harness do with the edit: None for a refusal, or the text.  And
    what the author of the edit meant, which is None if the place of the edit was changed.
        version    refuse, because the text changed since it was read
        unique     make the edit if its old string occurs once in the text as it is now
        place      the same, but only if the place of the edit in the snapshot was not changed
        carry      find the place in the snapshot and carry it through the changes"""
    now = par(batch, snapshot, where)
    both = places(batch + [edit], snapshot)
    meant = par(batch + [edit], snapshot, both) if both is not None else None
    unique = apply(edit, now)
    place = unique if both is not None or MUTANT == 'unique-only' else None
    return {'version': None, 'unique': unique, 'place': place, 'carry': meant}, meant


# ---------------------------------------------------------------------------------------------
# 6. The tests.
# ---------------------------------------------------------------------------------------------

MUTANTS = ('unsorted', 'overlap-ok', 'snapshot-clean', 'empty-touch', 'no-negative', 'forward', 'no-joint',
           'edge-reversed', 'triple-apart', 'unique-only')


def letters_for(rng, n):
    """Few letters, so that strings repeat, but enough for n old strings that occur once."""
    return ('ab' if rng.random() < 0.4 else 'abc') if n <= 3 else 'abc' if n == 4 and rng.random() < 0.5 else 'abcd'


def random_batch(rng, letters, length, n):
    """A random text and a valid batch of n edits for it, the old strings of one to three
    letters, the new ones of none to three."""
    while True:
        sizes = [rng.choice((1, 2, 2, 2, 3, 3)) for _ in range(n)]
        spare = length - sum(sizes)
        if spare < 0:
            continue
        gaps = sorted(rng.randrange(spare + 1) for _ in range(n))
        text = ''.join(rng.choice(letters) for _ in range(length))
        batch, at = [], 0
        for size, gap in zip(sizes, gaps):
            start = gap + at
            batch.append((text[start:start + size], ''.join(rng.choice(letters) for _ in range(rng.randrange(4)))))
            at += size
        if any(old == new for old, new in batch):
            continue
        rng.shuffle(batch)
        if places(batch, text) is not None:
            return text, batch


def check_batch(rng, text, batch, counts):
    """Every analysis of Sections 3 to 5 against running the edits, for one valid batch."""
    n = len(batch)
    where = places(batch, text)
    assert where is not None, 'a valid batch is called invalid'
    everything = frozenset(range(n))
    meaning = par(batch, text, where)
    works = working_orders(batch, text)

    # Theorem 3.2: an order works exactly if every edit is clean at its turn, and then the
    # result is the parallel meaning
    for order in permutations(range(n)):
        chain = all(clean(batch, text, where, k, set(order[:i])) for i, k in enumerate(order))
        assert chain == (order in works), 'an order works without every edit being clean at its turn, or the reverse'
        assert order not in works or run(order, batch, text) == meaning, 'an order that works gives another text than the parallel meaning'

    # Lemma 4.1 and Theorem 4.2: what a spurious occurrence touches, and what that says about orders
    plain = True
    for k in range(n):
        found = constraints(batch, text, where, k)
        for made in subsets(j for j in range(n) if j != k):
            for touched, cut, whole in spurious(batch, text, where, k, made):
                assert touched, 'a spurious occurrence touches no edit that was made'
                assert len(cut) <= 2 and not whole, 'a spurious occurrence cuts more than two old strings, or contains one'
                assert touched <= made and not cut & made
                counts['windows'] += 1
                counts['cutting'] += bool(cut)
            assert allowed(found, made) == clean(batch, text, where, k, made), 'the constraints say otherwise than the text'
        plain = plain and all(not cut for _, cut in found)

    # the sets that can be made, by subsets
    reach = reachable(batch, text, where)
    assert (everything in reach) == bool(works), 'the search over subsets finds an order where none works, or the reverse'

    # Theorem 5.1: from the end
    mono = monotone(batch, text, where)
    assert mono or not plain, 'a batch without cut old strings is not monotone'
    stuck = False
    for choose in (min, max, lambda ready: rng.choice(sorted(ready))):
        order = from_the_end(batch, text, where, choose)
        assert order is None or tuple(order) in works, 'the order built from the end does not work'
        assert not (mono and works and order is None), 'a monotone batch has an order and the building from the end finds none'
        stuck = stuck or (order is None and bool(works))

    # Theorem 5.2: a separated batch and its graph
    apart = separated(batch, text, where)
    if apart:
        pairs = before(batch, text, where)
        fit = [order for order in permutations(range(n)) if all(order.index(a) < order.index(b) for a, b in pairs)]
        assert fit == works, 'the orders of the graph are not the orders that work'
        order = sorted_by(n, pairs)
        assert (order is None) == (not works) and (order is None or tuple(order) in works), 'sorting the graph fails'
        assert mono, 'a separated batch is not monotone'

    # Proposition 5.4: context loses no order
    k = rng.randrange(n)
    space, _ = room(batch, text, where)
    wider = with_context(batch, text, where, k, rng.randint(0, space[k][0]), rng.randint(0, space[k][1]))
    there = places(wider, text)
    assert there is not None and par(wider, text, there) == meaning, 'an edit with context gives another batch'
    assert set(works) <= set(working_orders(wider, text)), 'an order is lost when an edit gets context'

    # no order: how many letters of context give one?
    if not works:
        found = repair(batch, text, where, 4)
        if found is not None:
            assert found[0] > 0 and working_orders(found[1], text) and places(found[1], text) is not None, 'the repair by context does not work'
            assert all(run(order, found[1], text) == meaning for order in working_orders(found[1], text))
        counts['repair'][found[0] if found else None] = counts['repair'].get(found[0] if found else None, 0) + 1

    # Proposition 5.5: two neighbours as one edit, and the whole batch as one edit
    by_place = sorted(range(n), key=lambda i: where[i])
    for j, k in zip(by_place, by_place[1:]):
        fewer = merged(batch, text, where, j, k)
        there = places(fewer, text)
        assert there is not None and par(fewer, text, there) == meaning, 'two neighbours as one edit give another batch'
    whole = batch
    while len(whole) > 1:
        there = places(whole, text)
        first, second = sorted(range(len(whole)), key=lambda i: there[i])[:2]
        whole = merged(whole, text, there, first, second)
    assert apply(whole[0], text) == meaning, 'the batch as one edit is refused or gives another text'
    counts['extra'] += len(whole[0][0]) - sum(len(old) for old, _ in batch)
    counts['letters'] += sum(len(old) for old, _ in batch)

    row = counts['by size'].setdefault(n, dict(batches=0, every=0, some=0, none=0, hard=0, stuck=0, apart=0))
    row['batches'] += 1
    row['every'] += len(works) == len(list(permutations(range(n))))
    row['none'] += not works
    row['some'] += 0 < len(works) < len(list(permutations(range(n))))
    row['hard'] += not mono
    row['stuck'] += stuck
    row['apart'] += apart
    counts['orders'] += len(list(permutations(range(n))))


def check_stale(rng, counts):
    """Theorem 6.1 for one snapshot, one batch made since, and one edit written for the snapshot."""
    n = rng.randrange(1, 4)
    letters = letters_for(rng, n)
    text, batch = random_batch(rng, letters, rng.randrange(6, 13), n)
    while True:
        a = rng.randrange(len(text))
        b = min(len(text), a + rng.randrange(1, 4))
        edit = (text[a:b], ''.join(rng.choice(letters) for _ in range(rng.randrange(4))))
        if edit[0] != edit[1] and len(occurrences(edit[0], text)) == 1:
            break
    where = places(batch, text)
    results, meant = stale(batch, text, where, edit)
    now = par(batch, text, where)
    for rule in ('version', 'place', 'carry'):
        assert results[rule] is None or results[rule] == meant, f'the rule "{rule}" makes an edit that its author did not mean'
    if meant is not None:                               # the place was not changed
        assert results['unique'] in (None, meant), 'an edit whose place was not changed is made somewhere else'
        assert (results['unique'] is None) == (len(occurrences(edit[0], now)) != 1)
        assert results['place'] == results['unique']
    elif results['unique'] is not None:                 # the place was changed, and the edit is made all the same
        segments = layout(batch, text, where, set(range(len(batch))))
        start = occurrences(edit[0], now)[0]
        touched, _, _ = touching(segments, start, start + len(edit[0]))
        assert touched, 'an edit whose place was changed is made in text that nobody changed'
    kind = ('kept' if meant is not None else 'changed') + (' made' if results['unique'] is not None else ' refused')
    counts[kind] = counts.get(kind, 0) + 1
    counts['trials'] = counts.get('trials', 0) + 1


def check_pairs(letters, longest):
    """Every text up to a length and every pair of edits with short strings."""
    texts = [''.join(chosen) for size in range(1, longest + 1) for chosen in product(letters, repeat=size)]
    olds = [''.join(chosen) for size in (1, 2) for chosen in product(letters, repeat=size)]
    news = [''.join(chosen) for size in (0, 1, 2) for chosen in product(letters, repeat=size)]
    edits = [(old, new) for old in olds for new in news if old != new]
    totals = dict(texts=len(texts), pairs=0, valid=0, both=0, one=0, neither=0, overlap=0, differ=0, example=None)
    for text in texts:
        for first, second in combinations(edits, 2):
            batch = [first, second]
            if any(len(occurrences(old, text)) != 1 for old, _ in batch):
                continue
            totals['pairs'] += 1
            results = [run(order, batch, text) for order in ((0, 1), (1, 0))]
            where = places(batch, text)
            if where is not None:
                totals['valid'] += 1
                meaning = par(batch, text, where)
                assert all(result in (None, meaning) for result in results), 'two edits at places apart give another text than the parallel meaning'
                assert all((result is not None) == clean(batch, text, where, order[1], {order[0]})
                           for result, order in zip(results, ((0, 1), (1, 0)))), 'the second of two edits'
                made = sum(result is not None for result in results)
                totals['both' if made == 2 else 'one' if made == 1 else 'neither'] += 1
            else:
                totals['overlap'] += 1
                if None not in results and results[0] != results[1]:
                    totals['differ'] += 1
                    size = len(text) + sum(len(old) + len(new) for old, new in batch)
                    if totals['example'] is None or size < totals['example'][0]:
                        totals['example'] = (size, text, batch, results)
    return totals


def check_hard(rng, counts):
    """Theorem 5.3 on one random instance: every order of the elements does what the pairs and
    triples ask exactly if the same order of the edits works."""
    m = rng.randrange(3, 7)
    elements = list(range(m))
    rng.shuffle(elements)
    triples = [tuple(elements[3 * i:3 * i + 3]) for i in range(rng.randrange(1, m // 3 + 1))]
    pairs = [(p, q) for p in range(m) for q in range(m) if p != q and rng.random() < 0.12]
    text, batch = as_batch(m, pairs, triples)
    assert places(batch, text) is not None, 'the batch of the reduction is not valid'
    some = False
    for order in permutations(range(m)):
        at = {x: i for i, x in enumerate(order)}
        asked = all(at[p] < at[q] for p, q in pairs) and not any(at[a] < at[k] < at[b] for a, k, b in triples)
        assert asked == (run(order, batch, text) is not None), 'an order of the reduction works when it should not, or the reverse'
        some = some or asked
    counts['instances'] = counts.get('instances', 0) + 1
    counts['solvable'] = counts.get('solvable', 0) + some
    counts['tried'] = counts.get('tried', 0) + len(list(permutations(range(m))))


def catches(name):
    """The check that notices the mistake, or None."""
    global MUTANT
    MUTANT = name
    rng = random.Random(2026)
    counts = {'by size': {}, 'windows': 0, 'cutting': 0, 'orders': 0, 'extra': 0, 'letters': 0, 'repair': {}}
    try:
        check_pairs('ab', 4)
        for _ in range(400):
            n = rng.choice((2, 3, 3, 4))
            text, batch = random_batch(rng, letters_for(rng, n), rng.randrange(2 * n + 2, 2 * n + 9), n)
            check_batch(rng, text, batch, counts)
            check_stale(rng, counts)
            check_hard(rng, counts)
        return None
    except AssertionError as failed:
        return str(failed) or 'a check without a name'
    finally:
        MUTANT = None


def percent(part, whole):
    return f'{100 * part / whole:.0f}'


def show(edit):
    return f'{edit[0]} to {edit[1] or "nothing"}'


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten', 'eleven', 'twelve']

    # Section 2: three accidents
    text = 'a = f(x)\nb = g(y)\n'
    batch = [('g(y)', 'f(x)'), ('f(x)', 'f(x, 0)')]
    where = places(batch, text)
    claim('distance', where is not None and working_orders(batch, text) == [(1, 0)]
          and run((1, 0), batch, text) == par(batch, text, where) == 'a = f(x, 0)\nb = f(x)\n'
          and spoils(batch, text, where, 0, 1) and not spoils(batch, text, where, 1, 0))
    lines.append('two edits on two lines: the order (second, first) works and the other is refused')

    text = 'lo = 1; hi = 9'
    batch = [('lo', 'hi'), ('hi', 'lo')]
    where = places(batch, text)
    claim('swap', where is not None and working_orders(batch, text) == [] and par(batch, text, where) == 'hi = 1; lo = 9'
          and separated(batch, text, where) and sorted_by(2, before(batch, text, where)) is None)
    lines.append('the swap of two names: no order works; the parallel meaning is "hi = 1; lo = 9"')
    found = repair(batch, text, where, 4)
    claim('swap-context', found is not None and found[0] == 1 and found[1] == [('lo', 'hi'), (' hi', ' lo')]
          and working_orders(found[1], text) == [(0, 1)])
    lines.append('the swap with one letter of context for the second edit: the order (first, second) works')

    text = 'abc'
    batch = [('ab', 'bcx'), ('bc', 'b')]
    claim('differ', places(batch, text) is None and run((0, 1), batch, text) == 'bxc' and run((1, 0), batch, text) == 'bcx')
    lines.append('two edits at places that overlap: both orders work, and they give "bxc" and "bcx"')

    # Section 4: two edits that spoil a third only together
    text = 'xy.ab'
    batch = [('x', 'a'), ('y', 'b'), ('ab', 'c')]
    where = places(batch, text)
    claim('joint', not spoils(batch, text, where, 0, 2) and not spoils(batch, text, where, 1, 2)
          and not clean(batch, text, where, 2, {0, 1}) and sorted(working_orders(batch, text)) == [(0, 2, 1), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
          and not separated(batch, text, where) and monotone(batch, text, where)
          and constraints(batch, text, where, 2) == {(frozenset({0, 1}), frozenset())})
    lines.append('two edits that spoil a third only together: four of six orders work')

    # Section 5: a batch for which the building from the end can get stuck
    text = 'pqr.xq'
    batch = [('p', 'x'), ('qr', 'y'), ('xq', 'p')]
    where = places(batch, text)
    claim('stuck', sorted(working_orders(batch, text)) == [(0, 1, 2), (1, 0, 2)] and not monotone(batch, text, where)
          and from_the_end(batch, text, where, lambda ready: 1 if 1 in ready else min(ready)) is None
          and from_the_end(batch, text, where, max) == [0, 1, 2]
          and (frozenset({0}), frozenset({1})) in constraints(batch, text, where, 2))
    lines.append('a batch that is not monotone: two orders work, and the building from the end fails if it takes the wrong edit last')

    # Section 6: an edit that is made in the wrong place
    text = 'def f():\n    return total\n'
    batch = [(text, 'def f():\n    return 0\n\ndef g():\n    return total\n')]
    edit = ('return total', 'return total + tax')
    results, meant = stale(batch, text, places(batch, text), edit)
    claim('wrong-place', meant is None and results['place'] is None and results['carry'] is None
          and results['unique'] == 'def f():\n    return 0\n\ndef g():\n    return total + tax\n')
    lines.append('an edit written for one function is made in another when only uniqueness is checked')

    # every pair of short edits on every short text
    totals = check_pairs('ab', 6)
    claim('pairs', totals['valid'] > 1000 and totals['one'] > 0 and totals['neither'] > 0 and totals['differ'] > 0
          and totals['both'] + totals['one'] + totals['neither'] == totals['valid'])
    size, text, batch, results = totals['example']
    lines.append(f"{totals['texts']} texts of up to six letters a and b, {totals['pairs']} pairs of edits whose old strings occur once: "
                 f"{totals['valid']} at places apart, of which both orders work for {totals['both']}, one for {totals['one']}, none for "
                 f"{totals['neither']}, and every order that works gives the parallel meaning; {totals['overlap']} at places that overlap, "
                 f"of which {totals['differ']} work in both orders with two results, for instance {show(batch[0])} and {show(batch[1])} "
                 f"on {text}, which give {results[0]} and {results[1]}")
    nums.update(PairTexts=str(totals['texts']), Pairs=f"{totals['pairs']:,}", PairValid=f"{totals['valid']:,}",
                PairBoth=f"{totals['both']:,}", PairOne=f"{totals['one']:,}", PairNeither=f"{totals['neither']:,}",
                PairOverlap=f"{totals['overlap']:,}", PairDiffer=f"{totals['differ']:,}")

    # random batches of two to five edits
    counts = {'by size': {}, 'windows': 0, 'cutting': 0, 'orders': 0, 'extra': 0, 'letters': 0, 'repair': {}}
    rounds = {2: 3000, 3: 3000, 4: 2000, 5: 1000}
    for n, many in rounds.items():
        for _ in range(many):
            text, batch = random_batch(rng, letters_for(rng, n), rng.randrange(2 * n + 2, 2 * n + 9), n)
            check_batch(rng, text, batch, counts)
    rows = counts['by size']
    total = {key: sum(row[key] for row in rows.values()) for key in next(iter(rows.values()))}
    claim('one-meaning', total['batches'] == sum(rounds.values()) and counts['windows'] > 1000 and counts['cutting'] > 0)
    claim('orders', total['some'] > 0 and total['none'] > 0 and total['hard'] > 0 and total['stuck'] > 0 and total['apart'] > 100
          and all(rows[n]['every'] / rows[n]['batches'] > rows[n + 1]['every'] / rows[n + 1]['batches'] for n in (2, 3, 4)))
    tables['orders'] = []
    for n in sorted(rows):
        row = rows[n]
        tables['orders'].append(f"{n} & {row['batches']:,} & {percent(row['every'], row['batches'])} & "
                                f"{percent(row['some'], row['batches'])} & {percent(row['none'], row['batches'])} & "
                                f"{percent(row['hard'], row['batches'])} & {row['stuck']} & {percent(row['apart'], row['batches'])} \\\\")
        lines.append(f"batches of {n} edits: {row['batches']}, every order works for {row['every']}, some for {row['some']}, none for "
                     f"{row['none']}; {row['hard']} are not monotone, the building from the end gets stuck for {row['stuck']} "
                     f"that have an order, {row['apart']} are separated")
    lines.append(f"merged into one edit, a batch has {counts['letters'] + counts['extra']} letters in its old string "
                 f"where the edits had {counts['letters']} in all")
    lines.append(f"{total['batches']} random batches, {counts['orders']} orders run: an order works exactly if every edit is clean at "
                 f"its turn, and then it gives the parallel meaning; {counts['windows']} spurious occurrences, each touching an edit "
                 f"that was made, {counts['cutting']} of them cutting one or two old strings; the constraints, the search over subsets, "
                 f"the building from the end and the graph of a separated batch agree with running the edits")
    nums.update(Batches=f"{total['batches']:,}", Orders=f"{counts['orders']:,}", Windows=f"{counts['windows']:,}",
                Cutting=f"{counts['cutting']:,}", Every=percent(total['every'], total['batches']),
                Some=percent(total['some'], total['batches']), NoOrder=percent(total['none'], total['batches']),
                Hard=f"{total['hard']:,}", Stuck=f"{total['stuck']:,}", Apart=f"{total['apart']:,}",
                EveryTwo=percent(rows[2]['every'], rows[2]['batches']), EveryFive=percent(rows[5]['every'], rows[5]['batches']),
                MergeFactor=f"{(counts['letters'] + counts['extra']) / counts['letters']:.1f}")

    # no order: context
    fixed = counts['repair']
    stuck_for_good = fixed.get(None, 0)
    claim('context', sum(fixed.values()) == total['none'] and fixed.get(1, 0) > 0 and stuck_for_good > 0)
    lines.append(f"context loses no order; of the {total['none']} batches with no order, one letter of context gives an order to "
                 f"{fixed.get(1, 0)}, two letters to {fixed.get(2, 0)}, three or four to {fixed.get(3, 0) + fixed.get(4, 0)}, "
                 f"and {stuck_for_good} have none with four")
    nums.update(NoOrderCount=f"{total['none']:,}", RepairOne=f"{fixed.get(1, 0):,}", RepairTwo=f"{fixed.get(2, 0):,}",
                RepairMore=f"{fixed.get(3, 0) + fixed.get(4, 0):,}", RepairNone=f"{stuck_for_good:,}")

    # Theorem 5.3: an ordering problem that is NP-complete, as batches
    hard = {}
    for _ in range(400):
        check_hard(rng, hard)
    claim('hard', hard['instances'] == 400 and 0 < hard['solvable'] < hard['instances'])
    lines.append(f"{hard['instances']} random instances of the ordering problem with pairs and disjoint triples, {hard['tried']} orders: "
                 f"an order does what is asked exactly if the same order of the edits works; {hard['solvable']} instances have such an order")
    nums.update(HardInstances=f"{hard['instances']:,}", HardSolvable=f"{hard['solvable']:,}", HardOrders=f"{hard['tried']:,}")

    # a snapshot that is no longer current
    seen = {}
    for _ in range(20000):
        check_stale(rng, seen)
    claim('stale', all(seen.get(kind, 0) > 0 for kind in ('kept made', 'kept refused', 'changed made', 'changed refused')))
    kept, changed = seen['kept made'] + seen['kept refused'], seen['changed made'] + seen['changed refused']
    tables['stale'] = [
        f"the text changed: refuse & 0 & 0 & {kept:,} \\\\",
        f"the old string occurs once now & {seen['kept made'] + seen['changed made']:,} & {seen['changed made']:,} & {seen['kept refused']:,} \\\\",
        f"\\dots and its place was not changed & {seen['kept made']:,} & 0 & {seen['kept refused']:,} \\\\",
        f"carry the place through the changes & {kept:,} & 0 & 0 \\\\",
    ]
    lines.append(f"{seen['trials']} edits written for a snapshot that changed: the place was kept for {kept} "
                 f"(the edit is made as meant for {seen['kept made']} and refused for {seen['kept refused']}) and changed for {changed} "
                 f"(the edit is made all the same for {seen['changed made']}, each time in text that was changed)")
    nums.update(StaleTrials=f"{seen['trials']:,}", StaleKept=f"{kept:,}", StaleChanged=f"{changed:,}",
                StaleWrong=f"{seen['changed made']:,}", StaleWrongShare=percent(seen['changed made'], changed),
                StaleRefused=f"{seen['kept refused']:,}", StaleRefusedShare=percent(seen['kept refused'], kept))

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)],
                Size=f"{round(len(open(os.path.join(here, 'edits.py')).readlines()), -2):,}")

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
        f.write('% written by edits.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by edits.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
