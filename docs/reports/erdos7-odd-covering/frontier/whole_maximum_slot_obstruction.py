#!/usr/bin/env python3
"""A whole even cover with no compatible family of local maximum matchings.

Python 3.9+, standard library only; no repository, data or solver imports.
Enumerates all original points and all full/truncated matching menus, with
full CRT tails and independent Hall-cut rank checks. Three actual sources
must use only two actual residual slots, even without forced-edge conditions.
Full binary relations have complete projections but their triple join is empty.
This refutes a general whole-cover gluing assertion. It does not settle
Erdos #7, assert an odd extremal counterexample, certify a whole-AP
replacement, or constitute a Lean proof. Checks remain active under -O.
"""
from collections import Counter, defaultdict
from itertools import combinations, product
from math import gcd, lcm
import json


APS = ((0, 2), (0, 3), (0, 5), (5, 6), (0, 7), (7, 9),
       (9, 10), (13, 14), (7, 15), (4, 21), (16, 25), (8, 35),
       (19, 42), (28, 45), (11, 50), (58, 63), (31, 70),
       (31, 75), (73, 105), (51, 175), (121, 225), (1, 315),
       (121, 350), (1, 525))
MODES = ('full', 'truncated')
CRITICAL = ((3, 351), (5, 3025), (7, 1351))
COUNTS = Counter()


def check(condition, name):
    COUNTS['checks'] += 1
    if not condition:
        raise ArithmeticError(name)


def height(n, q):
    e = 0
    while n % q == 0:
        e += 1
        n //= q
    return e


def primes_of(n):
    primes, q = [], 2
    while q * q <= n:
        if n % q == 0:
            primes.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        primes.append(n)
    return tuple(primes)


def prepare():
    A = {d: a for a, d in APS}
    Q = lcm(*A)
    primes = primes_of(Q)
    check(Q == 3150 and len(A) == len(APS) == 24, 'literal original inventory changed')
    check(all(d > 1 and 0 <= a < d for d, a in A.items()), 'noncanonical original AP')
    check(all(q in A and A[q] == 0 for q in primes), 'missing normalized original prime')
    check(all(e in A for d in A for e in range(2, d+1) if d % e == 0), 'divisor closure fails')
    check(all((A[d]-A[e]) % gcd(d, e) for d, e in combinations(A, 2)
              if d % e == 0 or e % d == 0), 'comparable original classes intersect')
    hits = tuple(frozenset(d for d, a in A.items() if z % d == a) for z in range(Q))
    check(all(hits), 'whole original cover has a gap')
    private = {d: tuple(z for z in range(Q) if hits[z] == {d}) for d in A}
    check(all(private.values()), 'an original label has no private witness')
    COUNTS['full_period_points'] += Q
    return A, Q, primes, hits, private


def maximum_menus(q, rows, forced):
    color = lambda d: d // q ** height(d, q)
    valid = []
    # The None choice leaves a root unmatched. This enumerates every matching,
    # including those omitting forced edges, before determining maximum rank.
    for choice in product(*[(None, *row) for row in rows]):
        labels = tuple(sorted(d for d in choice if d is not None))
        if len(set(map(color, labels))) == len(labels):
            valid.append(labels)
    rank = max(map(len, valid))
    deficiency = 0
    for size in range(q):
        for roots in combinations(range(q-1), size):
            neighbors = {color(d) for root in roots for d in rows[root]}
            deficiency = max(deficiency, len(roots)-len(neighbors))
            COUNTS['hall_subsets'] += 1
    check(rank == q-1-deficiency, 'enumeration differs from the Hall maximum rank')
    all_maximum = sorted(set(ds for ds in valid if len(ds) == rank))
    retained = [ds for ds in all_maximum if forced.issubset(ds)]
    check(bool(retained), 'no maximum matching retains all forced edges')
    return dict(rows=rows, rank=rank, all_maximum_menus=all_maximum,
                forced_maximum_menus=retained,
                forced_menu_heights=[sum(height(d, q) for d in ds) for ds in retained])


def source_menus(A, Q, primes, hits, private):
    records = {}
    for q in primes:
        H = height(Q, q)
        power, B = q ** H, Q // q ** H
        # Recover every lift by its literal complete-period coordinates,
        # independently of a closed-form CRT root-reset implementation.
        coordinates = {(z % B, (z % power) // q, z % q): z for z in range(Q)}
        check(len(coordinates) == Q, 'full CRT coordinates are not bijective')
        forced = set()
        for root in range(1, q):
            labels = [d for d, a in A.items() if d % q == 0 and a % q == root]
            if len(labels) == 1:
                d = labels[0]
                check(d > q and height(d, q) == 1, 'singleton original root is not a mixed child')
                forced.add(d)
        R = {x for x in range(B) if all(x % d != a for d, a in A.items() if d % q)}
        actual = {(y % B, (y % power) // q) for y in private[q]}
        check(actual == set(product(R, range(q ** (H-1)))), 'original cofactor or full tail omitted')
        for y in private[q]:
            x, tail = y % B, (y % power) // q
            heights = defaultdict(list)
            for d, a in A.items():
                e = height(d, q)
                m = d // q ** e
                if e and m > 1 and x % m == a % m:
                    heights[m].append(e)
            check(len(heights) >= q-1, 'too few compatible nonpure columns')
            cutoff = sorted(map(max, heights.values()), reverse=True)[q-2]
            rows = {mode: [] for mode in MODES}
            targets = []
            for root in range(1, q):
                z = coordinates[x, tail, root]
                targets.append(z)
                check(z % B == x and (z % power) // q == tail, 'root lift changes cofactor or tail')
                check(all(d % q == 0 for d in hits[z]), 'prime-private lift meets a q-free AP')
                check(any(height(d, q) <= cutoff for d in hits[z]), 'truncation loses literal root coverage')
                for mode in MODES:
                    bound = H if mode == 'full' else cutoff
                    row = sorted(d for d in hits[z] if height(d, q) <= bound and d // q ** height(d, q) > 1)
                    check(all(A[d] % q == root for d in row), 'row loses original first-root identity')
                    rows[mode].append(row)
                COUNTS['literal_root_checks'] += 1
            record = dict(q=q, y=y, H=H, cutoff=cutoff, forced=sorted(forced), root_targets=targets)
            for mode in MODES:
                record[mode] = maximum_menus(q, rows[mode], forced)
            records[q, y] = record
            COUNTS['sources'] += 1
    check({q: len(private[q]) for q in primes} == {2: 397, 3: 165, 5: 25, 7: 8}, 'prime source counts changed')
    check(len(records) == 595, 'complete source count changed')
    return records


def footprint(source, labels, A, hits):
    targets = ((source['root_targets'][A[d] % source['q']-1], d) for d in labels)
    return frozenset((z, d) for z, d in targets if len(hits[z]) >= 2)


def critical_control(A, primes, hits, records):
    check(hits[1] == {315, 525} and not hits[1].intersection(primes), 'critical residual target changed')
    critical = [records[key] for key in CRITICAL]
    check([r['forced'] for r in critical] == [[6], [10, 15], [14, 21, 42]], 'global forced children changed')
    for r in critical:
        check(r['root_targets'][0] == 1 and r['cutoff'] == 1, 'critical source or cutoff changed')
        for mode in MODES:
            data = r[mode]
            check(data['rank'] == r['q']-1, 'critical maximum does not saturate every root')
            check(bool(data['rows'][0]) and set(data['rows'][0]) <= {315, 525}, 'critical row leaves the two slots')
            for menu in data['all_maximum_menus']:
                used = [d for d in menu if A[d] % r['q'] == 1]
                check(len(used) == 1 and used[0] in (315, 525), 'maximum matching avoids the critical row')
                check(set(r['forced']).issubset(menu), 'critical maximum omits a forced child')
    controls = {}
    for mode in MODES:
        menus = [r[mode]['all_maximum_menus'] for r in critical]
        fps = [[footprint(r, ds, A, hits) for ds in menu] for r, menu in zip(critical, menus)]
        check([len(menu) for menu in menus] == ([2, 4, 2] if mode == 'full' else [1, 2, 2]),
              'critical complete menu counts changed')
        pairs = []
        for i, j in combinations(range(3), 2):
            check(set(critical[i]['root_targets']) & set(critical[j]['root_targets']) == {1},
                  'critical sources share another original target')
            relation = [(a, b) for a, left in enumerate(fps[i]) for b, right in enumerate(fps[j]) if left.isdisjoint(right)]
            projections = [len({a for a, _ in relation}) == len(menus[i]),
                           len({b for _, b in relation}) == len(menus[j])]
            check(bool(relation), 'a critical binary relation is empty')
            if mode == 'full':
                check(all(projections), 'full binary relation lacks a complete projection')
            common = set().union(*fps[i]) & set().union(*fps[j])
            pairs.append(dict(sources=[CRITICAL[i], CRITICAL[j]], shared_slots=sorted(common),
                              compatible_menu_indices=relation, complete_projections=projections))
        compatible, patterns, minimum_load = 0, Counter(), 3
        for indices in product(*(range(len(menu)) for menu in menus)):
            selected = [menus[i][index] for i, index in enumerate(indices)]
            labels = [next(d for d in ds if A[d] % r['q'] == 1) for ds, r in zip(selected, critical)]
            loads = Counter(slot for i, index in enumerate(indices) for slot in fps[i][index])
            check(loads[1, 315] + loads[1, 525] == 3, 'critical triple does not use exactly three slots')
            minimum_load = min(minimum_load, max(loads.values()))
            compatible += max(loads.values()) <= 1
            patterns[','.join(map(str, labels))] += 1
        check(compatible == 0 and minimum_load == 2, 'critical triple capacity obstruction changed')
        controls[mode] = dict(triples_checked=sum(patterns.values()), compatible_triples=compatible,
                              minimum_maximum_slot_load=minimum_load,
                              critical_slot_pattern_counts=dict(patterns), binary_relations=pairs)
    return critical, controls


def main():
    A, Q, primes, hits, private = prepare()
    records = source_menus(A, Q, primes, hits, private)
    critical, controls = critical_control(A, primes, hits, records)
    totals = {mode: dict(rank_sum=sum(r[mode]['rank'] for r in records.values()),
                         all_maximum_menus=sum(len(r[mode]['all_maximum_menus']) for r in records.values()),
                         forced_maximum_menus=sum(len(r[mode]['forced_maximum_menus']) for r in records.values()),
                         independent_minimum_height=sum(min(r[mode]['forced_menu_heights']) for r in records.values()))
              for mode in MODES}
    check(totals['full'] == dict(rank_sum=863, all_maximum_menus=881,
                                forced_maximum_menus=877, independent_minimum_height=879), 'full menu totals changed')
    check(totals['truncated'] == dict(rank_sum=863, all_maximum_menus=853,
                                     forced_maximum_menus=849, independent_minimum_height=879), 'truncated menu totals changed')
    print(json.dumps(dict(scope=__doc__.strip(), period=Q, original_classes=len(A), aps=APS,
                          aps_order='[residue, modulus]', counts=dict(sorted(COUNTS.items())),
                          private_witnesses={d: zs[0] for d, zs in private.items()},
                          prime_source_counts={q: len(private[q]) for q in primes},
                          actual_target=dict(point=1, active_labels=sorted(hits[1])),
                          critical_sources=critical, controls=controls, all_source_totals=totals,
                          conclusion='No unit-slot-compatible family of local maximum matchings exists in either graph; the obstruction does not require forced-edge obligations.'),
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
