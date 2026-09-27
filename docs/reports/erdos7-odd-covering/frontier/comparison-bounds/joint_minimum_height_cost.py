#!/usr/bin/env python3
"""Exact cost of compatible shallow matchings in one literal period-3150 cover.

Python 3.9+, standard library only; no repository, data or solver imports.
Enumerates every forced maximum matching at every original private source,
checks its rank by all Hall cuts, and retains full original heights and tails.
The actual interaction components have two sources, so exhaustive pair menus
give the exact compatible minimum. All checks remain active with python -O.
This is an even-cover control, not an odd-cover counterexample, a general
exchange theorem, a whole-AP replacement, or a Lean proof.
"""
from collections import Counter, defaultdict
from itertools import combinations
from math import gcd, lcm
import json


COUNTS = Counter()
APS = ((0, 2), (0, 3), (0, 5), (5, 6), (0, 7), (4, 9),
       (1, 10), (3, 14), (4, 15), (4, 21), (8, 25), (7, 30),
       (33, 35), (43, 45), (23, 50), (28, 75), (13, 105),
       (93, 175), (163, 225), (43, 525))


def check(condition, name):
    COUNTS['checks'] += 1
    if not condition:
        raise ArithmeticError(name)


def height(n, q):
    e = 0
    while n % q == 0:
        n //= q
        e += 1
    return e


def primes_of(n):
    answer, p = [], 2
    while p * p <= n:
        if n % p == 0:
            answer.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        answer.append(n)
    return tuple(answer)


def reset(y, q, root, Q):
    power = q ** height(Q, q)
    B = Q // power
    a = y % power - y % q + root
    return a if B == 1 else (a + power * ((y-a) * pow(power, -1, B) % B)) % Q


def prepare():
    A = dict((d, a) for a, d in APS)
    check(len(A) == len(APS) and all(d > 1 and 0 <= a < d for d, a in A.items()), 'invalid original APs')
    Q, primes = lcm(*A), primes_of(lcm(*A))
    check(Q == 3150 and all(p in A and A[p] == 0 for p in primes), 'wrong full period or original primes')
    for d in A:
        check(all(e in A for e in range(2, d+1) if d % e == 0), 'divisor closure fails')
    for d, m in combinations(A, 2):
        if d % m == 0 or m % d == 0:
            check((A[d]-A[m]) % gcd(d, m) != 0, 'comparable original classes intersect')
    hits = tuple(frozenset(d for d, a in A.items() if z % d == a) for z in range(Q))
    check(all(hits), 'literal full-period coverage fails')
    private = {d: tuple(z for z, E in enumerate(hits) if E == {d}) for d in A}
    check(all(private.values()), 'a selected original class has no private point')
    COUNTS['full_period_points'] += Q
    return A, Q, primes, hits, private


def source_menus(A, Q, primes, hits, private):
    sources = {}
    for q in primes:
        H, roots = height(Q, q), tuple(range(1, q))
        power, B = q ** H, Q // q ** H
        forced = set()
        for root in roots:
            labels = [d for d in A if d % q == 0 and A[d] % q == root]
            if len(labels) == 1:
                d = labels[0]
                check(height(d, q) == 1 and d > q, 'forced edge is not mixed height one')
                forced.add(d)
        cofactor_tails = defaultdict(set)
        for y in private[q]:
            x, t = y % B, (y % power) // q
            cofactor_tails[x].add(t)
            columns = {}
            for d, a in A.items():
                e = height(d, q)
                m = d // q ** e
                if e and m > 1 and x % m == a % m:
                    columns[m] = max(e, columns.get(m, 0))
            check(len(columns) >= q-1, 'not enough actual compatible columns')
            ell = sorted(columns.values(), reverse=True)[q-2]
            rows, targets = {}, {}
            for root in roots:
                z = reset(y, q, root, Q)
                check(z % B == x and (z % power) // q == t, 'root lift changes original cofactor or tail')
                full = hits[z]
                check(all(d % q == 0 for d in full), 'prime-private lift meets a q-free class')
                low = {d for d in full if height(d, q) <= ell}
                check(bool(low), 'truncation loses an original root')
                rows[root] = tuple(sorted(d for d in low if d // q ** height(d, q) > 1))
                for d in rows[root]:
                    check(A[d] % q == root and z % d == A[d], 'edge lost original label identity')
                    targets[d] = (z, d)
                COUNTS['literal_root_checks'] += 1
            color = lambda d: d // q ** height(d, q)
            defect = 0
            for mask in range(1 << len(roots)):
                rr = [r for i, r in enumerate(roots) if mask >> i & 1]
                neighbor = {color(d) for r in rr for d in rows[r]}
                defect = max(defect, len(rr)-len(neighbor))
                COUNTS['hall_subsets'] += 1
            rank = len(roots)-defect
            available = sorted(set().union(*(set(row) for row in rows.values())))
            menu = tuple(ds for ds in combinations(available, rank)
                         if forced <= set(ds) and len({A[d] % q for d in ds}) == rank
                         and len({color(d) for d in ds}) == rank)
            check(bool(menu), 'forced menu does not attain the Hall maximum rank')
            costs = tuple(sum(height(d, q) for d in ds) for ds in menu)
            minimum = min(costs)
            minima = tuple(ds for ds, c in zip(menu, costs) if c == minimum)
            footprints = {}
            for ds in menu:
                fp = frozenset(targets[d] for d in ds if len(hits[targets[d][0]]) >= 2)
                check(all(not set(primes) & hits[z] for z, _ in fp), 'shared slot leaves the no-prime region')
                footprints[ds] = fp
            sources[q, y] = dict(q=q, y=y, H=H, cutoff=ell, roots=roots, rows=rows,
                                 forced=sorted(forced), rank=rank, menu=menu, costs=costs,
                                 minimum=minimum, minima=minima, footprints=footprints)
            COUNTS['sources'] += 1
            COUNTS['maximum_menus'] += len(menu)
            COUNTS['minimum_menus'] += len(minima)
        R = {x for x in range(B) if all(x % d != a for d, a in A.items() if d % q)}
        check(set(cofactor_tails) == R and all(ts == set(range(q ** (H-1))) for ts in cofactor_tails.values()),
              'enumerated sources omit an original cofactor or full tail')
    return sources


def joint_minimum(sources):
    users = defaultdict(set)
    for key, source in sources.items():
        for footprint in source['footprints'].values():
            for slot in footprint:
                users[slot].add(key)
    shared = {slot: ss for slot, ss in users.items() if len(ss) > 1}
    neighbors, edge_slots = defaultdict(set), defaultdict(list)
    for slot, ss in shared.items():
        check(len(ss) == 2, 'fixture has a shared slot with more than two sources')
        a, b = sorted(ss)
        neighbors[a].add(b)
        neighbors[b].add(a)
        edge_slots[a, b].append(slot)
    check(all(len(ns) == 1 for ns in neighbors.values()), 'interaction has a component larger than two sources')
    chosen = {key: s['minima'][0] for key, s in sources.items()}
    independent = sum(s['minimum'] for s in sources.values())
    exact = independent
    components = []
    for (a, b), slots in sorted(edge_slots.items()):
        left, right = sources[a], sources[b]
        pairs = tuple((u, v) for u in left['menu'] for v in right['menu']
                      if not left['footprints'][u] & right['footprints'][v])
        check(bool(pairs), 'full maximum menus have no compatible pair')
        cost = lambda pair: sum(height(d, a[0]) for d in pair[0]) + sum(height(d, b[0]) for d in pair[1])
        selected = min(pairs, key=lambda pair: (cost(pair), pair))
        joint_cost = cost(selected)
        local_cost = left['minimum'] + right['minimum']
        exact += joint_cost-local_cost
        chosen[a], chosen[b] = selected
        minimum_pairs = tuple(pair for pair in pairs if pair[0] in left['minima'] and pair[1] in right['minima'])
        components.append(dict(sources=[a, b], shared_slots=sorted(slots),
                               maximum_menu_sizes=[len(left['menu']), len(right['menu'])],
                               compatible_pairs=pairs, compatible_minimum_pairs=minimum_pairs,
                               original_projections_full=[len({u for u, _ in pairs}) == len(left['menu']),
                                                          len({v for _, v in pairs}) == len(right['menu'])],
                               independent_height=local_cost, compatible_height=joint_cost,
                               chosen_pair=selected))
    # All cross-source restrictions occur inside these disjoint pairs.
    # Each pair has been exhaustively minimized; isolated sources use minima.
    actual = sum(sum(height(d, q) for d in ds) for (q, _), ds in chosen.items())
    check(actual == exact >= independent, 'component optimum is not attained')
    return independent, exact, chosen, components, shared


def check_selection(A, Q, hits, sources, selection):
    check(selection.keys() == sources.keys(), 'selection omits an original source')
    loads = Counter()
    for (q, y), ds in selection.items():
        source = sources[q, y]
        check(ds in source['menu'], 'selection is not a forced truncated maximum matching')
        for d in ds:
            z = reset(y, q, A[d] % q, Q)
            check(d in hits[z], 'selected edge misses its original AP')
            if len(hits[z]) >= 2:
                loads[z, d] += 1
    return loads


def main():
    A, Q, primes, hits, private = prepare()
    sources = source_menus(A, Q, primes, hits, private)
    independent, exact, chosen, components, shared = joint_minimum(sources)
    check(len(sources) == 655 and independent == 963 and exact == 964, 'wrong complete source minima')
    check(len(shared) == 6 and len(components) == 5, 'wrong actual interaction decomposition')
    check(sorted(c['compatible_height'] for c in components) == [6, 6, 6, 6, 7], 'component cost certificate changed')
    left, right = sources[3, 1413], sources[5, 685]
    check(hits[1063] == {105, 225} and {q for q in primes if all(d % q == 0 for d in hits[1063])} == {3, 5},
          'critical actual target family changed')
    check(reset(1063, 3, 0, Q) == 1413 and reset(1063, 5, 0, Q) == 685, 'critical source resets changed')
    check(left['H'] == right['H'] == 2 and left['cutoff'] == 2 and right['cutoff'] == 1, 'original heights or cutoffs changed')
    check(left['rows'] == {1: (105, 225), 2: (6,)}
          and right['rows'] == {1: (10,), 2: (30,), 3: (105,), 4: (15,)}, 'critical complete root menus changed')
    check(left['menu'] == ((6, 105), (6, 225)) and left['costs'] == (2, 3)
          and right['menu'] == ((10, 15, 30, 105),) and right['costs'] == (4,), 'critical complete maximum menus changed')
    check(left['forced'] == [6] and right['forced'] == [10, 15, 30], 'critical forced edges changed')
    impossible = [c['sources'] for c in components if not c['compatible_minimum_pairs']]
    check(impossible == [[(3, 1413), (5, 685)]], 'wrong empty minimum-menu relation')
    good_loads = check_selection(A, Q, hits, sources, chosen)
    check(all(n <= 1 for n in good_loads.values()), '964 witness has a shared-slot collision')
    low = dict(chosen)
    low[3, 1413] = (6, 105)
    check(all(ds in sources[key]['minima'] for key, ds in low.items()), '963 witness leaves a local minimum menu')
    check(sum(sum(height(d, q) for d in ds) for (q, _), ds in low.items()) == independent, '963 minimum not attained')
    bad_loads = check_selection(A, Q, hits, sources, low)
    check({slot: n for slot, n in bad_loads.items() if n > 1} == {(1063, 105): 2}, '963 witness has a different collision')
    check({slot for slot in good_loads.keys() | bad_loads.keys() if good_loads[slot] != bad_loads[slot]}
          == {(1063, 105), (1063, 225)}, 'height-one repair changes another slot')
    per_prime = [dict(q=q, source_count=sum(p == q for p, _ in sources),
                      independent_height=sum(s['minimum'] for (p, _), s in sources.items() if p == q),
                      compatible_height=sum(sum(height(d, q) for d in ds) for (p, _), ds in chosen.items() if p == q))
                 for q in primes]
    print(json.dumps(dict(scope=__doc__.strip(), counts=dict(sorted(COUNTS.items())),
                          period=Q, original_classes=len(A), aps=APS, aps_order='[residue, modulus]',
                          private_witnesses={d: xs[0] for d, xs in private.items()},
                          independent_minimum=independent, compatible_minimum=exact,
                          per_prime=per_prime, shared_slots=len(shared), components=components,
                          critical_sources=[{k: s[k] for k in ('q', 'y', 'H', 'cutoff', 'roots', 'rows', 'rank', 'forced', 'menu', 'costs', 'minima')}
                                            for s in (left, right)],
                          sole_963_collision=dict(slot=[1063, 105], load=2),
                          repair=dict(source=[3, 1413], old_label=105, new_label=225, extra_height=1,
                                      changed_slots=[[1063, 105], [1063, 225]], new_maximum_slot_load=max(good_loads.values()))),
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
