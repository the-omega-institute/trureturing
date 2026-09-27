#!/usr/bin/env python3
"""Exact original-label head optimization under full-history atom caps.

The input prime tuple fixes the head order before sampling. A state retains
the original labels whose earlier coordinate requirements still match.
All Bellman arithmetic is integral, and no exponent is cut off.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import gcd, lcm, prod
import json
import random


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def prime(p):
    return p >= 2 and all(p % d for d in range(2, int(p ** .5) + 1))


def prepare(primes, heights, labels):
    check(len(primes) == len(heights) and primes and 3 in primes, 'head shape')
    check(len(set(primes)) == len(primes) and all(prime(p) and 3 <= p <= 73 for p in primes), 'distinct head primes in a fixed prescribed order')
    check(all(isinstance(h, int) and h >= 1 for h in heights), 'full finite heights')
    period = prod(p ** h for p, h in zip(primes, heights))
    check(len({n for n, _ in labels}) == len(labels), 'distinct original numerical moduli')
    check(all(isinstance(n, int) and isinstance(r, int) and n > 1 and n % 2 and period % n == 0 for n, r in labels), 'original labels divide head')
    rows = []
    for n, r in labels:
        rest = n
        row = []
        for p in primes:
            e = 0
            q = 1
            while rest % p == 0:
                rest //= p
                e += 1
                q *= p
            row.append((e, r % q))
        check(rest == 1, 'complete factorization')
        rows.append(tuple(row))
    cardinalities = tuple((3 ** h - 1) // 2 if p == 3 else ((p - 3) * p ** h + 2) // (p - 1) for p, h in zip(primes, heights))
    return tuple(rows), cardinalities, period


def partition_coordinate(rows, active, axis, p, height):
    """Group ALL p^height leaves by the exact set of matching labels.

    Only queried trie nodes are expanded; unqueried branches retain their
    exact geometric multiplicity. Original label indices are never merged.
    """
    output = defaultdict(int)

    def visit(depth, inherited, pending):
        hits = inherited + tuple(j for j in pending if rows[j][axis][0] == depth)
        deeper = [j for j in pending if rows[j][axis][0] > depth]
        if not deeper:
            output[tuple(sorted(hits))] += p ** (height - depth)
            return
        children = defaultdict(list)
        power = p ** depth
        for j in deeper:
            digit = (rows[j][axis][1] // power) % p
            children[digit].append(j)
        missing = p - len(children)
        output[tuple(sorted(hits))] += missing * p ** (height - depth - 1)
        for child in children.values():
            visit(depth + 1, hits, child)

    visit(0, (), active)
    output = {key: value for key, value in output.items() if value}
    check(sum(output.values()) == p ** height, 'full coordinate partition')
    return tuple(sorted(output.items()))


def solve(primes, heights, labels, retain_certificate=False):
    rows, cardinalities, period = prepare(primes, heights, labels)
    dimension = len(primes)
    suffix_size = [prod(cardinalities[i:]) for i in range(dimension + 1)]
    certificate = {}

    @lru_cache(None)
    def value(axis, active):
        if not active:
            return 0
        if any(all(rows[j][i][0] == 0 for i in range(axis, dimension)) for j in active):
            return suffix_size[axis]
        check(axis < dimension, 'terminal union accounted')
        groups = partition_coordinate(rows, active, axis, primes[axis], heights[axis])
        ranked = sorted((value(axis + 1, hits), hits, multiplicity) for hits, multiplicity in groups)
        remaining = cardinalities[axis]
        optimum = 0
        selected = []
        for child_value, hits, multiplicity in ranked:
            take = min(remaining, multiplicity)
            if take:
                optimum += take * child_value
                selected.append(dict(active=list(hits), multiplicity=multiplicity, taken=take, child_numerator=child_value))
                remaining -= take
            if not remaining:
                break
        check(remaining == 0, 'enough genuine current leaves')
        check(0 <= optimum <= suffix_size[axis], 'probability numerator')
        if retain_certificate:
            certificate[(axis, active)] = dict(axis=axis, active=list(active), numerator=optimum, denominator=suffix_size[axis], selected=selected)
        return optimum

    numerator = value(0, tuple(range(len(rows))))
    result = dict(primes=list(primes), heights=list(heights), original_labels=[list(x) for x in labels],
                  original_period=period, cardinalities=list(cardinalities), numerator=numerator,
                  denominator=suffix_size[0], minimum_bad_mass=str(Fraction(numerator, suffix_size[0])),
                  meets_nine_twentieths=20 * numerator <= 9 * suffix_size[0], states=value.cache_info().currsize)
    if retain_certificate:
        result['policy_states'] = [certificate[key] for key in sorted(certificate)]
    return result


def dense_check(primes, heights, labels):
    """Independent full-word Bellman calculation, plus actual CRT union."""
    sizes = tuple(p ** h for p, h in zip(primes, heights))
    rows, ks, period = prepare(primes, heights, labels)
    # Determine each full tuple's union membership by original integer CRT.
    membership = {}
    for x in range(period):
        membership[tuple(x % n for n in sizes)] = int(any(x % n == r % n for n, r in labels))

    def recurse(prefix):
        axis = len(prefix)
        if axis == len(sizes):
            return membership[prefix], (prefix,)
        child = [(recurse(prefix + (a,)), a) for a in range(sizes[axis])]
        child.sort(key=lambda item: (item[0][0], item[1]))
        chosen = child[:ks[axis]]
        return sum(item[0][0] for item in chosen), tuple(leaf for item in chosen for leaf in item[0][1])

    count, leaves = recurse(())
    check(len(leaves) == len(set(leaves)) == prod(ks), 'actual equal leaf mass')
    check(sum(membership[x] for x in leaves) == count, 'actual head event under policy')
    for axis, k in enumerate(ks):
        prefixes = defaultdict(lambda: defaultdict(int))
        for leaf in leaves:
            prefixes[leaf[:axis]][leaf[axis]] += 1
        for branch in prefixes.values():
            check(len(branch) == k, 'exact number of selected children')
            total = sum(branch.values())
            check(all(k * amount == total for amount in branch.values()), 'full-history leaf cap')
    candidate = solve(primes, heights, labels)
    check(count == candidate['numerator'], 'compressed/dense exact equality')
    # Audit every reachable active-state partition against all current leaves.
    states = {(0, tuple(range(len(rows))))}
    queries = 0
    while states:
        axis, active = states.pop()
        if axis == len(sizes):
            continue
        expected = defaultdict(int)
        for a in range(sizes[axis]):
            hits = tuple(j for j in active if a % (primes[axis] ** rows[j][axis][0]) == rows[j][axis][1])
            expected[hits] += 1
        actual = dict(partition_coordinate(rows, active, axis, primes[axis], heights[axis]))
        check(actual == dict(expected), 'all-leaf signature partition')
        queries += 1
        if axis + 1 < len(sizes):
            states.update((axis + 1, hits) for hits in actual)
    return dict(period=period, states=candidate['states'], partition_queries=queries,
                minimum_bad_mass=candidate['minimum_bad_mass'], selected_leaves=len(leaves))


def ternary_three_tree_orbit():
    """Full C_(3,3) orbit by local child swaps in the actual LSB-digit tree."""
    canonical = set()
    for height in range(1, 4):
        canonical = {3 * a for a in range(3 ** (height - 1))} | {3 * a + 1 for a in canonical}
    canonical = tuple(sorted(canonical))
    check(len(canonical) == 13, 'canonical ternary C3 cardinality')
    generators = []
    for depth in range(3):
        modulus = 3 ** depth
        for prefix in range(modulus):
            for lower in (0, 1):
                permutation = []
                for a in range(27):
                    image = a
                    if a % modulus == prefix:
                        digit = (a // modulus) % 3
                        if digit == lower:
                            image += modulus
                        elif digit == lower + 1:
                            image -= modulus
                    permutation.append(image)
                check(sorted(permutation) == list(range(27)), 'actual tree generator permutation')
                generators.append(tuple(permutation))
    seen = {canonical}
    queue = deque([canonical])
    while queue:
        subset = queue.popleft()
        for permutation in generators:
            image = tuple(sorted(permutation[a] for a in subset))
            check(len(image) == 13, 'tree orbit preserves subset size')
            if image not in seen:
                seen.add(image)
                queue.append(image)
    check(len(generators) == 26 and len(seen) == 108, 'complete ternary C3 tree orbit')
    return canonical, tuple(sorted(seen))


def strict_correlation_gap_189():
    """Exact separation for three admissible-law classes on original labels.

    For arbitrary capped product marginals, a bilinear minimum is attained at
    a pair of marginal-polytope vertices: fix one marginal and minimize the
    other, then reverse. These vertices are uniform k-subsets. Thus all 21
    column subsets and the 13 cheapest actual CRT rows give the real-cap
    product minimum. Tree orbits are a strictly smaller product-law class.
    """
    labels = [(3, 0), (9, 1), (27, 4), (7, 0), (21, 1), (63, 2), (189, 59)]
    optimum = solve((3, 7), (3, 1), labels, retain_certificate=True)
    check(optimum['cardinalities'] == [13, 5] and optimum['numerator'] == 0,
          'strict example correlated optimum and full-power caps')
    crt = {(a, b): (28 * a + 162 * b) % 189 for a, b in product(range(27), range(7))}
    check(len(set(crt.values())) == 189 and all(x % 27 == a and x % 7 == b for (a, b), x in crt.items()),
          'strict example actual original integer CRT')
    bad = {cell: int(any(x % n == r % n for n, r in labels)) for cell, x in crt.items()}
    pure3 = [(n, r) for n, r in labels if 27 % n == 0]
    survivors = tuple(a for a in range(27) if not any(a % n == r % n for n, r in pure3))
    check(survivors == (2, 5, 7, 8, 11, 13, 14, 16, 17, 20, 22, 23, 25, 26),
          'actual pure-3 surviving original rows')
    source_groups = defaultdict(list)
    for a in survivors:
        source_groups[tuple(b for b in range(7) if bad[a, b])].append(a)
    check(dict(source_groups) == {(0,): [8, 14, 17, 23, 26], (0, 1): [7, 13, 16, 22, 25],
                                  (0, 2): [2, 11, 20], (0, 3): [5]},
          'actual original-label survivor source groups')

    # Explicit full-history policy: uniform 13 rows, then five actual safe
    # columns for each row. Its conditional law is allowed to depend on a.
    conditional_rows = []
    support = []
    for a in survivors[:13]:
        chosen = [b for b in range(7) if not bad[a, b]][:5]
        check(len(chosen) == 5, 'five actual safe conditional leaves')
        conditional_rows.append(dict(row=a, columns=chosen))
        support.extend((a, b) for b in chosen)
    check(len(conditional_rows) == 13 and len(set(support)) == 65 and
          all(not bad[cell] for cell in support), 'actual zero-risk 13-by-5 conditional witness')

    column_subsets = tuple(combinations(range(7), 5))
    product_cases = []
    row_costs = {}
    for columns in column_subsets:
        costs = tuple(sum(bad[a, b] for b in columns) for a in range(27))
        row_costs[columns] = costs
        product_cases.append(dict(columns=list(columns), numerator=sum(sorted(costs)[:13])))
    product_minimum = min(case['numerator'] for case in product_cases)
    check(len(product_cases) == 21 and product_minimum == 3, 'all capped product laws minimum 3/65')
    product_minimizers = []
    for columns, costs in row_costs.items():
        if sum(sorted(costs)[:13]) != product_minimum:
            continue
        cutoff = sorted(costs)[12]
        mandatory = [a for a in range(27) if costs[a] < cutoff]
        tied = [a for a in range(27) if costs[a] == cutoff]
        for selection in combinations(tied, 13 - len(mandatory)):
            rows = sorted(mandatory + list(selection))
            bad_integers = sorted(crt[a, b] for a, b in product(rows, columns) if bad[a, b])
            check(len(bad_integers) == 3, 'actual capped product minimizer')
            product_minimizers.append(dict(rows=rows, columns=list(columns), bad_original_integers=bad_integers))

    canonical, orbit = ternary_three_tree_orbit()
    orbit_minimum = 66
    orbit_minimizers = []
    per_orbit_histogram = Counter()
    pure3_free = []
    for rows in orbit:
        if set(rows) <= set(survivors):
            pure3_free.append(rows)
        best_row_numerator = 66
        for columns in column_subsets:
            numerator = sum(bad[a, b] for a, b in product(rows, columns))
            best_row_numerator = min(best_row_numerator, numerator)
            if numerator < orbit_minimum:
                orbit_minimum = numerator
                orbit_minimizers = []
            if numerator == orbit_minimum:
                orbit_minimizers.append(dict(rows=list(rows), columns=list(columns),
                                            bad_original_integers=sorted(crt[a, b] for a, b in product(rows, columns) if bad[a, b])))
        per_orbit_histogram[best_row_numerator] += 1
    check(orbit_minimum == 4 and len(orbit_minimizers) == 2, 'actual tree-orbit product minimum 4/65')
    check(len(pure3_free) == 2 and all(set(range(2, 27, 3)) <= set(rows) for rows in pure3_free),
          'pure-3-free tree orbits contain all root-2 leaves')
    check(all([sum(bad[a, b] for a in rows) for b in range(7)] == [13, 4, 3, 1, 0, 0, 0]
              for rows in pure3_free), 'pure-3-free tree-orbit column certificate')
    check(sum(per_orbit_histogram.values()) == 108, 'complete orbit minimum histogram')
    reverse = dense_check((7, 3), (1, 3), labels)
    reverse_row_numerators = [sum(sorted(bad[a, b] for a in range(27))[:13]) for b in range(7)]
    check(reverse_row_numerators == [13, 4, 2, 0, 0, 0, 0], 'actual reverse-order full-power rows')
    check(sum(sorted(reverse_row_numerators)[:5]) == 2 and reverse['minimum_bad_mass'] == '2/65',
          'fixed reversed head order exact optimum 2/65')
    return dict(name='strict-correlation-gap-189', exact_label_lcm=lcm(*(n for n, _ in labels)),
                **optimum, comparison=dict(
                    denominator=65,
                    pure3_surviving_rows=list(survivors),
                    actual_survivor_groups=[dict(forbidden_columns=list(columns), rows=rows)
                                            for columns, rows in sorted(source_groups.items())],
                    correlated=dict(minimum_bad_mass='0', first_row_mass='1/13',
                                    conditional_leaf_mass='1/5', conditional_rows=conditional_rows,
                                    actual_support_size=len(support)),
                    capped_product=dict(minimum_bad_mass=str(Fraction(product_minimum, 65)),
                                        all_column_subset_minima=product_cases, minimizers=product_minimizers),
                    fixed_order_comparison=dict(forward_primes=[3, 7], forward_minimum='0',
                                                reverse_primes=[7, 3], reverse_heights=[1, 3],
                                                reverse_row_numerators=reverse_row_numerators,
                                                reverse_dense_check=reverse),
                    tree_orbit_product=dict(minimum_bad_mass=str(Fraction(orbit_minimum, 65)),
                                            canonical_ternary_C3=list(canonical), orbit_size=len(orbit),
                                            product_pairs=len(orbit) * len(column_subsets),
                                            minimizers=orbit_minimizers,
                                            per_orbit_minimum_numerator_histogram=dict(sorted(per_orbit_histogram.items())),
                                            pure3_free_rows=[list(rows) for rows in pure3_free],
                                            pure3_free_column_bad_counts=[13, 4, 3, 1, 0, 0, 0])))


def counterexample_78_labels():
    """Fixed original residues; one global phase for each numerical modulus."""
    return [(3, 0), (5, 0), (7, 2), (9, 4), (11, 7), (13, 2),
            (15, 14), (17, 6), (19, 1), (21, 14), (25, 21), (27, 10),
            (33, 20), (35, 27), (39, 22), (45, 43), (49, 43), (51, 35),
            (55, 11), (57, 5), (63, 7), (65, 33), (75, 53), (77, 67),
            (81, 46), (85, 36), (91, 12), (95, 76), (99, 70), (105, 17),
            (117, 7), (119, 39), (121, 41), (125, 26), (133, 68), (135, 109),
            (143, 47), (147, 68), (153, 97), (165, 143), (169, 135), (171, 25),
            (175, 66), (187, 50), (189, 28), (195, 143), (209, 93), (221, 123),
            (225, 79), (231, 32), (243, 100), (245, 197), (247, 127), (255, 8),
            (273, 173), (275, 206), (285, 158), (289, 251), (297, 181), (315, 52),
            (323, 150), (325, 206), (343, 78), (351, 154), (357, 26), (361, 170),
            (363, 323), (375, 308), (385, 277), (399, 257), (405, 154), (425, 368),
            (429, 245), (441, 232), (455, 318), (459, 190), (475, 161), (495, 394)]


def independent_leaf_survival(primes, heights, labels):
    """Direct local-leaf max-survival and CRT cardinality, without the trie.

    GCDs extract original prime-power conditions. Each actual coordinate leaf
    is evaluated individually, and original-label bitsets only memoize states.
    """
    sizes = tuple(p ** h for p, h in zip(primes, heights))
    caps = tuple((N - 1) // 2 if p == 3 else N - 2 * sum(p ** j for j in range(h))
                 for p, h, N in zip(primes, heights, sizes))
    requirements = tuple(tuple((gcd(n, N), a % gcd(n, N)) for N in sizes) for n, a in labels)
    leaf_masks = [tuple(sum(1 << j for j, row in enumerate(requirements)
                            if a % row[axis][0] == row[axis][1]) for a in range(N))
                  for axis, N in enumerate(sizes)]
    finished = tuple(sum(1 << j for j, row in enumerate(requirements)
                         if all(q == 1 for q, _ in row[axis:]))
                     for axis in range(len(primes) + 1))
    suffix_k = tuple(prod(caps[axis:]) for axis in range(len(primes) + 1))
    suffix_n = tuple(prod(sizes[axis:]) for axis in range(len(primes) + 1))
    leaf_visits = 0

    @lru_cache(None)
    def maximum(axis, active):
        nonlocal leaf_visits
        if active == 0:
            return suffix_k[axis], suffix_n[axis]
        if active & finished[axis]:
            return 0, 0
        check(axis < len(primes), 'original-label terminal state')
        children = [maximum(axis + 1, active & mask) for mask in leaf_masks[axis]]
        leaf_visits += len(children)
        good = sum(sorted((value for value, _ in children), reverse=True)[:caps[axis]])
        count = sum(count for _, count in children)
        check(0 <= good <= suffix_k[axis] and 0 <= count <= suffix_n[axis], 'survival bounds')
        return good, count

    good, count = maximum(0, (1 << len(labels)) - 1)
    return dict(maximum_survivor_numerator=good, denominator=suffix_k[0],
                actual_survivor_count=count, original_period=suffix_n[0],
                states=maximum.cache_info().currsize, direct_coordinate_leaf_evaluations=leaf_visits)


def numerical_order_counterexample_78():
    primes = (3, 5, 7, 11, 13, 17, 19)
    heights = (5, 3, 3, 2, 2, 2, 2)
    labels = counterexample_78_labels()
    check(len(labels) == len({n for n, _ in labels}) == 78, '78 distinct original moduli')
    check(all(n > 1 and n % 2 and 0 <= a < n for n, a in labels), 'literal odd original classes')

    def smooth(n):
        for p in primes:
            while n % p == 0:
                n //= p
        return n == 1

    check([n for n, _ in labels] == [n for n in range(3, 501, 2) if smooth(n)], 'exact 19-smooth modulus set')
    sizes = [p ** h for p, h in zip(primes, heights)]
    check(all(N in {n for n, _ in labels} for N in sizes) and lcm(*(n for n, _ in labels)) == prod(sizes),
          'counterexample heights belong to the actual original family')
    optimum = solve(primes, heights, labels)
    independent = independent_leaf_survival(primes, heights, labels)
    K = optimum['denominator']
    bad = optimum['numerator']
    check(K == independent['denominator'] == 1938999971129067, 'counterexample denominator')
    check(optimum['original_period'] == independent['original_period'] == 22227341715203625,
          'counterexample actual CRT period')
    check(bad == K - independent['maximum_survivor_numerator'] == 875843233809638,
          'trie min-bad agrees with independent leaf max-survival')
    check(independent['actual_survivor_count'] == 1157800229415935, 'actual survivor cardinality')
    check(20 * bad - 9 * K == 65864936031157 and 20 * bad > 9 * K, 'strict numerical-order refutation')
    check(all(19 % n != a for n, a in labels), 'original integer 19 remains uncovered')
    return dict(name='numerical-order-counterexample-78', exact_label_lcm=lcm(*(n for n, _ in labels)),
                **optimum, independent_leaf_survival=independent,
                strict_margin_20b_minus_9K=20 * bad - 9 * K, uncovered_integer=19,
                haar_slack_20S_minus_11K=20 * independent['actual_survivor_count'] - 11 * K,
                conclusion='The numerical-order universal 9/20 fixed-cap wish is false. This input is not a cover; its other fixed orders are not settled here.')


def counterexample_154_labels():
    """Complete fixed original family; independent of the 78-label phases."""
    return [(3, 0), (5, 0), (7, 2), (9, 4), (11, 7), (13, 2),
            (15, 14), (17, 6), (19, 1), (21, 14), (23, 6), (25, 21),
            (27, 10), (29, 17), (31, 23), (33, 20), (35, 27), (37, 20),
            (39, 22), (41, 20), (43, 17), (45, 43), (47, 12), (49, 43),
            (51, 35), (53, 25), (55, 11), (57, 5), (59, 20), (61, 60),
            (63, 7), (65, 33), (67, 19), (69, 35), (71, 10), (73, 37),
            (75, 53), (77, 67), (81, 46), (85, 17), (87, 50), (91, 12),
            (93, 8), (95, 76), (99, 70), (105, 17), (111, 8), (115, 21),
            (117, 1), (119, 39), (121, 41), (123, 59), (125, 26), (129, 118),
            (133, 68), (135, 109), (141, 14), (143, 47), (145, 142), (147, 68),
            (153, 97), (155, 78), (159, 35), (161, 36), (165, 143), (169, 135),
            (171, 25), (175, 66), (177, 59), (183, 55), (185, 111), (187, 50),
            (189, 28), (195, 143), (201, 155), (203, 15), (205, 32), (207, 43),
            (209, 90), (213, 187), (215, 91), (217, 207), (219, 215), (221, 123),
            (225, 79), (231, 32), (235, 132), (243, 100), (245, 197), (247, 127),
            (253, 201), (255, 8), (259, 138), (261, 124), (265, 6), (273, 173),
            (275, 206), (279, 25), (285, 158), (287, 200), (289, 251), (295, 183),
            (297, 181), (299, 70), (301, 11), (305, 196), (315, 52), (319, 303),
            (323, 150), (325, 206), (329, 57), (333, 250), (335, 277), (341, 170),
            (343, 78), (345, 41), (351, 154), (355, 117), (357, 26), (361, 170),
            (363, 2), (365, 3), (369, 367), (371, 64), (375, 308), (377, 354),
            (385, 277), (387, 352), (391, 333), (399, 257), (403, 188), (405, 154),
            (407, 104), (413, 284), (423, 7), (425, 368), (427, 166), (429, 245),
            (435, 161), (437, 45), (441, 232), (451, 258), (455, 318), (459, 190),
            (465, 398), (469, 243), (473, 96), (475, 161), (477, 226), (481, 235),
            (483, 53), (493, 126), (495, 394), (497, 197)]


def all_order_counterexample_154():
    primes = tuple(p for p in range(3, 74, 2) if prime(p))
    heights = (5, 3, 3, 2, 2, 2, 2) + (1,) * 13
    labels = counterexample_154_labels()
    check(len(primes) == 20 and len(labels) == len({n for n, _ in labels}) == 154,
          '20 odd primes and 154 distinct original moduli')
    check(all(n > 1 and n % 2 and 0 <= a < n for n, a in labels), 'fixed odd original phases')

    def smooth(n):
        for p in primes:
            while n % p == 0:
                n //= p
        return n == 1

    check([n for n, _ in labels] == [n for n in range(3, 501, 2) if smooth(n)],
          'exact original odd 73-smooth modulus set')
    sizes = [p ** h for p, h in zip(primes, heights)]
    check(all(N in {n for n, _ in labels} for N in sizes) and lcm(*(n for n, _ in labels)) == prod(sizes),
          '154-family full actual original heights')
    optimum = solve(primes, heights, labels)
    independent = independent_leaf_survival(primes, heights, labels)
    K = optimum['denominator']
    S = independent['actual_survivor_count']
    check(K == independent['denominator'] == 4385364744027208669814574741078700875,
          '154-family exact joint cap denominator')
    check(optimum['original_period'] == independent['original_period'] == 93334171363271157468761359267761115875,
          '154-family actual original CRT period')
    check(S == 2254630674715456873605308528779445940, '154-family actual survivor cardinality')
    check(optimum['numerator'] == K - independent['maximum_survivor_numerator'] == 2412632030500994251235961799423987575,
          '154 numerical-order min-bad and independent max-survival agree')
    check(11 * K - 20 * S == 3146398689990157895854151576276790825 and 11 * K > 20 * S,
          'order-independent joint-atom-cap obstruction')
    check(all(34 % n != a for n, a in labels), 'original integer 34 remains uncovered')
    return dict(name='all-order-joint-atom-counterexample-154', exact_label_lcm=lcm(*(n for n, _ in labels)),
                **optimum, independent_leaf_survival=independent,
                gap_11K_minus_20S=11 * K - 20 * S,
                every_joint_atom_capped_law_bad_mass_at_least=str(Fraction(K - S, K)),
                uncovered_integer=34,
                conclusion='The universal 9/20 fixed-cap wish fails for every fixed order and every joint law retaining atom cap 1/K. This actual original family is not a cover.')


def examples():
    rng = random.Random(504073)
    fixtures = []
    fixed = [(3, 0), (5, 0), (7, 0), (15, 11), (21, 16), (35, 18), (105, 29)]
    fixtures.append(('product-local-trap', (3, 5, 7), (1, 1, 1), fixed))
    for h in (2, 3, 8, 20):
        fixtures.append(('full-height-padding-' + str(h), (3, 5, 7), (h, h, h), fixed))
    genuine = fixed + [(p ** 20, 1 + p + p ** 19) for p in (3, 5, 7)]
    fixtures.append(('genuine-original-exponent-20', (3, 5, 7), (20, 20, 20), genuine))
    cases = []
    for p, h in (((3, 5), (2, 2)), ((3, 5, 7), (2, 1, 1)), ((3, 5, 7), (2, 2, 1)), ((3, 7), (3, 1))):
        moduli = [prod(q ** a for q, a in zip(p, powers)) for powers in product(*(range(e + 1) for e in h)) if any(powers)]
        for trial in range(6):
            labels = [(n, rng.randrange(n)) for n in moduli if trial != 5 or rng.randrange(2)]
            result = dense_check(p, h, labels)
            cases.append(dict(primes=p, heights=h, trial=trial, **result))
    fixture_results = [dict(name=name, exact_label_lcm=lcm(*(n for n, _ in labels)),
                            **solve(p, h, labels, retain_certificate=True)) for name, p, h, labels in fixtures]
    check(fixture_results[-1]['exact_label_lcm'] == fixture_results[-1]['original_period'],
          'genuine exponent-20 fixture has exact full-power original-label lcm')
    fixture_results.append(strict_correlation_gap_189())
    fixture_results.append(numerical_order_counterexample_78())
    fixture_results.append(all_order_counterexample_154())
    return dict(fixture_results=fixture_results, dense_checks=cases,
                period_field_meaning='original_period is the ambient head coordinate product; exact_label_lcm is the lcm of the supplied original numerical moduli.')



import argparse
from pathlib import Path
import hashlib
import importlib.util
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/source-budgets/capped_head_bellman.json'
SOURCES = ('certificate_io.py',
           'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md',
           'problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md',
           'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md',
           '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean',
           '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Probability.lean',
           '../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean',
           '../../../Library/Arith/schroeder2026noncoverage.md')


def calculate(base):
    result = dict(scope='Exact finite original-head optimum for each supplied fixed order. Literal original families refute the universal 9/20 fixed-cap wish in numerical order and, by survivor cardinality, for all fixed orders and all laws retaining the same joint atom cap.', **examples())
    result['schema'] = 'capped-head-bellman-v1'
    result['source_sha256'] = {name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('capped_head_bellman_certificate_io',args.base/'certificate_io.py')
    check(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        check(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),'exact capped-head Bellman replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
