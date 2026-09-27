#!/usr/bin/env python3
"""Exact controls for diagonal prefix sources and their minimax certificate.

The companion report proves the full-height statement. These controls do
not assert actual odd-cover realizability or test the excluded-root class.
All checks remain enabled under -O; no numerical optimization is used.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


def moment(height):
    return sum((F((t + 1) ** 4 - t ** 4, 5 ** t)
                for t in range(height + 1)), F())


def comparison(height):
    total = 1 + sum((F(2 * a + 1, 3 ** a)
                     for a in range(1, height + 1)), F())
    check(total == 3 - F(height + 2, 3 ** height),
          'finite comparison identity')
    return total ** 2


def source(height):
    return tuple((sum(u[j] * 5 ** j for j in range(height)),
                  sum(u[j] * 7 ** j for j in range(height)))
                 for u in product(range(5), repeat=height))


def finite_control(height):
    points = source(height)
    size = len(points)
    check(size == 5 ** height and len(set(points)) == size,
          'literal source cardinality')
    check({x % 5 for x, _ in points} == set(range(5)),
          'all roots present: excluded-root scope does not apply')
    divisors = tuple((a, b, 5 ** a, 7 ** b)
                     for a, b in product(range(height + 1), repeat=2))
    check(len({p * q for _, _, p, q in divisors}) == (height + 1) ** 2,
          'distinct original divisor labels retained')
    nonempty_cells = 0
    for a, b, p, q in divisors:
        counts = Counter((x % p, y % q) for x, y in points)
        check(set(counts.values()) == {5 ** (height - max(a, b))},
              'every nonempty literal cylinder has the exact mass')
        check(len(counts) == 5 ** max(a, b), 'all common prefixes counted')
        nonempty_cells += len(counts)

    expected = moment(height)
    double = sum((F((2 * a + 1) * (2 * b + 1), 5 ** max(a, b))
                  for a, b, _, _ in divisors), F())
    check(expected == double, 'two independent exponent counts agree')
    # Each source point receives the same cost averaged over all centers.
    # This is a lower certificate for every supported law, not one law.
    row_sums = []
    column_sums = [0] * size
    for x, y in points:
        total = 0
        for j, (u, v) in enumerate(points):
            load = sum(x % p == u % p and y % q == v % q
                       for _, _, p, q in divisors)
            cost = load ** 2
            total += cost
            column_sums[j] += cost
        check(F(total, size) == expected, 'pointwise exact dual certificate')
        row_sums.append(total)
    check(all(F(total, size) == expected for total in column_sums),
          'each centered layout attains the upper bound under the uniform law')
    return {'height': height, 'points': size,
            'divisor_labels': len(divisors), 'nonempty_cylinders': nonempty_cells,
            'center_source_pairs': size ** 2, 'minimax': str(expected),
            'comparison': str(comparison(height)),
            'gap': str(expected - comparison(height))}


def main():
    local_pairs = 0
    for a in combinations(range(5), 3):
        for b in combinations(range(7), 5):
            check(set(a) & set(b), 'product-tree next digit exists')
            local_pairs += 1
    for a in combinations(range(7), 3):
        check(set(a) & set(range(5)), 'standalone 7-tree next digit exists')
    controls = [finite_control(h) for h in (1, 2, 3)]
    expected = {1: F(4), 2: F(33, 5), 3: F(8), 4: F(5369, 625),
                5: F(27516, 3125)}
    gaps = {1: F(0), 2: F(28, 405), 3: F(56, 729),
            4: F(13376, 455625), 5: -F(4220216, 184528125)}
    for h in expected:
        check(moment(h) == expected[h], 'exact finite minimax value')
        check(moment(h) - comparison(h) == gaps[h], 'exact signed comparison gap')
    limit = F(5 * (5 ** 3 + 11 * 5 ** 2 + 11 * 5 + 1), (5 - 1) ** 4)
    check(limit == F(285, 32) and 9 - limit == F(3, 32),
          'reused fourth-moment limit is below nine')
    print(json.dumps({'scope': 'abstract all-root diagonal sources only',
                      'local_product_choices': local_pairs,
                      'local_standalone_choices': 35,
                      'controls': controls, 'limit': str(limit),
                      'excluded_root_case': 'not addressed'}, indent=2))


if __name__ == '__main__':
    main()
