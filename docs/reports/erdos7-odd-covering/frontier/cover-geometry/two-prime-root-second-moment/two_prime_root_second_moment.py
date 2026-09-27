#!/usr/bin/env python3
"""Exact checks for a height-one 5-by-7 blocker second-moment theorem.

Checks stay enabled under -O. Uniform-tail controls do not test arbitrary
constrained tails. General proofs are in the companion report.
"""
from itertools import combinations, combinations_with_replacement, permutations, product
from fractions import Fraction
from collections import Counter
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


def valid(rows):
    return (all(rows) and (rows[0] | rows[1] | rows[2] | rows[3]).bit_count() >= 5
            and all((a | b).bit_count() >= 3 for a, b in combinations(rows, 2)))


def edges(rows):
    return tuple((i, j) for i, a in enumerate(rows)
                 for j in range(7) if (a >> j) & 1)


TEMPLATES = {
    'A': (1, 6, 7, 24),
    'B': (1, 6, 10, 18),
    'C': (1, 6, 10, 20),
    'D': (1, 6, 10, 48),
    'E': (3, 5, 6, 24),
    'F': (1, 6, 24, 96),
    'M': (1, 2, 4, 8, 16),
}
EXPECTED = {'A': Fraction(4), 'B': Fraction(35, 9), 'C': Fraction(4),
            'D': Fraction(4), 'E': Fraction(29, 8), 'F': Fraction(25, 7), 'M': Fraction(4)}
checks = []
for name, rows in TEMPLATES.items():
    support = edges(rows)
    padded = rows + (0,) * (5 - len(rows))
    check(all((a | b | c).bit_count() >= 3 for a, b, c in combinations(padded, 3))
          and len({j for _, j in support}) >= 5,
          'template satisfies all unrestricted root source conditions')
    denominator = 18 if name == 'B' else len(support)
    numerators = {(i, j): (2 if name == 'B' and j == 1 else 3)
                  if name == 'B' else 1 for i, j in support}
    check(sum(numerators.values()) == denominator, 'one normalized supported law')
    row_mass = Counter()
    col_mass = Counter()
    for (i, j), weight in numerators.items():
        row_mass[i] += weight
        col_mass[j] += weight
    best = -1
    witness = None
    count = 0
    # All residue choices, including absent rows, columns, and point cells.
    for a, b, u, v in product(range(5), range(7), range(5), range(7)):
        direct = sum(weight * (1 + (i == a) + (j == b) + ((i, j) == (u, v))) ** 2
                     for (i, j), weight in numerators.items())
        expanded = (denominator + 3 * row_mass[a] + 3 * col_mass[b]
                    + 2 * numerators.get((a, b), 0)
                    + (3 + 2 * (u == a) + 2 * (v == b)) * numerators.get((u, v), 0))
        check(direct == expanded, 'independent direct and expanded layout costs')
        count += 1
        if direct > best:
            best, witness = direct, (a, b, (u, v))
    gamma = Fraction(best, denominator)
    check(gamma == EXPECTED[name] <= 4, 'full independent-layout maximum')
    checks.append(dict(template=name, row_bitmasks=list(rows), edges=len(support),
                       denominator=denominator,
                       weights=[[i, j, numerators[(i, j)]] for i, j in support],
                       independent_layouts=count, exact_gamma=str(gamma), witness=witness))

# Complete six-column reduced classification, independently of the hand proof.
choices = [a for a in range(1, 64) if a.bit_count() <= 3]
permutation_tables = [tuple(sum(1 << sigma[j] for j in range(6) if a >> j & 1)
                            for a in range(64)) for sigma in permutations(range(6))]
canonical_templates = {min(tuple(sorted(table[a] for a in rows))
                           for table in permutation_tables): name
                       for name, rows in TEMPLATES.items() if name in 'ABCDE'}
check(len(canonical_templates) == 5, 'five distinct column and row isomorphism classes')
valid_count = 0
minimal_count = 0
orbit_counts = Counter()
examined_count = 0
for rows in combinations_with_replacement(choices, 4):
    examined_count += 1
    if not valid(rows):
        continue
    valid_count += 1
    if any(valid(rows[:i] + (a ^ (1 << j),) + rows[i + 1:])
           for i, a in enumerate(rows) for j in range(6) if a >> j & 1):
        continue
    minimal_count += 1
    canonical = min(tuple(sorted(table[a] for a in rows)) for table in permutation_tables)
    check(canonical in canonical_templates, 'every minimal graph has a declared template')
    orbit_counts[canonical_templates[canonical]] += 1
check(examined_count == 135751 and valid_count == 83210 and minimal_count == 900,
      'complete reduced enumeration counts')
check(dict(orbit_counts) == {'A': 180, 'B': 120, 'C': 360, 'D': 180, 'E': 60},
      'complete minimal labeled orbit counts')


def series(p, height):
    return sum((Fraction(2 * a + 1, p ** (a - 1))
                for a in range(1, height + 1)), Fraction(0))


def upper_bound(a, b):
    return (4 + Fraction(3, 8) * (a - 3) + Fraction(1, 3) * (b - 3)
            + Fraction(1, 6) * (a * b - 9))


def auxiliary(heights):
    factors = [1 + sum((Fraction(2 * a + 1, 3 ** a) for a in range(1, h + 1)),
                      Fraction(0)) for h in heights]
    return factors[0] * factors[1]


lift_controls = []
for case in checks:
    weights = {(i, j): weight for i, j, weight in case['weights']}
    denominator = case['denominator']
    for heights in ((2, 1), (1, 2), (2, 2)):
        h5, h7 = heights
        tail_count = 5 ** (h5 - 1) * 7 ** (h7 - 1)
        lifted = [(i + 5 * u, j + 7 * v, weight)
                  for (i, j), weight in weights.items()
                  for u in range(5 ** (h5 - 1)) for v in range(7 ** (h7 - 1))]
        check(sum(weight for _, _, weight in lifted) == denominator * tail_count,
              'full uniform-tail law normalizes')
        divisors = tuple(product(range(h5 + 1), range(h7 + 1)))
        caps = {}
        for a, b in divisors:
            fibres = Counter()
            for i, j, weight in lifted:
                fibres[i % (5 ** a), j % (7 ** b)] += weight
            caps[a, b] = Fraction(max(fibres.values()), denominator * tail_count)
            root_fibres = Counter()
            for (i, j), weight in weights.items():
                root_fibres[i if a else 0, j if b else 0] += weight
            root_cap = Fraction(max(root_fibres.values()), denominator)
            tail_factor = Fraction(1, (5 ** (a - 1) if a else 1)
                                   * (7 ** (b - 1) if b else 1))
            check(caps[a, b] == root_cap * tail_factor,
                  'full cylinder maximum has exact uniform-tail scaling')
            common_cap = ((Fraction(1, 5) if a or b else Fraction(1))
                          if case['template'] == 'M' else
                          Fraction(1, 6) if a and b else Fraction(3, 8) if a
                          else Fraction(1, 3) if b else Fraction(1))
            check(root_cap <= common_cap, 'same law satisfies all three root caps')
        added = sum((caps[max(a, c), max(b, d)]
                     for a, b in divisors for c, d in divisors
                     if max(a, c, b, d) > 1), Fraction(0))
        split_bound = Fraction(case['exact_gamma']) + added
        universal_bound = upper_bound(series(5, h5), series(7, h7))
        comparator = auxiliary(heights)
        check(split_bound <= universal_bound < comparator,
              'root-square and deeper-pair estimate respects uniform-tail comparison')
        lift_controls.append(dict(template=case['template'], heights=list(heights),
                                  source_points=len(lifted), cylinder_count=len(divisors),
                                  root_and_deeper_pair_upper=str(split_bound),
                                  universal_upper=str(universal_bound),
                                  auxiliary_moment=str(comparator)))

limit_5, limit_7 = Fraction(35, 8), Fraction(35, 9)
limit_upper = upper_bound(limit_5, limit_7)
check(limit_upper == Fraction(3541, 576) < 7, 'uniform-tail upper-limit constant')
slope_5 = Fraction(3, 8) + Fraction(1, 6) * limit_7
slope_7 = Fraction(1, 3) + Fraction(1, 6) * limit_5
check(slope_5 == Fraction(221, 216) and slope_7 == Fraction(17, 16),
      'two unrestricted-height slope constants')
check(slope_5 / 5 / Fraction(2, 9) == Fraction(221, 240) < 1,
      'first strict 5-height increment ratio')
check(slope_7 / 7 / Fraction(2, 9) == Fraction(153, 224) < 1,
      'first strict 7-height increment ratio')
matching_limit = 4 + (limit_5 - 3 + limit_7 - 3 + limit_5 * limit_7 - 9) / 5
check(matching_limit == Fraction(109, 18), 'separate five-matching lift constant')
check(Fraction(3, 40) - (limit_7 - 3) / 30 == Fraction(49, 1080) > 0,
      'old envelope dominates matching bound at all heights')

print(json.dumps(dict(
    scope='All 5-by-7 root sources satisfying the rectangle and column-projection conditions, and full uniform tails only; no arbitrary constrained-tail or E7 conclusion',
    template_laws=checks, reduced_enumeration_columns=6,
    examined_row_unordered_reduced_supports=examined_count,
    admissible_reduced_supports=valid_count, minimal_reduced_supports=minimal_count,
    minimal_orbit_counts=dict(sorted(orbit_counts.items())),
    total_full_independent_layouts=sum(case['independent_layouts'] for case in checks),
    uniform_tail_controls=lift_controls, uniform_tail_upper_limit=str(limit_upper),
    five_matching_uniform_tail_limit=str(matching_limit),
    strict_height_increment_ratios=[str(Fraction(221, 240)), str(Fraction(153, 224))],
    complete_reduced_enumeration_is_not_the_general_classification_proof=True
), indent=2, sort_keys=True))
