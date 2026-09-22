#!/usr/bin/env python3
"""Exact complete-layout second moment for the abstract source of report 388.

Standard library only; checks remain enabled under -O. General all-height
claims use the proof in report 389, not the finite control list below.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import lcm, prod
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


P = (5, 7, 11)
ROOT_CENTER = (1, 4, 5)
R = tuple(sorted({(u + 1, i + 1, i + (0, 1, 3)[u] + d + 1)
                  for u in range(3) for i in range(6) for d in (0, 1)}))
check(len(R) == 36, "root source size")


def crt(values, moduli):
    x, period = 0, 1
    for a, modulus in zip(values, moduli):
        x += ((a - x) * pow(period, -1, modulus) % modulus) * period
        period *= modulus
        x %= period
    return x


root_moduli = tuple(sorted(prod(p for p, bit in zip(P, bits) if bit)
                           for bits in product((0, 1), repeat=3)))
root_values = tuple(crt(x, P) for x in R)
root_center_value = crt(ROOT_CENTER, P)
check(root_center_value == 291, "specified CRT centre")
expected_caps = {1: F(1), 5: F(1, 3), 7: F(1, 6), 11: F(1, 6),
                 35: F(1, 18), 55: F(1, 18), 77: F(1, 18), 385: F(1, 36)}
root_caps = {}
for d in root_moduli:
    counts = Counter(x % d for x in root_values)
    root_caps[d] = F(max(counts.values()), len(R))
    check(root_caps[d] == expected_caps[d], "root cylinder maximum")
    check(F(counts[root_center_value % d], len(R)) == root_caps[d],
          "one root centre simultaneously attains every cylinder maximum")

lcm_counts = Counter(lcm(d, e) for d in root_moduli for e in root_moduli)
check(lcm_counts == {1: 1, 5: 3, 7: 3, 11: 3, 35: 9, 55: 9, 77: 9, 385: 27},
      "all ordered squarefree divisor pairs")
root_upper = sum((count * root_caps[d] for d, count in lcm_counts.items()), F(0))
root_direct = F(sum(sum((x - root_center_value) % d == 0 for d in root_moduli) ** 2
                    for x in root_values), len(R))
check(root_upper == root_direct == F(21, 4), "complete root-layout sharp bound")


def A(p, height):
    return sum((F(2 * a + 1, p ** (a - 1)) for a in range(1, height + 1)), F(0))


def moment_polynomial(values):
    a, b, c = values
    return 1 + a / 3 + (b + c) / 6 + (a * b + a * c + b * c) / 18 + a * b * c / 36


def auxiliary_moment(heights):
    return prod(1 + sum((F(2 * a + 1, r ** a) for a in range(1, h + 1)), F(0))
                for r, h in zip((3, 3, 5), heights))


height_controls = []
for heights in ((1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2), (2, 2, 2)):
    moduli = tuple(p ** h for p, h in zip(P, heights))
    exponent_vectors = tuple(product(*(range(h + 1) for h in heights)))
    divisors = {es: prod(p ** e for p, e in zip(P, es)) for es in exponent_vectors}
    full_points = tuple(tuple(root + p * tail for root, p, tail in zip(x, P, tails))
                        for x in R
                        for tails in product(*(range(p ** (h - 1))
                                               for p, h in zip(P, heights))))
    actual_values = tuple(crt(x, moduli) for x in full_points)
    expected_size = len(R) * prod(p ** (h - 1) for p, h in zip(P, heights))
    check(len(actual_values) == len(set(actual_values)) == expected_size,
          "entire lifted source without duplicate points")
    # A different, nonzero high tail stresses simultaneous attainment.
    full_center = tuple(c + p * (p ** (h - 1) - 1)
                        for c, p, h in zip(ROOT_CENTER, P, heights))
    center_value = crt(full_center, moduli)
    caps = {}
    for es, d in divisors.items():
        rad = prod(p for p, e in zip(P, es) if e)
        predicted = root_caps[rad] * prod(F(1, p ** (e - 1))
                                         for p, e in zip(P, es) if e)
        counts = Counter(x % d for x in actual_values)
        caps[d] = F(max(counts.values()), expected_size)
        check(caps[d] == predicted, "actual lifted cylinder maximum")
        check(F(counts[center_value % d], expected_size) == predicted,
              "one full centre attains every divisor maximum")
    expanded = sum((caps[lcm(d, e)] for d in divisors.values()
                    for e in divisors.values()), F(0))
    polynomial = moment_polynomial(tuple(A(p, h) for p, h in zip(P, heights)))
    direct = F(sum(sum((x - center_value) % d == 0 for d in divisors.values()) ** 2
                   for x in actual_values), expected_size)
    check(expanded == polynomial == direct, "three independent moment evaluations")
    comparator = auxiliary_moment(heights)
    check(polynomial < comparator, "finite control has strict second-moment comparison")
    height_controls.append(dict(heights=list(heights), source_points=expected_size,
                                divisors=len(divisors), exact_gamma=str(polynomial),
                                finite_auxiliary_moment=str(comparator)))


limits = tuple(F(p * (3 * p - 1), (p - 1) ** 2) for p in P)
check(limits == (F(35, 8), F(35, 9), F(88, 25)), "infinite positive-series factors")
limit_gamma = moment_polynomial(limits)
check(limit_gamma == F(256543, 32400) < 8, "exact all-height supremum")
for p, limit in zip(P, limits):
    for height in range(1, 9):
        remainder = F(1, p ** (height - 1)) * (F(2 * height + 3, p - 1)
                                               + F(2, (p - 1) ** 2))
        check(limit - A(p, height) == remainder > 0,
              "closed geometric-tail remainder control")
case_a_lower = F(23, 9) * 2 * F(8, 5)
case_a_gap = case_a_lower - limit_gamma
case_b_upper = 3 + F(3, 4) * limits[2]
case_b_gap = F(32, 5) - case_b_upper
check(case_a_lower == F(368, 45) and case_a_gap == F(8417, 32400) > 0,
      "first all-height branch gives strict positive gap")
check(case_b_upper == F(141, 25) and case_b_gap == F(19, 25) > case_a_gap,
      "second all-height branch gives larger positive gap")
independent_limit = prod(1 + F(3 * r - 1, (r - 1) ** 2) for r in (3, 3, 5))
check(independent_limit == F(135, 8) > limit_gamma, "independent geometric limit")


print(json.dumps(dict(
    scope="One abstract source and its uniform independent-tail lifts; no actual odd-cover residual or universal source theorem",
    source_points=len(R), root_center=list(ROOT_CENTER), root_center_crt=root_center_value,
    complete_divisor_caps={str(d): str(root_caps[d]) for d in root_moduli},
    ordered_lcm_counts={str(d): lcm_counts[d] for d in root_moduli},
    exact_root_gamma=str(root_upper), target_root_comparison=str(F(32, 5)),
    height_controls=height_controls, positive_series_limits=[str(a) for a in limits],
    all_height_gamma_supremum=str(limit_gamma),
    all_height_gap_cases=dict(first=str(case_a_gap), second=str(case_b_gap)),
    independent_geometric_limit=str(independent_limit),
    finite_controls_are_not_the_all_height_proof=True
), indent=2, sort_keys=True))
