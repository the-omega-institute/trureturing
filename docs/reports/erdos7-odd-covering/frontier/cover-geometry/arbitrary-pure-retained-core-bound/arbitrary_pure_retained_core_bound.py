#!/usr/bin/env python3
"""Exact retained-core debit at the twenty arbitrary-pure source corners.

Reuses the actual source construction and corner classification of Report624
and the retained-inventory union estimate of Report613.  The ordinary proof
transfers these finite bounds to arbitrary finite pure phases.  No complete
remaining-original/query gate, unrestricted covering result, or Lean check.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path

THREE = ((0, 1), (0, 3), (3, 4), (3, 0))
FIVE = ((0, 1), (0, 5), (5, 6), (5, 0), (5, 10))
ORBIT3 = (6, 9, 6, 9)
ORBIT5 = (20, 75, 60, 75, 150)
QS = (7, 11, 13, 17, 19)
CHECKS = []


def check(name, condition):
    if not condition:
        raise ArithmeticError(name)
    CHECKS.append(name)


def evaluate(case, z3, h3, z5, h5):
    # Normalized live-root leaf indices, exactly as in Report624.
    w = [F() if l == z3 else F(1, 9) if l == h3 else F(2, 9)
         for l in range(6)]
    v = [F() if m == z5 else F(3, 75) if m == h5 else F(4, 75)
         for m in range(20)]
    check(f'case{case}_probability_sources', sum(w) == sum(v) == 1)
    check(f'case{case}_pure_source_caps', max(w) <= F(2, 9) and
          max(v) <= F(4, 75) and w[z3] == v[z5] == 0)
    mass = {(l, m): w[l] * v[m]
            for l, m in product(range(6), range(20))
            if (l // 3, m // 5) != (0, 0)}

    def support(predicate):
        return sum((p for (l, m), p in mass.items() if predicate(l, m)), F())

    profiles = {
        'row': [support(lambda l, m, i=i: l // 3 == i) for i in range(2)] + [F()],
        'column': [support(lambda l, m, j=j: m // 5 == j) for j in range(4)] + [F()],
        'point': [support(lambda l, m, i=i, j=j: (l // 3, m // 5) == (i, j))
                  for i, j in product(range(3), range(5))],
        'leaf9': [support(lambda l, m, a=a: l == a) for a in range(6)] + [F()] * 3,
        'leaf25': [support(lambda l, m, a=a: m == a) for a in range(20)] + [F()] * 5,
    }
    check(f'case{case}_all57_roles', sum(map(len, profiles.values())) == 57)
    maxima = {name: max(values) for name, values in profiles.items()}
    mu = sum(mass.values(), F())
    R, C, P, A, B = (maxima[k] for k in ('row', 'column', 'point', 'leaf9', 'leaf25'))
    r = {q: F(1, q - 1) for q in QS}
    a = {q: F(1, q * (q - 2)) for q in QS}
    kappa = sum((r[q] * r[s] + a[q] * r[s] + r[q] * a[s]
                 for q, s in combinations(QS, 2)), F())
    star = sum(r.values()) * (R + C + P + A + B) + sum(a.values()) * (R + C)
    pair = kappa * (mu + R + C + P)
    lower = mu - star - pair
    check(f'case{case}_positive_retained_bound', lower > 0)
    return dict(case=case, source=(z3, h3, z5, h5), weights3=w, weights5=v,
                unmasked_mass=mu, profiles=profiles, maxima=maxima,
                star_debit=star, pair_debit=pair, retained_lower=lower)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = ap.parse_args()
    check('corner_orbit_totals', sum(ORBIT3) == 30 and sum(ORBIT5) == 380 and
          sum(x * y for x, y in product(ORBIT3, ORBIT5)) == 11400)
    rows = [evaluate(i, *t3, *t5)
            for i, (t3, t5) in enumerate(product(THREE, FIVE))]
    lower = min(row['retained_lower'] for row in rows)
    minimizers = [row['case'] for row in rows if row['retained_lower'] == lower]
    check('exact_uniform_minimum', lower == F(2023457597, 269374248000) and minimizers == [2, 4])
    check('retained_mass_exceeds_three_over_four_hundred', lower > F(3, 400))

    labels = [15]
    for q in QS:
        labels.extend([3*q, 5*q, 15*q, 9*q, 25*q, 3*q*q, 5*q*q])
    for q, s in combinations(QS, 2):
        for e, f in ((1, 1), (2, 1), (1, 2)):
            labels.extend(3**i * 5**j * q**e * s**f for i, j in product(range(2), repeat=2))
    check('distinct156_odd_nonunit_mixed_labels', len(labels) == len(set(labels)) == 156 and
          all(m > 1 and m % 2 == 1 for m in labels))
    density = F(8, 3) * prod(F(q, q - 2) for q in QS)
    haar = lower / density
    check('exact_density_conversion', density == F(13832, 2025) and
          haar == F(289065371, 262856056320) and haar > F(1, 910))
    result = dict(
        schema='arbitrary-pure-retained-core-bound-v1',
        scope='Arbitrary finite pure phases and all globally fixed phases at the156 retained mixed labels. No other mixed originals are paid.',
        sources='Report624 actual pure sources and20 corner orbits; Report613 retained-inventory union estimate.',
        coordinate_primes=[3, 5, *QS], rows=rows,
        ternary_orbit_sizes=ORBIT3, quinary_orbit_sizes=ORBIT5,
        labels=sorted(labels), retained_source_lower=lower, minimum_cases=minimizers,
        density_cap=density, haar_lower=haar, strict_haar_lower='1/910',
        checks=CHECKS, check_count=len(CHECKS),
        universal_claim_basis='Ordinary source construction, separate concavity and digit-injection proof; finite checks do not establish the universal quantifiers.',
        new_lean_verification=False, remaining_LW_paid=False,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result, default=str, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('retained_source_lower', 'minimum_cases',
                                          'density_cap', 'haar_lower', 'check_count')}, default=str))


if __name__ == '__main__':
    main()
