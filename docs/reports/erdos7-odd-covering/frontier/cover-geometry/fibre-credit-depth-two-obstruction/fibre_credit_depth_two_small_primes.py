#!/usr/bin/env python3
"""Exact owner-independent depth-two source/query certificates; no phase scan.

Standard-library only. Every tail uses its full mass and first moment.
All assertions use explicit exceptions and remain active under -O.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json

QS = (5, 7, 11, 13, 17, 19)
B = tuple(F(1, q-2) for q in QS)
C = tuple(F(q-1, q-2) for q in QS)
P = tuple(c/q for c, q in zip(C, QS))
W = (F(1, 4), F(1, 4), F(1, 6), F(1, 6), F(1, 6))
ROOTS = ((0, 1), (2, 3, 4))
CHOICES = tuple(tuple(1+int(l in root)+int(l == leaf) for l in range(5))
                for root in ROOTS for leaf in range(5))
T = F(615, 49)
THRESHOLD = 6


def need(test, message):
    if not test:
        raise RuntimeError(message)


def mul(xs):
    return prod(xs, start=F(1))


def atom(q, c, mass, value):
    return mass-c/q if value == 1 else c*F(q-1, q**value)


def coefficients():
    result = []
    for k in (1, 2, 3):
        values = [sum((W[l]*mul(choice[l] for choice in choices)
                       for l in range(5)), F(0))
                  for choices in product(CHOICES, repeat=k)]
        value = max(values) if k % 2 else min(values)
        result.append(value)
    need(result == [F(7, 4), F(29, 12), F(37, 4)], 'exact three source coefficients')
    return result


def signed_residuals(masses):
    norm = tuple(b/m for b, m in zip(B, masses))
    cap = {d: 3*mul(norm[i] for i in range(6) if d >> i & 1)
           for d in range(1, 64) if d.bit_count() >= 2}
    z = {0: F(1)}
    for mask in range(1, 64):
        bit = mask & -mask
        z[mask] = z[mask ^ bit]-sum((cd*z[mask ^ d]
                   for d, cd in cap.items() if d & bit and d & mask == d), F(0))
    low = {mask: value for mask, value in z.items() if mask.bit_count() <= 4}
    minimum = min(low.values())
    need(minimum > 0, 'all <=4-coordinate residuals strictly positive on every leaf')
    return minimum, [mask for mask, value in low.items() if value == minimum], z[63]


def source(masses, kappas):
    # N(h,k): partitions of an h-set into k blocks of size >=2.
    parts = {(0, 0): 1}
    for h in range(1, 7):
        for k in range(1, h//2+1):
            parts[h, k] = (k*parts.get((h-1, k), 0)
                           +(h-1)*parts.get((h-2, k-1), 0))
    value = mul(masses)
    for mask in range(1, 64):
        scale = mul(B[i] if mask >> i & 1 else masses[i] for i in range(6))
        for k in range(1, mask.bit_count()//2+1):
            value += (-1)**k*kappas[k-1]*parts[mask.bit_count(), k]*scale
    need(value > 0, 'positive common source lower bound')
    return value


def query(masses):
    low = {1: F(1)}
    for q, c, mass in zip(QS, C, masses):
        fresh = {}
        for old, p in low.items():
            for value in range(1, THRESHOLD):
                if old*value < THRESHOLD:
                    fresh[old*value] = fresh.get(old*value, F(0))+p*atom(q, c, mass, value)
        low = fresh
    total = mul(masses)
    moment = mul(m+b for m, b in zip(masses, B))
    tail_mass = total-sum(low.values(), F(0))
    tail_first = moment-sum((n*p for n, p in low.items()), F(0))
    need(tail_mass >= 0 and tail_first >= THRESHOLD*tail_mass, 'exact full product tail')

    def phi(n):
        return sum((weight*max(mult*n-THRESHOLD, 0)
                    for mult, weight in ((1, F(1, 2)), (2, F(1, 4)), (3, F(1, 4)))), F(0))

    value = F(7, 4)*tail_first-THRESHOLD*tail_mass
    value += sum((p*phi(n) for n, p in low.items()), F(0))
    correction = {1: F(17, 4), 2: F(5, 2), 3: F(3, 2), 4: F(1), 5: F(1, 2)}
    closed = F(7, 4)*moment-6*total+sum((correction[n]*p for n, p in low.items()), F(0))
    need(value == closed, 'five-small-atom closed query formula')
    # Compare every allocation at all hinge breakpoints. For n>=6 the
    # functions are affine, so n=6 plus the exact slope suffices.
    for choice in CHOICES:
        for n in (F(0), F(2), F(3), F(6)):
            need(sum((W[l]*max(choice[l]*n-6, 0) for l in range(5)), F(0)) <= phi(n),
                 'fixed winning root/leaf corner at every real hinge breakpoint')
        need(sum((W[l]*choice[l] for l in range(5)), F(0)) <= F(7, 4),
             'fixed winning root/leaf corner at infinity')
    return value, low


def certificate(name, budget, kappas, score_floor, query_ceiling):
    masses = tuple(1-c*b for c, b in zip(budget, B))
    need(all(m >= p for m, p in zip(masses, P)), 'nonnegative auxiliary zero atoms')
    residual, masks, top = signed_residuals(masses)
    g = source(masses, kappas)
    h, low = query(masses)
    score = (T-6)*g-h
    r = 5+h/g
    need(score > score_floor and r < query_ceiling and query_ceiling < T-1,
         'strict same-source continuation certificate')
    return dict(name=name, star_budget_multipliers=list(map(str, budget)),
                target_masses=list(map(str, masses)),
                four_coordinate_minimum=str(residual),
                minimum_coordinate_sets=[[QS[i] for i in range(6) if mask >> i & 1] for mask in masks],
                six_coordinate_max_cap_residual=str(top),
                minimum_query_zero_atom=str(min(m-p for m, p in zip(masses, P))),
                source_lower=str(g), source_lower_decimal=float(g),
                query_hinge_upper=str(h), small_product_atoms={str(n): str(p) for n, p in low.items()},
                score=str(score), score_decimal=float(score), strict_score_floor=str(score_floor),
                query_upper=str(r), query_upper_decimal=float(r), strict_query_ceiling=str(query_ceiling))


def calculate():
    kappas = coefficients()
    certificates = [
        certificate('all six star budgets <=9b/10', (F(9, 10),)*6, kappas, F(1, 50), F(113, 10)),
        certificate('small 5/7 budgets <=2b/3; 11/13/17/19 budgets <=2b',
                    (F(2, 3),)*2+(F(2),)*4, kappas, F(7, 500), F(113, 10)),
    ]
    first_level_forcing = []
    for q, expected in ((5, F(4, 45)), (7, F(8, 105))):
        b, c = F(1, q-2), F(q-1, q-2)
        tail = 2*c/F(q*(q-1))
        cutoff = F(2, 3)*b-tail
        need(tail == 2*b/q and cutoff == expected, 'complete higher-star-tail forcing arithmetic')
        first_level_forcing.append(dict(prime=q, original_first_labels=[3*q, 9*q],
                                         full_higher_tail_cap=str(tail),
                                         forced_first_union_mass_strictly_above=str(cutoff)))
    result = dict(scope='Conditional whole-family v3<=2 with six core q coordinates and pure-conditioned outside23/29. Actual leafwise masks satisfy the displayed bounds; no global profile-cover assertion.',
                  method='Uniform thinning of one actual carrier; shared original root/leaf inventories; full signed-support lower and full-tail same-carrier query upper.',
                  primes=QS, weights=list(map(str, W)), threshold=THRESHOLD,
                  target_plus_one=str(T), source_coefficients=list(map(str, kappas)),
                  certificates=certificates, first_level_forcing=first_level_forcing,
                  evidence='Ordinary proof and exact rational verification; no new Lean verification.')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with exact replay')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
