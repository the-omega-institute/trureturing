#!/usr/bin/env python3
"""Exact shared-phase obstruction to the retained-core full-inventory certificate.

Ordinary rational calculations, not Lean or a covering-system counterexample.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path
import argparse
import json

Q = (5, 7, 11, 13, 17, 19, 23)
SLOTS = (15, 21, 45, 33, 35, 39, 63, 51, 57, 55, 105, 75,
         69, 65, 99, 77, 85, 117, 95, 165, 91, 147, 225)
LEAVES = (4, 7, 2, 5, 8)
COUNT = 0


def need(ok, label):
    global COUNT
    COUNT += 1
    if not ok:
        raise ValueError(label)


def data(m):
    n, h = m, 0
    while n % 3 == 0:
        n //= 3
        h += 1
    D = sum(1 << i for i, q in enumerate(Q) if n % q == 0)
    return h, n, D


def bit_core(bits, distinguished, short):
    non = bits & ~(1 << distinguished)
    return (not bits >> distinguished & 1 and non.bit_count() <= 1) if short else non == 0


def zero_clause(h, residue, hits, distinguished):
    if h == 0:
        return hits.bit_count() >= 2
    if residue % 3 == 0 or (h == 2 and residue % 9 == 1):
        return True
    if residue % 3 == 1:
        return bool(hits >> distinguished & 1) or (hits & ~(1 << distinguished)).bit_count() >= 2
    return bool(hits & ~(1 << distinguished))


def responses(distinguished, D):
    zero, one = F(1), F(0)
    for i, q in enumerate(Q):
        if i == distinguished or D >> i & 1:
            continue
        t = F(1, q)
        zero, one = zero * (1 - t), one * (1 - t) + zero * t
    outside = F(1) if D >> distinguished & 1 else F(Q[distinguished] - 1, Q[distinguished])
    return outside * (zero + one), zero


def calculate(certificate):
    global COUNT
    COUNT = 0
    need(certificate['schema'] == 'common-core-phase-obstruction-v1', 'schema')
    need(tuple(certificate['primes']) == Q and tuple(certificate['selected_labels']) == SLOTS,
         'fixed common numerical family')
    family = certificate['actual_family']
    need(len(family) == 25 and len({row[0] for row in family}) == 25, 'one phase per25 distinct originals')
    actual = dict(family)
    need(actual.get(3) == 0 and actual.get(9) == 1 and set(actual) == set(SLOTS) | {3, 9}, 'fixed pure anchors')
    for m, residue in family:
        need(type(m) is int and type(residue) is int and m > 1 and m % 2 == 1 and 0 <= residue < m,
             'odd nonunit canonical original')
    pair_supports = []
    for m in SLOTS:
        h, n, D = data(m)
        residue = actual[m]
        need(residue % n == 0, 'one global actual zero phase on every nonternary cofactor')
        if h:
            need(residue % (3 ** h) == (1 if h == 1 else 4), 'all actual ternary mixed phases in the short root')
            for i, q in enumerate(Q):
                if D >> i & 1:
                    need(3 * q in actual and residue % (3 * q) == actual[3 * q], 'actual mixed class contained in an actual3q star')
        else:
            need(D.bit_count() == 2 and n == prod(q for i, q in enumerate(Q) if D >> i & 1), 'actual no3 pair edge')
            pair_supports.append(D)

    caps = tuple(F(q - 1, q - 2) for q in Q)
    beta = tuple(F(prod(F(1, q - 2) for i, q in enumerate(Q) if D >> i & 1)) for D in range(128))
    remain = [[beta[D] if D and (h > 0 or D.bit_count() > 1) else F(0) for D in range(128)] for h in range(3)]
    for m in SLOTS:
        h, n, D = data(m)
        remain[h][D] -= prod(caps[i] for i in range(7) if D >> i & 1) / n
    need(all(value >= 0 for row in remain for value in row), 'nonnegative complete remaining inventories')
    P0 = prod(F(q - 1, q) for q in Q)
    fixed_a, fixed_b = F(3, 16), F(5, 24)
    all_results = []
    for distinguished, p in enumerate(Q):
        response = tuple(responses(distinguished, D) for D in range(128))
        A0, B0 = response[0]
        T = P0 * sum(F(1, q - 1) for q in Q if q != p)
        need(A0 - P0 == T, 'phase-independent exact short-root excess')
        phase_rows = []
        for match in range(128):
            # Each reference phase is either actual0 or one common nonzero representative.
            zero, one = F(1), F(0)
            for i, q in enumerate(Q):
                if i == distinguished:
                    continue
                miss = F(q - 1 if match >> i & 1 else q - 2, q)
                hit = F(0) if match >> i & 1 else F(1, q)
                zero, one = zero * miss, one * miss + zero * hit
            miss_p = F(p - 1 if match >> distinguished & 1 else p - 2, p)
            short = A0 - miss_p * (zero + one)
            long = F(0)
            for zeros in range(128):
                if not any(zeros & pair == pair for pair in pair_supports):
                    continue
                probability = F(1)
                for i, q in enumerate(Q):
                    z, same = bool(zeros >> i & 1), bool(match >> i & 1)
                    if i == distinguished:
                        probability *= F(1 if z else q - 1, q)
                    elif same:
                        probability *= F(0) if z else F(q - 1, q)
                    else:
                        probability *= F(1 if z else q - 2, q)
                long += probability
            need(short >= T and long >= 0, 'uniform conditional union lower bound for all reference phases')
            if match == 127:
                need(short == T and long == 0, 'same common reference attains the union minimum')
            failed = []
            for m in SLOTS:
                h, n, D = data(m)
                hits = D & match
                clause = zero_clause(h, actual[m], hits, distinguished)
                direct = not any(leaf % (3 ** h) == actual[m] % (3 ** h)
                                 and bit_core(hits, distinguished, leaf % 3 == 1) for leaf in LEAVES)
                need(clause == direct, 'finite shared-reference clause agrees with direct core possibility')
                if not clause:
                    failed.append(m)
            need(all(3 * q in failed for q in Q if q != p), 'at least six incompatible actual singleton stars')
            phase_rows.append(dict(match_mask=match, short_union=str(short), long_union=str(long),
                                   fixed_law_union=str(2 * fixed_a * short + 3 * fixed_b * long),
                                   failed_zero_labels=failed))

        def bound_at(a):
            b = (1 - 2 * a) / 3
            mass = 2 * a * A0 + 3 * b * B0
            high = sum(beta[D] * max(a * A, b * B) / 2 for D, (A, B) in enumerate(response))
            low = sum(remain[h][D] * (2 * a * A + 3 * b * B, max(2 * a * A, 3 * b * B), max(a * A, b * B))[h]
                      for D, (A, B) in enumerate(response) for h in range(3))
            return mass - high - low

        # Sweep every slope-change point; compare each against the original max formula.
        value = B0 - sum(remain[0][D] * B for D, (A, B) in enumerate(response))
        slope = 2 * (A0 - B0) - 2 * T - sum(2 * remain[0][D] * (A - B) for D, (A, B) in enumerate(response))
        jumps = {F(0): F(0), F(1, 2): F(0)}
        for D, (A, B) in enumerate(response):
            c1, c2 = remain[1][D], remain[2][D] + beta[D] / 2
            value -= c1 * B + c2 * B / 3
            slope += 2 * c1 * B + 2 * c2 * B / 3
            if c1:
                point = B / (2 * (A + B))
                jumps[point] = jumps.get(point, F(0)) - 2 * c1 * (A + B)
            if c2:
                point = B / (3 * A + 2 * B)
                jumps[point] = jumps.get(point, F(0)) - c2 * (A + 2 * B / 3)
        points, previous = [], F(0)
        for a, change in sorted(jumps.items()):
            need(0 <= a <= F(1, 2) and change <= 0, 'complete concave slope-change range')
            value += slope * (a - previous)
            need(value == bound_at(a) - 2 * a * T, 'slope sweep equals direct repaired formula exactly')
            points.append(dict(a=str(a), repaired_certificate=str(value)))
            previous, slope = a, slope + change
        best = max(points, key=lambda row: F(row['repaired_certificate']))
        need(F(best['repaired_certificate']) < 0, 'all symmetric laws fail this complete-inventory certificate')
        fixed_value, fixed_leak = bound_at(fixed_a), 2 * fixed_a * T
        need(fixed_value - fixed_leak < 0, 'actual-vector repair already fails before query continuation')
        # Elementary finite controls for the analytic within-root averaging bridge.
        for w1 in range(5):
            for w2 in range(5 - w1):
                for w3 in range(5 - w1 - w2):
                    for w4 in range(5 - w1 - w2 - w3):
                        w5 = 4 - w1 - w2 - w3 - w4
                        w = tuple(F(x, 4) for x in (w1, w2, w3, w4, w5))
                        s = w[0] + w[1]
                        for A, B in response:
                            need(max(A * max(w[:2]), B * max(w[2:])) >= max(A * s / 2, B * (1 - s) / 3),
                                 'within-root averaging weakly lowers every leaf/deep debit')
        all_results.append(dict(distinguished=p, phase_cases=phase_rows, fixed_law_certificate=str(fixed_value),
                                fixed_law_minimum_union=str(fixed_leak), fixed_law_repaired=str(fixed_value - fixed_leak),
                                breakpoint_count=len(points), breakpoints=points, maximizing_a=best['a'],
                                all_symmetric_maximum=best['repaired_certificate'],
                                all_symmetric_maximum_decimal=float(F(best['repaired_certificate']))))

    # Exact residual common affine options preserving the two actual pure anchors.
    affine = []
    for u in range(9):
        if gcd(u, 9) != 1:
            continue
        for v in range(9):
            if v % 3 == 0 and (u + v) % 9 == 1:
                need(all((u * leaf + v) % 3 == leaf % 3 for leaf in LEAVES), 'residual common affine maps fix short/long roots')
                affine.append([u, v])
    need(affine == [[1, 0], [4, 6], [7, 3]], 'all residual affine classes modulo9')
    period = lcm(*(m for m, residue in family))
    pure_product = period // 9
    witness = next(1 + k * pure_product for k in range(9) if (1 + k * pure_product) % 9 == 2)
    need(all(witness % m != residue for m, residue in family), 'one common uncovered integer for the actual finite family')
    best = max(all_results, key=lambda row: F(row['all_symmetric_maximum']))
    need(F(all_results[0]['fixed_law_minimum_union']) == F(501984, 5311735), 'exact minimum over distinguished primes and phases')
    return dict(schema='common-core-phase-obstruction-result-v1', checks=COUNT,
                scope='One fixed25-original noncovering family. All common reference phases, all7 distinguished primes, and all five-leaf probability laws fail only the stated23-slot complete-remaining-inventory lower certificate. No covering counterexample or impossibility of another source method.',
                actual_family=family, common_period=period, uncovered_integer=witness,
                residual_affine_mod9=affine, no_actual_zero_mass=str(P0), rows=all_results,
                global_maximum_repaired_certificate=best['all_symmetric_maximum'],
                global_maximum_decimal=best['all_symmetric_maximum_decimal'],
                global_maximum_distinguished=best['distinguished'], global_maximum_symmetric_a=best['maximizing_a'])


def main():
    path = Path(__file__)
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificate', type=Path, default=path.with_name(path.stem + '_certificate.json'))
    parser.add_argument('--result', type=Path, default=path.with_suffix('.json'))
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = calculate(json.loads(args.certificate.read_text()))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        need(json.loads(args.result.read_text()) == result, 'retained result exact replay')
    print(json.dumps({k: result[k] for k in ('checks', 'common_period', 'uncovered_integer',
                                           'global_maximum_repaired_certificate', 'global_maximum_decimal')}, indent=2))


if __name__ == '__main__':
    main()
