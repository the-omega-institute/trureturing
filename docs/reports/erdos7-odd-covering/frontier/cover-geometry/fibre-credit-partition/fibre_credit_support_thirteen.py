#!/usr/bin/env python3
"""Exact support-Shearer source bound and thirteen-prime height-one continuation.

Checks every actual beta-triangle vertex, the low-dimensional strict-region
premise and the complete-tail scalar query. This is ordinary mathematical
verification, not a new Lean proof or an unrestricted odd-covering result.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import prod
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate():
    qs = (5, 7, 11, 13, 17, 19, 23, 29, 31)
    n, full = len(qs), (1 << len(qs)) - 1
    supports = [d for d in range(full + 1) if d.bit_count() >= 2]
    caps = {d: 2 * prod(F(1, qs[i] - 3) for i in range(n) if d >> i & 1)
            for d in supports}
    residuals = [F(1)] * (full + 1)
    for mask in range(1, full + 1):
        bit = mask & -mask
        residuals[mask] = residuals[mask ^ bit] - sum(
            (caps[d] * residuals[mask ^ d] for d in supports
             if d & bit and d & mask == d), F(0))
    minima = [min(z for mask, z in enumerate(residuals) if mask.bit_count() == k)
              for k in range(n + 1)]
    need(minima[:7] == [F(1), F(1), F(3, 4), F(17, 32), F(21, 64),
                        F(789, 4480), F(3251, 71680)],
         'all low-dimensional residual minima, including the strict six-coordinate premise')
    need(sum(mask.bit_count() <= 6 for mask in range(full + 1)) == 466,
         'complete low-dimensional subset inventory')
    # The new two-external-coordinate bridge excludes every possible bad seven-set.
    possible_bad = [mask for mask in range(full + 1)
                    if mask.bit_count() == 7 and residuals[mask] <= 0]
    need(len(possible_bad) == 5, 'all potentially nonpositive seven-coordinate residuals')
    lower_products = [prod(F(1, qs[i] - 2) for i in range(n) if mask >> i & 1)
                      for mask in range(full + 1)]
    upper_products = [prod(F(1, qs[i] - 3) for i in range(n) if mask >> i & 1)
                      for mask in range(full + 1)]
    bad_rows = []
    for mask in possible_bad:
        outside = [qs[i] for i in range(n) if not mask >> i & 1]
        inside_subsets = [d for d in range(1, full + 1) if d & mask == d]
        S1 = sum((lower_products[d] * residuals[mask ^ d] for d in inside_subsets), F(0))
        S2 = sum(((2 ** d.bit_count() - 2) * upper_products[d] for d in inside_subsets), F(0))
        margin = (sum(outside) - 5) * S1 - 4 * S2
        pair_cap = 2 * upper_products[full ^ mask]
        need(S1 > 0 and S2 >= 0 and pair_cap < 1 and margin > 20,
             'each bad seven-set forces a strictly negative nine-coordinate top')
        bad_rows.append(dict(inside=[qs[i] for i in range(n) if mask >> i & 1],
                             outside=outside, S1_lower=S1, S2_upper=S2,
                             maximal_residual=residuals[mask], pair_cap_upper=pair_cap,
                             sign_margin=margin))

    # Associated Stirling numbers: partitions into blocks of size at least two.
    partitions = [[0] * 5 for _ in range(n + 1)]
    partitions[0][0] = 1
    for size in range(1, n + 1):
        for k in range(1, 5):
            partitions[size][k] = k * partitions[size - 1][k]
            if size >= 2:
                partitions[size][k] += (size - 1) * partitions[size - 2][k - 1]
    need(partitions[9][1:] == [1, 246, 1918, 1260], 'complete nine-coordinate partition counts')
    terms = [(full ^ mask, [(k, partitions[mask.bit_count()][k])
                           for k in range(1, 5) if partitions[mask.bit_count()][k]])
             for mask in supports]
    denominator = 2 * prod(q - 2 for q in qs)
    numerators, minimizers = [], []
    minimum = None
    # 0: neither star budget used, 1: root1 saturated, 2: root2 saturated.
    for beta in product(range(3), repeat=n):
        left, right = [1] * (full + 1), [1] * (full + 1)
        for mask in range(1, full + 1):
            bit = mask & -mask
            i, rest = bit.bit_length() - 1, mask ^ bit
            left[mask] = left[rest] * (qs[i] - 2 - (beta[i] == 1))
            right[mask] = right[rest] * (qs[i] - 2 - (beta[i] == 2))
        numerator = left[full] + right[full]
        for rest, counts in terms:
            for k, count in counts:
                values = [(1 << j) * left[rest] + (1 << (k - j)) * right[rest]
                          for j in range(k + 1)]
                numerator += count * min(values) if k % 2 == 0 else -count * max(values)
        numerators.append(numerator)
        if minimum is None or numerator < minimum:
            minimum, minimizers = numerator, [beta]
        elif numerator == minimum:
            minimizers.append(beta)
    alpha = F(minimum, denominator)
    need(len(numerators) == 19683, 'every actual beta triangle vertex, without saturation')
    need(alpha == F(213341593, 2490621210), 'uniform actual-source mass lower bound')
    need(minimizers == [(1, 2, 2, 2, 2, 2, 2, 2, 2), (2, 1, 1, 1, 1, 1, 1, 1, 1)],
         'the only minimizing triangle vertices')

    # The complete first moment plus small exact product atoms determine the hinge.
    small, mean = {1: F(1, 2), 2: F(1, 2)}, F(3, 2)
    for q in qs:
        c = F(q - 1, q - 2)
        atoms = {1: 1 - c / q}
        atoms.update({j: c * F(q - 1, q ** j) for j in range(2, 9)})
        following = {}
        for a, b in product(small, atoms):
            if a * b <= 8:
                following[a * b] = following.get(a * b, F(0)) + small[a] * atoms[b]
        small = following
        mean *= 1 + F(1, q - 2)
    hinge = mean - 8 + sum(((8 - j) * p for j, p in small.items() if j < 8), F(0))
    tail_ge = 1 - sum((p for j, p in small.items() if j < 8), F(0))
    tail_gt = 1 - sum((p for j, p in small.items() if j <= 8), F(0))
    need(tail_gt < alpha < tail_ge, 'unique real-threshold minimum at eight')
    need(hinge == F(3012006036358254380805213652237644965724836482183382598542856635170684840645349,
                   6619317806701440471602539645918396385988189732561371318277541508887884652968750),
         'complete-tail scalar hinge at eight')
    outside = (37, 41, 43)
    Q = prod(F(q - 1, q - 2) for q in outside) - 1
    s = sum((F(1, q - 2) for q in outside), F(0))
    A8 = 1 + s - 8 * Q
    reserve = A8 * alpha - Q * hinge
    cap = F(3, 2) * prod(F(q - 1, q - 2) for q in qs + outside)
    density = reserve / cap
    need((Q, s, A8, cap) == (F(43, 533), F(4399, 55965),
                             F(24244, 55965), F(1048576, 262769)),
         'same-source pure-conditioned continuation constants')
    need(density > F(1, 11000), 'thirteen-prime actual Haar density lower bound')
    no3 = qs + outside + (47,)
    no3_cap = prod(F(q - 1, q - 2) for q in no3)
    no3_reserve = 2 + sum((F(1, q - 2) for q in no3), F(0)) - no3_cap
    no3_density = no3_reserve / no3_cap
    need(no3_density == F(987063241, 7428112384) and no3_density > F(1, 11000),
         'separate no-three branch from the empty-core pure-product theorem')
    return dict(scope=__doc__, nonternary_core_primes=qs,
                low_dimension_residual_count=466,
                maximal_cap_residual_minima_by_size=minima,
                maximal_cap_full_value=residuals[full], bad_seven_rows=bad_rows,
                partition_counts=partitions,
                actual_triangle_vertex_count=len(numerators),
                vertex_order='lexicographic product(range(3), repeat=9), 0 unused, 1 root1, 2 root2',
                vertex_numerator_sha256=sha256(json.dumps(numerators, separators=(',', ':')).encode()).hexdigest(),
                common_denominator=denominator, minimum_numerator=minimum,
                minimizing_vertices=minimizers, actual_source_mass_lower=alpha,
                multiplier_full_mean=mean, multiplier_small_atoms=small,
                multiplier_tail_ge8=tail_ge, multiplier_tail_gt8=tail_gt,
                query_threshold=8, complete_hinge_upper=hinge,
                query_sum_upper=7 + hinge / alpha, outside_primes=outside,
                continuation_Q=Q, continuation_s=s, continuation_A8=A8,
                unnormalized_reserve=reserve, full_haar_density_cap=cap,
                thirteen_prime_haar_lower=density, simple_haar_lower=F(1, 11000),
                no_three_primes=no3, no_three_haar_lower=no3_density,
                boundary='Every original has v3(m)<=1 and at most thirteen actual support primes. All other exponents are arbitrary finite. Low-dimensional positivity alone is insufficient here. The completed caps satisfy t_D <= c_D <= 2t_D, and the five checked two-external-coordinate inequalities exclude every nonpositive seven-set under a positive top. No unrestricted noncoverage claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(encode(calculate()), sort_keys=True, indent=2) + '\n'
    if args.output is None:
        expected = Path(__file__).resolve().with_suffix('.json')
        need(json.loads(expected.read_text()) == json.loads(result), 'retained result agrees with exact replay')
        print(result, end='')
    else:
        args.output.write_text(result)


if __name__ == '__main__':
    main()
