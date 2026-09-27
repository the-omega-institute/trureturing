#!/usr/bin/env python3
"""Exact full outside-carrier checks of weighted merged phase suppliers.

Every row retains its distinct original numerical modulus and CRT residue.
Reads no files, writes only --output, and performs no directory traversal.
These finite controls supplement the ordinary proofs; they are not Lean.
"""
import argparse
from fractions import Fraction as Q
from math import lcm, prod
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def original(d, b, retained, outside):
    modulus = d * b
    residue = outside + b * (((retained - outside) * pow(b, -1, d)) % d) if d > 1 else outside
    residue %= modulus
    require(residue % d == retained % d and residue % b == outside % b,
            'original CRT reconstruction failed')
    return (d, b, retained % d, outside % b, modulus, residue)


def omega(d):
    out = Q(1)
    remaining = d
    for p in (3, 5, 7):
        height = 0
        while remaining % p == 0:
            height += 1
            remaining //= p
        if height:
            out *= Q(p - 1, (p - 2) * p ** height)
    require(remaining == 1, 'retained modulus not B-smooth')
    return out


def evaluate(rows):
    require(len({r[4] for r in rows}) == len(rows), 'original numerical collision')
    require(all(r[4] > 1 and r[4] % 2 for r in rows), 'invalid original modulus')
    outside_period = lcm(*(r[1] for r in rows))
    ds = sorted({r[0] for r in rows if r[0] > 1})
    excess_totals = {d: 0 for d in ds}
    survivors = 0
    collision_points = 0
    for y in range(outside_period):
        if any(d == 1 and y % b == a for d, b, _, a, _, _ in rows):
            continue
        survivors += 1
        phases = {d: set() for d in ds}
        for d, b, r, a, _, _ in rows:
            if d > 1 and y % b == a:
                phases[d].add(r)
        excess = {d: max(0, len(phases[d]) - 1) for d in ds}
        collision_points += any(excess.values())
        for d, n in excess.items():
            excess_totals[d] += n
    require(survivors > 0, 'empty actual outside avoidance event')
    h = sum((Q(excess_totals[d], survivors * d) for d in ds), Q(0))
    s = sum((omega(d) * Q(excess_totals[d], survivors) for d in ds), Q(0))
    return {
        'original_labels': len(rows), 'outside_period': outside_period,
        'outside_survivors': survivors, 'collision_points': collision_points,
        'source_mass': Q(survivors, outside_period), 'H': h, 'S': s,
        'rows': [{'retained_modulus': d, 'outside_modulus': b,
                  'retained_residue': r, 'outside_residue': a,
                  'original_modulus': m, 'original_residue': z}
                 for d, b, r, a, m, z in rows]
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    depth_rows = [original(3 ** e, b, phase, 0)
                  for e in range(1, 121)
                  for b, phase in ((143, 0), (1573, 1))]
    depth = evaluate(depth_rows)
    retained_h = (1 - Q(1, 3 ** 120)) / 2
    require(depth['outside_period'] == 1573 and depth['collision_points'] == 1,
            'depth source collision inventory changed')
    require(depth['H'] == retained_h / 1573 and depth['S'] == 2 * depth['H'],
            'depth source exact expectation differs')
    require(retained_h / 120 < Q(5, 48) and 2 * retained_h / 120 < Q(1, 3),
            'weighted row supplier fails')
    depth.update({'unweighted_row_envelope': Q(120, 120),
                  'weighted_H_envelope': retained_h / 120,
                  'weighted_S_envelope': 2 * retained_h / 120,
                  'outside_support_sets': 1, 'retained_numerical_depths': 120})

    denominator = evaluate([original(1, 11, 0, 0), original(3, 1, 0, 0),
                            original(3, 11, 1, 1)])
    require(denominator['source_mass'] == Q(10, 11), 'incorrect conditioning source')
    require(denominator['H'] == Q(1, 30), 'incorrect conditioned excess')
    require(denominator['H'] > Q(1, 33), 'missing-denominator error not detected')
    denominator['unnormalized_H_envelope'] = Q(1, 33)

    primes = (13, 17)
    shared = evaluate([original(3, multiplier * p, phase, 0)
                       for p in primes for multiplier, phase in ((11, 0), (121, 1))])
    exact_h = (1 - prod(Q(p - 1, p) for p in primes)) / 363
    row_h = sum((Q(1, p - 1) for p in primes), Q(0)) / 30
    require(shared['H'] == exact_h and shared['S'] == 2 * exact_h,
            'shared-support exact phase union differs')
    require(shared['H'] < Q(1, 363) < row_h,
            'single coordinate envelope did not beat separate support rows')
    shared.update({'H_row_envelope': row_h, 'H_shared_envelope': Q(1, 363),
                   'outside_support_sets': len(primes)})

    prime_prefix = (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                    53, 59, 61, 67, 71, 73, 79, 83, 89, 97)
    tail_denominators = (2520, 2580, 2700, 2760, 2880, 3060, 3120, 3300)
    square_upper = sum((Q(1, (p - 2) ** 2) for p in prime_prefix), Q(0))
    square_upper += sum((Q(1, n) for n in tail_denominators), Q(0))
    require(square_upper < Q(1, 24), 'existing infinite-tail upper bound changed')
    require(prod(Q(p, p - 1) for p in (3, 5, 7)) - 1 == Q(19, 16),
            'complete Haar retained weight sum differs')
    require(prod(1 + Q(1, p - 2) for p in (3, 5, 7)) - 1 == Q(11, 5),
            'complete survivor retained weight sum differs')
    degree_cases = []
    for k in range(8):
        for k0 in range(49):
            denom = 1 - Q(k0, 2) * square_upper
            if 57 * k + 5 * k0 <= 240:
                upper = Q(19 * k, 32) * square_upper / denom
                require(denom > 0 and upper < Q(5, 48), 'H degree inequality fails')
                degree_cases.append({'kind': 'H', 'k': k, 'k0': k0, 'upper': upper})
            if 33 * k + 5 * k0 <= 240:
                upper = Q(11 * k, 10) * square_upper / denom
                require(denom > 0 and upper < Q(1, 3), 'S degree inequality fails')
                degree_cases.append({'kind': 'S', 'k': k, 'k0': k0, 'upper': upper})
    result = {'status': 'PASS', 'scope': 'ordinary proofs plus finite exact controls, not Lean',
              'depth_family': depth, 'conditioning_counterexample': denominator,
              'shared_envelope_family': shared, 'degree_cases': degree_cases,
              'square_sum_upper': square_upper}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({'status': 'PASS', 'original_labels': sum(x['original_labels'] for x in (depth, denominator, shared)),
                      'outside_points': sum(x['outside_period'] for x in (depth, denominator, shared)),
                      'degree_cases': len(degree_cases), 'positive_collision_families': 3,
                      'shared_H': str(exact_h)}))


if __name__ == '__main__':
    main()
