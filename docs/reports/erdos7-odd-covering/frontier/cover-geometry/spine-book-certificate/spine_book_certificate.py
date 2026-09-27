#!/usr/bin/env python3
"""Exact arithmetic for books of K4 pages with common spine {3,5}.

Reuses the pinned ordinary anchor geometry and helper of Chapter 30.
Checks 29 page-fee rows, one analytic tail constant, a four-prime source
prefix, and 13 finite-to-infinite split-core branches at all 32 vertices.
The conditional-probability proof, source comparison, monotone coupling,
joint-spine marginal bound and branch exhaustion are mathematical inputs.
No source verifier is imported; no geometry or Lean checker is executed.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

GEOMETRY_SHA256 = '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'
HELPER_SHA256 = '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4'
SCHEDULE = (
    (13, 2, 1), (17, 3, 1), (19, 3, 2), (23, 4, 2),
    (29, 4, 3), (31, 4, 3), (37, 5, 3), (41, 5, 3),
    (43, 5, 4), (47, 6, 4), (53, 7, 4), (59, 7, 4),
    (61, 7, 5), (67, 8, 5), (71, 8, 5), (73, 8, 5),
    (79, 8, 5), (83, 9, 6), (89, 9, 6), (97, 10, 6),
    (101, 10, 6), (103, 10, 6), (107, 10, 7), (109, 10, 7),
    (113, 11, 7), (127, 11, 7), (131, 11, 8), (137, 12, 8),
    (139, 12, 8),
)
# (scope, lower proxy u, lower proxy v, definitely retired fee indices).
BRANCHES = (
    ('u >= 31, v > u', 31, 37, ()),
    ('u = 13, v >= 23', 13, 23, (13,)),
    ('u = 13, v = 17', 13, 17, (13, 17)),
    ('u = 13, v = 19', 13, 19, (13, 19)),
    ('u = 17, v >= 23', 17, 23, (17,)),
    ('u = 17, v = 19', 17, 19, (17, 19)),
    ('u = 19, v >= 31', 19, 31, (19,)),
    ('u = 19, v = 23', 19, 23, (19, 23)),
    ('u = 19, v = 29', 19, 29, (19, 29)),
    ('u = 23, v >= 37', 23, 37, (23,)),
    ('u = 23, v = 29', 23, 29, (23, 29)),
    ('u = 23, v = 31', 23, 31, (23, 31)),
    ('u = 29, v >= 31', 29, 31, (29,)),
)


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def page_fee(p, r, t3, t5):
    x, y = Q(1, p - 2), Q(1, r - 2)
    T = (t3 + 1) * (t5 + 1) - 1
    zq, zr = 1 - T * x, 1 - T * y
    z = zq * zr - (T + 1) * x * y
    load = x * zr + y * zq + x * y
    rem = Q(15, 8) * (Q(1, 3 ** (t3 + 1)) + Q(1, 5 ** (t5 + 1))
                      - Q(1, 3 ** (t3 + 1) * 5 ** (t5 + 1)))
    assert min(zq, zr, z, load, rem) > 0
    assert z == 1 - T * (x + y) + (T * T - T - 1) * x * y
    assert load == x + y + (1 - 2 * T) * x * y
    return {'minimum_private_prime': p, 'comparison_partner': r,
            'cutoffs': [t3, t5], 'shallow_exponent_pair_count': T,
            'singleton_residuals': [str(zq), str(zr)], 'joint_residual': str(z),
            'conditional_load_numerator': str(load), 'spine_tail_mass': str(rem),
            'fee': str(load * rem / z)}


def multiplier_prefixes(primes, thresholds):
    table, mean, out = {1: Q(1)}, Q(1), []
    for p, t in zip(primes, thresholds):
        assert 1 <= t < p - 1
        cap = Q(p - 1, p - 1 - t)
        assert 1 < cap < p and cap * (1 - Q(1, p - 1)) >= 1
        out.append((dict(table), mean))
        nxt = defaultdict(Q)
        for m, weight in table.items():
            for new in range(m, 32, m):
                n = new // m
                prob = 1 - cap / p if n == 1 else cap * Q(p - 1, p ** n)
                assert prob >= 0
                nxt[new] += weight * prob
        table = nxt
        mean *= 1 + cap / Q(p - 1)
    return out


def source_mass(helper, envelopes, primes, thresholds):
    distributions = multiplier_prefixes(primes, thresholds)
    rows = []
    for node, reserve, (a0, whole, values) in envelopes:
        losses = []
        for p, t, (table, mean) in zip(primes, thresholds, distributions):
            small = {m: w for m, w in table.items() if m < t}
            below = sum(small.values(), Q(0))
            below_first = sum((m * w for m, w in small.items()), Q(0))
            assert 0 <= below <= 1 and 0 <= below_first <= mean
            numerator = (sum((m * w * values[Q(t, m)] for m, w in small.items()), Q(0))
                         + (mean - below_first) * whole - t * (1 - below) * a0)
            cost = numerator / (p - 1 - t)
            rounded = helper.ceil_decimal(cost)
            assert 0 <= cost <= rounded < cost + Q(1, 10 ** 10)
            losses.append(rounded)
        live = (reserve - sum(losses, Q(0))) / 135
        assert live > 0
        rows.append({'node': list(node), 'reserve_cell_units': str(reserve),
                     'upward_rounded_losses_cell_units': list(map(str, losses)),
                     'live_mass_lower_bound': str(live)})
    worst = min(rows, key=lambda r: Q(r['live_mass_lower_bound']))
    return {'later_prime_proxies': list(primes), 'thresholds': list(thresholds),
            'vertex_count': len(rows), 'mass_lower_bound': worst['live_mass_lower_bound'],
            'worst_node': worst['node'], 'rows': rows}


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geometry', type=Path, required=True)
    parser.add_argument('--helper', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    geometry_raw, helper_raw = args.geometry.read_bytes(), args.helper.read_bytes()
    assert hashlib.sha256(geometry_raw).hexdigest() == GEOMETRY_SHA256
    assert hashlib.sha256(helper_raw).hexdigest() == HELPER_SHA256
    geometry = json.loads(geometry_raw)
    assert geometry['schema'] == 'six-prime-prefix-geometry-input-v1'
    assert len(geometry['batches']) == 72
    spec = importlib.util.spec_from_file_location('spine_book_ordinary_helper', args.helper)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)

    fee_rows = []
    assert [p for p, _, _ in SCHEDULE] == [p for p in range(13, 140) if prime(p)]
    assert not any(prime(p) for p in range(140, 149))
    for p, t3, t5 in SCHEDULE:
        r = next(n for n in range(p + 1, 2 * p + 2) if prime(n))
        fee_rows.append(page_fee(p, r, t3, t5))
    fees = {r['minimum_private_prime']: Q(r['fee']) for r in fee_rows}
    finite_sum = sum(fees.values(), Q(0))
    finite_bound, tail_bound, total_bound = Q(197, 2000), Q(65, 11664), Q(21, 200)
    assert finite_sum < finite_bound
    n = 6
    assert tail_bound == (Q(45, 2 * n) + Q(45, 4 * n * n)) * Q(1, 3 ** n)
    assert finite_bound + tail_bound < total_bound

    nodes = sorted((a, b, c, -1, j, 0, 0, 0, -1)
                   for a in (1, 2) for b in (2, 4) for c in (a, 3 - a) for j in range(1, 5))
    assert len(nodes) == len(set(nodes)) == 32
    envelopes = []
    for node in nodes:
        a, b, c, _, j, *_ = node
        gamma = 3 * (a == 1) + (b % 3 == a % 3)
        reserve = Q(135, 4) + gamma + (9 - gamma) * (Q(c == a, 5) + Q(j == a, 20))
        envelopes.append((node, reserve, helper.envelope(geometry['batches'], a, b, c, j)))
    assert set(helper.BATCHES) == set(geometry['batches'])
    assert len(helper.BATCHES) == 72 and helper.QUERIES == 51840
    anchor_reserve = min(reserve / 135 for _, reserve, _ in envelopes)
    assert anchor_reserve == Q(1, 4) > total_bound
    four_core = source_mass(helper, envelopes, (7, 11), (2, 4))
    assert Q(four_core['mass_lower_bound']) == Q(697794991, 5400000000) > total_bound

    branches = []
    for scope, u, v, discount_indices in BRANCHES:
        result = source_mass(helper, envelopes, (7, 11, u, v), (2, 4, 4, 8))
        discount = sum((fees[p] for p in discount_indices), Q(0))
        margin = Q(result['mass_lower_bound']) + discount - total_bound
        assert margin > 0
        branches.append({'scope': scope, 'source': result,
                         'retired_fee_indices': list(discount_indices),
                         'fee_discount': str(discount), 'strict_margin': str(margin)})
    assert len(branches) == 13
    worst = min(branches, key=lambda r: Q(r['strict_margin']))
    out = {'schema': 'spine-book-certificate-v1',
           'scope': 'Exact rational page fees, source-prefix bounds and 13 range witnesses. Ordinary mathematical proof, not Lean; inherited geometry and infinite-height source comparison are separate premises.',
           'source': {key: geometry[key] for key in ('source_doi', 'source_archive_url', 'source_archive_sha256', 'source_verifier_sha256', 'source_geometry_cpp_sha256')},
           'geometry_input_sha256': GEOMETRY_SHA256, 'ordinary_helper_sha256': HELPER_SHA256,
           'source_verifier_imported': False, 'geometry_reexecuted': False,
           'fee_rows': fee_rows, 'finite_fee_sum': str(finite_sum),
           'finite_fee_sum_strict_bound': str(finite_bound),
           'analytic_tail_bound': str(tail_bound),
           'combined_intermediate_bound': str(finite_bound + tail_bound),
           'strict_total_fee_bound': str(total_bound),
           'anchor_only_reserve': str(anchor_reserve), 'four_prime_core': four_core,
           'four_prime_margin': str(Q(four_core['mass_lower_bound']) - total_bound),
           'split_core_branches': branches,
           'minimum_split_margin': worst['strict_margin'], 'minimum_split_scope': worst['scope'],
           'unique_geometry_batches': len(helper.BATCHES), 'integer_query_reads': helper.QUERIES}
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(f'PASS: {len(fee_rows)} page fees, analytic tail < {total_bound}, 32 source vertices per core, 13 split branches.')
    print(f'Minimum split margin: {worst["strict_margin"]}; {worst["scope"]}.')


if __name__ == '__main__':
    main()
