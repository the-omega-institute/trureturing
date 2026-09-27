#!/usr/bin/env python3
"""Exact certificate for eight-prime cores containing 3, 5, 7 and 11.

All other actual graph blocks have at most seven vertices. This bounded
calculation checks eleven six-child CK rows and three ordinary source
families on the inherited 32 anchor vertices. Mathematical transfer and
graph premises are stated in Chapter 38. No source verifier, new geometry,
or Lean checker is run. Python 3.10+; all paths are explicit arguments.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from math import isqrt, prod
from pathlib import Path
import sys


GEOMETRY_SHA256 = '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'
HELPER_SHA256 = '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4'
SOURCE_HELPER_SHA256 = '601c9c94018ab960abe63a126c1cf0d96b84b6b335ef5630c84adfb113db44de'
THRESHOLDS = (2, 4, 4, 8, 8, 12)
SCHEDULE = ((13, 5), (17, 8), (19, 10), (23, 13), (29, 16),
            (31, 19), (37, 23), (41, 26), (43, 28), (47, 30), (53, 30))
SOURCE_ROWS = (
    ('case_b', (3, 5, 7, 11, 13, 17, 23, 29), 19,
     Q(290064917, 30000000000), Q(165, 8)),
    ('case_c', (3, 5, 7, 11, 13, 19, 23, 29), 17,
     Q(12314552263, 675000000000), Q(297, 16)),
    ('case_d', (3, 5, 7, 11, 17, 19, 23, 29), 13,
     Q(13939935091, 337500000000), Q(33, 2)),
)


def import_file(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def ck(children, t):
    assert len(children) == 6 and len(set(children)) == 6
    b = [Q(1, q - 3) for q in children]
    products = [Q(1)] * 64
    for mask in range(1, 64):
        bit = mask & -mask
        products[mask] = products[mask ^ bit] * b[bit.bit_length() - 1]
    v = [Q(0)] + [products[mask] * (t if mask.bit_count() == 1 else t + 1)
                   for mask in range(1, 64)]
    z = [Q(1)] + [Q(0)] * 63
    for mask in range(1, 64):
        bit = mask & -mask
        value, support = z[mask ^ bit], mask
        while support:
            if support & bit:
                value -= v[support] * z[mask ^ support]
            support = (support - 1) & mask
        z[mask] = value
    assert min(z) > 0
    L = sum((products[s] * z[63 ^ s] for s in range(1, 64)), Q(0))
    assert L > 0
    return {'proxy_children': list(children), 'cutoff': t,
            'coordinate_caps': list(map(str, b)), 'residuals': list(map(str, z)),
            'minimum_residual': str(min(z)), 'L': str(L),
            'K3': str(L / (2 * 3 ** t * z[-1]))}


def parent_comparisons(proxies, caps, rows):
    fee_coefficients = tuple(alpha * (Q(1) if p == 3 else Q(3, 10)
                                     if p == 5 else Q(2, p - 1))
                             for p, alpha in zip(proxies, caps))
    assert max(fee_coefficients) <= 1
    nonroot, count = [], 0
    for row in rows:
        t = row['cutoff']
        for p, alpha in zip(proxies, caps):
            ratio = alpha * Q(2 * 3 ** t, p ** t * (p - 1))
            assert ratio <= 1
            if p != 3:
                nonroot.append(ratio)
            count += 1
    return {'finite_parent_comparison_count': count,
            'largest_nonroot_finite_parent_ratio': str(max(nonroot)),
            'large_minimum_fee_coefficients': list(map(str, fee_coefficients))}


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geometry', type=Path, required=True)
    parser.add_argument('--helper', type=Path, required=True)
    parser.add_argument('--source-helper', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    geometry_raw = args.geometry.read_bytes()
    assert sha256(geometry_raw).hexdigest() == GEOMETRY_SHA256
    assert sha256(args.helper.read_bytes()).hexdigest() == HELPER_SHA256
    assert sha256(args.source_helper.read_bytes()).hexdigest() == SOURCE_HELPER_SHA256
    geometry = json.loads(geometry_raw)
    assert geometry['schema'] == 'six-prime-prefix-geometry-input-v1'
    helper = import_file('variable_core_geometry_helper', args.helper)
    source_helper = import_file('variable_core_source_helper', args.source_helper)
    nodes = sorted((a, b, c, -1, j, 0, 0, 0, -1)
                   for a in (1, 2) for b in (2, 4) for c in (a, 3 - a)
                   for j in range(1, 5))
    assert len(nodes) == len(set(nodes)) == 32
    envelopes = []
    for node in nodes:
        a, b, c, _, j, *_ = node
        gamma = 3 * (a == 1) + (b % 3 == a % 3)
        reserve = Q(135, 4) + gamma + (9 - gamma) * (Q(c == a, 5) + Q(j == a, 20))
        envelopes.append((node, reserve, helper.envelope(geometry['batches'], a, b, c, j)))
    assert set(helper.BATCHES) == set(geometry['batches'])
    assert len(helper.BATCHES) == 72 and helper.QUERIES == 51840

    assert [p for p, _ in SCHEDULE] == [p for p in range(13, 54) if prime(p)]
    rows = [ck(tuple(q for q in range(p, 200) if prime(q))[:6], t) for p, t in SCHEDULE]
    assert Q(rows[0]['K3']) == Q(499487, 159722442)
    tail = Q(1, 2 ** 28)
    losses = {s: tail + sum((Q(row['K3']) for row in rows
                            if row['proxy_children'][0] >= s), Q(0))
              for s in (13, 17, 19, 23)}
    simple_losses = {13: Q(17, 5000), 17: Q(13, 50000),
                     19: Q(7, 400000), 23: Q(27, 50000000)}
    assert all(losses[s] < simple_losses[s] for s in losses)
    simple = Q(1, 2200000)
    haar_seed = Q(1, 1002375)
    case_a_proxies = (3, 5, 7, 11, 13, 17, 19, 29)
    case_a_rows = [row for row in rows if row['proxy_children'][0] >= 23]
    assert losses[23] < Q(27, 50000000)
    assert haar_seed - Q(27, 50000000) > simple
    cases = {'case_a': {
        'scope': 'Core {3,5,7,11,13,17,19,v}, v>=29.',
        'measure': 'Haar restriction to original core survivors, using the attributed eight-prime density theorem.',
        'core_lower_proxies': list(case_a_proxies),
        'coordinate_caps': ['1'] * 8, 'joint_density_cap': '1',
        'mass_lower_bound': str(haar_seed), 'minimum_outside_prime': 23,
        'deletion_upper_bound': str(losses[23]),
        'weighted_mass_lower_bound': str(haar_seed - losses[23]),
        'extendible_core_haar_lower_bound': str(haar_seed - losses[23]),
        **parent_comparisons(case_a_proxies, (Q(1),) * 8, case_a_rows),
    }}
    scopes = {
        'case_b': 'Core {3,5,7,11,13,17,u,v}, 23<=u<v.',
        'case_c': 'Core contains {3,5,7,11,13}, omits17; remaining ordered primes>=19,23,29.',
        'case_d': 'Core contains {3,5,7,11}, omits13; remaining ordered primes>=17,19,23,29.',
    }
    for key, proxies, minimum, expected_mass, expected_D in SOURCE_ROWS:
        source = source_helper.source_mass(helper, envelopes, proxies[2:], THRESHOLDS)
        mass = Q(source['mass_lower_bound'])
        assert mass == expected_mass
        caps = (Q(1), Q(1)) + tuple(Q(p - 1, p - 1 - t)
                                    for p, t in zip(proxies[2:], THRESHOLDS))
        D = prod(caps)
        assert D == expected_D
        weighted = mass - losses[minimum]
        assert weighted / D > simple
        assert (mass - simple_losses[minimum]) / D > simple
        applicable = [row for row in rows if row['proxy_children'][0] >= minimum]
        cases[key] = {
            'scope': scopes[key], 'core_lower_proxies': list(proxies),
            'source': source, 'coordinate_caps': list(map(str, caps)),
            'joint_density_cap': str(D), 'minimum_outside_prime': minimum,
            'deletion_upper_bound': str(losses[minimum]),
            'weighted_mass_lower_bound': str(weighted),
            'extendible_core_haar_lower_bound': str(weighted / D),
            **parent_comparisons(proxies, caps, applicable),
        }
    assert losses[19] < Q(7, 400000)
    assert losses[17] < Q(13, 50000)
    assert losses[13] < Q(17, 5000)
    assert Q(1, 1200000) > simple
    out = {
        'schema': 'variable-eight-core-certificate-v1',
        'scope': 'An actual eight-vertex core containing {3,5,7,11}; every other actual graph block has at most seven vertices. Arbitrary original finite heights and residues; no Lean claim.',
        'source': {key: geometry[key] for key in ('source_doi', 'source_archive_url', 'source_archive_sha256', 'source_verifier_sha256', 'source_geometry_cpp_sha256')},
        'geometry_input_sha256': GEOMETRY_SHA256,
        'ordinary_helper_sha256': HELPER_SHA256,
        'ordinary_source_helper_sha256': SOURCE_HELPER_SHA256,
        'source_verifier_imported': False, 'geometry_reexecuted': False,
        'attachment_rows': rows, 'positive_coordinate_residual_count': 64 * len(rows),
        'large_minimum_tail': str(tail),
        'distinct_minimum_deletion_bounds': {str(k): str(v) for k, v in losses.items()},
        'simple_strict_deletion_bounds': {str(k): str(v) for k, v in simple_losses.items()},
        'baseline_first_eight_core': {
            'premise': 'Chapter 35, inherited rather than reverified here.',
            'strict_extendible_core_haar_bound': '1/1200000',
        },
        'cases': cases,
        'ordinary_source_vertex_count': 96,
        'ordinary_source_stage_loss_count': 576,
        'finite_parent_comparison_count': sum(row['finite_parent_comparison_count'] for row in cases.values()),
        'uniform_strict_extendible_core_haar_lower_bound': str(simple),
        'unique_geometry_batches': len(helper.BATCHES),
        'integer_query_reads': helper.QUERIES,
    }
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print('PASS: 11 CK rows, 704 positive residuals, 96 source vertices, and four shared attachment budgets.')
    print('Scope: actual eight-prime core containing 3,5,7,11; all other blocks at most seven vertices.')
    print('Extendible core Haar density > 1/2200000')


if __name__ == '__main__':
    main()
