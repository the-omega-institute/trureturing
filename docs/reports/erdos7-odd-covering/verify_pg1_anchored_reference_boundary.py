#!/usr/bin/env python3
"""Exact all-real-reference boundary for the fixed old PG1 AF1 functional.

Requires NumPy and the adjacent verify_point_geometry.py. Reuses its exact
group oracle; no depth-box square calculation or search is performed.
Default: compare the complete recomputation with the stored certificate.
Use --write explicitly to write a certificate. --source-directory selects
the directory containing the canonical PG1 and original9 certificates and
the group oracle (default: this script's directory).
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm, prod
from pathlib import Path
import argparse
import importlib.util
import json

import numpy as np

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-anchored-reference-boundary-v1'
SOURCES = ('certificates/mod3_conditioned_geometry_certificate.json',
           'certificates/original9_conditioned_geometry_certificate.json')
SCOPE = ('Exact minimum over all real references of the fixed AF1 plus fixed '
         'old grouped-deletion functional with the independent interval '
         'Q in [q0,1]. Not a true-moment lower bound, not an all-low-test '
         'upper bound, and not a boundary for Rcap, a new survival bound, '
         'or a whole-cost criterion retaining other costs jointly with Q.')


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def load_oracle(directory):
    spec = importlib.util.spec_from_file_location(
        'pg1_boundary_point_geometry', directory / 'verify_point_geometry.py')
    require(spec is not None and spec.loader is not None, 'group oracle module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def evaluate(directory, expected_hashes=None):
    raw = {name: read_artifact_bytes(directory / name) for name in SOURCES}
    hashes = {name: sha256(value).hexdigest() for name, value in raw.items()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'hash-bound canonical inputs')
    source, original9 = (json.loads(raw[name]) for name in SOURCES)
    require(original9['source_sha256'] == hashes[SOURCES[0]]
            and original9['source_case'] == 'PG1', 'original9 dependency chain')
    cases = [case for case in source['cases'] if case['name'] == 'PG1']
    require(len(cases) == 1, 'unique PG1 source case')
    case = cases[0]
    points = case['points']
    weights = case['weight_numerators']
    den = case['weight_denominator']
    require(len(points) == len(weights) == 75
            and all(type(x) is int and 0 <= x < 315 for x in points)
            and all(type(w) is int and w >= 0 for w in weights)
            and sum(weights) == den == 1000000007, 'unchanged PG1 probability')
    require(points == [x for x in range(315)
                       if all(x % d != a for d, a in case['family'])],
            'actual original-label PG1 carrier')
    require(case['old_points'] == sorted({x % 45 for x in points}),
            'actual old45 projection')
    ds = [d for d in range(1, 316) if 315 % d == 0]
    family = {d: 47 % d for d in ds}
    loads = [sum(x % d == a for d, a in family.items()) for x in points]

    def cap(values, d):
        totals = [sum(v for x, v in zip(points, values) if x % d == a)
                  for a in range(d)]
        value = max(totals)
        return value, totals.index(value)

    saturated = {d: {p for p, h in ((3, 2), (5, 1), (7, 1))
                     if d % p**h == 0} for d in ds}
    aa = {d: prod((F(p, p - 1) for p in saturated[d]), start=F(1)) for d in ds}
    gamma = {d: aa[d] - 1 for d in ds}
    kappa = {(d, e): prod((F(p * (p + 1), (p - 1)**2)
                          if p in saturated[d] & saturated[e] else F(p, p - 1)
                          for p in saturated[d] | saturated[e]), start=F(1))
             - aa[d] - aa[e] + 1 for d in ds for e in ds}
    require(min(gamma.values()) >= 0 and min(kappa.values()) >= 0,
            'complete nonnegative geometric moment coefficients')
    plain_caps = {d: cap(weights, d)[0] for d in ds}
    low_square = F(sum(w * b*b for w, b in zip(weights, loads)), den)
    cross = 2 * sum((gamma[d] * F(cap([w*b for w, b in zip(weights, loads)], d)[0], den)
                     for d in ds), F(0))
    high = sum((kappa[d, e] * F(plain_caps[lcm(d, e)], den)
                for d in ds for e in ds), F(0))
    unconditional = low_square + cross + high
    # Exact full first moments minus the original one-extra-prime groups.
    # These coefficients have no finite-height cutoff.
    rem = {d: gamma[d] - (F(1, 2) if d in (9, 45) else 0)
           - (F(1, 4) if d in (5, 15, 45, 35) else 0)
           - (F(1, 6) if d % 7 == 0 else 0) for d in ds}
    require(min(rem.values()) >= 0, 'complete nonnegative deletion remainder')
    pg = load_oracle(directory)
    setup = pg.group_setup({'survivors': points, 'points': case['old_points']},
                           (9, 45), 35)

    def deletion(values, witness=False):
        require(len(values) == len(points)
                and all(type(v) is int and v >= 0 for v in values)
                and 48 * sum(values) < 2**63, 'nonnegative exact int64 oracle input')
        vector = np.array(values, dtype=np.int64)
        best, _, _ = pg.group_oracle(vector, setup)
        caps = {d: cap(values, d) for d in ds}
        upper = F(best['value'], 48 * den) + sum(
            (rem[d] * F(caps[d][0], den) for d in ds), F(0))
        result = {'group_numerator48': best['value'],
                  'cap_numerators': {str(d): caps[d][0] for d in ds},
                  'deletion_upper': str(upper)}
        if not witness:
            return result
        # Replay the maximizing group's original residues, with deterministic
        # least-residue tie breaking for its remaining six independent labels.
        A = [sum(x % d == a for d, a in zip((9, 45), best['A_residues']))
             for x in points]
        B5 = [sum(x % d == a for d, a in zip((5, 15, 45), best['B_residues']))
              for x in points]
        E = [int(x % 35 == best['extra_residue']) for x in points]
        T = [2-a for a in A]
        factor = [t*(4-b-e) for t, b, e in zip(T, B5, E)]
        row = [24*a+6*t*(b+e) for a, t, b, e in zip(A, T, B5, E)]
        e7 = []
        for d in (7, 21, 35, 63, 105, 315):
            _, residue = cap([v*k for v, k in zip(values, factor)], d)
            e7.append(residue)
            row = [r+k*int(x % d == residue) for r, k, x in zip(row, factor, points)]
        require(all(0 <= r <= 48 for r in row)
                and sum(v*r for v, r in zip(values, row)) == best['value'],
                'actual original-residue group witness equals oracle maximum')
        result['witness'] = {
            'group_residues': {'A': list(best['A_residues']),
                               'B5': list(best['B_residues']),
                               'extra35': best['extra_residue'], 'E7': e7},
            'group_coefficients48': row,
            'cap_residues': {str(d): caps[d][1] for d in ds}}
        return result

    mass = deletion(weights)
    q0 = F(original9['result']['survival_lower'])
    source_order = [3**a * 5**b * 7**c for a, b, c in product(range(3), range(2), range(2))]
    require([plain_caps[d] for d in source_order] == original9['result']['cap_numerators']
            and mass['group_numerator48'] == original9['result']['group_numerator48']
            and 0 < q0 <= 1 and 1 - F(mass['deletion_upper']) == q0,
            'exact original9 source observations and Rold(mu)=1-q0')
    endpoints = {}
    common = None
    for reference in (32, 33):
        row = deletion([w * max(reference-b*b, 0) for w, b in zip(weights, loads)],
                       witness=reference == 32)
        if reference == 32:
            common = row.pop('witness')
        row['signed_excess'] = str(unconditional + F(row['deletion_upper']) - reference)
        endpoints[str(reference)] = row
    require(common is not None, 'attained endpoint witness')
    active = [int(b <= 5) for b in loads]
    require(all((32-b*b > 0) == (33-b*b > 0) == bool(t)
                for b, t in zip(loads, active)), 'fixed positive-part support on [32,33]')
    coefficients = common['group_coefficients48']
    alpha = F(sum(w*r*t for w, r, t in zip(weights, coefficients, active)), 48*den)
    beta = F(sum(w*r*t*b*b for w, r, t, b in zip(weights, coefficients, active, loads)), 48*den)
    for d in ds:
        residue = common['cap_residues'][str(d)]
        alpha += rem[d] * F(sum(w*t for x, w, t in zip(points, weights, active)
                                if x % d == residue), den)
        beta += rem[d] * F(sum(w*t*b*b for x, w, t, b in zip(points, weights, active, loads)
                               if x % d == residue), den)
    require(all(alpha*k-beta == F(endpoints[str(k)]['deletion_upper']) for k in (32, 33)),
            'one feasible affine witness attains both endpoint upper bounds')
    require(0 <= alpha < 1, 'strict affine slope below one')
    root = (unconditional-beta) / (1-alpha)
    require(32 < root < 33 and F(endpoints['32']['signed_excess']) > 0
            and F(endpoints['33']['signed_excess']) < 0, 'unique zero in affine interval')
    common.update({'alpha': str(alpha), 'beta': str(beta)})
    result = {'original_low_residues': {str(d): family[d] for d in ds},
              'low_load': loads,
              'anchored': {'low_square': str(low_square), 'cross': str(cross),
                           'higher_higher': str(high), 'upper': str(unconditional)},
              'complete_deletion_remainder': {str(d): str(rem[d]) for d in ds},
              'plain_deletion': mass, 'source_survival_lower': str(q0),
              'endpoints': endpoints, 'common_affine_witness': common,
              'affine_interval': [32, 33], 'reference_domain': 'all real K',
              'minimum_reference': str(root), 'minimum_value': str(root), 'scope': SCOPE}
    return {'schema': SCHEMA, 'source_sha256': hashes, 'source_case': 'PG1', 'result': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE / 'certificates/pg1_anchored_reference_boundary_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'certificate schema')
    actual = evaluate(args.source_directory,
                      None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2) + '\n')
    else:
        require(expected == actual, 'complete exact reference-boundary certificate')
    print(json.dumps({'minimum_reference': actual['result']['minimum_reference'],
                      'minimum_value': actual['result']['minimum_value'],
                      'reference_domain': actual['result']['reference_domain']}))


if __name__ == '__main__':
    main()
