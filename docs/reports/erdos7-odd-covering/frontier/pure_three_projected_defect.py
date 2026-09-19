#!/usr/bin/env python3
"""Project every deep pure3 forbidden label onto one five-coordinate defect.

Retain the complete missing-label budget, actual seven union loss and
the source measure. Geometric tail evaluation reuses profile66.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/pure_three_projected_defect.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/endpoint_linear_neighborhood.py': 'e9d1eb6487f95874b2c577496b41083ff140138ef5a59d630144d1c72aae279a',
    'frontier/source_cost_endpoint_attainment.py': 'b7daf5ab9c8656d922681e298b030c199c5f9bcc36af7a43e84a5bef156fb68f',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def projected_coefficients(eta, shallow_density):
    require(len(eta) == len(shallow_density) == 5 and min(eta) >= 0
            and all(F(3, 5) <= x <= 1 for x in shallow_density), 'Actual five-cell source and shallow carrier density')
    h = sum(eta)
    require(F(1, 2) <= h <= F(5, 9), 'Effective source ternary mass')
    coefficient = sum(x*y for x, y in zip(eta, shallow_density))-F(1, 90)
    require(coefficient >= F(13, 45), 'Projected reference is a positive measure')
    return h, coefficient


def concentrated_upper(sigma):
    sigma = F(sigma)
    require(0 <= sigma < F(1, 2), 'One K orientation selected by concentration')
    return {'h_upper': F(1, 2)+sigma/18,
            'coefficient_upper': F(2, 5)+13*sigma/90,
            'extra_capacity_defect_upper': sigma/240}


def finite_projection(base, parent, constructor, source, tail, mode):
    height, A, B, P = 3, 27, 125, 343
    source_labels = [constructor.source(a, b, 'off-diagonal')
                     for a, b in product(range(height+1), repeat=2) if a+b]
    q = []
    for y in range(B):
        killed = any(a == 0 and y % (5**b) == rb for a, _, b, rb in source_labels)
        q.append(F(int(not killed), B))
    old = [(x, y) for x, y in product(range(A), range(B))
           if not any(x % (3**a) == ra and y % (5**b) == rb for a, ra, b, rb in source_labels)]
    d, n, eta, s, _ = source.data(parent.parameter(height))
    z, dmax = sum(q), max(d)
    require(s == F(len(old), A*B) and z == parent.parameter(height)[4], 'Inherited actual source construction')
    pure7 = set(range(P))
    for e in range(1, height+1):
        pure7.difference_update(range(6*7**(e-1), P, 7**e))
    labels = []
    for a, e in product(range(1, height+1), repeat=2):
        if a >= 3 and mode == 'absent':
            continue
        if a == 1:
            residue = 1
        elif a == 2:
            residue = 3
        elif mode == 'cell1':
            residue = 3
        elif mode == 'root1':
            residue = 1
        else:
            residue = (11*a+7*e+e*e) % (3**a)
        re = (a+e) % (7**e)
        actual_seven = set(range(re, P, 7**e)) & pure7
        labels.append((a, residue, F(6, 5*7**e), actual_seven))
    vdeep, survivor = [F(0)]*B, [F(0)]*B
    virtual_mass = deleted_mass = F(0)
    for x, y in old:
        virtual, deep, union = F(0), F(0), set()
        for a, residue, u, seven in labels:
            if x % (3**a) == residue:
                virtual += u
                deep += u if a >= 3 else 0
                union.update(seven)
        deleted = F(len(union), len(pure7))
        require(0 <= deleted <= min(1, virtual), 'Actual seven union is dominated by its same-label cap sum')
        virtual_mass += virtual/(A*B)
        deleted_mass += deleted/(A*B)
        survivor[y] += (1-deleted)/(A*B)
        vdeep[y] += deep/(A*B)
    xi = [x/90-y for x, y in zip(q, vdeep)]
    E3, omega = dmax/90-sum(vdeep), virtual_mass-deleted_mass
    require(min(xi) >= 0 and E3 >= 0 and omega >= 0 and z >= dmax,
            'One positive projected defect, complete missing-label capacity and one union error')
    require(sum(xi) == E3+(z-dmax)/90, 'Exact complete projected-defect mass identity')
    shallow_weight = sum(F(6, 5*7**e) for e in range(1, height+1))
    # Absent shallow labels complete the actual carrier mixture with(-1,-1).
    shallow_density = [1-shallow_weight*(int(c >= 2)+int(c == 1)) for c in range(5)]
    h, coefficient = projected_coefficients(eta, shallow_density)
    excess = [max(m-coefficient*qj, 0) for m, qj in zip(survivor, q)]
    error_mass = E3+omega+(z-dmax)/90
    require(max(excess) <= h/B and sum(excess) <= error_mass, 'Positive survivor excess has Haar domination and the one complete defect budget')
    complete_tail, crossing = tail.min_geometric(error_mass, h, 5, 2)
    bounds = []
    for label_mode in range(3):
        value = sum(sum(m for y, m in enumerate(survivor) if y % (5**b) == (label_mode*(b*b+3)+1) % (5**b))
                    for b in range(2, height+1))
        require(value <= coefficient/20+complete_tail, 'Independent original five tests obey the complete descendant bound')
        bounds.append({'test': label_mode, 'finite_integral': value, 'complete_upper': coefficient/20+complete_tail})
    return {'height': height, 'mode': mode, 'z': z, 'dmax': dmax, 'h': h,
            'virtual_deep3_mass': sum(vdeep), 'complete_unused_deep3_capacity': E3,
            'projected_defect_mass': sum(xi), 'union_cap_error': omega,
            'reference_coefficient': coefficient, 'positive_survivor_excess_mass': sum(excess),
            'common_error_mass_upper': error_mass, 'complete_descendant_error': complete_tail,
            'geometric_crossing': crossing, 'independent_tests': bounds}


def calculate(base):
    io = module('pure3_projection_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    parent = module('pure3_projection_parent', base/'frontier/source_cost_endpoint_attainment.py')
    constructor = parent.load(base, 'frontier/sharp_source_mass_endpoints.py', 'pure3_projection_constructor')
    source = parent.load(base, 'verify_joint_frontier.py', 'pure3_projection_source')
    tail = module('pure3_projection_tail', base/'frontier/endpoint_linear_neighborhood.py')
    require(F(1, 18)*F(1, 5) == F(1, 90) and F(1, 25)/(1-F(1, 5)) == F(1, 20),
            'Both original exponent series are complete')
    eta_face = (F(1, 18),)+(F(1, 9),)*4
    density_face = (F(1), F(4, 5), F(4, 5), F(4, 5), F(4, 5))
    h, c = projected_coefficients(eta_face, density_face)
    require(h == F(1, 2) and c == F(2, 5) and c/20 == F(1, 50), 'Recover75 complete pure-five tail at the K face')
    near = []
    for sigma in (F(0), F(1, 100), F(1, 27), F(2, 27), F(1, 3)):
        upper = concentrated_upper(sigma)
        raw = (5-(1-sigma)/2)/9-(1-sigma)*F(4, 45)-F(1, 90)
        require(raw == upper['coefficient_upper'] and (3*sigma/8)/90 == upper['extra_capacity_defect_upper'],
                'Exact concentrated reference and shared-defect coefficients')
        require(raw <= F(2, 5)+sigma/6-sigma*sigma/45, 'The shared total deficit improves the separate root/cell bounds')
        for remaining in (F(0), F(1, 10**6), F(1, 60000)):
            error = remaining+upper['extra_capacity_defect_upper']
            complete, crossing = tail.min_geometric(error, upper['h_upper'], 5, 2)
            near.append({'sigma': sigma, 'E3_plus_omega_upper': remaining, **upper,
                         'complete_error': complete, 'crossing': crossing,
                         'complete_descendant_upper': upper['coefficient_upper']/20+complete})
    cases = [finite_projection(base, parent, constructor, source, tail, mode)
             for mode in ('cell1', 'root1', 'scrambled', 'absent')]
    return {'schema': 'erdos7-pure-three-projected-defect-v1', 'source_sha256': {**PINS, **parent.PINS},
            'complete_projection_coefficient': F(1, 90), 'complete_five_descendant_sum': F(1, 20),
            'face_reference_coefficient': c, 'face_complete_five_tail': c/20,
            'concentrated_bounds': near, 'actual_finite_cases': cases,
            'scope': 'Ordinary complete deep-pure3 projected measure identity and an actual off-face pure-five tail interface. Independent original labels, missing labels, all exponent tails and the same capacity/union budget are retained. Does not restore forced27, the whole109 mean correction or a new global comparison.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('pure3_projection_writer', args.base/'certificate_io.py')
    result = encode(calculate(args.base))
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical projected pure3 defect certificate')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('PASS: four actual source/cofactor cases, common projected-defect identities and all complete geometric tails.')
    print('The K-face pure-five tail1/50 has an explicit off-face interface; no new global K asserted.')


if __name__ == '__main__':
    main()
