#!/usr/bin/env python3
"""Transport the complete deep5/3deep5 mean-head credit with one budget."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/deep_five_mean_transport.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/source_cost_endpoint_attainment.py': '9c22b67d249f21e86e0292189c7808db023fd9c45090911f7c58bffa6b6d1ea2',
}
ROOT = (0, 0, 1, 1, 1)
CELLS = (0, 3, 1, 4, 7)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def mean_credit(eta, test_root, test_cell, E5deep, E15deep):
    eta = tuple(map(F, eta))
    E5deep, E15deep = F(E5deep), F(E15deep)
    require(len(eta) == 5 and min(eta) >= 0 and test_root in (0, 1)
            and test_cell in range(5) and min(E5deep, E15deep) >= 0, 'Actual ternary data and nonnegative deep-family defects')
    roots = (sum(eta[:2]), sum(eta[2:]))
    gap = roots[1]-roots[0]
    require(gap > 0, 'Root1 is separated from every wrong surviving root')
    ratio = roots[1]/gap
    M5 = 1+int(ROOT[test_cell] == test_root)
    M15 = int(test_root == 1)+int(ROOT[test_cell] == 1)
    reference = ((1+test_root)*roots[test_root]+(1+ROOT[test_cell])*eta[test_cell])/100
    penalty = M5*E5deep+M15*ratio*E15deep
    return {'reference': reference, 'M5': M5, 'M15': M15, 'root_ratio': ratio,
            'defect_penalty': penalty, 'affine_credit': reference-penalty,
            'nonnegative_credit': max(reference-penalty, 0)}


def concentrated_ratio(sigma):
    sigma = F(sigma)
    require(0 <= sigma < F(1, 2), 'Concentrated K orientation')
    return (6-sigma)/(3-2*sigma)


def finite_case(parent, constructor, source, mode):
    height, A, B = 3, 27, 125
    labels = [constructor.source(a, b, 'off-diagonal')
              for a, b in product(range(height+1), repeat=2) if a+b]
    old = [(x, y) for x, y in product(range(A), range(B))
           if not any(x % (3**a) == ra and y % (5**b) == rb for a, ra, b, rb in labels)]
    eta_atoms = [F(int(not any(b == 0 and x % (3**a) == ra for a, ra, b, _ in labels)), A)
                 for x in range(A)]
    _, _, eta, s, _ = source.data(parent.parameter(height))
    h0, h1 = sum(eta[:2]), sum(eta[2:])
    require(s == F(len(old), A*B) and sum(eta_atoms) == h0+h1, 'Inherited actual raw source and pure3 projection')
    v5, v15correct, v15all = ([F(0)]*A for _ in range(3))
    for a, b, e in product((0, 1), range(2, height+1), range(1, height+1)):
        if mode == 'absent':
            continue
        if a == 0:
            root = 0
        elif mode == 'correct':
            root = 1
        elif mode == 'wrong':
            root = 0
        else:
            root = (b+e) % 3
        residue5 = (2*b*b+7*e+3*b*e) % (5**b)
        u = F(6, 5*7**e)
        for x, y in old:
            if y % (5**b) == residue5 and (a == 0 or x % 3 == root):
                if a == 0:
                    v5[x] += u/(A*B)
                else:
                    v15all[x] += u/(A*B)
                    if root == 1:
                        v15correct[x] += u/(A*B)
    E5, E15 = (h0+h1)/100-sum(v5), h1/100-sum(v15all)
    xi5 = [v/100-w for v, w in zip(eta_atoms, v5)]
    xi15 = [v*int(x % 3 == 1)/100-w for x, (v, w) in enumerate(zip(eta_atoms, v15correct))]
    wrong_mass = sum(v15all)-sum(v15correct)
    require(min(E5, E15, *xi5, *xi15) >= 0 and sum(xi5) == E5
            and sum(xi15) == E15+wrong_mass <= h1/(h1-h0)*E15,
            'Complete missing-label identities and the one wrong-root capacity price')
    checks = []
    for r, c in product(range(2), range(5)):
        credit = mean_credit(eta, r, c, E5, E15)
        psi = [int(x % 3 == r)+int(x % 9 == CELLS[c]) for x in range(A)]
        actual = sum(p*(v+w) for p, v, w in zip(psi, v5, v15all))
        require(actual >= credit['nonnegative_credit'], 'Both complete deep families pay the same original root/cell head')
        checks.append({'test_root': r, 'test_cell': c, **credit, 'actual_virtual_credit': actual})
    return {'mode': mode, 'height': height, 'h0': h0, 'h1': h1,
            'E5deep': E5, 'E15deep': E15, 'wrong_root_virtual_mass': wrong_mass,
            'xi5_mass': sum(xi5), 'xi15_mass': sum(xi15), 'head_checks': checks}



def positive_finite_case(parent, constructor, source):
    """Genuine finite labels in a verified product fiber, with nonzero root spill."""
    height, A, B = 3, 27, 125
    labels = [constructor.source(a, b, 'off-diagonal')
              for a, b in product(range(height+1), repeat=2) if a+b]
    old = {(x, y) for x, y in product(range(A), range(B))
           if not any(x % (3**a) == ra and y % (5**b) == rb for a, ra, b, rb in labels)}
    eta_atoms = [F(int(not any(b == 0 and x % (3**a) == ra for a, ra, b, _ in labels)), A)
                 for x in range(A)]
    _, _, eta, s, _ = source.data(parent.parameter(height))
    h0, h1 = sum(eta[:2]), sum(eta[2:])
    require(s == F(len(old), A*B), 'Same genuine height3 source')
    require(all(((x, y) in old) == bool(eta_atoms[x])
                for x in range(A) for y in range(4, B, 5)),
            'H=4 is an exact complete source-free five fiber above every surviving ternary atom')
    v5, v15correct, v15all = ([F(0)]*A for _ in range(3))
    for b, e in product(range(2, 7), range(1, 7)):
        weight = F(6, 5*7**e*5**b)
        root = 0 if (b, e) == (6, 6) else 1
        for x, mass in enumerate(eta_atoms):
            v5[x] += weight*mass
            if x % 3 == root:
                v15all[x] += weight*mass
                if root == 1:
                    v15correct[x] += weight*mass
    E5, E15 = (h0+h1)/100-sum(v5), h1/100-sum(v15all)
    xi5 = [v/100-w for v, w in zip(eta_atoms, v5)]
    xi15 = [v*int(x % 3 == 1)/100-w for x, (v, w) in enumerate(zip(eta_atoms, v15correct))]
    wrong_mass = sum(v15all)-sum(v15correct)
    require(min(E5, E15, *xi5, *xi15) >= 0 and sum(xi5) == E5
            and sum(xi15) == E15+wrong_mass <= h1/(h1-h0)*E15 and wrong_mass > 0,
            'Positive deep-family defect and nonzero actual wrong-root spill retain every missing tail')
    checks = []
    for r, c in product(range(2), range(5)):
        credit = mean_credit(eta, r, c, E5, E15)
        actual = sum((int(x % 3 == r)+int(x % 9 == CELLS[c]))*(v+w)
                     for x, (v, w) in enumerate(zip(v5, v15all)))
        require(actual >= credit['nonnegative_credit'] > 0,
                'Every actual long-family root/cell head has strictly positive transported credit')
        checks.append({'test_root': r, 'test_cell': c, **credit, 'actual_virtual_credit': actual})
    return {'mode': 'positive-product-fiber-with-wrong-root', 'source_height': height,
            'present_b_interval': [2, 6], 'present_e_interval': [1, 6],
            'five_residue_for_each_label': 4, 'wrong_root_label': [1, 6, 6],
            'h0': h0, 'h1': h1, 'E5deep': E5, 'E15deep': E15,
            'wrong_root_virtual_mass': wrong_mass, 'xi5_mass': sum(xi5),
            'xi15_mass': sum(xi15), 'head_checks': checks,
            'minimum_positive_credit': min(v['nonnegative_credit'] for v in checks)}


def calculate(base):
    io = module('deep_five_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    parent = module('deep_five_parent', base/'frontier/source-budgets/source_cost_endpoint_attainment.py')
    source = parent.load(base, 'verify_joint_frontier.py', 'deep_five_source')
    constructor = parent.load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'deep_five_constructor')
    require(F(1, 25)/(1-F(1, 5))*F(1, 5) == F(1, 100), 'Both complete b/e exponent families have coefficient1/100')
    face = [mean_credit((F(1, 18),)+(F(1, 9),)*4, r, c, 0, 0) for r, c in product(range(2), range(5))]
    require(all(row['root_ratio'] == 2 and row['defect_penalty'] == 0 for row in face), 'Recover every109 deep-five mean-head credit at the K face')
    ratios = []
    for sigma in (F(0), F(1, 27), F(2, 27), F(1, 3)):
        y, x = (1-sigma)/2, sigma/2
        require((3-x)/(1+y-x) == concentrated_ratio(sigma), 'Coupled total-deficit extremum for the root ratio')
        ratios.append({'sigma': sigma, 'root_ratio_upper': concentrated_ratio(sigma)})
    return {'schema': 'erdos7-deep-five-mean-transport-v1', 'source_sha256': {**PINS, **parent.PINS},
            'complete_exponent_coefficient': F(1, 100), 'face_head_credits': face, 'concentrated_ratios': ratios,
            'actual_source_projection_cases': [finite_case(parent, constructor, source, mode)
                                               for mode in ('correct', 'wrong', 'mixed', 'absent')],
            'positive_finite_case': positive_finite_case(parent, constructor, source),
            'scope': 'Ordinary off-face transport of109 C5 from two distinct complete deep-five families with one actual residual budget. The clipped credit is not asserted to preserve convexity in a numerical consumer. Does not supply a complete off-face numerator or new global K.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned certificate IO')
    io = module('deep_five_writer', args.base/'certificate_io.py')
    result = encode(calculate(args.base))
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical deep-five mean transport certificate')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('PASS: complete1/100 families, five actual source projections,50 head credits including10 strictly positive and coupled root-ratio bounds.')
    print('Transported C5 only; no complete off-face numerator or new global comparison claimed.')


if __name__ == '__main__':
    main()
