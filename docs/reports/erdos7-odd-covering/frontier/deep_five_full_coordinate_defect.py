#!/usr/bin/env python3
"""Complete first/second moments for full-coordinate deep-five defects.

Every potential absent label receives an ideal cylinder. Actual correct
labels keep their own residue. The ordinary theorem is profile123.
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
CERTIFICATE = 'certificates/source_norms/deep_five_full_coordinate_defect.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/source_cost_endpoint_attainment.py': 'b7daf5ab9c8656d922681e298b030c199c5f9bcc36af7a43e84a5bef156fb68f',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source '+str(path))
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


def rational(value):
    require(isinstance(value, (int, F)) and not isinstance(value, bool), 'Exact rational input')
    return F(value)


def cylinder_coefficient(k):
    require(isinstance(k, int) and k >= 0, 'An original five-cylinder depth, including the unit')
    if k < 2:
        return F(1, 100)
    return F(4*k-3, 20*5**k)


def moment_tail(degree, start):
    require(degree in (1, 2) and isinstance(start, int) and start >= 2, 'Complete first/second moment tail')
    if degree == 1:
        return F(2*start-1, 8*5**start)
    return F(16*start*start-28*start+15, 32*5**start)


def complete_moment(error, ternary_mass, degree=1):
    """Exact sum of [(k-1)^degree-(k-2)^degree]*min(E,H*a_k), k>=2."""
    error, ternary_mass = map(rational, (error, ternary_mass))
    require(error >= 0 and ternary_mass >= 0 and degree in (1, 2), 'Nonnegative defect and ternary cap')
    if error == 0 or ternary_mass == 0:
        return {'upper': F(0), 'crossing': None}
    N = 2
    while ternary_mass*cylinder_coefficient(N) > error:
        N += 1
    result = error*(N-2)**degree+ternary_mass*moment_tail(degree, N)
    require(result <= ternary_mass*moment_tail(degree, 2), 'Complete geometric moment ceiling')
    return {'upper': result, 'crossing': N}


def cylinder_bound(error, ternary_mass, k):
    error, ternary_mass = map(rational, (error, ternary_mass))
    require(error >= 0 and ternary_mass >= 0, 'Nonnegative actual defect and ternary mass')
    return min(error, ternary_mass*cylinder_coefficient(k))


def finite_case(parent, constructor, source, mode):
    height, A, B = 3, 27, 125
    labels = [constructor.source(a, b, 'off-diagonal')
              for a, b in product(range(height+1), repeat=2) if a+b]
    eta = [F(int(not any(b == 0 and x % 3**a == ra for a, ra, b, _ in labels)), A) for x in range(A)]
    raw = [[F(int(not any(x % 3**a == ra and y % 5**b == rb for a, ra, b, rb in labels)), A*B)
            for y in range(B)] for x in range(A)]
    _, _, eta_cells, source_mass, _ = source.data(parent.parameter(height))
    h, h0, h1 = sum(eta), sum(eta_cells[:2]), sum(eta_cells[2:])
    require(h == sum(eta_cells) and sum(sum(row) for row in raw) == source_mass, 'Independent original source mask')
    require(h1 > h0, 'Actual root1 capacity branch')
    ideal_five = [[F(0)]*B for _ in range(2)]
    v5, v15correct, v15wrong = [[[F(0)]*B for _ in range(A)] for _ in range(3)]
    for family, b, e in product(range(2), range(2, height+1), range(1, height+1)):
        present = mode != 'absent'
        root = 1 if mode in ('aligned', 'source-intersections') else 0 if mode == 'wrong' else (b+e) % 3
        residue = (2*b*b+7*e+3*b*e) % 5**b if mode == 'source-intersections' else 4
        correct = family == 0 or root == 1
        # Correct actual labels retain their exact residue; wrong/absent copies use4.
        ideal_residue = residue if present and correct else 4
        u = F(6, 5*7**e)
        for y in range(ideal_residue, B, 5**b):
            ideal_five[family][y] += u/B
        if present:
            for x, y in product(range(A), range(residue, B, 5**b)):
                if family == 0:
                    v5[x][y] += u*raw[x][y]
                elif x % 3 == root:
                    (v15correct if root == 1 else v15wrong)[x][y] += u*raw[x][y]
    # Every remaining potential label is absent and has the complete ideal F=4.
    # First keep b=2,3 and sum every e>3. Then sum all b>3 and all e>=1.
    for family in range(2):
        for b in range(2, height+1):
            for y in range(4, B, 5**b):
                ideal_five[family][y] += F(1, 5*7**height*B)
        ideal_five[family][4] += F(1, 4*5**(height+1))
        require(sum(ideal_five[family]) == F(1, 100), 'All missing b/e labels have their exact complete ideal capacity')
    I5 = [[eta[x]*ideal_five[0][y] for y in range(B)] for x in range(A)]
    I15 = [[eta[x]*int(x % 3 == 1)*ideal_five[1][y] for y in range(B)] for x in range(A)]
    Xi5 = [[I5[x][y]-v5[x][y] for y in range(B)] for x in range(A)]
    Xi15 = [[I15[x][y]-v15correct[x][y] for y in range(B)] for x in range(A)]
    mass = lambda m: sum(sum(row) for row in m)
    E5, E15 = h/100-mass(v5), h1/100-mass(v15correct)-mass(v15wrong)
    wrong, ratio = mass(v15wrong), h1/(h1-h0)
    require(min(v for m in (Xi5, Xi15) for row in m for v in row) >= 0,
            'Positive full-coordinate differences, not just positive projections')
    require(mass(Xi5) == E5 and mass(Xi15) == E15+wrong <= ratio*E15,
            'Exact full-coordinate mass identities and same wrong-root budget')
    checks, moment_checks, digest = 0, 0, sha256()
    for name, Xi, error, support_root in (('five', Xi5, E5, None), ('fifteen', Xi15, ratio*E15, 1)):
        for a in range(height+1):
            for residue3 in range(3**a):
                xs = tuple(range(residue3, A, 3**a))
                H = sum(eta[x] for x in xs if support_root is None or x % 3 == support_root)
                marginal = [sum(Xi[x][y] for x in xs) for y in range(B)]
                for k in range(height+1):
                    cap = cylinder_bound(error, H, k)
                    for residue5 in range(5**k):
                        observed = sum(marginal[y] for y in range(residue5, B, 5**k))
                        require(observed <= cap, 'Independent original ternary/five cylinder cap')
                        digest.update(json.dumps(encode([name, a, residue3, k, residue5, observed, cap]), separators=(',', ':')).encode())
                        checks += 1
                for first, second in product(range(3), repeat=2):
                    loads = [[sum(int(y % 5**k == (pattern*(k*k+3)+1) % 5**k)
                                  for k in range(2, height+1)) for y in range(B)] for pattern in (first, second)]
                    observed1 = sum(v*l for v, l in zip(marginal, loads[0]))
                    observed2 = sum(v*l*r for v, l, r in zip(marginal, *loads))
                    require(observed1 <= complete_moment(error, H, 1)['upper']
                            and observed2 <= complete_moment(error, H, 2)['upper'],
                            'Independent original finite loads fit the full infinite moment upper')
                    moment_checks += 2
    return {'mode': mode, 'h': h, 'h0': h0, 'h1': h1, 'E5deep': E5, 'E15deep': E15,
            'wrong_root_mass': wrong, 'Xi5_mass': mass(Xi5), 'Xi15_mass': mass(Xi15),
            'cylinder_checks': checks, 'moment_checks': moment_checks, 'all_cylinder_checks_sha256': digest.hexdigest(),
            'complete_first_moments': {'five': complete_moment(E5, h), 'fifteen': complete_moment(ratio*E15, h1)},
            'complete_second_moments': {'five': complete_moment(E5, h, 2), 'fifteen': complete_moment(ratio*E15, h1, 2)}}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('deep_full_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    parent = module('deep_full_parent', base/'frontier/source_cost_endpoint_attainment.py')
    source = parent.load(base, 'verify_joint_frontier.py', 'deep_full_source')
    constructor = parent.load(base, 'frontier/sharp_source_mass_endpoints.py', 'deep_full_constructor')
    # Complete identities are checked by the tail recurrence and its initial value.
    algebra = 0
    for degree, k in product((1, 2), range(2, 33)):
        count = (k-1)**degree-(k-2)**degree
        require(moment_tail(degree, k)-moment_tail(degree, k+1) == count*cylinder_coefficient(k),
                'Exact complete moment-tail recurrence')
        intersection_sum = F(k-1, 5**k)+F(1, 4*5**k)
        require(intersection_sum/5 == cylinder_coefficient(k), 'All possible deep ideal labels intersect an independent original cylinder')
        algebra += 1
    require(moment_tail(1, 2) == F(3, 200) and moment_tail(2, 2) == F(23, 800), 'Exact complete first/second ceilings')
    sum_checks = []
    for H, E in product((F(0), F(1, 9), F(1, 3), F(1, 2), F(1)),
                        (F(0), F(1, 10**8), F(1, 10000), F(9, 2500), F(1, 100), F(1))):
        for degree in (1, 2):
            result = complete_moment(E, H, degree)
            if result['crossing'] is not None:
                N = result['crossing']
                correction = sum(((k-1)**degree-(k-2)**degree)*(H*cylinder_coefficient(k)-E) for k in range(2, N))
                require(result['upper'] == H*moment_tail(degree, 2)-correction, 'Independent exact finite-correction evaluation')
            sum_checks.append({'H': H, 'E': E, 'degree': degree, **result})
    budget, slope, inner = F(1, 100), F(3, 2), F(9, 2500)
    counterexample = [{'E': E, 'q': budget-E,
                       'value': slope*(budget-E)+complete_moment(E, F(1))['upper']} for E in (F(0), inner, budget)]
    require(counterexample[0]['value'] == counterexample[2]['value'] == F(3, 200)
            and counterexample[1]['value'] == F(91, 5000) > F(3, 200), 'A strict interior maximum defeats a blanket budget-vertex argument')
    cases = [finite_case(parent, constructor, source, mode)
             for mode in ('aligned', 'wrong', 'mixed', 'source-intersections', 'absent')]
    return encode({'schema': 'erdos7-deep-five-full-coordinate-defect-v1', 'source_sha256': {**PINS, **parent.PINS},
                   'algebra_checks': algebra, 'complete_sum_checks': sum_checks, 'actual_finite_cases': cases,
                   'cylinder_checks': sum(c['cylinder_checks'] for c in cases),
                   'moment_checks': sum(c['moment_checks'] for c in cases),
                   'budget_vertex_counterexample': counterexample,
                   'scope': 'Ordinary full-coordinate positive deep-five defects with arbitrary independent original cylinders and complete first/second moment tails. Ideal copies complete absent labels. No survivor-excess, forced27 transport, complete off-face numerator, global K or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('deep_full_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact semantic full-coordinate deep-five certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: complete full-coordinate ideals, independent cylinder caps, first/second infinite moment tails and an interior budget obstruction.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
