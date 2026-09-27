#!/usr/bin/env python3
"""A supporting affine old49 margin sharpens the complete whole-J reserve."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_affine_margin_reserve.json'
PINS = {
    'certificates/source_norms/j-geometry/j_family_error_reserve.json': 'ab5043b757c5c79e11276bd7fc6b2cf9c9f36a530b9b59bbb6eaaa51bdbd578c',
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
    'frontier/endpoint-bounds/endpoint_linear_neighborhood.py': 'f8921b87de7b31cf834ef0c1fdd3df4802266e0dc990b19d86bf666221df235d',
    'frontier/j-geometry/j_family_error_reserve.py': '8f531511ef044a1dc881852ea502af42a49cc59036a39c134fe13eaf3412170b',
    'profile-notes/065-128/66-explicit-linear-endpoint-neighborhood.md': '40f806a9438493aeb51d181059f0c64190bf28ef8d22837f8c515f7bad79216d',
    'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md': 'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8',
    'profile-notes/129-192/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md': '845d9a84f41391240f05f8c5be35cf074d6614abf1dfc493046e8619521f3945',
    'profile-notes/193-256/197-the-whole-j-reserve-keeps-each-original-family-error.md': '9480a9921773085a9c21cee529818aa368e68a06810e7e98086745e787064ebd',
}
B = (2, 3, 1, 1, 1)
C = (1, 2, 2, 2, 2)
K = tuple(6-b for b in B)
NC = tuple(map(F, ('29/10', '13/10', '47/10', '47/10', '47/10')))
EC = tuple(map(F, ('-23/50', '-59/100', '-27/20', '-11/10', '-11/10')))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def affine_support(dat):
    d, n, eta, _, _ = dat
    return (-F(1381, 48600)-d[0]/9
            +sum(a*v for a, v in zip(NC, n))
            +sum(a*v for a, v in zip(EC, eta)))


def supported_expression(dat):
    """Replace each subtracted maximum by its stated affine lower support."""
    d, n, eta, s, _ = dat
    h, h1 = sum(eta), sum(eta[2:])
    cap = s/2+n[1]+d[0]/18+(h+h1+eta[1])/4+F(1, 72)
    ceta = sum(a*v for a, v in zip(C, eta))
    U = (6*s/5+cap/5+sum(v*(b-1) for v, b in zip(n, B))
         +d[0]/18+ceta/5+ceta/20+F(1, 72))
    w = tuple(9*v*k for v, k in zip(eta, K))
    T = (F(13, 243)*(4*d[0]-F(1, 5))+F(1, 486)*4*d[0]
         +(sum(w)+sum(w[2:])+w[2])/36+F(5, 72))
    carrier = 4*n[0]+6*n[1]-(eta[0]+4*eta[1])/5
    return 6*s-U-(carrier+T)/5


def fixed_margin(original, dat, carrier):
    d, n, eta, s, _ = dat
    a = tuple(k*v-c*e/5 for k, v, c, e in zip(K, n, C, eta))
    z = tuple(k*v-F(c, 5) for k, v, c in zip(K, d, C))
    w = tuple(9*e*k for e, k in zip(eta, K))
    T = (F(13, 243)*max(z)+F(1, 486)*max(k*v for k, v in zip(K, d))
         +(sum(w)+original.roots(w)+max(w))/36+F(5, 72))
    root, cell = carrier
    score = (sum(a[:2]) if root == 0 else sum(a[2:]) if root == 1 else F(0))
    score += a[cell] if cell >= 0 else 0
    bases = tuple(tuple(1+int((i >= 2) == bool(r))+int(i == j)
                        for i in range(5)) for r in range(2) for j in range(5))
    return 6*s-original.exact_old_U(dat, B, C, bases)-(score+T)/5


def reserve_bound(delta, rho, family):
    """Same136 domain and197 complete errors; only the old49 margin changes."""
    delta, rho = map(F, (delta, rho))
    row = family.reserve_bound(delta, rho)
    error = row['complete_zero7_error']
    bound = F(79, 1944)-6*delta-error
    require(bound == row['old49_replacement_reserve_lower']+48*delta,
            'Only the old margin source price changes; complete family error retained')
    return {**row, 'previous_old49_replacement_reserve_lower': row['old49_replacement_reserve_lower'],
            'old49_replacement_reserve_lower': bound, 'replacement_delta_price': F(6),
            'old49_margin_delta_price': F(2), 'reserve_gain': 48*delta}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical reader')
    io = module('j_affine_io', base/'certificate_io.py')
    family = module('j_affine_family', base/'frontier/j-geometry/j_family_error_reserve.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_family_error_reserve.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    original = module('j_affine_original', base/'frontier/endpoint-bounds/endpoint_linear_neighborhood.py')
    source = module('j_affine_source', base/'verify_joint_frontier.py')
    require(B in source.BASES and C in source.BASES, 'The same actual independent fixed layouts')
    # Both expressions are affine in the15 inputs after s=sum n. Basis
    # evaluation identifies all coefficients, not a sample of a nonlinear map.
    basis = []
    for index in range(-1, 15):
        vectors = [[F(0)]*5 for _ in range(3)]
        if index >= 0:
            vectors[index//5][index % 5] = F(1)
        dat = (*vectors, sum(vectors[1]), F(0))
        require(supported_expression(dat) == affine_support(dat), 'Every affine coefficient and constant')
        basis.append(affine_support(dat))
    require(all(a > 0 for a in NC) and all(a < 0 for a in EC)
            and max(-a for a in EC[1:]) == F(27, 20), 'Required source coefficient signs')
    np = NC[0]/18+NC[1]/36+NC[2]*F(2, 9)
    nq = (NC[0]-NC[2])/72
    dp, ep, cp = F(1, 18), F(27, 20)/18, F(1, 2)
    require((np, nq) == (F(149, 120), -F(1, 40))
            and np+dp+ep+cp == F(337, 180) < 2
            and F(239, 60)+2 < 6, 'Full actual source and carrier price, with correct signs')
    require((F(10, 9)+F(8, 45))/5 == F(58, 225) < cp,
            'One carrier change costs less than one half throughout the source domain')
    # These endpoint checks detect implementation mistakes. The accompanying
    # max-support and concentration inequalities prove the continuous claim.
    carriers = [(r, c) for r in (-1, 0, 1) for c in (-1, 0, 1, 2, 3, 4)]
    checks, minimum = 0, None
    face_values = []
    for i, parameter in enumerate(source.vertices()):
        dat = source.data(parameter)
        fixed = fixed_margin(original, dat, (0, 1))
        slack = affine_support(dat)-fixed
        require(slack >= 0, 'Affine support dominates each original fixed-layout diagnostic endpoint')
        minimum = slack if minimum is None else min(minimum, slack)
        for carrier in carriers:
            require(fixed_margin(original, dat, carrier)-fixed <= F(58, 225),
                    'Independent carrier-oscillation endpoint check')
            checks += 1
        if i in (402, 404, 406, 414, 416, 418, 426, 428, 430):
            require(fixed == affine_support(dat) == F(10661, 48600),
                    'Same support is exact on every product-face vertex')
            face_values.append({'index': i, 'fixed_margin': fixed})
    require(checks == 23328 and len(face_values) == 9, 'All original diagnostic endpoints and J vertices')
    rectangles = []
    for delta, rho in ((F(1, 2500), F(1, 100000)), (F(1, 1250), F(1, 100000)),
                       (F(1, 1100), F(1, 100000)), (F(1, 1020), F(1, 100000)),
                       (F(1, 1000), F(0))):
        row = reserve_bound(delta, rho, family)
        require(row['old49_replacement_reserve_lower'] > 0, 'Positive complete reserve on the stated rectangle')
        rectangles.append(row)
    return encode({'schema': 'erdos7-j-affine-margin-reserve-v1', 'source_sha256': pins,
        'domain_delta_plus_rho': F(1, 1000), 'baseline_layout': B, 'five_layout': C,
        'distinguished_carrier': [0, 1], 'affine_constant': -F(1381, 48600),
        'availability_coefficients': [-F(1, 9), 0, 0, 0, 0],
        'source_mass_coefficients': NC, 'width_coefficients': EC,
        'affine_basis_values': basis, 'old49_face_margin': F(10661, 48600),
        'positive_source_linear_price': np, 'source_quadratic_term': nq,
        'availability_price': dp, 'width_price': ep, 'carrier_price': cp,
        'total_linear_price': np+dp+ep+cp, 'rounded_old49_margin_price': F(2),
        'rounded_replacement_delta_price': F(6), 'carrier_oscillation_upper': F(58, 225),
        'diagnostic_carrier_checks': checks, 'minimum_diagnostic_affine_slack': minimum,
        'product_face_values': face_values, 'complete_rectangles': rectangles,
        'scope': 'Ordinary affine-support proof on both whole136 J neighborhoods, delta+rho<=1/1000. The exact original49 identity direction is compared using its actual carrier average; every197 family error, infinite tail and actual residual is unchanged. Endpoint checks are diagnostics, not the proof of the continuous inequality. The reserve replaces only old49 direction40. No full global bound, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_affine_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact affine whole-J reserve')
    print('PASS: whole-J old49 affine margin price2, complete replacement price6 and unchanged infinite errors.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
