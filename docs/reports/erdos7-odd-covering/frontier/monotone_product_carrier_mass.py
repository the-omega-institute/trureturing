#!/usr/bin/env python3
"""Cancel signed source changes before optimizing coupled K-product losses."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/monotone_product_carrier_mass.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/product_coupled_carrier_mass.py': 'b6b7a61906ca5210ba0cb55f207d9d8221089bc65b92a1662820c2dd69966f3c', 'certificates/source_norms/product_coupled_carrier_mass.json': 'add39ab619b7574d236b9e823467313137c3c5b020cf895960d3db0c1513d301'}
EARLY_LIMIT, SLOPE, FACE_MASS = F(6, 49), F(1, 10), F(53, 360)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
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


def bound_S0(sigma):
    sigma = F(sigma)
    require(0 <= sigma <= EARLY_LIMIT, 'Proved monotone product domain')
    return FACE_MASS+SLOPE*sigma


def bound_E(sigma, rho):
    rho = F(rho)
    require(rho >= 0, 'The same actual residual')
    return bound_S0(sigma)+rho


def add(*polys):
    result = {}
    for p in polys:
        for term, value in p.items():
            result[term] = result.get(term, F(0))+value
    return {k: v for k, v in result.items() if v}


def scale(p, c):
    return {k: F(c)*v for k, v in p.items() if c*v}


def mul(p, q):
    return add(*({tuple(sorted(a+b)): x*y} for a, x in p.items() for b, y in q.items()))


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('monotone_mass_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    previous = module('monotone_mass_predecessor', base/'frontier/product_coupled_carrier_mass.py')
    old = previous.calculate(base)
    require(F(old['face_mass']) == FACE_MASS, 'Unchanged actual-source mass and coupled product inputs')
    one = {(): F(1)}
    ua, uz, ub, ud, ul, up = ({(k,): F(1)} for k in ('alpha', 'z', 'beta', 'deficit', 'late', 'carrier'))
    z = add(scale(one, F(3, 4)), scale(uz, F(1, 4)))
    w0 = add(scale(one, F(1, 2)), scale(ud, F(1, 2)))
    alpha = scale(add(one, scale(ua, -1)), F(1, 4))
    beta = scale(add(one, scale(ub, -1)), F(1, 4))
    late = scale(add(one, scale(ul, -1)), F(1, 72))
    a = add(scale(one, F(4, 5)), scale(up, F(1, 5)))
    remaining_n = add(scale(z, F(4, 9)), scale(alpha, F(-1, 3)), scale(beta, F(-1, 9)))
    rest = add(scale(z, F(1, 18)), scale(add(scale(one, F(9, 2)), scale(ud, F(1, 2))), F(1, 36)),
               scale(one, F(3, 36)+F(1, 36)+F(1, 72)))
    bound = add(scale(mul(w0, z), F(1, 9)), scale(late, -1), mul(a, remaining_n), scale(rest, F(-1, 5)))
    scaled_excess = scale(add(bound, scale(one, -FACE_MASS)), 360)
    expected = {('alpha',): F(24), ('z',): F(36), ('beta',): F(8), ('deficit',): F(14),
                ('late',): F(5), ('carrier',): F(16), ('deficit', 'z'): F(5), ('carrier', 'z'): F(8),
                ('alpha', 'carrier'): F(6), ('beta', 'carrier'): F(2)}
    require(scaled_excess == expected, 'Exact symbolic expansion of the signed original source formula')
    width_margin = F(4, 5)*F(1, 4)/9-F(3, 180)
    availability_margin = F(4, 5)*F(1, 2)/9-F(1, 90)
    require((width_margin, availability_margin) == (F(1, 180), F(1, 30)),
            'Strict coordinate monotonicity pays all max-function cap changes')
    require(24+6*EARLY_LIMIT <= 36*(1-EARLY_LIMIT)
            and 8+2*EARLY_LIMIT <= 36*(1-EARLY_LIMIT)
            and 5 <= 16*(1-EARLY_LIMIT), 'Whole-domain product compression guards')
    # Multiply the coupled envelope difference by1-y and compare coefficients
    # for sigma,y,sigma*y,y*y. This is an exact polynomial identity.
    require((36-30, -36+30, -36-13, 36+13) == (6, -6, -49, 49),
            '(1-y)*(36sigma-36y)-(30+13y)*(sigma-y)=(sigma-y)*(6-49y)')
    checks = []
    for sigma in (F(0), F(1, 10000), F(1, 100), F(21, 500), F(3, 61), F(2, 27), EARLY_LIMIT):
        slacks = []
        for j in range(5):
            y = sigma*j/4
            x = (sigma-y)/(1-y)
            slack = 36*sigma-(36*y+(30+13*y)*x)
            require(slack == (sigma-y)*(6-49*y)/(1-y) >= 0, 'Exact factorized envelope')
            slacks.append(slack)
        checks.append({'sigma': sigma, 'S0_upper': bound_S0(sigma), 'factor_slacks': slacks})
    sigma, y = F(1, 8), F(123, 1000)
    x = (sigma-y)/(1-y)
    obstruction = 36*y+(30+13*y)*x-36*sigma
    require(x == F(2, 877) and (1-y)*(1-x) == 1-sigma and obstruction == F(27, 438500) > 0,
            'Exact non-extension witness for the reduced two-product relaxation only')
    return encode({'schema': 'erdos7-monotone-product-carrier-mass-v1', 'source_sha256': PINS,
                   'face_mass': FACE_MASS, 'sigma_limit': EARLY_LIMIT, 'S0_sigma_coefficient': SLOPE,
                   'E_rho_coefficient': F(1), 'width_monotonicity_margin': width_margin,
                   'availability_monotonicity_margin': availability_margin,
                   'signed_source_expansion': [{'term': k, 'scaled_coefficient': v} for k, v in sorted(scaled_excess.items())],
                   'examples': checks,
                   'scalar_nonextension': {'sigma': sigma, 'common_z_loss': y, 'deficit_and_carrier_loss': x,
                                           'scaled_excess': obstruction,
                                           'scope': 'Only a two-product relaxation witness; actual qK constraints may exclude it.'},
                   'scope': 'Ordinary theorem S0<=53/360+sigma/10 and E<=S0+rho on0<=sigma<=6/49. Uses monotonicity of the same full carrier mass formula to remove nonselected source losses before expanding and compressing two coupled products. No probabilistic independence, second residual, global comparison, Lean or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('monotone_mass_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact monotone product-mass certificate')
    print('PASS: signed source cancellation, monotone coordinate prices and1/10 slope through6/49.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
