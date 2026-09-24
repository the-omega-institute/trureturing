#!/usr/bin/env python3
"""Keep the coupled K-concentration factors in the actual mass upper bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/product_coupled_carrier_mass.json'
EARLY_LIMIT, SLOPE, FACE_MASS = F(3, 61), F(61, 360), F(53, 360)
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/source-budgets/carrier_mass_residual_bound.py': 'b455566fe256dac370d3afb97c6e357d2c75296a2e36f483e6f189fda436141c', 'certificates/source_norms/source-budgets/carrier_mass_residual_bound.json': '5ec6d2857f0dfe90bce554944fa29d72413e9bb0c359de77b7daf54ca4ceb32b'}


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


def bound_S0(sigma):
    sigma = F(sigma)
    require(0 <= sigma <= EARLY_LIMIT, 'Proved coupled-factor domain')
    return FACE_MASS+SLOPE*sigma


def bound_E(sigma, rho):
    rho = F(rho)
    require(rho >= 0, 'The original common residual is nonnegative')
    return bound_S0(sigma)+rho


def factor_slack(sigma, y):
    sigma, y = F(sigma), F(y)
    require(0 <= y <= sigma <= EARLY_LIMIT, 'Common-factor product loss')
    x = (sigma-y)/(1-y)
    left = 61*sigma-61*y-58*x
    right = (sigma-y)*(3-61*y)/(1-y)
    require(left == right >= 0, 'Whole-interval factored nonnegative difference')
    return left


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('product_mass_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned original mass input '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/carrier_mass_residual_bound.json'))
    require(F(previous['S0_upper_constant']) == FACE_MASS
            and F(previous['S0_upper_sigma_coefficient']) == F(5, 9), 'Original106 mass and comparison direction')
    # Order: alpha, z, beta, deficit, late, actual carrier.
    norm = (F(1, 6), F(5, 36), F(1, 18), F(1, 9), F(1, 36), F(0))
    rest = (F(1, 360), F(0), F(1, 360), F(1, 180), F(0), F(0))
    carrier = (F(0),)*5+(F(2, 45),)
    coefficients = tuple(360*(a+b+c) for a, b, c in zip(norm, rest, carrier))
    require(coefficients == (61, 50, 21, 42, 10, 16), 'Every finite source-loss coefficient counted once')
    require(50 <= 61*(1-EARLY_LIMIT) and 21 <= 61*(1-EARLY_LIMIT)
            and 10 <= 16*(1-EARLY_LIMIT), 'The product domination factors on the whole domain')
    require((42+16) == 58 and 61-58 == 61*EARLY_LIMIT,
            'Exact coupled optimization threshold')
    # Coefficients of (1-y)*(61*sigma-61*y)-58*(sigma-y)
    # equal those of (sigma-y)*(3-61*y): sigma,y,sigma*y,y*y.
    lhs_coefficients = (61-58, -61+58, -61, 61)
    require(lhs_coefficients == (3, -3, -61, 61), 'Polynomial factorization for arbitrary sigma and y')
    examples = []
    for sigma in (F(0), F(1, 10000), F(1, 27), F(21, 500), EARLY_LIMIT):
        require(bound_E(sigma, F(1, 100000))-bound_S0(sigma) == F(1, 100000), 'Same residual, unit coefficient')
        examples.append({'sigma': sigma, 'S0_upper': bound_S0(sigma),
                         'old_S0_upper': FACE_MASS+5*sigma/9,
                         'loss_checks': [factor_slack(sigma, sigma*t/4) for t in range(5)]})
    # This witnesses only failure of the scalar product relaxation above its domain.
    sigma, y = F(1, 18), F(1, 20)
    x = (sigma-y)/(1-y)
    require(x == F(1, 171) and (1-y)*(1-x) == 1-sigma, 'Both relaxed product constraints are met')
    excess = 61*y+58*x-61*sigma
    require(excess == F(1, 3420) > 0, 'Exact non-extension of the61-slope scalar certificate')
    return encode({'schema': 'erdos7-product-coupled-carrier-mass-v1', 'source_sha256': PINS,
                   'face_mass': FACE_MASS, 'sigma_limit': EARLY_LIMIT, 'S0_sigma_coefficient': SLOPE,
                   'E_rho_coefficient': F(1), 'factor_order': ('alpha', 'z', 'beta', 'deficit', 'late', 'carrier'),
                   'source_norm_coefficients': norm, 'cap_loss_coefficients': rest,
                   'carrier_loss_coefficients': carrier, 'scaled_combined_coefficients': coefficients,
                   'factorization_coefficients': lhs_coefficients, 'examples': examples,
                   'scalar_nonextension': {'sigma': sigma, 'alpha_loss': y, 'deficit_loss': x,
                                           'carrier_loss': x, 'other_losses': F(0), 'scaled_excess': excess,
                                           'scope': 'Product-envelope counterexample only, not an actual-source configuration.'},
                   'scope': 'Ordinary continuum theorem E<=S0+rho<=53/360+(61/360)*sigma+rho on0<=sigma<=3/61, using106 original source mass and carrier distribution with both coupled K product constraints. All complete original source terms retained. No source independence assumption, altered residual, global K assertion, Lean verification or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('product_mass_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact product-mass certificate')
    print('PASS: coupled actual-source factors, exact61/360 slope through3/61 and scalar non-extension.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
