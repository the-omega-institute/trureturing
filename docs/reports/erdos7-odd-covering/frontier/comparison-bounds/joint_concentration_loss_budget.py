#!/usr/bin/env python3
"""One actual K-concentration budget for six source/carrier factor losses."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/joint_concentration_loss_budget.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/source-budgets/monotone_product_carrier_mass.py': '320fb41c8422ac579e18563d2f776470d9caf109ff5cd84248080b5f285160ac', 'frontier/source-budgets/carrier_mass_residual_bound.py': 'b455566fe256dac370d3afb97c6e357d2c75296a2e36f483e6f189fda436141c'}
ORDER = ('alpha', 'z', 'beta', 'deficit', 'late', 'carrier')


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


def total_loss_upper(delta):
    delta = F(delta)
    require(0 <= delta < F(1, 2), 'The actual orientation domain')
    return delta/(1-delta)


def weighted_loss_upper(prices, delta):
    values = tuple(map(F, prices))
    require(len(values) == 6 and min(values) >= 0, 'One nonnegative price per actual factor loss')
    return max(values)*total_loss_upper(delta)


def norm_prices(mass_price, pure_price, availability_price):
    n, e, d = map(F, (mass_price, pure_price, availability_price))
    require(min(n, e, d) >= 0, 'Nonnegative complete raw-source prices')
    return (n/6+d/4, 5*n/36+d/4, n/18+d/4, (n+e)/9, n/36, F(0))


def norm_bounds(delta):
    t = total_loss_upper(delta)
    return {'mass_L1': t/6, 'pure_L1': F(delta)/9, 'availability_Linfinity': t/4,
            'carrier_mass_minus_raw_mass_increase_without_rho': 2*t/45}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('joint_loss_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned concentration input '+path)
    algebra = module('joint_loss_polynomials', base/'frontier/source-budgets/monotone_product_carrier_mass.py')
    add, scale, mul = algebra.add, algebra.scale, algebra.mul
    one = {(): F(1)}
    ud, ul, up = ({(k,): F(1)} for k in ('deficit', 'late', 'carrier'))
    product = mul(mul(add(one, scale(ud, -1)), add(one, scale(ul, -1))), add(one, scale(up, -1)))
    t = add(product, mul(mul(ud, ul), up))
    B = add(ud, ul, up, scale(mul(ud, ul), -1), scale(mul(ud, up), -1), scale(mul(ul, up), -1))
    require(t == add(one, scale(B, -1)), 'Both orientation contributions cancel the cubic term exactly')
    N = norm_prices(1, 0, 0)
    E = norm_prices(0, 1, 0)
    D = norm_prices(0, 0, 1)
    R = (F(1, 360), F(0), F(1, 360), F(1, 180), F(0), F(0))
    carrier = (F(0),)*5+(F(2, 45),)
    mass_difference = tuple(n/5+r+c for n, r, c in zip(N, R, carrier))
    require(max(N) == F(1, 6) and max(D) == F(1, 4) and max(mass_difference) == F(2, 45),
            'Exact largest factor prices; no sum of six separate worst losses')
    examples = []
    for delta in (F(0), F(1, 10000), F(1, 50), F(1, 27), F(2, 27), F(1, 4)):
        values = []
        for j in range(5):
            y = delta*j/4
            combined = y/(1-y)+(delta-y)/((1-y)*(1-delta))
            require(combined == total_loss_upper(delta), 'Exact cancellation of the auxiliary common loss y')
            values.append(combined)
        examples.append({'delta': delta, 'total_loss_upper': total_loss_upper(delta),
                         'norm_bounds': norm_bounds(delta),
                         'old_mass_L1_bound': delta/2, 'old_availability_bound': 3*delta/4,
                         'old_mass_difference_bound_without_rho': 7*delta/45,
                         'auxiliary_y_checks': values})
    require((F(3, 4)*F(9, 2)-F(1, 4)*3-F(1, 4))/9-F(1, 72) == F(1, 4),
            'Independent global raw-source mass floor from the original budget caps')
    return encode({'schema': 'erdos7-joint-concentration-loss-budget-v1', 'source_sha256': PINS,
                   'factor_order': ORDER, 'mass_norm_prices': N, 'pure_norm_prices': E,
                   'availability_norm_prices': D, 'mass_difference_prices': mass_difference,
                   'two_orientation_polynomial': [{'term': k, 'coefficient': v} for k, v in sorted(t.items())],
                   'raw_source_mass_lower': F(1, 4), 'examples': examples,
                   'scope': 'Ordinary actual-source theorem sum of the six K-concentration factor losses<=sigma/(1-sigma) for0<=sigma<1/2, using both original orientation contributions and the same carrier law. Norm corollaries use the valid actual first-beta projection. Positive price vectors may be combined before taking their maximum. No sharpness, source-TV, new globalK, Lean or unrestricted Erdos7 claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_loss_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact joint concentration budget certificate')
    print('PASS: actual six-factor budget, complete source norm prices and raw mass floor.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
