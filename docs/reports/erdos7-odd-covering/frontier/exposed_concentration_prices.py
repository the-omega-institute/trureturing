#!/usr/bin/env python3
"""Rational joint prices from six exposed actual concentration inequalities."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/exposed_concentration_prices.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/joint_concentration_loss_budget.py': '41dd03ec2ced1cd33643f2e2955ded85dd2113b633f72f9d5954d6862c2e8fa2', 'certificates/source_norms/joint_concentration_loss_budget.json': '1e8795d2380b186d40a9f4c866bbb5698db269c2055b9159a0d183584f05d725', 'frontier/monotone_product_carrier_mass.py': '4e8dd576a31b445445502e1bd089151919822e70cf57d3a473d4dc29d5f62747'}
ORDER = ('alpha', 'z', 'beta', 'deficit', 'late', 'carrier')


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def price_record(prices, delta):
    delta = F(delta)
    values = tuple(map(F, prices))
    require(0 <= delta < F(1, 2) and len(values) == 6 and min(values) >= 0,
            'Six nonnegative prices and actual orientation domain')
    indices = sorted(range(6), key=lambda i: (-values[i], i))
    ordered = tuple(values[i] for i in indices)
    prefix, rows = F(0), []
    for k, c in enumerate(ordered, 1):
        prefix += c
        coordinate = delta/(k-(k-1)*delta)
        witness = tuple(coordinate if i in indices[:k] else F(0) for i in range(6))
        total = sum(witness)
        require(all(u+(1-delta)*(total-u) <= delta for u in witness), 'Exact outer-polytope vertex')
        value = prefix*coordinate
        require(sum(p*u for p, u in zip(values, witness)) == value, 'Exact price at the vertex')
        rows.append({'active_count': k, 'coordinate': coordinate, 'price_upper': value,
                     'outer_polytope_witness': witness})
    upper = max(row['price_upper'] for row in rows)
    require(upper <= max(values)*delta/(1-delta), 'The exposed envelope improves the old single-budget bound')
    corner = ordered[0] > 0 and ordered[1] <= (1-delta)*ordered[0]
    if corner:
        require(upper == delta*ordered[0], 'The exact nonlinear one-coordinate support when the price gap is sufficient')
    return {'factor_order': ORDER, 'prices': values, 'sorted_indices': indices, 'delta': delta,
            'upper': upper, 'corner_criterion': corner, 'vertices': rows,
            'scope': 'Exact support of the proved outer polytope; nonlinear support is asserted only under corner_criterion.'}


def weighted_loss_upper(prices, delta):
    return price_record(prices, delta)['upper']


def norm_prices(mass_price, pure_price, availability_price):
    n, e, d = map(F, (mass_price, pure_price, availability_price))
    require(min(n, e, d) >= 0, 'Nonnegative original raw-source norm prices')
    return (n/6+d/4, 5*n/36+d/4, n/18+d/4, (n+e)/9, n/36, F(0))


def joint_norm_upper(mass_price, pure_price, availability_price, delta):
    return weighted_loss_upper(norm_prices(mass_price, pure_price, availability_price), delta)


def norm_bounds(delta):
    return {'mass_L1': joint_norm_upper(1, 0, 0, delta),
            'pure_L1': joint_norm_upper(0, 1, 0, delta),
            'availability_Linfinity': joint_norm_upper(0, 0, 1, delta)}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('exposed_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    budget = module('exposed_old_budget', base/'frontier/joint_concentration_loss_budget.py')
    require(budget.calculate(base) == json.loads(io.read_artifact_bytes(base/'certificates/source_norms/joint_concentration_loss_budget.json')),
            'Reconstruct153 actual factors and complete original norm-price conversion')
    algebra = module('exposed_algebra', base/'frontier/monotone_product_carrier_mass.py')
    add, mul, scale = algebra.add, algebra.mul, algebra.scale
    one = {(): F(1)}
    d, l, p = ({(k,): F(1)} for k in ('d', 'l', 'p'))
    minus = lambda q: add(one, scale(q, -1))
    T2 = add(mul(minus(l), minus(p)), mul(l, p))
    T3 = add(mul(mul(minus(d), minus(l)), minus(p)), mul(mul(d, l), p))
    require(add(mul(minus(d), T2), scale(T3, -1)) == mul(add(one, scale(d, -2)), mul(l, p)),
            'Expose one late coordinate with a nonnegative residual T2 relaxation')
    require(add(minus(l), scale(T2, -1)) == mul(p, add(one, scale(l, -2))),
            'Residual pair individually dominates remaining losses before invoking their smaller radius')
    mass_difference = tuple(map(F, ('13/360', '1/36', '1/72', '1/36', '1/180', '2/45')))
    results = []
    for delta in (F(0), F(1, 10000), F(1, 50), F(1, 27), F(1, 20), F(1, 6), F(3, 16), F(1, 3)):
        norms = norm_bounds(delta)
        require(norm_prices(3, 4, 5) == budget.norm_prices(3, 4, 5), 'Original norm prices are unchanged')
        require(norms['pure_L1'] == delta/9 and norms['availability_Linfinity'] == 3*delta/(4*(3-2*delta)),
                'Exact rational pure and availability envelopes')
        if delta <= F(1, 6):
            require(norms['mass_L1'] == delta/6, 'Mass price corner holds through1/6')
        difference = weighted_loss_upper(mass_difference, delta)
        if delta <= F(3, 16):
            require(difference == 2*delta/45, 'Signed source-difference corner holds through3/16')
        records = [price_record(prices, delta) for prices in
                   ((F(1),)*6, norm_prices(1, 0, 0), norm_prices(0, 0, 1), norm_prices(3, 4, 5), mass_difference)]
        require(records[0]['upper'] == 6*delta/(6-5*delta), 'Exact six-way equal-price polytope support')
        combined = joint_norm_upper(3, 4, 5, delta)
        separate = 3*norms['mass_L1']+4*norms['pure_L1']+5*norms['availability_Linfinity']
        require(combined <= separate and (delta == 0 or combined < separate),
                'A genuine joint price improvement, not separate norm maxima')
        results.append({'delta': delta, 'norm_bounds': norms, 'mass_difference_price': difference,
                        'joint_raw_example': combined, 'separately_priced_example': separate, 'price_records': records})
    # Rational two-coordinate witness for necessity of the price-gap condition.
    sigma, epsilon, top, second = F(1, 20), F(1, 1000), F(1), F(24, 25)
    first = (sigma-epsilon)/(1-epsilon)
    require((1-first)*(1-epsilon) == 1-sigma and 0 < first < sigma and epsilon < sigma,
            'Feasible two-coordinate nonlinear slice')
    gain = top*first+second*epsilon-top*sigma
    require(gain == epsilon*(second-top*(1-sigma)/(1-epsilon)) > 0, 'Corner failure when the second price exceeds the threshold')
    return encode({'schema': 'erdos7-exposed-concentration-prices-v1', 'source_sha256': PINS,
                   'examples': results, 'corner_failure_example': {'sigma': sigma, 'losses': (first, epsilon),
                         'prices': (top, second), 'gain': gain},
                   'scope': 'Ordinary six exposed concentration inequalities for0<=sigma<1/2 and exact rational support of their outer polytope. Joint prices add vectors before optimization. Sharpness refers to this polytope, or to the nonlinear relaxation only under the proved price-gap criterion. No original-family attainment, new complete comparison, Lean or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('exposed_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact exposed-price certificate')
    print('PASS: six exposed inequalities, rational joint prices and proved corner criteria.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
