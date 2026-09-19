#!/usr/bin/env python3
"""Joint source prices for the complete seven-containing tails and157 consumer."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/seven_pair_source_prices.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/exposed_concentration_prices.py': '9c2e6d7ea0777df07559c90a506dcd19d40e2af6febadaee7833a0d66b20488a',
    'certificates/source_norms/comparison-bounds/exposed_concentration_prices.json': '4cbde5374198bbf645157ef6bb7765e3b8fed57569cd2c99b85c25741f38fd25',
    'frontier/comparison-bounds/wide_k_signed_tail_comparison.py': '248c4af165fc4e636c4f4a3c61947384afd9128cae6c652b07819e20a55da484',
    'certificates/source_norms/comparison-bounds/wide_k_signed_tail_comparison.json': '4fa3ff52514576814c380e21caaeb2cc9341180815cab34e5b64c8c6e896bade',
}
SOURCE_ORDER = ('s', 'N3', 'N9', 'D', 'h', 'h1', 'eta_max', 'constant')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def dot(a, b):
    require(len(a) == len(b), 'Matching exact coefficient vectors')
    return sum(x*y for x, y in zip(a, b))


def source_prices(delta):
    """One six-loss vector for each original scalar source coordinate."""
    delta = F(delta)
    require(0 <= delta <= F(2, 27), 'Original oriented-source domain')
    require(delta**2+7*delta <= 2, 'Root0 mass stays below the root1 face reference')
    return ((F(1, 12), F(1, 8), F(1, 36), (5+delta)/72, F(1, 72), F(0)),
            (F(1, 12), F(1, 12), F(1, 36), F(1, 72), F(0), F(0)),
            (F(0), F(1, 36), F(0), F(0), F(0), F(0)),
            (F(0), F(1, 4), F(0), F(0), F(0), F(0)),
            (F(0), F(0), F(0), F(1, 18), F(0), F(0)),
            (F(0),)*6, (F(0),)*6, (F(0),)*6)


def raw_coefficients(factorial):
    g = factorial.geometric
    a0, aw, b1, bw1, b2, bw2 = (g(*args) for args in
        ((3, 3), (3, 3, 2, 1), (5, 1), (5, 1, 2, 1), (5, 2), (5, 2, 2, 1)))
    require((a0, aw, b1, bw1, b2, bw2) == (F(1, 18), F(4, 9), F(1, 4), F(7, 8), F(1, 20), F(11, 40)),
            'All complete original geometric series')
    g3, g5 = g(3, 3, 2, -2), g(5, 2, 2, -1)
    linear = (F(1), F(1), F(1), a0, b1, b1, b1, a0*b1)
    square = (F(1), F(3), F(5), aw, bw1, 3*bw1, 5*bw1, aw*bw1)
    O = (F(0), F(0), F(0), g3/5, g5/5, 3*g5/5, g5,
         (F(3, 5)*g3+aw*bw2-6*a0*b2)/5)
    P = tuple((4*q/15-p/5)/2 for p, q in zip(linear, square))
    require(O == tuple(map(F, ('0', '0', '0', '1/18', '7/200', '21/200', '7/40', '49/900'))),
            'Independent original old-positive7 expansion')
    require(P == tuple(map(F, ('1/30', '3/10', '17/30', '29/540', '11/120', '13/40', '67/120', '109/2160'))),
            'Independent original positive7-positive7 expansion, including its negative linear contribution')
    pair = tuple(a+b for a, b in zip(O, P))
    Z = tuple(map(F, ('0', '1/35', '1/5', '1/90', '11/700', '1/20', '1/20', '1/360')))
    face = tuple(map(F, ('1/4', '5/36', '1/12', '3/4', '1/2', '1/3', '1/9', '1')))
    require(min(O+P+pair+Z) >= 0 and (dot(O, face), dot(P, face), dot(pair, face), dot(Z, face)) ==
            (F(121, 720), F(97, 240), F(103, 180), F(779, 12600)),
            'Nonnegative complete coefficients and all exact face values')
    return {'source_order': SOURCE_ORDER, 'face': face, 'old_positive7': O,
            'positive7_positive7': P, 'pair': pair, 'positive7_complement': Z}


def bounds(prices, raw, delta):
    matrix = source_prices(delta)
    pZ = tuple(sum(raw['positive7_complement'][j]*matrix[j][i] for j in range(8)) for i in range(6))
    pF = tuple(sum(raw['pair'][j]*matrix[j][i] for j in range(8)) for i in range(6))
    require(pZ == tuple(map(F, ('1/420', '3/280', '1/1260', '4/3150', '0', '0'))),
            'Whole-source complement price after cancellation')
    require(pF == (F(1, 36), F(13, 180), F(1, 108), (146+5*delta)/10800, F(1, 2160), F(0)),
            'Seven-containing factorial pairs have one combined source price')
    z, pair = prices.price_record(pZ, delta), prices.price_record(pF, delta)
    require(z['corner_criterion'] and pair['corner_criterion']
            and z['sorted_indices'][0] == pair['sorted_indices'][0] == 1,
            'Both exact rational supports use the same exposed z coordinate')
    require(z['upper'] == 3*delta/280 and pair['upper'] == 13*delta/180,
            'Exact156 price values throughout the specified domain')
    return {'delta': delta, 'source_price_matrix': matrix, 'Z_price': z, 'pair_price': pair,
            'Z_upper': F(779, 12600)+z['upper'], 'pair_upper': F(103, 180)+pair['upper']}


def algebra_check(algebra):
    add, mul, scale = algebra.add, algebra.mul, algebra.scale
    one = {(): F(1)}
    a, z, b, d, ell = ({(k,): F(1)} for k in ('a', 'z', 'b', 'd', 'ell'))
    minus = lambda x: add(one, scale(x, -1))
    numerator = add(mul(add(scale(one, 3), z), add(scale(one, 9), d)),
                    scale(mul(minus(a), add(scale(one, 6), scale(d, -1))), -1),
                    scale(mul(minus(b), add(scale(one, 2), scale(d, -1))), -1), scale(minus(ell), -1))
    expanded = add(scale(one, 18), scale(z, 9), scale(a, 6), scale(b, 2), scale(d, 5), ell,
                   mul(d, add(z, scale(a, -1), scale(b, -1))))
    require(numerator == expanded, 'Exact original raw-mass upper polynomial before discarding favorable products')
    return {'cleared_raw_mass_upper': [{'term': k, 'coefficient': v} for k, v in sorted(expanded.items())]}


def consume(prices, previous, bound, raw):
    head = previous['missing_head_completion']
    pair_old = head['factorial_pairs']
    raw_upper = tuple(map(F, pair_old['raw_coefficient_upper']))
    oldF = F(pair_old['old_positive7'])+F(pair_old['positive7_positive7_distinct'])
    require(dot(raw['old_positive7'], raw_upper) == F(pair_old['old_positive7'])
            and dot(raw['positive7_positive7'], raw_upper) == F(pair_old['positive7_positive7_distinct']),
            'Independent reconstruction of both retained157 complete pair terms')
    oldold = F(pair_old['old_old_distinct'])
    require(F(pair_old['tail_distinct_pairs']) == oldold+oldF, 'Exact partition of the old-old and seven-containing tails')
    zsave = F(previous['parameters']['positive7'])-bound['Z_upper']
    fsave = oldF-bound['pair_upper']
    require(zsave > 0 and fsave > 0, 'Both new complete source bounds improve the existing157 inputs')
    den_price = sum(F(r['weight'])*sum(F(a) for a in r['coefficients'].values()) for r in previous['denominator']['costs'])
    mean_price = sum(F(r['weight'])*sum(F(a) for a in r['coefficients'].values()) for r in head['mean_costs'])
    quad_price = sum(F(r['weight'])*sum(F(a) for a in r['coefficients'].values()) for r in head['quadratic_costs'])
    pair_price = sum(F(r['weight'])*F(r['factorial_tail_coefficient']) for r in head['quadratic_costs'])
    # Recover the single-H2 coefficient from the independently pinned 141 data
    # supplied by calculate, not from a hand-written copy of the final total.
    h2_price = F(previous['_single_H2_coefficient'])
    numerator_price = mean_price+h2_price+quad_price
    rows = []
    for old in previous['comparisons']:
        oldN, oldD, offset = map(F, (old['signed_endpoint'], old['denominator_lower'], old['offset']))
        N = oldN-numerator_price*zsave-pair_price*fsave
        d = oldD+den_price*zsave
        require(N > 0 and d > 0, 'Positive exact endpoint and actual denominator')
        target = offset+N/d
        coefficient = F(old['remaining_S_coefficient'])+(target-F(old['comparison_upper']))*(1-F(1, 614922))
        require(coefficient > 0 and F(old['raw_s_coefficient']) > 0 and target < F(old['comparison_upper']),
                'Retained favorable source-mass signs and strict complete improvement')
        az = (target-offset)*den_price+numerator_price
        combined = tuple(az*x+pair_price*y for x, y in zip(bound['Z_price']['prices'], bound['pair_price']['prices']))
        record = prices.price_record(combined, bound['delta'])
        require(record['corner_criterion'] and record['sorted_indices'][0] == 1
                and record['upper'] == az*bound['Z_price']['upper']+pair_price*bound['pair_price']['upper'],
                'The complete signed target pays one combined exposed source price')
        margin = ((target-offset)*oldD-oldN
                  +az*(F(previous['parameters']['positive7'])-F(779, 12600))
                  +pair_price*(oldF-F(103, 180))-record['upper'])
        require(margin == 0 and (target-offset)*d-N == 0, 'Two exact forms of the full signed comparison agree')
        require(old['all_original_indices'] == list(range(52)), 'Unchanged complete52-label inventory')
        rows.append({'name': old['name'], 'signed_endpoint': N, 'denominator_lower': d,
                     'comparison_upper': target, 'previous_comparison_upper': F(old['comparison_upper']),
                     'remaining_S_coefficient': coefficient, 'raw_s_coefficient': F(old['raw_s_coefficient']),
                     'single_joint_source_price': record, 'exact_signed_margin': margin,
                     'original_test_indices': old['all_original_indices']})
    return {'Z_saving': zsave, 'pair_saving': fsave, 'denominator_Z_coefficient': den_price,
            'numerator_Z_coefficients': {'mean11': mean_price, 'single_H2': h2_price, 'joint_quadratic9': quad_price},
            'factorial_pair_coefficient': pair_price, 'old_old_distinct_unchanged': oldold,
            'new_complete_pair_upper': oldold+bound['pair_upper'], 'comparisons': rows,
            'new_original_head_evaluations': 0, 'reused_original_head_evaluations': 9750000}


def calculate(base):
    io = module('pair_price_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    prices = module('pair_exposed', base/'frontier/comparison-bounds/exposed_concentration_prices.py')
    exposed = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/exposed_concentration_prices.json'))
    require(prices.calculate(base) == exposed, 'Exact independently verified156 exposed-price predecessor')
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/wide_k_signed_tail_comparison.json'))
    pins = {**previous['source_sha256'], **exposed['source_sha256'], **PINS}
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete original source closure '+path)
    factorial = module('pair_original_series', base/'frontier/moments-survival/complete_off_face_factorial_tail.py')
    algebra = module('pair_source_polynomial', base/'frontier/source-budgets/monotone_product_carrier_mass.py')
    algebra_record = algebra_check(algebra)
    raw = raw_coefficients(factorial)
    examples = [bounds(prices, raw, d) for d in (F(0), F(1, 50), F(1, 27), F(2, 27))]
    selected = [r for r in examples if r['delta'] == F(previous['delta'])]
    require(len(selected) == 1, 'Exactly the previously certified source radius')
    simple = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/moments-survival/uniform_single_hinge_cost_portfolio.json'))
    previous['_single_H2_coefficient'] = simple['radii'][0]['weighted_coefficients']['H2']
    complete = consume(prices, previous, selected[0], raw)
    return prices.encode({'schema': 'erdos7-seven-pair-source-prices-v1', 'source_sha256': pins,
                          'source_coefficients': raw, 'raw_mass_polynomial': algebra_record,
                          'source_radius_examples': examples, 'complete157_consumer': complete,
                          'scope': 'Ordinary actual-source price vectors for the entire positive-seven complement and both seven-containing factorial pair subseries on0<=sigma<=delta<=2/27. Complete geometric series reconstructed from the original definitions; one156 joint source price in the complete157 signed comparison. Every old-old defect-min tail, finite head, original52 test and the one residual is unchanged. No original-family attainment, new globalK, Lean theorem or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('pair_price_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact original seven-pair source certificate')
    for row in result['complete157_consumer']['comparisons']:
        print('PASS: '+row['name']+' complete K <= '+row['comparison_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
