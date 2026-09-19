#!/usr/bin/env python3
"""Transport the two adopted heavy vector controllers over an actual K radius."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/uniform_heavy_vector_neighborhood.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/uniform_k_neighborhood_cost.py': '2868fc48d2b02e889402f7c2cbf89cd4236d28a3d575b53cf3cbdf48cd2dd781',
    'frontier/complete_off_face_cost.py': '6ab17509f6946409cef6b431cdfb316cc35c9055d21de93eb2906c723d93e234',
    'frontier/finite_source_face_transport.py': 'aa4099317ddf1b7cca16df4916166b1399d0b6e44cbe6459dde081075db8d332',
    'frontier/shared_budget_affine_tail.py': '0b0a509626dda7f44ecccf56825c2a3027fce2e4269c64a0419e65da3bce1136',
    'frontier/joint_deep_mean_transport.py': 'a63225e637c6e926e80b04822ab8c83b79f8b99d3069b283375838df69ea4534',
    'frontier/broad_weighted_identity_source.py': 'e0a89669a6b8b6ff732391b4c27dddd21bf5517f8a37928120e75955349dd98f',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/uniform_quadratic_cost_portfolio.py': 'b048b643172621a583e12efbccf0d7a2b64167799b87d2887aa4cbee3058460c',
    'frontier/source_barrier_saturation.py': '92076ee71a6be16655bbe5c2ac223db6502da1ab5c3553a7f83bb555dbbb8363',
    'frontier/full_linear_carrier_frontier.py': '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888',
    'frontier/vector_marked_source.py': 'd4fb958ac95a62a766debf18b8a7079081d922430e471d594725274acf321fbc',
    'certificates/source_norms/vector_marked_face.json': 'e720af09ec258566a14e9f6bb34c8903130748332ac54dc8233dc25d85f707b0',
    'certificates/source_norms/whole_cost_mean_stop_loss.json': 'd535a2f69617536a06655c61a1166813bfd2ce3e17416fc329dcead0ba3201da'}
SIGMA = F(13, 1215)
INDICES = (0, 16)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def project(parameter, first_beta):
    """Fill the root1 beta deficit in its actual first-label cell."""
    beta = [F(0), F(0), *parameter[2][2:]]
    beta[first_beta] += F(1, 4)-sum(beta)
    require(beta[first_beta] >= F(1, 5) and sum(beta) == F(1, 4),
            'The projected beta lies in the whole95 actual first-beta triangle')
    return ((F(1, 2), F(0), F(0), F(0), F(0)), (F(0), F(1, 4)), tuple(beta),
            (F(1, 72), F(0), F(0), F(0), F(0)), F(3, 4))


def raw_price(coefficients, n, eta, availability):
    return (coefficients['mass_L1']*n+coefficients['pure_L1']*eta
            +coefficients['availability_Linfinity']*availability)


def branch_bounds(engine, raw, uniform, index, delta, rho):
    par = uniform.parameters(delta, rho)
    require(par['rbar'] < F(1, 2500) and 3*delta/4 <= F(1, 18),
            'Original91 general-packing domain, including actual r<=5rho')
    source, spec = engine.source, engine.specs[index]
    C = F(engine.thresholds[index]['constant'])
    n, eta, availability = delta/2, delta/9, 3*delta/4
    hplus = F(1, 2)+delta/18
    cap_growth = delta/90+par['v0']/6+par['v1']/3
    budget_growth = sum(par['budget_increments'])+delta/45+3*par['rbar']
    marker_non_H = (14*delta/225+2*SIGMA*availability+cap_growth+budget_growth
                    +16*delta*hplus/135)
    marker_H = 2*delta/225+SIGMA*(18*par['rbar']+2*availability)
    marker_price = max(marker_non_H, marker_H)
    raw_zero = raw.raw35_lipschitz(source, spec['zero'])
    raw_full = raw.raw_source_lipschitz(source, spec['tag'])
    common_price = raw_price(raw_full, n, eta, availability)+raw_price(raw_zero, n, eta, availability)
    branches = []
    for item in spec['layouts']:
        baseline = item['baseline']
        values = tuple(source.zero5_cost(spec['tag'], v) for v in baseline)
        derivative = tuple(source.zero5_cost(spec['tag'], v+1)-source.zero5_cost(spec['tag'], v)
                           for v in baseline)
        v = max(derivative)
        k = max(C-value for value in values)
        require(min(derivative) >= 0 and all(0 <= C-value <= k for value in values),
                'Original nonnegative derivatives and barrier deficits')
        for c5 in source.BASES:
            correction = max(a*b for a, b in zip(derivative, c5))
            score_price = 2*delta*(k/4+correction/10)+2*(k*n+correction*eta/5)
            rest_price = k*availability/18+3*k*eta/4
            old_price = (C*n+common_price+max(map(abs, item['psi']))*n
                         +max(map(abs, item['correction']))*eta
                         +raw_zero['availability_Linfinity']*availability
                         +raw_zero['positive_five_pure_price']*eta+(score_price+rest_price)/5)
            residual_price = max(v, hplus*v/(5*F(241, 22500)))
            error = old_price+v*marker_price+2*SIGMA*k*availability+residual_price*rho
            branches.append({'baseline': baseline, 'positive_five_baseline': c5,
                             'old_branch_error': old_price, 'marker_error': v*marker_price,
                             'selected_deep_shift_error': 2*SIGMA*k*availability,
                             'residual_coefficient': residual_price, 'residual_error': residual_price*rho,
                             'total_error': error})
    require(len(branches) == 100, 'All original fixed branches retained')
    return {'index': index, 'parameters': par, 'barrier': C, 'raw_zero_prices': raw_zero,
            'raw_complete_prices': raw_full, 'common_price': common_price,
            'non_H_cap_growth': cap_growth, 'non_H_budget_growth': budget_growth,
            'non_H_marker_price_per_max_derivative': marker_non_H,
            'H_marker_price_per_max_derivative': marker_H,
            'branches': branches, 'uniform_margin_error': max(row['total_error'] for row in branches)}


def calculate(base):
    io = module('heavy_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    uniform = module('heavy_uniform', base/'frontier/uniform_k_neighborhood_cost.py')
    raw = module('heavy_raw', base/'frontier/uniform_quadratic_cost_portfolio.py')
    engine = module('heavy_engine', base/'frontier/source_barrier_saturation.py').Experiment(base)
    source = engine.source
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/vector_marked_face.json'))
    accepted = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_cost_mean_stop_loss.json'))
    outputs = []
    for delta, rho in ((F(0), F(0)), (F(1, 10000), F(1, 100000))):
        results = []
        for index in INDICES:
            row = branch_bounds(engine, raw, uniform, index, delta, rho)
            prior = old['costs'][index]
            margin = F(prior['constant_old_margin'])+F(prior['uniform_source_gain'])
            face_upper = row['barrier']*F(53, 360)-margin
            require(face_upper == F(accepted['improved_cost_bounds'][index]),
                    'Transport the exact adopted95 controller, not an unadopted mean LP')
            upper = face_upper+row['barrier']*(5*delta/9+rho)+row['uniform_margin_error']
            if not delta and not rho:
                require(upper == face_upper and all(b['total_error'] == 0 for b in row['branches']),
                        'Each branch error vanishes exactly at zero radius')
            row.update({'face_upper': face_upper, 'uniform_upper': upper,
                        'uniform_excess': upper-face_upper, 'weight': engine.weights[index]})
            results.append(row)
        outputs.append({'delta': delta, 'rho_radius': rho, 'results': results,
                        'weighted_upper': sum(r['weight']*r['uniform_upper'] for r in results),
                        'weighted_excess': sum(r['weight']*r['uniform_excess'] for r in results)})
    # Two genuine finite sources test every pointwise branch transport against
    # the already proved91 function; the continuum claim uses the ordinary proof.
    vector = module('heavy_vector', base/'frontier/vector_marked_source.py')
    broad = module('heavy_broad', base/'frontier/broad_weighted_identity_source.py')
    full = module('heavy_full', base/'frontier/full_linear_carrier_frontier.py')
    finite = module('heavy_finite', base/'frontier/finite_source_face_transport.py')
    complete = module('heavy_complete', base/'frontier/complete_off_face_cost.py')
    checks = []
    for height in (12, 15):
        actual = complete.actual_398_case(finite, source, height)
        parameter = actual['parameter']
        projected = project(parameter, 2)
        star = source.data(projected)
        n = sum(abs(a-b) for a, b in zip(actual['dat'][1], star[1]))
        eta = sum(abs(a-b) for a, b in zip(actual['dat'][2], star[2]))
        availability = max(abs(a-b) for a, b in zip(actual['dat'][0], star[0]))
        delta, rho = outputs[1]['delta'], outputs[1]['rho_radius']
        require(n <= delta/2 and eta <= delta/9 and availability <= 3*delta/4
                and actual['defects']['rho'] <= rho, 'Actual finite source lies in the same projected radius')
        for record in outputs[1]['results']:
            index = record['index']
            a = vector.cost_bound(engine, broad, full, parameter, actual['pi'], index,
                                  r=actual['point']['r'], partitions=('three_groups',), details=True)
            b = vector.cost_bound(engine, broad, full, projected, broad.point_carrier(1, 1), index,
                                  partitions=('three_groups',), details=True)
            require('all_branches' in a and 'all_branches' in b, 'Actual finite source passes91 necessary conditions')
            gaps = []
            for current, reference, price in zip(a['all_branches'], b['all_branches'], record['branches']):
                require(current['b'] == reference['b'] == price['baseline']
                        and current['c5'] == reference['c5'] == price['positive_five_baseline'], 'Same original test branch')
                error = price['total_error']-price['residual_error']
                gap = current['new_branch']-reference['new_branch']+error
                require(gap >= 0, 'Actual branch is dominated by its proved source continuity price')
                gaps.append(gap)
            checks.append({'height': height, 'index': index, 'branches': len(gaps), 'minimum_transport_slack': min(gaps)})
    require(len(checks) == 4, 'Four actual independent controller comparisons')
    return uniform.encode({'schema': 'erdos7-uniform-heavy-vector-neighborhood-v1',
                           'source_sha256': PINS, 'indices': INDICES, 'radii': outputs,
                           'actual_source_checks': checks,
                           'scope': 'Ordinary source-uniform continuum transport of the two adopted95 heavy linear controllers on134 actual K neighborhood. All100 original branches per cost, both orientations, the whole first-beta triangle, the actual carrier and one complete residual are retained. Complete raw operator Lipschitz prices include every infinite tail. No new global K, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('heavy_write', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact heavy vector radius certificate')
    print('PASS: both adopted heavy vector bounds '+str([(r['index'], r['uniform_upper']) for r in result['radii'][1]['results']]))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
