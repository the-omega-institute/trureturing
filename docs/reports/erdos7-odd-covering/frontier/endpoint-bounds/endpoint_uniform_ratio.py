#!/usr/bin/env python3
"""Reuse the52 exact cost majorants with square114/25 and actual survival.

All costs, signed barriers, independent original tests and complete AP tails
are retained. The denominator is the uniform endpoint bound of profile67.
This is not a global source-domain comparison or a Lean theorem.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_uniform_ratio.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/endpoint-bounds/endpoint_numerator_common_costs.py': '1b665058c35f8aaadc60d4513939e6c4255cff212b6289d8c0e3beb7bd1d02d6',
    'certificates/source_norms/endpoint-bounds/endpoint_numerator_common_costs.json': '75154048adef87983ab5c776537f73e74f9864714b5cc24b54bfa674dcca26f6',
    'frontier/endpoint-bounds/endpoint_square_positive5.py': 'e6d4a2ae2ac9f369048603d328da7e73cb719e9a622c2a6633ddd61e5609b00d',
    'certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json': 'feb9333e4714f3408029d9e24711fb2886d016c0c4265c0f039ab99419b99405',
    'frontier/endpoint-bounds/endpoint_survival_scalar_barrier.py': '10e915082ee01cef1219125367fd455374c82c98d812654cc4283b2fe7ac3358',
    'certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json': 'a4a4092e9d198b126b85afe96d00b399105a35e73c1e309f3d364e19633ec430',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
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


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('uniform_ratio_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    prior = read('certificates/source_norms/endpoint-bounds/endpoint_numerator_common_costs.json')
    square = read('certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json')
    survival = read('certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json')
    for previous in (prior, square, survival):
        require(previous['source_vertex'] == 404 and previous['carrier'] == [0, 1], 'Identical actual endpoint class')
        for path, pin in previous['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    D, L = F(prior['mass']), F(prior['linear_upper'])
    Qold, Q = F(prior['square_upper']), F(square['full_square_upper'])
    delta = Qold-Q
    require((D, L, Qold, Q, delta) == (F(3, 20), F(1157, 1800), F(469, 100), F(114, 25), F(13, 100)), 'Fixed mass, first moment and new square gain')
    require(F(square['surviving_mass']) == F(survival['mass']) == D and square['barrier'] == 45, 'Same mass and square barrier45')
    source = module('uniform_ratio_source', base/'verify_joint_frontier.py')
    schedule = module('uniform_ratio_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('uniform_ratio_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    majorant = module('uniform_ratio_majorant', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    require(len(specs) == 46, 'Complete AP transformed cost inventory')
    old49 = read('certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    row = next(r for group in old49['frontier']['row_blocks'] for r in group if r['index'] == 404)
    records = row['linear_directions']+row['quadratic_directions']
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    bounds = [F(v) for v in prior['universal_cost_constraint_bounds']]
    require(len(bounds) == len(tags) == 54 and bounds[:2] == [L, Qold], 'All54 original constraints and order')
    bounds[1] = Q
    functions = [lambda v, tag=tag: source.zero5_cost(tag, v) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    require(tuple(entry[0] for entry in majorant.MAJORANTS) == tuple(range(2, 54)), 'All52 unchanged rational majorants')
    finite, tails = source.ap_product_distribution(schedule.CAPS, 9)
    raw = [(n, pn) for n, pn in sorted(finite.items()) if n < 7]
    require([n for n, _ in raw] == list(range(1, 7)), 'All six raw81 low terms')
    weights = [F(r['weight']) for r in records[:41]]+[source.AC]*5+[pn*n*n for n, pn in raw]
    require(len(weights) == 52 and min(weights) > 0, 'Every comparison coefficient is positive')
    rows, costs, slopes = [], [], []
    proof_digest = sha256()
    for i, (target, alpha, multipliers) in enumerate(majorant.MAJORANTS):
        multipliers = [(j, F(value)) for j, value in multipliers]
        proof = majorant.verify_majorant(target, F(alpha), multipliers, functions, metadata, bounds, D)
        require(proof['target'] == target == i+2, 'Identical majorant target order')
        old_proof = prior['majorants'][i]
        require(old_proof['target'] == target and F(old_proof['mass_coefficient']) == F(alpha)
                and [(j, F(v)) for j, v in old_proof['weights']] == multipliers, 'Unchanged exact dual coefficients')
        slope = sum(w for j, w in multipliers if j == 1)
        require(F(old_proof['bound'])-proof['bound'] == slope*delta, 'Exact cost sensitivity to the square cap')
        old_cap = F(prior['universal_cost_constraint_bounds'][target])
        old_cost = F(prior['new_cost_bounds'][i])
        cost = min(bounds[target], proof['bound'])
        require(old_cost == min(old_cap, F(old_proof['bound'])), 'Retain the old min branch exactly')
        if slope > 0:
            require(F(old_proof['bound']) <= old_cap, 'Sensitive majorant was already active throughout the square interval')
        require(old_cost-cost == slope*delta and cost >= 0, 'Exact positive improvement after min with the old cap')
        costs.append(cost)
        slopes.append(slope)
        proof_digest.update(json.dumps(encode(proof), separators=(',', ':'), sort_keys=True).encode())
        rows.append({'target': target, 'square_multiplier': slope, 'comparison_weight': weights[i],
                     'old65_upper': old_cost, 'new_upper': cost, 'weighted_numerator_gain': weights[i]*(old_cost-cost)})
    oQ = F(read('certificates/source_norms/source-budgets/shared_source_deficits.json')['source_profiles']['quadratic_tail_weight'])
    H16, H41, A81, cG = (F(old49[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    require(oQ == F(1600217, 12882870), 'Complete transformed-square complement')
    require(cG == tails[2]+sum(pn*n*n for n, pn in finite.items() if n in (7, 8)), 'Raw81 includes7,8 and the full n>=9 tail')
    square_margin = 45*D-Q
    require(square_margin == F(219, 100), 'Unchanged signed square barrier45')
    M41 = sum(F(r['weight'])*(F(r['constant'])*D-costs[i]) for i, r in enumerate(records[:41]))
    Mquad = sum(F(records[i]['constant'])*D-costs[i] for i in range(41, 46))+oQ*square_margin
    raw81 = sum(pn*n*n*costs[46+k] for k, (n, pn) in enumerate(raw))
    N = (source.AC*H16+H41+A81)*D-source.AC*Mquad-M41-cG*square_margin+raw81
    direct_slope = source.AC*oQ+cG
    total_slope = direct_slope+sum(w*s for w, s in zip(weights, slopes))
    residual = F(prior['positive_cost_residual_slope'])
    expanded = residual*D+sum(w*c for w, c in zip(weights, costs))+direct_slope*Q
    Nold = F(prior['numerator_upper'])
    require(N == expanded == Nold-total_slope*delta, 'Signed comparison, positive cost expansion and full sensitivity agree')
    gains = {'linear41': sum(r['weighted_numerator_gain'] for r in rows[:41]),
             'quadratic5_and_complement': sum(r['weighted_numerator_gain'] for r in rows[41:46])+source.AC*oQ*delta,
             'six_raw81_costs': sum(r['weighted_numerator_gain'] for r in rows[46:]),
             'raw81_square_tail': cG*delta}
    require(min(gains.values()) >= 0 and sum(gains.values()) == Nold-N, 'Four disjoint complete numerator gain groups')
    denominator = F(survival['exact_AP11_optimal_scalar_denominator'])
    offset = F(prior['offset'])
    require(denominator == F(4067559874193, 52947452250000) > 0 and offset == source.WHOLE_CONST, 'Uniform actual endpoint denominator and unchanged offset')
    ratio = offset+N/denominator
    prior_ratio = offset+Nold/denominator
    required = N/(403-offset)
    # Both laws from67 remain feasible after the stronger square cap. This
    # preserves its sharp scalar obstruction without asserting actual layouts.
    augmented_functions = functions+[lambda v, t=t: max(F(v)-t, F(0)) for t in (F(5, 2), F(4), F(5))]
    augmented_bounds = bounds+[F(v) for v in survival['original53_hinge_uppers']]
    primal_checks = {}
    for name, law in survival['laws'].items():
        support = [(v, F(mass)) for v, mass in law['support']]
        slacks = [cap-sum(mass*fn(v) for v, mass in support) for fn, cap in zip(augmented_functions, augmented_bounds)]
        require(min(slacks) >= 0, 'Updated57 scalar constraints still admit both67 primal laws')
        primal_checks[name] = {'square_slack': Q-F(law['second_moment']), 'minimum_constraint_slack': min(slacks)}
    require(403 < ratio < prior_ratio and required > denominator, 'Strict endpoint ratio gain with an explicit remaining gap')
    return {'schema': 'erdos7-endpoint-uniform-ratio-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': used, 'mass': D, 'first_moment_upper': L, 'old_square_upper': Qold,
            'square_upper': Q, 'square_gain': delta, 'signed_square_margin': square_margin,
            'cost_rows': rows, 'all52_majorants_sha256': proof_digest.hexdigest(),
            'square_direct_coefficient': direct_slope, 'complete_square_sensitivity': total_slope,
            'sensitive_cost_count': sum(s > 0 for s in slopes), 'M41': M41, 'Mquad': Mquad,
            'raw81': raw81, 'complete_raw81_square_coefficient': cG,
            'positive_cost_residual_slope': residual, 'numerator_gain_components': gains,
            'old65_numerator': Nold, 'numerator_upper': N, 'total_numerator_gain': Nold-N,
            'uniform_actual_endpoint_denominator': denominator, 'offset': offset,
            'endpoint_comparison_upper': ratio, 'old65_with_same_actual_denominator': prior_ratio,
            'endpoint_comparison_gain': prior_ratio-ratio,
            'required_denominator_for403': required, 'denominator_gap_to403': required-denominator,
            'updated_scalar_primal_feasibility': primal_checks,
            'scope': ('Uniform endpoint comparison using square114/25, all52 unchanged rational majorants '
                      'and profile67 actual survival denominator. No tensor denominator substitution, '
                      'global source-domain K, finite neighborhood upgrade or Lean verification.')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('uniform_ratio_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical complete endpoint comparison')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:52 unchanged all-load majorants, complete square sensitivity, signed barriers and full AP tails.')
    print('Uniform endpoint numerator '+str(float(F(result['numerator_upper'])))+
          '; ratio with actual uniform survival '+str(float(F(result['endpoint_comparison_upper'])))+'.')
    print('This is an endpoint comparison; the global source-domain K certificate is unchanged.')


if __name__ == '__main__':
    main()
