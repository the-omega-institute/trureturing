#!/usr/bin/env python3
"""Consume whole-face vector margins in the complete 52-cost AP comparison.

Use each cost's strongest proved bound, then one simultaneous substitution
in the already certified all-load majorants. Keep the signed mass, square
complements, all tails, and the complete surviving-tail denominator.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/vector_face_complete_ratio.json'
LINEAR = 'certificates/source_norms/endpoint-bounds/vector_marked_face.json'
QUADRATIC = 'certificates/source_norms/moments-survival/quadratic_vector_marked_source.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/vector_marked_face.py': '5dccdefcf9ee3836d62a01da4db3190a17d079351f2edd9eb33c5b684243c38d',
    LINEAR: '5283295effd38457803d6ebef55c09fdefd4656f77bdf86a544630db54b98a60',
    'frontier/moments-survival/quadratic_vector_marked_source.py': '558355784f1334f0ba57c73df492588cc9174c9eb7ea611536f27bc33b752322',
    QUADRATIC: 'd8f9e368de10504974e4d7e6abf98c85bc958764d33b36b4b6085c9cacfd3f40',
    'frontier/endpoint-bounds/k_face_complete_ratio.py': 'e94a6532ff6951d464a224f1a56415aaea90251c520c7b06fc9afe4e6a82c5db',
    'certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json': 'ccb1debedef1dc49cbc6a31e01c712f156992dc238bd0576e4f51ee8dd6f6888',
    'frontier/endpoint-bounds/k_face_surviving_tail_ratio.py': '8939d32f56b42c7d02dbafbf316fdd3c79160d47f3190cc50badbc2277ad5096',
    'certificates/source_norms/endpoint-bounds/k_face_surviving_tail_ratio.json': 'b9c283262fd9c06798d4082f30da570d97926c271768e4790f94be7c6e70cb09',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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


def verify_denominator(previous, old):
    D, L = F(previous['mass']), F(previous['linear_upper'])
    U4, U5 = (F(previous['uniform_hinge_uppers'][str(t)]) for t in (4, 5))
    coeff = {key: F(value) for key, value in previous['denominator_coefficients'].items()}
    lower = coeff['mass']*D-coeff['linear']*L-coeff['hinge4']*U4-coeff['hinge5']*U5
    p = lambda n: F(28, 33) if n == 1 else F(50, 3*11**n)
    ratio = F(1, 11)
    tail0 = F(50, 3)*ratio**5/(1-ratio)
    tail1 = F(50, 3)*ratio**5*(5-4*ratio)/(1-ratio)**2
    interpolate = lambda t: (4-t)*(L-D)/3+(t-1)*U4/3
    complete = D-U4/6-(p(1)*U5+sum(p(n)*n*interpolate(F(5, n)) for n in (2, 3, 4))
                      +tail1*L-5*tail0*D)/7
    require(complete == lower == F(previous['uniform_denominator_lower']) == F(40455251803, 517708422000) > 0,
            'Same positive denominator from the full AP11 expansion and coefficient formula')
    require(encode({'mass': tail0, 'first_moment': tail1}) == previous['full_AP11_tail'] == old['full_AP11_tail'],
            'Every original AP11 tail term is retained')
    return lower


def propagate(majorant, functions, metadata, direct, old_costs, D, L, Q):
    bounds = [L, Q]+list(direct)
    require(tuple(row[0] for row in majorant.MAJORANTS) == tuple(range(2, 54)), 'All52 cost targets, including six raw81 terms')
    proofs, values = [], []
    for target, alpha, terms in majorant.MAJORANTS:
        proof = majorant.verify_majorant(target, F(alpha), [(i, F(w)) for i, w in terms],
                                        functions, metadata, bounds, D)
        proofs.append(proof)
        values.append(min(old_costs[target-2], bounds[target], proof['bound']))
    require(len(proofs) == len(values) == 52 and all(0 <= value <= old for value, old in zip(values, old_costs)),
            'One simultaneous legal substitution preserves every earlier bound')
    return values, proofs


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('vector_ratio_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    old = read('certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json')
    previous = read('certificates/source_norms/endpoint-bounds/k_face_surviving_tail_ratio.json')
    linear = read(LINEAR)
    quadratic = read(QUADRATIC)
    for record in (old, previous, linear, quadratic):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited input: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
            used[path] = pin
    engine = module('vector_ratio_engine', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    for path, pin in engine.pins.items():
        require(path in used and used[path] == pin, 'Every engine input is already pinned')
    source = engine.source
    majorant = module('vector_ratio_majorants', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    specs = engine.specs+engine.quadratic_specs
    require(len(specs) == 46 and linear['schema'] == 'erdos7-vector-marked-face-v1', 'Whole-face linear theorem and complete transformed inventory')
    require(old['faces'] == previous['faces'] and old['mass'] == previous['mass'], 'Same saturated faces and surviving mass')
    require(linear['vertices'] == [['1/4', '0', '0'], ['1/5', '1/20', '0'], ['1/5', '0', '1/20']]
            and linear['constant_geometry']['r'] == '0' and len(linear['relabellings']) == 12,
            'All actual first-beta triangles, both orientations, and r=0')
    D, L = F(old['mass']), F(old['linear_upper'])
    Q = F(old['square_sums']['full_square_upper'])
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(374, 75)), 'Unchanged exact mass and complete moments')
    weights = list(map(F, old['cost_weights']))
    old_costs = list(map(F, old['improved_cost_bounds']))
    residual, square_weight = F(old['signed_mass_coefficient']), F(old['complete_square_weight'])
    old_N = residual*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    require(len(old_costs) == len(weights) == 52 and min(weights) > 0 and residual < 0 < square_weight,
            'All52 positive cost weights, negative mass and complete square complements')
    require(old_N == F(old['numerator_upper']) == F(previous['retained_numerator']['numerator_upper']) > 0,
            'Reconstruct the entire current numerator')
    require(encode(old_costs) == previous['retained_numerator']['cost_upper_bounds']
            and encode(weights) == previous['retained_numerator']['cost_weights'], 'The current comparison uses exactly these52 costs')
    direct = list(old_costs)
    updates = []
    require(len(linear['costs']) == 41, 'All41 linear costs of the whole-face theorem')
    for i, row in enumerate(linear['costs']):
        require(row['index'] == i and row['name'] == specs[i]['name'] and row['tuple'] == specs[i]['tuple']
                and F(row['weight']) == weights[i] == engine.weights[i], 'Same original cost identity, ordering and weight')
        margin = F(row['constant_old_margin'])+F(row['uniform_source_gain'])
        require(F(row['uniform_source_gain']) > 0 and all(F(x) == margin for x in row['vertex_new_minima']),
                'The uniform margin comes from the proved same-branch whole-face theorem')
        C = F(engine.thresholds[i]['constant'])
        bound = C*D-margin
        direct[i] = min(old_costs[i], bound)
        updates.append({'index': i, 'name': row['name'], 'tuple': row['tuple'], 'constant': C,
                        'uniform_new_margin': margin, 'new_cost_bound': bound, 'previous_cost_bound': old_costs[i],
                        'accepted_cost_bound': direct[i], 'weighted_improvement': weights[i]*(old_costs[i]-direct[i])})
    require([r['index'] for r in updates if r['weighted_improvement'] > 0] == [0, 1, 7, 16, 17, 23, 32],
            'Only seven new linear bounds improve the already strengthened current costs')
    linear_direct_gain = sum(r['weighted_improvement'] for r in updates)
    require(linear_direct_gain == F(8627577205613326039286845075631489, 720420499726946075006749800000000000),
            'No duplicate deduction of the full41-cost gain from the current numerator')
    require(quadratic['schema'] == 'erdos7-quadratic-vector-marked-source-v1'
            and quadratic['whole_face']['vertices'] == linear['vertices']
            and quadratic['whole_face']['constant_geometry'] == linear['constant_geometry']
            and quadratic['whole_face']['relabellings'] == linear['relabellings'],
            'The quadratic absolute-margin theorem has the same complete face domain')
    quad_updates = []
    require(len(quadratic['whole_face']['costs']) == 5, 'All five complete quadratic costs')
    for j, row in enumerate(quadratic['whole_face']['costs']):
        i = 41+j
        require(row['index'] == j and row['tuple'] == specs[i]['tuple']
                and F(row['barrier']) == engine.quadratic_constants[j]
                and weights[i] == F(quadratic['comparison_weight']) == source.AC,
                'Same original quadratic cost, barrier and positive comparison weight')
        C, margin = F(row['barrier']), F(row['uniform_absolute_margin_lower'])
        require(all(F(x) == margin for x in row['vertex_new_minima']), 'The whole-face absolute new margin matches all fixed-dual endpoints')
        bound = C*D-margin
        require(bound == F(row['zero_residual_cost_upper']), 'Same saturated-mass quadratic upper bound')
        direct[i] = min(old_costs[i], bound)
        quad_updates.append({'index': i, 'quadratic_index': j, 'tuple': row['tuple'], 'constant': C,
                             'uniform_new_margin': margin, 'new_cost_bound': bound, 'previous_cost_bound': old_costs[i],
                             'accepted_cost_bound': direct[i], 'weighted_improvement': weights[i]*(old_costs[i]-direct[i])})
    require([row['quadratic_index'] for row in quad_updates if row['weighted_improvement'] > 0] == [0, 1, 3],
            'Only quadratic00,01,10 improve the previously strengthened bounds')
    quadratic_direct_gain = sum(row['weighted_improvement'] for row in quad_updates)
    require(quadratic_direct_gain == F(quadratic['weighted_usable_improvement_over84']) > 0,
            'Exactly the independently certified usable quadratic improvement')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    functions = [lambda n, tag=tag: source.zero5_cost(tag, n) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    old_again, _ = propagate(majorant, functions, metadata, old_costs, old_costs, D, L, Q)
    require(old_again == old_costs, 'The old52-cost bound is already stable under this single substitution')
    costs, proofs = propagate(majorant, functions, metadata, direct, old_costs, D, L, Q)
    numerator = residual*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagated_gain = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N-numerator == direct_gain+propagated_gain and numerator > 0 and propagated_gain > 0,
            'All positive numerator improvements are disjoint and the signed identity balances')
    denominator = verify_denominator(previous, old)
    offset = F(previous['offset'])
    require(offset == F(old['offset']) == source.WHOLE_CONST, 'Same fixed comparison offset')
    comparison = offset+numerator/denominator
    old_comparison = F(previous['comparison_upper'])
    require(old_comparison == offset+old_N/denominator and 403 < comparison < old_comparison,
            'The complete face comparison improves but does not reach403')
    return {'schema': 'erdos7-vector-face-complete-ratio-v1', 'source_sha256': used,
            'faces': old['faces'], 'mass': D, 'r': F(0), 'rho': F(0),
            'linear_upper': L, 'square_sums': old['square_sums'],
            'linear_cost_updates': updates, 'quadratic_cost_updates': quad_updates, 'direct_cost_bounds': direct,
            'majorants': proofs, 'improved_cost_bounds': costs, 'cost_weights': weights,
            'signed_mass_coefficient': residual, 'complete_square_weight': square_weight,
            'linear_direct_numerator_gain': linear_direct_gain, 'quadratic_direct_numerator_gain': quadratic_direct_gain,
            'direct_numerator_gain': direct_gain,
            'propagated_numerator_gain': propagated_gain, 'total_numerator_gain': old_N-numerator,
            'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
            'previous_numerator': old_N, 'numerator_upper': numerator,
            'uniform_hinge_uppers': previous['uniform_hinge_uppers'],
            'full_AP11_tail': previous['full_AP11_tail'], 'denominator_coefficients': previous['denominator_coefficients'],
            'uniform_denominator_lower': denominator, 'offset': offset,
            'previous_comparison': old_comparison, 'comparison_upper': comparison,
            'comparison_improvement': old_comparison-comparison,
            'reused_layout_count': previous['reused_joint_layout_checks'],
            'reused_layout_sha256': previous['reused_all_layout_and_dual_sha256'],
            'scope': 'Ordinary proof on both complete actual K-control faces at r=rho=0 and saturated mass53/360. Uses the whole-face linear and quadratic vector theorems, all52 cost bounds and one simultaneous all-load majorant substitution. Retains all signed and tail terms and the complete denominator. No off-face neighborhood, new global K, Lean verification or unrestricted Erdos7 solution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('vector_ratio_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical complete vector face comparison')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: whole-face vector costs, all52 all-load majorants, signed mass, complete square and AP11 tails.')
    print('Numerator '+str(float(F(result['numerator_upper'])))+'; denominator '+str(float(F(result['uniform_denominator_lower'])))
          +'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
