#!/usr/bin/env python3
"""Assemble every adopted original cost on the proved actual K neighborhood."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/uniform_complete_k_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/moments-survival/whole_quadratic_same_head.py': '84d7995521352aebd522659d189081eee31dbd200ccb4b1f638e7881d3c145b7', 'certificates/source_norms/moments-survival/whole_quadratic_same_head.json': 'c0f131821927a5aaa8e6e4f1b9fa7ed972ee3c5481e78ff39234f2653a25704f', 'frontier/comparison-bounds/uniform_mean_cost_portfolio.py': 'ac23f83b0b99ff97bbff947826aff3c170aa4279517d3f440550f9277b769238', 'certificates/source_norms/comparison-bounds/uniform_mean_cost_portfolio.json': '3af277a1826a305b8437add5ee0d09105142408de45ac95f6cfa84615d3c3b3b', 'frontier/moments-survival/uniform_ap_survival_denominator.py': '181a1793bd15059074d2998eb820322a3b9c2158bac5edfcb3bc057b7e78f180', 'certificates/source_norms/moments-survival/uniform_ap_survival_denominator.json': '080ecc953d56c722d9026fcc8517fa08dbd67ae7381a5af581c3afc20d48db3a', 'frontier/moments-survival/uniform_quadratic_cost_portfolio.py': '5e0d7a5e1c8412c999739c288dce17a7d9221c0b4944dff6b5e18cb4fe3d55e1', 'certificates/source_norms/moments-survival/uniform_quadratic_cost_portfolio.json': '93e53920ef2d3e8194ed35bb3d62dd1907b3b355545e0e69149230a8ebe082bf', 'frontier/moments-survival/uniform_single_hinge_cost_portfolio.py': 'f4ab355bae0849c45ad4fe5ec300cbd99b68a93a3bfb89723caedc5018f41b81', 'certificates/source_norms/moments-survival/uniform_single_hinge_cost_portfolio.json': '6c726d71fa95860740a742d98ae6441194bb9947b2e5adf62da64ce8f965be71', 'frontier/source-budgets/uniform_heavy_vector_neighborhood.py': '47e4858bc86dd1ff12155e20d84421f1aac7fd45b51fa080c8e3a5fe9016423e', 'certificates/source_norms/source-budgets/uniform_heavy_vector_neighborhood.json': 'b9f9f26b98f4ab84a47c3cc4d002cb166bb402190a6d37ae1017b500dd6afd38', 'frontier/cover-geometry/uniform_square_and_raw81_neighborhood.py': '3d47bd0d7ff5f5c4f8114d02538073de8bc87e455265817e9e9d80ca4bc5a62c', 'certificates/source_norms/cover-geometry/uniform_square_and_raw81_neighborhood.json': 'ef616cedcdd59317eeb75e8c20b4f69ceff69e24573e85c53ad33e4f08658595'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable certificate IO')
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


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical artifact reader')
    io = module('complete_uniform_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    used = dict(PINS)

    def read(name):
        data = json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', f'{name}.json')))
        for path, pin in data['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent source identity '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Verified source input '+path)
            used[path] = pin
        return data

    old = read('whole_quadratic_same_head')
    mean = read('uniform_mean_cost_portfolio')
    den = read('uniform_ap_survival_denominator')
    quad = read('uniform_quadratic_cost_portfolio')
    simple = read('uniform_single_hinge_cost_portfolio')
    heavy = read('uniform_heavy_vector_neighborhood')
    square = read('uniform_square_and_raw81_neighborhood')
    weights = tuple(F(v) for v in old['cost_weights'])
    face_costs = tuple(F(v) for v in old['improved_cost_bounds'])
    require(len(weights) == len(face_costs) == 52 and min(weights) > 0,
            'Every original positive numerator weight retained')
    par = mean['parameters']
    require(par == den['parameters'] == quad['radius_results'][1]['parameters']
            == simple['radii'][1]['parameters'] == square['radius_results'][1]['parameters'],
            'One common source/residual rectangle, including its tail constants')
    require(all(r['parameters'] == par for r in heavy['radii'][1]['results']),
            'Heavy controllers use that same actual-source rectangle')
    delta, rho = F(par['delta']), F(par['rho'])
    require((delta, rho) == (F(1, 10000), F(1, 100000)), 'The proved domain')
    Slo, Shi = F(53, 360)-101*delta/180, F(53, 360)+5*delta/9+rho
    require(Slo == F(den['S_lower']) > 0, 'Correctly directed common mass lower bound')
    rows, groups = {}, []

    def group(name, entries, expected):
        indices, value = [], F(0)
        for index, weight, face, upper in entries:
            weight, face, upper = F(weight), F(face), F(upper)
            require(index not in rows and 0 <= index < 52, 'Disjoint original-label cost partition')
            require(weight == weights[index] and face == face_costs[index] and upper >= face,
                    'Same adopted controller and original outside weight')
            rows[index] = {'index': index, 'group': name, 'weight': weight,
                           'face_upper': face, 'uniform_upper': upper,
                           'weighted_excess': weight*(upper-face)}
            indices.append(index)
            value += weight*upper
        require(value == F(expected), 'Exact original portfolio sum '+name)
        groups.append({'name': name, 'indices': indices, 'weighted_upper': value,
                       'weighted_face_upper': sum(weights[i]*face_costs[i] for i in indices)})

    group('137 eleven mean costs',
          ((r['index'], r['weight'], r['face_upper'], r['selected_support']['upper']) for r in mean['cost_results']),
          mean['shared_portfolio']['upper'])
    q = quad['radius_results'][1]
    qrows = [(r['index'], r['weight'], r['face_upper'], r['selected_support']['upper']) for r in q['joint_cost_results']]
    raw47 = q['retained_raw81_n2']
    qrows.append((47, raw47['weight'], raw47['face_upper'], raw47['uniform_upper']))
    group('140 ten quadratic costs', qrows, q['shared_portfolio']['upper'])
    for name, data, key in [('141 twenty-eight affine/hinge costs', simple['radii'][1], 'cost_results'),
                            ('142 two vector costs', heavy['radii'][1], 'results')]:
        group(name, ((r['index'], r['weight'], r['face_upper'], r['uniform_upper']) for r in data[key]),
              data['weighted_upper'])
    sq = square['radius_results'][1]
    raw46 = sq['raw81']
    group('143 first raw81 cost', [(46, raw46['outside_weight'], raw46['face_upper'], raw46['uniform_upper'])],
          weights[46]*F(raw46['uniform_upper']))
    require(sorted(rows) == list(range(52)) and sum(len(g['indices']) for g in groups) == 52,
            'Exactly52 costs, with no omissions, duplication or untransported face minimum')
    signed, square_weight = F(old['signed_mass_coefficient']), F(old['complete_square_weight'])
    require(signed < 0 < square_weight and square_weight == F(sq['full_square_outside_weight']),
            'The original signed mass and full-square complement')
    Q, Qface = F(sq['square']['full_square_upper']), F(old['complete_square_upper'])
    require(Qface == F(374, 75) and Q >= Qface, 'Complete LCM square retained')
    # A negative coefficient requires a lower bound for actual mass.
    mass_payment = signed*Slo
    positive_costs = sum(g['weighted_upper'] for g in groups)
    N = mass_payment+positive_costs+square_weight*Q
    Nface = signed*F(53, 360)+sum(w*c for w, c in zip(weights, face_costs))+square_weight*Qface
    require(Nface == F(old['numerator_upper']), 'Every zero-radius component reconstructs113 exactly')
    d, dface = F(den['uniform_denominator_lower']), F(den['zero_denominator_lower'])
    tail = den['full_count_tail']
    reconstructed_d = (1-F(tail['remaining_S_coefficient'])/7)*Slo
    reconstructed_d -= F(den['shared_finite_cost']['upper'])+F(tail['remaining_H1_coefficient'])*F(den['H1']['upper'])/7
    require(d == reconstructed_d > 0 and dface == F(old['uniform_denominator_lower']),
            'Four AP11 blocks, independent AP13 and complete count tails, with positive division')
    offset = F(old['offset'])
    upper, face_upper = offset+N/d, offset+Nface/dface
    require(N > 0 and N > Nface and d < dface and face_upper == F(old['comparison_upper']),
            'Positive numerator upper and exact zero-radius complete comparison')
    require(403 < upper < 461, 'Complete local comparison below461, still above the403 sufficient target')
    excess_parts = {g['name']: g['weighted_upper']-g['weighted_face_upper'] for g in groups}
    excess_parts['signed_mass'] = signed*(Slo-F(53, 360))
    excess_parts['complete_square'] = square_weight*(Q-Qface)
    require(all(v >= 0 for v in excess_parts.values()) and sum(excess_parts.values()) == N-Nface,
            'All changes accounted once with the correct sign')
    numerator_effect, denominator_effect = (N-Nface)/d, Nface*(dface-d)/(d*dface)
    require(upper-face_upper == numerator_effect+denominator_effect,
            'Exact attribution of neighborhood loss, without cross-source reserve transfer')
    return encode({'schema': 'erdos7-uniform-complete-k-comparison-v1', 'source_sha256': used,
                   'parameters': par, 'original_slot_bound': F(1, 520), 'cost_count': 52,
                   'mass_lower': Slo, 'mass_upper': Shi, 'signed_mass_coefficient': signed,
                   'signed_mass_upper': mass_payment, 'cost_results': [rows[i] for i in range(52)],
                   'cost_groups': groups, 'positive_cost_sum': positive_costs,
                   'complete_square_weight': square_weight, 'complete_square_upper': Q,
                   'complete_square_payment': square_weight*Q, 'numerator_upper': N,
                   'zero_numerator_upper': Nface, 'numerator_excess_by_component': excess_parts,
                   'uniform_denominator_lower': d, 'zero_denominator_lower': dface,
                   'offset': offset, 'comparison_upper': upper, 'zero_comparison_upper': face_upper,
                   'neighborhood_comparison_loss': upper-face_upper,
                   'numerator_effect_on_comparison': numerator_effect,
                   'denominator_effect_on_comparison': denominator_effect,
                   'gap_above403': upper-403, 'room_below461': 461-upper,
                   'scope': 'All52 original independently labelled costs, signed actual mass, full LCM square and complete AP11/AP13 denominator on both actual K source neighborhoods sigma<=1e-4,rho<=1e-5,r<=1/520. Whole beta faces and all exponent/count tails retained. Component certificates and ordinary proofs are prerequisites, not re-proved by aggregation. No untransported face-only minima, global K improvement, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('complete_uniform_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete52-term certificate')
    print('PASS: every original52-term input, signed mass, complete square and positive denominator.')
    print('Complete local comparison: '+str(float(F(result['comparison_upper']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
