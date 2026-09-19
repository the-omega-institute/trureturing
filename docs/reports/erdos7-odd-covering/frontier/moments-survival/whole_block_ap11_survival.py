#!/usr/bin/env python3
"""Combine AP11 count outcomes while retaining each original block test.

Each finite block objective uses one source layout across its hinges.
The complete count tail is summed before any comparison is evaluated.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/whole_block_ap11_survival.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/whole_cost_common_stop_loss.py': 'a43c2d8ec4228d1a58e8d8511db17f91c8f47470c0114460656be59ccfce2327',
    'certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json': '8d2770aa7147105fe03c4428293b588feae64b140afe80585583c786146bbbc5',
    'frontier/moments-survival/whole_face_second_factorial_tail.py': '22719d229784f56d72ec22037163756f520fe46b4fa8eafc353eff14ace7f49e',
    'certificates/source_norms/moments-survival/whole_face_second_factorial_tail.json': 'cae2588d128708ece05769b2162b189fadb2bf222c746f43388e49d97ab587c4',
    'frontier/moments-survival/whole_face_ap11_survival.py': '73547fa6455e9e3c613f3c7166537c1f048177998c611ade97996720a549cf76',
    'certificates/source_norms/moments-survival/whole_face_ap11_survival.json': '17259c5e49d417f5fa58dc794ac3a2447e3f5c7396447ef5dccf89ce4b0f1a16',
}


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require('certificate_io.py' in PINS, 'Completed source pins')
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('ap11_block_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name)))
    previous = read('whole_face_second_factorial_tail.json')
    stop, survival = read('whole_face_stop_loss_generator.json'), read('whole_face_ap11_survival.json')
    for prior in (previous, stop, survival):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited source')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    common = module('ap11_block_common', base/'frontier/comparison-bounds/whole_cost_common_stop_loss.py')
    bridge = module('ap11_block_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    law = module('ap11_block_law', base/'frontier/moments-survival/whole_face_ap11_survival.py')
    source = module('ap11_block_source', base/'verify_joint_frontier.py')
    U = {int(t): F(v) for t, v in previous['uniform_hinge_uppers'].items()}
    D, L = F(previous['mass']), F(previous['linear_upper'])
    require(previous['r'] == previous['rho'] == '0' and D == F(53, 360) and U[1] == L-D,
            'Both complete saturated faces and the original first moment')
    probabilities = {n: source.ap_count_probability(11, F(5, 3), n) for n in range(1, 5)}
    identities = {n: law.integer_hinge_identity(n)['hinge_coefficients'] for n in range(1, 5)}
    tail0, tail1 = tuple(F(50, 3)*x for x in source.geom(11, 5)[:2])
    require((tail0, tail1) == (F(5, 43923), F(17, 29282))
            and sum(probabilities.values())+tail0 == 1
            and sum(n*p for n, p in probabilities.items())+tail1 == F(7, 6), 'Entire original AP11 count law')
    problem = common.CommonHead(bridge, stop)
    records, coefficients = [], []
    for e in range(4):
        # h1 accounts for the entire n>=5 tail for this fixed original block.
        coeff = {t: sum(probabilities[n]*F(identities[n].get(t, 0), n) for n in range(e+1, 5))
                 +(tail0 if t == 1 else 0) for t in (1, 2, 3, 5)}
        old = sum(c*U[t] for t, c in coeff.items())
        row = {'index': e, 'expansion': {'at_one': F(0), 'first_difference': coeff[1],
                    'curvatures': {str(t): c for t, c in coeff.items() if t > 1}, 'cost_upper': old}}
        records.append(problem.prepare(row, D, U[1], old))
        coefficients.append(coeff)
    active = [r for r in records if r['status'] == 'enumerate']
    require([r['index'] for r in active] == [0, 1]
            and all(r['status'] == 'homogeneous-single-hinge' for r in records[2:]),
            'Exactly two distinct mixed-curvature block objectives require new maxima')
    best, witnesses, ties, count, digest = {}, {}, {0: 0, 1: 0}, 0, sha256()
    extras = [(root, slot, problem.extra(root, slot)) for root, slot in product(range(2), range(5))]
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        for root, slot, extra in extras:
            for row in active:
                e = row['index']
                value, detail = problem.objective(row, B, extra)
                digest.update(json.dumps([li, root, slot, e, value], separators=(',', ':')).encode())
                count += 1
                if e not in best or value > best[e]:
                    best[e], ties[e] = value, 1
                    witnesses[e] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot, **detail}
                elif value == best[e]:
                    ties[e] += 1
    require(count == 250000, 'Every original head/projection for both new block objectives')
    results, block_bounds = [], []
    for row, coeff in zip(records, coefficients):
        e = row['index']
        bound = row['old_bound'] if e not in best else row['affine_bound']+row['factor']*F(best[e], common.TOTAL)
        require(0 <= bound <= row['old_bound'], 'Same-test subadditivity improves or preserves each original block')
        block_bounds.append(bound)
        result = {k: v for k, v in row.items() if k not in ('head', 'increments')}
        result.update({'hinge_coefficients': coeff, 'block_upper': bound,
                       'denominator_gain': (row['old_bound']-bound)/7})
        if e in best:
            result.update({'maximizing_witness': witnesses[e], 'maximizer_count': ties[e]})
        results.append(result)
    require([r['denominator_gain'] for r in results]
            == [F(3268, 19370043), F(68347, 542361204), F(0), F(0)], 'Two exact positive block gains')
    # For e>=4 all terms are affine. Sum their coefficients and the whole
    # constant contribution analytically; no reciprocal-count tail is truncated.
    remaining_h1, remaining_constant = tail1-4*tail0, tail1-5*tail0
    require(remaining_h1 > 0 and remaining_constant > 0, 'Complete nonnegative remaining count contributions')
    remainder = remaining_h1*U[1]+remaining_constant*D
    old_cost = sum(r['old_bound'] for r in records)+remainder
    require(old_cost == sum(probabilities[n]*sum(c*U[t] for t, c in identities[n].items())
                            for n in range(1, 5))+tail1*L-5*tail0*D,
            'Regrouping by original test preserves the full old dilation law exactly')
    old_denominator = D-U[4]/6-old_cost/7
    denominator = D-U[4]/6-(sum(block_bounds)+remainder)/7
    gain = sum(r['denominator_gain'] for r in results)
    require(old_denominator == F(previous['uniform_denominator_lower'])
            == F(survival['uniform_denominator_lower']) and denominator-old_denominator == gain > 0,
            'Only AP11 same-block coupling changes the complete denominator; standalone AP13 is retained')
    weights, costs = list(map(F, previous['cost_weights'])), list(map(F, previous['improved_cost_bounds']))
    signed, square_weight, square = map(F, (previous['signed_mass_coefficient'], previous['complete_square_weight'], previous['complete_square_upper']))
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight
            and square == F(374, 75), 'All complete signed numerator terms retained')
    numerator = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*square
    offset = F(previous['offset'])
    comparison = offset+numerator/denominator
    require(numerator == F(previous['numerator_upper']) > 0 and old_denominator > 0
            and offset+numerator/old_denominator == F(previous['comparison_upper'])
            and 403 < comparison < F(previous['comparison_upper']), 'Strict full-face improvement with unchanged108 numerator')
    return {'schema': 'erdos7-whole-block-ap11-survival-v1', 'source_sha256': used,
            'faces': previous['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
            'count_probabilities': probabilities, 'all_load_identities': identities,
            'blocks': results, 'joint_layout_checks': count, 'joint_objectives_sha256': digest.hexdigest(),
            'full_count_tail': {'probability': tail0, 'first_moment': tail1,
                                'remaining_hinge1_coefficient': remaining_h1,
                                'whole_constant_coefficient': remaining_constant, 'remaining_cost_upper': remainder},
            'standalone_hinge4_penalty': U[4]/6, 'previous_denominator_lower': old_denominator,
            'uniform_denominator_gain': gain, 'uniform_denominator_lower': denominator,
            'cost_weights': weights, 'improved_cost_bounds': costs, 'signed_mass_coefficient': signed,
            'complete_square_weight': square_weight, 'complete_square_upper': square,
            'numerator_upper': numerator, 'offset': offset, 'previous_comparison': F(previous['comparison_upper']),
            'comparison_upper': comparison, 'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary full-face result at r=rho=0. Each original AP11 block keeps its own test across auxiliary outcomes; different blocks remain independently labelled. Complete n>=5 tails and the standalone AP13 loss are retained. Same-test source objectives are combined before maxima; first moments still use the original independent uniform bound. Unchanged108 complete52-cost numerator. No off-face, global K, Lean or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('ap11_block_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact full-block AP11 certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: 250000 same-block head/projection objectives, all original blocks, complete AP11 count tail and unchanged52-cost numerator.')
    print('Denominator '+str(float(F(result['uniform_denominator_lower'])))+'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
