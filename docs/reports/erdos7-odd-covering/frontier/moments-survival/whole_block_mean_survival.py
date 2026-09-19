#!/usr/bin/env python3
"""Combine each original AP11 block's mean with all its curvature hinges.

Use109's same-layout certified mean deletion and110's complete block law.
Different original blocks retain independent layouts and every tail.
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
CERTIFICATE = 'certificates/source_norms/moments-survival/whole_block_mean_survival.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/whole_cost_mean_stop_loss.py': '21caf2496428ab1772ffd544c38a82a65b3336d32b8f4aa99307810f54478ac0',
    'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json': '01f227f4a8ae19cfec1e2394b242d0fd30e14b442bebaa3299acde78907c2b26',
    'frontier/moments-survival/whole_block_ap11_survival.py': 'fbefa044091efe0cac30fa1e173edc0d0abd523e7f19490f494221cf22171fbd',
    'certificates/source_norms/moments-survival/whole_block_ap11_survival.json': '5d28dc74ed4578eec27deace152fb0a0cc35fefa2f559037fd62fd44a6b1f1fc',
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
    require('certificate_io.py' in PINS, 'Completed109 and110 source pins')
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('mean_block_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name)))
    prior, current, stop = read('whole_block_ap11_survival.json'), read('whole_cost_mean_stop_loss.json'), read('whole_face_stop_loss_generator.json')
    for data in (prior, current, stop):
        for path, pin in data['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited source')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    common = module('mean_block_common', base/'frontier/comparison-bounds/whole_cost_common_stop_loss.py')
    bridge = module('mean_block_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    mean = module('mean_block_engine', base/'frontier/comparison-bounds/whole_cost_mean_stop_loss.py')
    engine = mean.MeanHead(bridge, stop, common)
    require(current['faces'] == prior['faces'] and current['r'] == current['rho'] == prior['r'] == prior['rho'] == '0',
            'The identical whole saturated K faces and actual zero residuals')
    D, L = F(prior['mass']), F(prior['linear_upper'])
    require(D == F(current['mass']) == F(53, 360) and L == F(current['linear_upper']), 'Same actual mass and complete first moment')
    probabilities = {int(n): F(p) for n, p in prior['count_probabilities'].items()}
    ids = {int(n): {int(t): F(c) for t, c in v.items()} for n, v in prior['all_load_identities'].items()}
    tail0, tail1 = F(prior['full_count_tail']['probability']), F(prior['full_count_tail']['first_moment'])
    require((tail0, tail1) == (F(5, 43923), F(17, 29282)) and sum(probabilities.values())+tail0 == 1,
            'Original complete AP11 count law retained')
    records = []
    for e, old in enumerate(prior['blocks']):
        coeff = {t: sum(probabilities[n]*ids[n].get(t, 0)/n for n in range(e+1, 5))
                 +(tail0 if t == 1 else 0) for t in (1, 2, 3, 5)}
        require(encode(coeff) == old['hinge_coefficients'], 'The same fixed original test across all its count outcomes')
        records.append(engine.prepare(coeff))
    best, witnesses, ties, count, digest = {}, {}, {e: 0 for e in range(4)}, 0, sha256()
    extras = [(root, slot, engine.common.extra(root, slot)) for root, slot in product(range(2), range(5))]
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        correction = bridge.integer(mean.TOTAL*engine.correction(layout))
        for root, slot, extra in extras:
            for e, row in enumerate(records):
                raw, detail = engine.common.objective(row, B, extra)
                credit = row['primitive_coefficients'].get(1, 0)*correction
                require(raw >= credit >= 0, 'Only the certified mean-head deletion is subtracted')
                value = raw-credit
                digest.update(json.dumps([li, root, slot, e, value], separators=(',', ':')).encode())
                count += 1
                if e not in best or value > best[e]:
                    best[e], ties[e] = value, 1
                    witnesses[e] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                    **detail, 'scaled_mean_head_correction': credit}
                elif value == best[e]:
                    ties[e] += 1
    require(count == 500000, 'All four complete block objectives over every head/projection')
    results, gains = [], []
    for e, (record, old) in enumerate(zip(records, prior['blocks'])):
        bound = record['factor']*F(best[e], mean.TOTAL)
        previous = F(old['block_upper'])
        require(bound <= previous, 'The certified joint-mean objective preserves or strengthens each block')
        # Check the public109 API at each saved maximizing witness as well.
        witness = witnesses[e]
        value, _ = engine.objective(record, witness['layout'], bridge.head_load(witness['layout']),
                                    engine.common.extra(witness['positive7_root'], witness['positive7_slot']))
        require(value == best[e], 'Precomputed-correction evaluation agrees with the general109 interface')
        gain = (previous-bound)/7
        gains.append(gain)
        results.append({'block': e, 'hinge_coefficients': record['coefficients'], 'factor': record['factor'],
                        'primitive_coefficients': record['primitive_coefficients'], 'previous_upper': previous,
                        'joint_mean_upper': bound, 'denominator_gain': gain,
                        'maximizing_witness': witness, 'maximizer_count': ties[e]})
    require(gains == [F(21409, 1743303870), F(271, 35577630), F(0), F(0)], 'Two exact mean-coupling gains, two unchanged blocks')
    tail = prior['full_count_tail']
    require(F(tail['remaining_hinge1_coefficient']) == tail1-4*tail0
            and F(tail['whole_constant_coefficient']) == tail1-5*tail0
            and F(tail['remaining_cost_upper']) == (tail1-4*tail0)*(L-D)+(tail1-5*tail0)*D,
            'Every remaining block and the whole infinite-tail constant retained')
    standalone = F(prior['standalone_hinge4_penalty'])
    denominator = D-standalone-(sum(r['joint_mean_upper'] for r in results)+F(tail['remaining_cost_upper']))/7
    old_denominator = F(prior['uniform_denominator_lower'])
    require(denominator == old_denominator+sum(gains) > old_denominator > 0,
            'The separate AP13 loss and complete count tail are unchanged')
    costs, weights = list(map(F, current['improved_cost_bounds'])), list(map(F, current['cost_weights']))
    signed, square_weight, square = map(F, (current['signed_mass_coefficient'], current['complete_square_weight'], current['complete_square_upper']))
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight
            and square == F(374, 75), 'Every original signed numerator term retained')
    numerator = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*square
    offset = F(current['offset'])
    ratio = offset+numerator/denominator
    require(numerator == F(current['numerator_upper']) > 0 and numerator <= F(prior['numerator_upper'])
            and 403 < ratio < F(prior['comparison_upper']), 'Complete109 numerator and stronger denominator, still above403')
    return {'schema': 'erdos7-whole-block-mean-survival-v1', 'source_sha256': used,
            'faces': current['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
            'block_results': results, 'joint_layout_checks': count, 'joint_objectives_sha256': digest.hexdigest(),
            'full_count_tail': tail, 'standalone_hinge4_penalty': standalone,
            'previous_denominator_lower': old_denominator, 'uniform_denominator_gain': sum(gains),
            'uniform_denominator_lower': denominator, 'cost_weights': weights, 'improved_cost_bounds': costs,
            'signed_mass_coefficient': signed, 'complete_square_weight': square_weight, 'complete_square_upper': square,
            'numerator_upper': numerator, 'offset': offset, 'previous_comparison110': F(prior['comparison_upper']),
            'comparison_with_old_denominator': offset+numerator/old_denominator,
            'comparison_upper': ratio, 'improvement_over110': F(prior['comparison_upper'])-ratio,
            'scope': 'Ordinary saturated-face comparison. Each AP11 block combines its mean and curvature costs on one original layout with109 certified mean deletion. All infinite tails, the independent AP13 term and109 complete52-cost numerator remain. No identification of different tests, off-face extension, global K, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('mean_block_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete mean-block certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:500000 same-test mean/curvature objectives, full count tail, original AP13 loss and complete52-cost numerator.')
    print('Denominator '+str(float(F(result['uniform_denominator_lower'])))+'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
