#!/usr/bin/env python3
"""Use the complete expanded-seven interface for four AP11 blocks and AP13."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/expanded_seven_survival_comparison.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/load_two_cost_remainders.py': '46573a7effb28fac5eb6036991523f2fd34e5df54822b3ed09cca538e7d13d69',
    'certificates/source_norms/comparison-bounds/load_two_cost_remainders.json': 'ec6674b8507503f64616098d80047a0600f46fa513420020667516e61c89ce95',
    'frontier/comparison-bounds/expanded_seven_pair_comparison.py': 'a87399cd2b88dafa12ecaeb84fa2ea240537ded21815cb198f13c3e7a3083784',
    'certificates/source_norms/comparison-bounds/expanded_seven_pair_comparison.json': '89cdaf8085de7b8d35489e7352cc8ad1907c56a989f2504229947a7c3c99e1fa',
    'profile-notes/193-256/201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md': 'bfe4561a41e7d35ce0a9e1410bcdd92e3f732b2cfb7c86bc798ab4cd7cc0ab10',
    'frontier/moments-survival/whole_block_mean_survival.py': 'c82087240db64211520f9e268c177fb73a44ff6bb4117e7cd424c5251bee8510',
    'certificates/source_norms/moments-survival/whole_block_mean_survival.json': 'fb2194587d5a4297afd05dbcbfba6ecfd09cbac919a2c221373a94817ec95455',
    'frontier/moments-survival/whole_block_ap11_survival.py': 'fbefa044091efe0cac30fa1e173edc0d0abd523e7f19490f494221cf22171fbd',
    'certificates/source_norms/moments-survival/whole_block_ap11_survival.json': '5d28dc74ed4578eec27deace152fb0a0cc35fefa2f559037fd62fd44a6b1f1fc',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete source input')
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


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('seven_survival_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, block_prior, count_prior = map(read, ('load_two_cost_remainders',
        'whole_block_mean_survival', 'whole_block_ap11_survival'))
    pins = dict(PINS)
    for data in (prior, block_prior, count_prior):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent complete source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('seven_survival_'+name, io.named_artifact(base/'frontier', name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'Original52-cost inventory')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and all(data['faces'] == prior['faces'] and data['r'] == data['rho'] == '0'
                    and F(data['mass']) == D and F(data['linear_upper']) == L
                    for data in (prior, block_prior, count_prior)),
            'The same actual source, residuals and both entire saturated faces')

    # This is the complete original count law, including the entire n>=5 tail.
    probabilities = {int(n): F(p) for n, p in count_prior['count_probabilities'].items()}
    identities = {int(n): {int(t): F(c) for t, c in row.items()}
                  for n, row in count_prior['all_load_identities'].items()}
    law = module('seven_survival_count_law', base/'verify_joint_frontier.py')
    require(probabilities == {n: law.ap_count_probability(11, F(5, 3), n) for n in range(1, 5)},
            'The exact original AP11 count probabilities')
    tail0, tail1 = tuple(F(50, 3)*v for v in law.geom(11, 5)[:2])
    require((tail0, tail1) == (F(5, 43923), F(17, 29282))
            and sum(probabilities.values())+tail0 == 1
            and sum(n*p for n, p in probabilities.items())+tail1 == F(7, 6),
            'All original count mass and first moment, without a count cutoff')
    for n, row in identities.items():
        require(n in probabilities and min(row.values()) >= 0 and sum(row.values()) == n
                and sum(t*c for t, c in row.items()) == 5,
                'Positive integer-hinge identity has its exact affine continuation')
        require(all(sum(c*max(v-t, 0) for t, c in row.items()) == max(n*v-5, 0)
                    for v in range(1, 7)), 'Every finite transition of the original fractional hinge')
    require(set(identities) == set(probabilities) == set(range(1, 5)), 'Every original finite count outcome')
    tail = prior['full_count_tail']
    require(tail == block_prior['full_count_tail'] == count_prior['full_count_tail']
            and F(tail['probability']) == tail0 and F(tail['first_moment']) == tail1
            and F(tail['remaining_hinge1_coefficient']) == tail1-4*tail0
            and F(tail['whole_constant_coefficient']) == tail1-5*tail0
            and F(tail['remaining_cost_upper']) == (tail1-4*tail0)*(L-D)+(tail1-5*tail0)*D
            == F(3337, 52707600), 'All remaining original blocks and infinite-count constant retained')

    problem = load('expanded_seven_pair_comparison').CoupledSevenHead(base)
    targets = [F(8678906729, 50846362875), F(3407797, 71155260),
               F(33868, 5929605), F(16081, 27671490)]
    old_blocks = block_prior['block_results']
    require(len(old_blocks) == 4 and prior['AP11_block_results'] == old_blocks,
            'The unchanged111 original independent AP11 block bounds')
    records = []
    for e, old in enumerate(old_blocks):
        coefficients = {t: sum(probabilities[n]*identities[n].get(t, 0)/n for n in range(e+1, 5))
                        +(tail0 if t == 1 else 0) for t in (1, 2, 3, 5)}
        require(encode({t: c for t, c in coefficients.items() if c}) == old['hinge_coefficients']
                and old['block'] == e, 'One fixed original test throughout its complete count outcomes')
        scan = problem.scan(coefficients)
        previous = F(old['joint_mean_upper'])
        bound = min(previous, scan['complete_hinge_upper'])
        require(bound == scan['complete_hinge_upper'] == targets[e], 'Exact independently maximized complete block')
        records.append({'block': e, 'hinge_coefficients': scan['coefficients'],
            'previous_upper': previous, 'joint_mean_upper': bound,
            'denominator_gain': (previous-bound)/7, 'scan': scan})
        print('Checked independent AP11 block'+str(e)+': '+str(float(bound))+'.', flush=True)
    scan13 = problem.scan({4: F(1)})
    oldU4 = 6*F(prior['standalone_hinge4_penalty'])
    require(oldU4 == F(938213, 4630500), 'The original independent AP13 loss')
    U4 = min(oldU4, scan13['complete_hinge_upper'])
    require(U4 == scan13['complete_hinge_upper'] == F(295741, 1543500), 'Exact separate complete AP13 maximum')
    ap13gain = (oldU4-U4)/6
    denominator = D-U4/6-(sum(r['joint_mean_upper'] for r in records)+F(tail['remaining_cost_upper']))/7
    old_denominator = D-oldU4/6-(sum(F(r['joint_mean_upper']) for r in old_blocks)
        +F(tail['remaining_cost_upper']))/7
    gain = sum(r['denominator_gain'] for r in records)+ap13gain
    require(old_denominator == F(prior['uniform_denominator_lower']) == F(50511415637, 632754738000)
            and gain == F(16774211, 5042614500)
            and denominator == old_denominator+gain == F(1420639249067, 17084377926000) > 0,
            'Exactly the four separate AP11 gains and independent AP13 gain in the full denominator')

    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(encode(tags) == prior['original_cost_tags'] and prior['all_original_indices'] == list(range(52))
            and len(tags) == len(old_costs) == len(weights) == 52 and min(weights) > 0
            and signed < 0 < square_weight, 'Every original202 cost, signed mass and full square term retained')
    # The uniform h4 theorem also applies to this separate original cost test.
    # It is not an identification with the AP13 test or an extra mass credit.
    remainders = load('load_two_cost_remainders')
    support = [row for row in remainders.SUPPORTS if row[0] == 41]
    require(len(support) == 1, 'One complete original quadratic41 identity')
    identity = remainders.verify_identity(original.source, tags[41], support[0])
    saved_identity = [row for row in prior['exact_integer_identities'] if row['index'] == 41]
    require(len(saved_identity) == 1
            and all(saved_identity[0][k] == encode(v) for k, v in identity.items())
            and identity['hinge4'] == F(948, 143), 'Recheck the exact202 identity and its positive hinge coefficient')
    T5 = F(prior['second_factorial_tail_upper'])
    common_part = (identity['square_minus_mass']*(Q-D)+identity['raw_square9']*old_costs[48]
                   +identity['factorial5']*T5)
    require(T5 == F(619, 720) and common_part+identity['hinge4']*oldU4
            == F(saved_identity[0]['source_bound']) == old_costs[41],
            'All complete202 moment terms and its accepted original41 bound')
    costs = list(old_costs)
    costs[41] = min(old_costs[41], common_part+identity['hinge4']*U4)
    cost_gain = old_costs[41]-costs[41]
    require(cost_gain == F(805642, 11036025) > 0
            and weights[41]*cost_gain == F(955088591, 15891876000),
            'Only the positive h4 term changes in the full quadratic41 cost')
    old_numerator = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    numerator = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    offset = F(prior['offset'])
    comparison = offset+numerator/denominator
    require(old_numerator == F(prior['numerator_upper']) > numerator > 0
            and old_numerator-numerator == weights[41]*cost_gain
            and offset+old_numerator/old_denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']),
            'One exact h4 feedback in the complete202 numerator and stronger full denominator, still above403')
    return encode({'schema': 'erdos7-expanded-seven-survival-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
        'complete_square_upper': Q, 'count_probabilities': probabilities, 'all_load_identities': identities,
        'AP11_block_results': records, 'full_count_tail': tail,
        'AP13_result': {'hinge_coefficients': {4: F(1)}, 'previous_upper': oldU4, 'hinge_upper': U4,
                        'denominator_gain': ap13gain, 'scan': scan13},
        'standalone_hinge4_penalty': U4/6, 'uniform_hinge4_upper': U4,
        'previous_denominator_lower': old_denominator, 'uniform_denominator_gain': gain,
        'uniform_denominator_lower': denominator,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags,
        'cost_weights': weights, 'previous_cost_bounds': old_costs, 'improved_cost_bounds': costs,
        'improved_cost_indices': [41], 'signed_mass_coefficient': signed,
        'complete_square_weight': square_weight, 'previous_numerator_upper': old_numerator,
        'numerator_upper': numerator, 'numerator_improvement': old_numerator-numerator,
        'quadratic41_feedback': {**identity, 'second_factorial_tail_upper': T5,
            'previous_hinge4_upper': oldU4, 'hinge4_upper': U4,
            'previous_cost_upper': old_costs[41], 'cost_upper': costs[41],
            'cost_gain': cost_gain, 'weighted_numerator_gain': weights[41]*cost_gain},
        'offset': offset, 'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'rational_lp_count': sum(r['scan']['rational_lp_count'] for r in records)+scan13['rational_lp_count'],
        'scope': 'Four independently maximized original AP11 blocks and the separate original AP13 hinge use201 complete arbitrary-residue expanded-seven bridge. The same uniform h4 upper also improves the positive h4 term in202 original quadratic41, on its own independent test. All original count tails,52 costs, signed mass and square terms remain on both whole saturated actual K faces. No shared optimizer, actual attainment, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('seven_survival_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact full survival comparison certificate')
    print('PASS: five separate complete AP maxima, original count tail and52 costs; face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
