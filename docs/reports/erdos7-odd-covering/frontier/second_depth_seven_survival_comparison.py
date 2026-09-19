#!/usr/bin/env python3
"""Use the complete two-depth seven bridge for original AP11 block zero."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/second_depth_seven_survival_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/expanded_seven_linear_comparison.py': '5c8685804a3b7e564d0beed371c7393fa3772d6edd815a47cf14efb7df377387', 'certificates/source_norms/expanded_seven_linear_comparison.json': 'f8d61aa839bb338c2dab6fd806323f0b67aac97d5c49cbbaa9b5a9d5c397f0cc', 'frontier/second_depth_seven_comparison.py': '5544b70201a721be7ca0dfa92155c4b186235a19f52a5fd85346f85c02cfc950', 'certificates/source_norms/second_depth_seven_comparison.json': '25c75046bf1af7f19494d64cd0c15f4520d86cb8f3e7cd0c7a095397b61388d0', 'frontier/expanded_seven_survival_comparison.py': '4ada3c665b09b069389bec6168003dc5ec80b832c01d8ba3da7033977ed3217d', 'certificates/source_norms/expanded_seven_survival_comparison.json': 'c92797e6642566129f5d1f43bb2813324454900d79768a3381d6db44a6f88651', 'profile-notes/204-a-second-seven-depth-strengthens-both-complete-heavy-costs.md': 'c21f4b5c6e2a72008794b9d2a2052758d573df8df81d6fae0e71dcf3e58c9261'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete original input')
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
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader and full205 consumer')
    io = module('second_survival_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    prior, law_prior = read('expanded_seven_linear_comparison'), read('expanded_seven_survival_comparison')
    pins = dict(PINS)
    for data in (prior, law_prior):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('second_survival_'+name, base/'frontier'/(name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'All original52 functions')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and prior['faces'] == law_prior['faces'] and prior['r'] == prior['rho'] == '0',
            'The same actual measure and both entire saturated faces')

    # The original count law is p1=28/33 and pn=50/(3*11^n) for n>=2.
    probabilities = {1: F(28, 33), **{n: F(50, 3*11**n) for n in range(2, 5)}}
    q = F(1, 11)
    tail0 = F(50, 3)*q**5/(1-q)
    tail1 = F(50, 3)*q**5*(5-4*q)/(1-q)**2
    require(encode(probabilities) == law_prior['count_probabilities']
            and (tail0, tail1) == (F(5, 43923), F(17, 29282))
            and sum(probabilities.values())+tail0 == 1
            and sum(n*p for n, p in probabilities.items())+tail1 == F(7, 6),
            'The full original count probability and first moment')
    identities = {1: {5: F(1)}, 2: {2: F(1), 3: F(1)},
                  3: {1: F(1), 2: F(2)}, 4: {1: F(3), 2: F(1)}}
    require(encode(identities) == law_prior['all_load_identities'], 'The original finite count identities')
    for n, cs in identities.items():
        require(min(cs.values()) > 0 and sum(cs.values()) == n and sum(t*c for t, c in cs.items()) == 5
                and all(sum(c*max(v-t, 0) for t, c in cs.items()) == max(n*v-5, 0)
                        for v in range(1, 7)), 'Every positive integer load, including the affine continuation')
    coefficients = {t: sum(probabilities[n]*identities[n].get(t, 0)/n for n in range(1, 5))
                   +(tail0 if t == 1 else 0) for t in (1, 2, 3, 5)}
    old_blocks = prior['AP11_block_results']
    require(len(old_blocks) == 4 and old_blocks == law_prior['AP11_block_results']
            and encode(coefficients) == old_blocks[0]['hinge_coefficients'],
            'One original block-zero test is fixed throughout all count outcomes')
    tail = prior['full_count_tail']
    require(tail == law_prior['full_count_tail']
            and F(tail['probability']) == tail0 and F(tail['first_moment']) == tail1
            and F(tail['remaining_hinge1_coefficient']) == tail1-4*tail0
            and F(tail['whole_constant_coefficient']) == tail1-5*tail0
            and F(tail['remaining_cost_upper']) == (tail1-4*tail0)*(L-D)+(tail1-5*tail0)*D
            == F(3337, 52707600), 'All later blocks and every infinite-count constant remain')

    scan = load('second_depth_seven_comparison').SecondDepthSevenHead(base).scan(coefficients)
    old_bound = F(old_blocks[0]['joint_mean_upper'])
    bound = min(old_bound, scan['complete_hinge_upper'])
    require(old_bound == F(8678906729, 50846362875)
            and bound == scan['complete_hinge_upper'] == F(17233291753, 101692725750)
            and old_bound-bound == F(3, 2450), 'Exact complete original block-zero gain')
    blocks = [{'block': 0, 'hinge_coefficients': coefficients, 'previous_upper': old_bound,
               'joint_mean_upper': bound, 'denominator_gain': (old_bound-bound)/7, 'scan': scan}]+old_blocks[1:]
    require(prior['AP13_result'] == law_prior['AP13_result']
            and F(prior['uniform_hinge4_upper']) == 6*F(prior['standalone_hinge4_penalty'])
            == F(295741, 1543500), 'The separate AP13 bound remains exactly203/205')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in blocks)+F(tail['remaining_cost_upper']))/7
    old_denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in old_blocks)+F(tail['remaining_cost_upper']))/7
    require(old_denominator == F(prior['uniform_denominator_lower']) == F(1420639249067, 17084377926000)
            and denominator-old_denominator == F(3, 17150)
            and denominator == F(1423627769987, 17084377926000) > 0,
            'Only the original block-zero gain enters the complete denominator')

    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(encode(tags) == prior['original_cost_tags'] and prior['all_original_indices'] == list(range(52))
            and len(tags) == len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight,
            'Every complete205 cost, signed mass and complete square coefficient retained')
    numerator = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    offset = F(prior['offset'])
    comparison = offset+numerator/denominator
    require(numerator == F(prior['numerator_upper']) > 0
            and offset+numerator/old_denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']),
            'Unchanged full205 numerator and one stronger complete denominator, still above403')
    return encode({'schema': 'erdos7-second-depth-seven-survival-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'count_probabilities': probabilities, 'all_load_identities': identities,
        'AP11_block_results': blocks, 'full_count_tail': tail, 'AP13_result': prior['AP13_result'],
        'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_hinge4_upper': F(prior['uniform_hinge4_upper']),
        'previous_denominator_lower': old_denominator, 'uniform_denominator_gain': denominator-old_denominator,
        'uniform_denominator_lower': denominator, 'all_original_indices': list(range(52)), 'original_cost_tags': tags,
        'cost_weights': weights, 'previous_cost_bounds': costs, 'improved_cost_bounds': costs, 'improved_cost_indices': [],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'numerator_upper': numerator, 'numerator_improvement': F(0), 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'rational_lp_count': scan['rational_lp_count'],
        'scope': 'The original AP11 block-zero test alone uses204 complete second-depth-seven interface. All count outcomes use that one test; all infinite-count tails and independent later blocks remain. The complete205 numerator, all52 costs, original AP13 bound and h4 contribution to cost41 remain unchanged. This is an ordinary full-face source theorem, not an attainment, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('second_survival_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete survival certificate')
    print('PASS: complete original block-zero improvement with full205 vector; face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
