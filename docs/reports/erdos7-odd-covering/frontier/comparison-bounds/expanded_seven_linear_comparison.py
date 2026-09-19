#!/usr/bin/env python3
"""Apply the complete selected-intersection bridge to eleven original linear costs."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/expanded_seven_linear_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/comparison-bounds/second_depth_seven_comparison.py': 'b49a13dde9aa26ce8b1a132c11f3a9bc125d995b9497567c7bff26eb2f4bb239', 'certificates/source_norms/comparison-bounds/second_depth_seven_comparison.json': '0791019058d4f252d133a4cd2d48a313662098b014905ac7685f4eb975557aa8', 'frontier/comparison-bounds/expanded_seven_pair_comparison.py': 'a87399cd2b88dafa12ecaeb84fa2ea240537ded21815cb198f13c3e7a3083784', 'certificates/source_norms/comparison-bounds/expanded_seven_pair_comparison.json': '89cdaf8085de7b8d35489e7352cc8ad1907c56a989f2504229947a7c3c99e1fa'}
INDICES = (1, 2, 7, 10, 17, 18, 23, 26, 32, 33, 36)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete source')
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
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('linear_seven_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/second_depth_seven_comparison.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent complete source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('linear_seven_'+name, io.named_artifact(base/'frontier', name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'Original52-cost inventory')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and prior['r'] == prior['rho'] == '0', 'The same two whole actual saturated faces')
    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(encode(tags) == prior['original_cost_tags'] and prior['all_original_indices'] == list(range(52))
            and len(tags) == len(old_costs) == len(weights) == 52 and min(weights) > 0,
            'All original costs and positive weights retained')
    problem = load('expanded_seven_pair_comparison').CoupledSevenHead(base)
    direct, records = list(old_costs), []
    for i in INDICES:
        tag = tags[i]
        f = lambda n: original.source.zero5_cost(tag, n)
        degree, leading, constant, cutoff = original.source.zero5_cost_metadata(tag)
        require(degree == 1 and 1 <= cutoff <= 8, 'An original complete affine-tail function')
        coefficients = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        require(min(coefficients.values()) >= 0 and sum(coefficients.values()) > 0,
                'A nonzero positive hinge combination')
        expand = lambda n: f(1)+sum(c*max(n-t, 0) for t, c in coefficients.items())
        require(all(expand(n) == f(n) for n in range(1, 10))
                and sum(coefficients.values()) == leading
                and f(1)-sum(t*c for t, c in coefficients.items()) == constant,
                'Every finite transition and the complete infinite affine tail')
        scan = problem.scan(coefficients)
        bound = f(1)*D+scan['complete_hinge_upper']
        require(0 <= bound < old_costs[i], 'A strict uniform original-cost improvement')
        direct[i] = bound
        records.append({'index': i, 'tag': tag, 'at_one': f(1), 'tail_cutoff': cutoff,
                        'complete_tail_slope': leading, 'complete_tail_constant': constant,
                        'previous_cost_upper': old_costs[i], 'cost_upper': bound,
                        'weighted_gain': weights[i]*(old_costs[i]-bound), 'scan': scan})
        print('Checked independent linear cost'+str(i)+': '+str(float(bound))+'.', flush=True)
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: original.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [original.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    require(all(0 <= b <= a for a, b in zip(old_costs, costs)), 'Every preceding complete upper remains available')
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(signed < 0 < square_weight, 'The exact signed mass and positive complete square terms')
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    numerator = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower'])
            == F(1420639249067, 17084377926000) > 0,
            'All independent AP11 blocks, AP13 and the complete infinite-count remainder')
    offset = F(prior['offset'])
    comparison = offset+numerator/denominator
    require(oldN == F(prior['numerator_upper']) > numerator > 0
            and offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']),
            'One strict full52-cost comparison, still above403')
    return encode({'schema': 'erdos7-expanded-seven-linear-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
        'complete_square_upper': Q, 'linear_results': records,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
        'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct, 'improved_cost_bounds': costs,
        'majorants': majorants, 'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'previous_numerator_upper': oldN, 'numerator_upper': numerator, 'numerator_improvement': oldN-numerator,
        'AP11_block_results': prior['AP11_block_results'], 'AP13_result': prior['AP13_result'],
        'uniform_hinge4_upper': prior['uniform_hinge4_upper'], 'full_count_tail': prior['full_count_tail'],
        'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'rational_lp_count': sum(row['scan']['rational_lp_count'] for row in records),
        'scope': 'Eleven complete original affine-tail costs separately use the201 selected-intersection bridge; all original labels and residues remain independent. Both204 heavy bounds,199 square,202 integer identities and203 full denominator/h4 feedback remain in one52-cost comparison on both whole actual K faces. All infinite exponent and count tails retained. No joint optimizer, actual attainment, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('linear_seven_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete linear-cost comparison')
    print('PASS: eleven original complete linear costs and full52-cost consumer; face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
