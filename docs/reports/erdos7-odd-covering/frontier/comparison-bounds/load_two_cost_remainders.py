#!/usr/bin/env python3
"""Exact load-two remainder identities for eight complete original costs."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/load_two_cost_remainders.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/comparison-bounds/expanded_seven_pair_comparison.py': 'a87399cd2b88dafa12ecaeb84fa2ea240537ded21815cb198f13c3e7a3083784', 'certificates/source_norms/comparison-bounds/expanded_seven_pair_comparison.json': '89cdaf8085de7b8d35489e7352cc8ad1907c56a989f2504229947a7c3c99e1fa', 'frontier/comparison-bounds/whole_cost_mean_stop_loss.py': '21caf2496428ab1772ffd544c38a82a65b3336d32b8f4aa99307810f54478ac0', 'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json': '01f227f4a8ae19cfec1e2394b242d0fd30e14b442bebaa3299acde78907c2b26', 'frontier/moments-survival/whole_factorial_same_head.py': '02b5af74e00afc26b940d8c6b485fbea654a4d2f9dd52d986875c303a79faacd', 'certificates/source_norms/moments-survival/whole_factorial_same_head.json': 'b22d62e4c137abc20668305d67bf86f87345077f0ecf3d481e1bf83b2dedbd3c'}
# index, square-minus-mass, raw-square9, hinge4, factorial5, load-two remainder
SUPPORTS = (
    (41, '312522845/736900164', '127212451/736900164', '948/143', '632/429', '636062255/736900164'),
    (42, '34907/145002', '1928/24167', '0', '0', '9640/24167'),
    (43, '4955/145002', '56/24167', '0', '0', '280/24167'),
    (44, '1180709/4360356', '404875/4360356', '0', '0', '2024375/4360356'),
    (45, '198959/4360356', '1975/622908', '0', '0', '9875/622908'),
    (49, '63/128', '65/128', '0', '0', '189/128'),
    (50, '18/25', '7/25', '0', '0', '7/5'),
    (51, '27/32', '5/32', '0', '0', '25/32'),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
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


def verify_identity(source, tag, row):
    index, *coefficients = row
    a, b, c, e, remainder = map(F, coefficients)
    require(min(a, b, c, e) >= 0 and remainder > 0, 'Positive uniform moment coefficients and exact atom charge')
    degree, leading, constant, cutoff = source.zero5_cost_metadata(tag)
    require(degree == 2, 'Original cost has the certified complete quadratic tail')
    entrance = max(5, cutoff)
    phi = lambda n: F(max(n-5, 0)*(n-4), 2)
    upper = lambda n: a*(n*n-1)+b*max(n*n-9, 0)+c*max(n-4, 0)+e*phi(n)
    low = [upper(n)-source.zero5_cost(tag, n) for n in range(1, entrance)]
    require(low == [remainder if n == 2 else F(0) for n in range(1, entrance)],
            'Every load below the complete polynomial entrance has exactly its load-two remainder')
    polynomial = (-a-9*b-4*c+10*e, c-F(9, 2)*e, a+b+e/2)
    require(polynomial == (constant, F(0), leading),
            'The full infinite tail agrees coefficient by coefficient, without truncation')
    return {'index': index, 'original_tag': tag, 'square_minus_mass': a,
            'raw_square9': b, 'hinge4': c, 'factorial5': e,
            'load_two_remainder': remainder, 'low_load_gaps': low,
            'tail_entrance': entrance, 'identical_tail_polynomial': polynomial}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pin the complete201 source and logical certificate reader')
    io = module('load_two_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, hinge, factorial = map(read, ('expanded_seven_pair_comparison',
                                        'whole_cost_mean_stop_loss', 'whole_factorial_same_head'))
    pins = dict(PINS)
    for data in (prior, hinge, factorial):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Same original proof input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('load_two_'+name, io.named_artifact(base/'frontier', name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'All original52 costs and source inputs')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(encode(tags) == prior['original_cost_tags'] and tags[48] == ('s', F(9)),
            'Exact original cost identities and raw-square9 source')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    U4, T5 = F(hinge['uniform_hinge_uppers']['4']), F(factorial['second_factorial_tail_upper'])
    require((D, L, Q, U4, T5) == (F(53, 360), F(1151, 1800), F(8201, 1800), F(938213, 4630500), F(619, 720))
            and prior['faces'] == hinge['faces'] == factorial['faces']
            and all(data['r'] == data['rho'] == '0' and F(data['mass']) == D
                    for data in (prior, hinge, factorial)),
            'The same two entire actual saturated faces and complete moment bounds')
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(len(tags) == len(old_costs) == len(weights) == 52
            and prior['all_original_indices'] == list(range(52)) and min(weights) > 0,
            'Every complete201 original numerator term remains')
    costs = list(old_costs)
    identities = []
    for row in SUPPORTS:
        index = row[0]
        identity = verify_identity(engine.source, tags[index], row)
        bound = (identity['square_minus_mass']*(Q-D)+identity['raw_square9']*old_costs[48]
                 +identity['hinge4']*U4+identity['factorial5']*T5)
        costs[index] = min(costs[index], bound)
        identities.append({**identity, 'source_bound': bound, 'previous_cost_bound': old_costs[index],
                           'accepted_cost_bound': costs[index],
                           'weighted_numerator_gain': weights[index]*(old_costs[index]-costs[index])})
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(oldN == F(prior['numerator_upper']) and 0 < N < oldN
            and oldN-N == sum(row['weighted_numerator_gain'] for row in identities),
            'One complete numerator gains exactly its eight accepted replacements')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) > 0,
            'Every AP11 block, AP13 loss and complete infinite count tail remains')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper']) and 403 < comparison,
            'Strict complete-face improvement, still above403')
    return encode({'schema': 'erdos7-load-two-cost-remainders-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
        'complete_square_upper': Q, 'uniform_hinge4_upper': U4, 'second_factorial_tail_upper': T5,
        'original_cost_tags': tags, 'all_original_indices': list(range(52)),
        'cost_weights': weights, 'previous_cost_bounds': old_costs, 'improved_cost_bounds': costs,
        'exact_integer_identities': identities,
        'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'numerator_upper': N, 'numerator_improvement': oldN-N,
        'AP11_block_results': prior['AP11_block_results'], 'full_count_tail': prior['full_count_tail'],
        'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Eight exact identities on every positive integer load. The common positive moment bounds retain the load-two atom as an explicit nonnegative discarded remainder. Each original test has its own load-two event; no shared layout or simultaneous attainment is imposed. The complete consumer retains201 heavy costs,199 square, all52 costs and the full denominator on both saturated K faces. No positive load-two mass, global extension, Lean verification or unrestricted Erdos7 resolution is claimed.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('load_two_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact load-two remainder certificate')
    print('PASS: eight complete integer identities and full face comparison K='+str(float(F(result['comparison_upper']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
