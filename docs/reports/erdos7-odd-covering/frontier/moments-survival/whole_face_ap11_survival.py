#!/usr/bin/env python3
"""Use neighboring integer hinges in the original complete AP11 dilation law.

The same auxiliary count probabilities and original tests are retained.
For n=2,3,4 the fractional-threshold cost has an exact integer-load hinge
expansion. The entire n>=5 tail is affine and summed analytically.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/whole_face_ap11_survival.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/whole_face_stop_loss_generator.py': '8f02e3210c0e9477680a7f817fd3594db83fa1fb34221226b707f41e0a3f4784',
    'certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json': 'e2456850d6db2ac5445e9ff927cdd75c104e3a1a25c8b22159d72c201fe3b924',
    'frontier/endpoint-bounds/endpoint_survival_scalar_barrier.py': '10e915082ee01cef1219125367fd455374c82c98d812654cc4283b2fe7ac3358',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input: '+str(path))
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


def integer_hinge_identity(n):
    """Exact all-load identity, with a finite prefix and matching affine tail."""
    floor, remainder = divmod(5, n)
    coefficients = {floor: n-remainder}
    if remainder:
        coefficients[floor+1] = remainder
    require(min(coefficients.values()) > 0, 'All integer-hinge multipliers are positive')
    entrance = max(1, max(coefficients))
    values = []
    for v in range(1, entrance+2):
        original = max(n*v-5, 0)
        expanded = sum(weight*max(v-t, 0) for t, weight in coefficients.items())
        require(original == expanded, 'Exact integer prefix of the original dilated cost')
        values.append(original)
    require(sum(coefficients.values()) == n and sum(t*weight for t, weight in coefficients.items()) == 5,
            'Every remaining integer load has exactly the original affine slope and intercept')
    return {'count': n, 'threshold': F(5, n), 'hinge_coefficients': coefficients,
            'finite_values': values, 'affine_tail_entrance': entrance,
            'affine_tail_slope': n, 'affine_tail_offset': -5}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('ap11_neighbor_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input: '+path)
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
        used[path] = pin
    source = module('ap11_neighbor_source', base/'verify_joint_frontier.py')
    require(previous['schema'] == 'erdos7-whole-face-stop-loss-generator-v1' and previous['r'] == previous['rho'] == '0',
            'The complete stop-loss theorem on the same saturated faces')
    D, L = F(previous['mass']), F(previous['linear_upper'])
    U = {int(t): F(value) for t, value in previous['stop_loss_profile']['uniform_hinge_uppers'].items()}
    require(D == F(53, 360) and L == F(1151, 1800) and U[1] == L-D, 'Exact mass and same whole-face first moment')
    probability = lambda n: source.ap_count_probability(11, F(5, 3), n)
    probabilities = {n: probability(n) for n in range(1, 5)}
    require(probabilities == {1: F(28, 33), **{n: F(50, 3*11**n) for n in range(2, 5)}},
            'The original AP11 count law, with no change of probability measure')
    ratio = F(1, 11)
    tail0 = F(50, 3)*ratio**5/(1-ratio)
    tail1 = F(50, 3)*ratio**5*(5-4*ratio)/(1-ratio)**2
    require((tail0, tail1) == tuple(F(50, 3)*x for x in source.geom(11, 5)[:2])
            == (F(5, 43923), F(17, 29282)), 'Exact complete count tail in two independent formulas')
    require(sum(probabilities.values())+tail0 == source.ap_active_moment(11, F(5, 3), 0, 0) == 1
            and sum(n*p for n, p in probabilities.items())+tail1 == source.ap_active_moment(11, F(5, 3), 0, 1) == F(7, 6),
            'Full original count probability and first moment')
    identities = [integer_hinge_identity(n) for n in range(1, 5)]
    require([row['hinge_coefficients'] for row in identities]
            == [{5: 1}, {2: 1, 3: 1}, {1: 1, 2: 2}, {1: 3, 2: 1}], 'All four original finite dilation terms')
    terms = {row['count']: sum(weight*U[t] for t, weight in row['hinge_coefficients'].items()) for row in identities}
    tail_cost = tail1*L-5*tail0*D
    # For all n>=5 and all integer v>=1, n*v>=5; the entire hinge is n*v-5.
    require(tail_cost > 0, 'The full affine count tail has the retained valid upper bound')
    denominator = D-U[4]/6-(sum(probabilities[n]*terms[n] for n in range(1, 5))+tail_cost)/7
    coefficients = {'mass': 1+(5*tail0+probability(3)+3*probability(4))/7,
                    'linear': (tail1+probability(3)+3*probability(4))/7,
                    'hinge2': (probability(2)+2*probability(3)+probability(4))/7,
                    'hinge3': probability(2)/7, 'hinge4': F(1, 6), 'hinge5': probability(1)/7}
    require(coefficients == {'mass': F(308186, 307461), 'linear': F(1451, 614922),
                             'hinge2': F(2400, 102487), 'hinge3': F(50, 2541),
                             'hinge4': F(1, 6), 'hinge5': F(4, 33)}, 'Exact new full-law coefficient form')
    expanded = coefficients['mass']*D-coefficients['linear']*L-sum(coefficients['hinge'+str(t)]*U[t] for t in range(2, 6))
    require(expanded == denominator == F(1358432973299, 17084377926000), 'Count expansion and coefficient expansion agree')
    chord = lambda t: (4-t)*(L-D)/3+(t-1)*U[4]/3
    old_denominator = D-U[4]/6-(probability(1)*U[5]+sum(probability(n)*n*chord(F(5, n)) for n in (2, 3, 4))+tail_cost)/7
    require(old_denominator == F(previous['uniform_denominator_lower']), 'Reconstruct the preceding86/98 full-law denominator')
    term_gains = {n: probability(n)*(n*chord(F(5, n))-terms[n])/7 for n in (2, 3, 4)}
    require(min(term_gains.values()) > 0 and sum(term_gains.values()) == denominator-old_denominator
            == F(117048319, 85421889630), 'Three strictly positive disjoint gains; all other terms unchanged')
    weights = list(map(F, previous['cost_weights']))
    costs = list(map(F, previous['improved_cost_bounds']))
    mass_coefficient, square_coefficient = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    square = F(previous['square_sums']['full_square_upper'])
    require(len(weights) == len(costs) == 52 and min(weights) > 0 and mass_coefficient < 0 < square_coefficient
            and square == F(374, 75), 'Retain every signed numerator and complete square term')
    numerator = mass_coefficient*D+sum(w*c for w, c in zip(weights, costs))+square_coefficient*square
    require(numerator == F(previous['numerator_upper']) > 0, 'Unchanged entire98 numerator')
    offset = F(previous['offset'])
    comparison = offset+numerator/denominator
    require(offset+numerator/old_denominator == F(previous['comparison_upper'])
            and 403 < comparison < F(previous['comparison_upper']) and denominator > old_denominator > 0,
            'The complete face comparison improves but remains above403')
    return {'schema': 'erdos7-whole-face-ap11-survival-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0),
            'linear_upper': L, 'uniform_hinge_uppers': U, 'count_probabilities': probabilities,
            'integer_load_identities': identities, 'finite_dilated_cost_uppers': terms,
            'full_AP11_tail': {'mass': tail0, 'first_moment': tail1, 'integrated_cost_upper': tail_cost},
            'denominator_coefficients': coefficients, 'previous_denominator_lower': old_denominator,
            'count_term_denominator_gains': term_gains, 'uniform_denominator_gain': denominator-old_denominator,
            'uniform_denominator_lower': denominator,
            'retained_numerator': {'signed_mass_coefficient': mass_coefficient, 'cost_weights': weights,
                                   'cost_upper_bounds': costs, 'complete_square_weight': square_coefficient,
                                   'complete_square_upper': square, 'numerator_upper': numerator},
            'offset': offset, 'previous_comparison': F(previous['comparison_upper']),
            'comparison_upper': comparison, 'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary uniform comparison on both complete actual K-control faces with r=rho=0 and exact saturated mass53/360. Preserves the original AP11 count law, each original test and every count tail. Uses neighboring integer hinges on each test separately, without shared residues or resampling. Retains the entire98 numerator. No scalar-optimality, off-face neighborhood, new global K, Lean verification or unrestricted Erdos7 claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('ap11_neighbor_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical full AP11 survival certificate')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: original AP11 count law, exact all-integer dilation identities, complete tail and unchanged52-cost signed numerator.')
    print('Denominator '+str(float(F(result['uniform_denominator_lower'])))+'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
