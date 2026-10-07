"""Recover a weighted common-action input from saved complete joint floors."""

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx, fmpq


def rational_endpoint(item):
    mantissa, exponent = map(int, item['dyadic'])
    return Fraction(mantissa) * Fraction(2) ** exponent


def ball(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def upper_endpoint(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite weighted-input enclosure')
    upper = value.upper()
    return {'display': str(upper),
            'dyadic': [str(x) for x in upper.man_exp()]}


def exact_rational(value):
    return {'numerator': str(value.numerator),
            'denominator': str(value.denominator)}


def produce(input_dir, comparison_c):
    inputs = {}

    def read_data(name):
        raw = (input_dir / name).read_bytes()
        inputs[name] = hashlib.sha256(raw).hexdigest()
        return json.loads(raw)

    joint = read_data('joint-high-floor-result.json')
    derivative = read_data('derivative-bandwidth-result.json')
    center = read_data('sharp-center-result.json')
    forward = read_data('forward-action-result.json')
    high = read_data('high-trial-bounds-result.json')
    ground = read_data('ground-residual-result.json')

    c = Fraction(joint['matrix_c'] if comparison_c is None else comparison_c)
    if not 0 <= c < Fraction(1, 2):
        raise RuntimeError('Comparison parameter must be in [0,1/2)')
    for source in (joint, derivative, center, forward, high, ground):
        if source['bandwidth_N'] != joint['bandwidth_N']:
            raise RuntimeError('Saved source bandwidth mismatch')
    if (joint['derivative_source_sha256'] != inputs['derivative-bandwidth-result.json']
            or center['supplier_data_sha256'] != inputs['derivative-bandwidth-result.json']):
        raise RuntimeError('Joint/center derivative provenance mismatch')
    for source in (forward, high, ground):
        recorded = source.get('input_data_sha256', source.get('input_sha256', {}))
        for name, digest in inputs.items():
            if name in recorded and recorded[name] != digest:
                raise RuntimeError('Saved common-input provenance mismatch: ' + name)
    if (joint['bandwidth_N'] != 64
            or Fraction(joint['matrix_c']) != Fraction(3, 8)
            or forward['retained_gamma_terms'] != high['trial_gamma_terms']
            or forward['retained_prime_cutoff'] != high['trial_prime_cutoff']
            or ground['low_action_gamma_terms'] != forward['retained_gamma_terms']
            or ground['high_action_gamma_terms'] != high['sufficient_action_gamma_terms']):
        raise RuntimeError('Saved common-family parameter mismatch')

    radius = Fraction(joint['radius'])
    leakage = rational_endpoint(joint['leakage_product_upper'])
    if leakage != rational_endpoint(derivative['leakage_product_upper']):
        raise RuntimeError('Leakage source mismatch')
    exterior = rational_endpoint(joint['exterior_floor_lower']) - c - leakage
    if radius <= 0 or exterior <= 0:
        raise RuntimeError('Positive exterior potential not supplied')
    cells, end, square_caps = [], Fraction(0), []
    for source in joint['cells']:
        left, right = Fraction(source['left']), Fraction(source['right'])
        if left != end or right <= left or right > radius:
            raise RuntimeError('Saved joint cells do not form an exact contiguous cover')
        potential = rational_endpoint(source['joint_floor_lower']) - c - leakage
        s2_upper = rational_endpoint(source['s2_upper'])
        if potential <= 0 or s2_upper < 0:
            raise RuntimeError('Positive cell potential or theta cap not supplied')
        square_cap = s2_upper / potential
        square_caps.append(square_cap)
        cells.append({'left': str(left), 'right': str(right),
                      'potential': exact_rational(potential),
                      'inverse_weight': exact_rational(1 / potential),
                      'weighted_output_squared_cap': exact_rational(square_cap)})
        end = right
    if end != radius or len(cells) != joint['grid_boxes']:
        raise RuntimeError('Saved joint cover is incomplete')
    floor = min([exterior] + [Fraction(int(x['potential']['numerator']),
                                    int(x['potential']['denominator'])) for x in cells])
    inherited_floor = rational_endpoint(joint['complete_high_block_floor_lower']) - c
    if floor < inherited_floor or inherited_floor <= 0:
        raise RuntimeError('Step potential does not preserve the inherited scalar floor')

    k0 = ball(rational_endpoint(center['K0_upper']))
    decay_b = ball(Fraction(3, 8))
    exterior_squared = (k0 ** 2 * (-2 * decay_b * (2 * ball(radius)).exp()).exp()
                        / ball(exterior))
    exterior_cap = rational_endpoint(upper_endpoint(exterior_squared))
    output_squared = max(square_caps + [exterior_cap])
    output_cap_item = upper_endpoint(ball(output_squared).sqrt())
    output_cap = ball(rational_endpoint(output_cap_item))
    s0 = ball(rational_endpoint(forward['s_derivative_sup_upper'][0]))
    if not s0 > 0:
        raise RuntimeError('Positive inherited theta supremum cap not supplied')
    inverse_root_floor = 1 / ball(inherited_floor).sqrt()
    a64 = ball(rational_endpoint(forward['weighted_second_norm_coefficient_upper']))
    trial_u = ball(rational_endpoint(high['weighted_second_common_family_upper']))
    trial_r = ball(rational_endpoint(high['common_family_norm_upper']))
    map_a = ball(rational_endpoint(high['map_A_frobenius_upper']))
    prime = ball(rational_endpoint(forward['full_two_direction_prime_action_error_upper']))
    low_terms = ground['low_action_gamma_terms']
    high_terms = ground['high_action_gamma_terms']
    if low_terms < 1 or high_terms < 1 or min(a64, trial_u, trial_r, map_a, prime) < 0:
        raise RuntimeError('Invalid inherited regularity or action coefficient')

    def sigma(terms):
        return ball(Fraction(1, 2) / (2 * terms - Fraction(3, 2)) ** 2)

    low_derivative_cost = sigma(low_terms) * a64
    high_derivative_cost = sigma(high_terms) * trial_u
    low_prime_cost = inverse_root_floor * prime
    high_prime_cost = low_prime_cost * trial_r
    weighted_low = output_cap * low_derivative_cost + low_prime_cost
    weighted_high = output_cap * high_derivative_cost + high_prime_cost
    weighted_common = weighted_low + map_a * weighted_high
    scalar_low = inverse_root_floor * s0 * low_derivative_cost + low_prime_cost
    scalar_high = inverse_root_floor * s0 * high_derivative_cost + high_prime_cost
    scalar_common = scalar_low + map_a * scalar_high
    ratio = output_cap / (inverse_root_floor * s0)

    return {
        'scope': 'Conditional paper input from saved complete joint floors and common '
                 'regularity bounds; no retained weighted Gram, matrix sign, Lean or RH certificate',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                    'precision_bits': ctx.prec},
        'input_sha256': inputs,
        'bandwidth_N': joint['bandwidth_N'], 'comparison_c': str(c),
        'saved_trial_definition_c': joint['matrix_c'],
        'saved_retained_action_parameter_matches': c == Fraction(joint['matrix_c']),
        'radius': str(radius), 'grid_cells': len(cells),
        'theta_callbacks_executed': 0, 'old_producers_rerun': False,
        'scalar_floor': exact_rational(inherited_floor),
        'step_potential_floor': exact_rational(floor),
        'exterior_potential': exact_rational(exterior),
        'exterior_weighted_output_squared_upper': upper_endpoint(exterior_squared),
        'weighted_output_cap_upper': output_cap_item,
        'scalar_output_cap_upper': upper_endpoint(inverse_root_floor * s0),
        'gamma_budget_ratio_upper': upper_endpoint(ratio),
        'step_potential_dominates_inherited_scalar_floor': floor >= inherited_floor,
        'low_action_gamma_terms': low_terms, 'high_action_gamma_terms': high_terms,
        'prime_cutoff': forward['retained_prime_cutoff'],
        'weighted_low_action_error_upper': upper_endpoint(weighted_low),
        'weighted_high_family_action_error_upper': upper_endpoint(weighted_high),
        'weighted_common_ground_complement_action_error_upper': upper_endpoint(weighted_common),
        'same_input_scalar_common_action_error_upper': upper_endpoint(scalar_common),
        'common_budget_ratio_upper': upper_endpoint(weighted_common / scalar_common),
        'source_scope': 'Uniform on (I-Pi0)p through the SAME fixed Y, with exact '
                        'ground error zero; high trial Z is not redefined by later action cutoffs',
        'retained_weighted_Grams_evaluated': False,
        'cofinal_sign_certified': False,
        'cells': cells,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--c', help='Rational comparison parameter; defaults to the saved joint parameter')
    args = parser.parse_args()
    ctx.prec = 128
    result = produce(args.input_dir, args.c)
    output = args.output or args.input_dir / 'joint-weighted-input-result.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'cells'}, indent=2))


if __name__ == '__main__':
    main()
