#!/usr/bin/env python3
"""Exact capacity of118's unchanged outer branches after a small local repair.

The local quotient is a conditional input. This verifies the gluing criterion
and its outer bottleneck, not a new local theorem or a new canonical global K.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/local_to_global_escape_capacity.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/shared_slot_gap_global.py': 'c2b986c246c3c73cf02e5db512f4c1bccc206da0ec57e319de4d1578ec57b66e',
    'certificates/source_norms/shared_slot_gap_global.json': 'bebb0ea08476ffbec39505f269b7bbd79e60562112994ef56eacebd314d178c1',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
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
    io = module('local_global_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin,
                'Pinned input '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/shared_slot_gap_global.json'))
    predecessor = module('local_global_previous', base/'frontier/shared_slot_gap_global.py')
    require(encode(predecessor.calculate(base)) == previous,
            'Reconstruct118 with all original costs, complete tails and outer branches')
    keys = ('weighted_credit', 'combined_residual_penalty', 'combined_escape_penalty',
            'conservative_mass_coefficient', 'S0_upper_constant', 'S0_upper_sigma_coefficient',
            'first_escape_gap', 'next_escape_gap', 'concentration_delta', 'slot_loss_cutoff', 'old_K0')
    B, P, Q, A, a, b, gamma1, gamma2, delta, rcut, K0 = (F(previous[k]) for k in keys)
    old_h = F(previous['decrease_from_K0'])
    delta0, rho0, example_local_bound = F(1, 10000), F(1, 100000), F(461)
    require((delta, rcut, old_h, a, b) == (F(1, 27), F(1, 520), F(31, 250), F(53, 360), F(5, 9)),
            'Keep the full original target decrement, source rectangle and denominator direction')
    require(0 < delta0 < delta < F(1, 2) and 0 < 5*rho0 < rcut,
            'The local rectangle cannot cover the middle boundary or the large-r branch')
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    marked = lambda s, rho: B-Q*s+escape(s)+(A-P)*rho
    rows = []

    def row(name, numerator, denominator):
        require(numerator > 0 and denominator > 0, 'Positive original signed reserve and target payment')
        result = {'branch': name, 'signed_reserve_at_K0': numerator,
                  'target_payment_coefficient': denominator, 'decrement_cap': numerator/denominator}
        rows.append(result)
        return result

    for name, s, rho in (
            ('small_r_source_annulus_at_local_radius', delta0, F(0)),
            ('small_r_source_annulus_at_old_radius', delta, F(0)),
            ('small_r_excess_residual_at_zero_escape', F(0), rho0),
            ('small_r_excess_residual_at_local_radius', delta0, rho0)):
        row(name, marked(s, rho), a+b*s+rho)
    row('concentrated_large_r', A*rcut/5, a+b*delta+rcut/5)
    controlling = row('middle_at_old_radius', escape(delta), a+b*delta)
    row('middle_limit_at_half', escape(F(1, 2)), a+b/2)
    row('far_at_half', escape(F(1, 2)), F(1, 4)+F(11, 144))
    row('far_at_one', gamma1, F(1, 4))
    capacity = min(r['decrement_cap'] for r in rows)
    require(capacity == controlling['decrement_cap'] and
            all(r is controlling or r['decrement_cap'] > capacity for r in rows),
            'The unique unchanged outer bottleneck is the middle boundary')
    require(capacity > old_h and A-capacity > P and
            gamma2-gamma1-F(11, 36)*capacity > 0,
            'One residual remains after both payments; both escape polynomials remain concave')
    target = K0-capacity
    require(example_local_bound < target,
            'Conditional local input461 would leave the outer bottleneck unchanged')
    for r in rows:
        r['margin_at_capacity'] = r['signed_reserve_at_K0']-capacity*r['target_payment_coefficient']
        require(r['margin_at_capacity'] >= 0, 'Every unchanged outer branch passes at capacity')
    old_zero = B-capacity*a
    require(old_zero > 0,
            'The same capacity already follows on the entire original near region without any local input')
    # Any positive increment makes the controlling affine condition negative.
    exact_probe = capacity+F(1, 10**12)
    probe_margin = escape(delta)-exact_probe*(a+b*delta)
    require(probe_margin == -F(1, 10**12)*(a+b*delta) < 0,
            'Arithmetic witness for the analytic template ceiling')
    fallbacks = []
    for item in previous['fallbacks']:
        bound = F(item['complete_bound'])
        require(bound < target, 'All eight original complete fallback branches retained')
        fallbacks.append({'branch': item['branch'], 'complete_bound': bound, 'target_gap': target-bound})
    cores = []
    for item in previous['complete_cores']:
        error = F(item['unchanged_error'])
        require(error >= 0 and target+error-403 > 0, 'Every complete terminal error retained with its original sign')
        cores.append({'box': item['box'], 'unchanged_error': error, 'capacity_target_gap': target+error-403})
    denominator_lower = F(previous['positive_denominator_lower_factor'])
    coefficient = F(previous['old_mass_coefficient'])-F(23, 42)*capacity
    require(len(fallbacks) == 8 and len(cores) == 2 and denominator_lower > 0 and coefficient > 0,
            'Complete inherited branch counts, positive division and original target coefficient')
    return encode({'schema': 'erdos7-local-to-global-escape-capacity-v1', 'source_sha256': PINS,
                   'old_K0': K0, 'canonical118_K': F(previous['new_K']), 'already_spent_decrement': old_h,
                   'old_source_radius': delta, 'old_slot_cutoff': rcut,
                   'local_source_radius': delta0, 'local_residual_radius': rho0,
                   'conditional_local_input': {'bound': example_local_bound,
                                               'status': 'Only a conditional example; no local theorem is asserted or verified here.'},
                   'outer_branches': rows, 'template_decrement_capacity': capacity,
                   'template_target_at_capacity': target, 'unused118_decrement': capacity-old_h,
                   'old_zero_escape_margin_at_capacity': old_zero,
                   'conditional_local_target_room': target-example_local_bound,
                   'residual_after_all_charges_at_capacity': A-capacity-P,
                   'above_capacity_arithmetic_witness': {'decrement': exact_probe, 'middle_boundary_margin': probe_margin},
                   'tiny_box_only_escape_decrement_cap': escape(delta0)/(a+b*delta0),
                   'tiny_box_only_residual_decrement_cap': A*rho0/(a+b*delta0+rho0),
                   'positive_denominator_lower_factor': denominator_lower,
                   'target_mass_coefficient_at_capacity': coefficient,
                   'fallbacks': fallbacks, 'complete_cores': cores,
                   'scope': 'Exact capacity and conditional gluing criterion for118 unchanged signed outer branches. The local rectangle does not include the controlling middle boundary. Any hypothetical improved local quotient at most461 leaves the capacity unchanged. The same small unused target room already follows without a local theorem. All original tails, eight fallbacks and two terminal errors retained. No canonical globalK update, local theorem verification, actual-family optimum, Lean result or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('local_global_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact outer escape capacity certificate')
    print('PASS: unchanged outer ceiling, conditional local gluing, eight fallbacks and two complete errors.')
    print('Unused decrement beyond118: '+result['unused118_decrement'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
