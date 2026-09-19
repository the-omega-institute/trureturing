#!/usr/bin/env python3
"""Retain the marked theorem's own slot cutoff in the complete outer union."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/capped_slot_outer_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/full_slot_union_outer_comparison.py': '1182271c5399fc9f49eaa5193ced7060be672f8d46a8d6dafbddf8d62d9ce5b7', 'certificates/source_norms/full_slot_union_outer_comparison.json': '7bd2477f008ac55460ff20f798818d5174fd8e1c6c849181b1c952936878cfaa', 'profile-notes/155-the-signed-mass-bound-reaches-the-current-source-credit-ceiling.md': 'c09d0cc9716bbd72463ec9afb4d02482264619661ae502aaa11cd684a7120269', 'profile-notes/147-source-dependent-credits-cross-the-old-middle-bottleneck.md': '2e83e2915b88d81edf294704be80dcc3e22bc90e6c0fb95a811c9c6a89a91373'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def calculate(base):
    require(PINS, 'Pinned complete union and original unsimplified reserve')
    io = module('capped_slot_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    old = read('full_slot_union_outer_comparison')
    pins = dict(PINS)
    for path, pin in old['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    prior = module('capped_slot_prior', base/'frontier/full_slot_union_outer_comparison.py')
    require(old == prior.calculate(base), 'Reconstruct every old domain, endpoint, fallback and terminal term')
    source, outer = read('shared_slot_gap_global'), read('product_source_outer_comparison')
    mass = read('joint_mass_outer_comparison')
    A = F(source['conservative_mass_coefficient'])
    P, L5 = (F(outer[k]) for k in ('uniform_cost_residual_penalty', 'actual_slot_motion_residual_payment'))
    L = L5/5
    original = read('source_dependent_outer_comparison')
    require(L == F(original['slot_motion_price'])
            and L5 == F(original['slot_motion_residual_price']),
            'Exact unsimplified147 slot price and its old residual substitution')
    floor, cutoff = F(old['low_complement_residual_floor']), F(old['original_outer_slot_cutoff'])
    require((floor, cutoff) == (F(1, 1000), F(3, 1000)) and 5*floor > cutoff and L > 0,
            'The actual marked cutoff is strictly sharper than the residual-implied slot bound')
    improvement_in_reserve = L*(5*floor-cutoff)
    rows = []
    for entry in old['complete_outer_endpoints']:
        row = dict(entry)
        row['reserve_at_K0'] = F(row['reserve_at_K0'])
        row['target_payment_coefficient'] = F(row['target_payment_coefficient'])
        if row['branch'].startswith('low_source_marked_'):
            require(F(row['residual_lower']) == floor, 'The same low-source complementary residual')
            row['reserve_at_K0'] += improvement_in_reserve
        row['decrement_capacity'] = row['reserve_at_K0']/row['target_payment_coefficient']
        rows.append(row)
    h = min(row['decrement_capacity'] for row in rows)
    controllers = [row['branch'] for row in rows if row['decrement_capacity'] == h]
    require(len(rows) == 11 and controllers == ['residual_bridge_old_source_radius'],
            'All intervals remain, with the lower source bridge now controlling')
    for row in rows:
        row['margin'] = row['reserve_at_K0']-h*row['target_payment_coefficient']
    g1, g2 = F(source['first_escape_gap']), F(source['next_escape_gap'])
    B2 = F(mass['source_credit_polynomial']['positive_quadratic'])
    require(all(row['margin'] >= 0 for row in rows) and A-h-P > 0 and A-h > 0
            and g2-g1-B2 > 0 and g2-g1-F(11, 36)*h > 0,
            'New residual coefficients and all interval concavity conditions hold')
    target = F(old['old_K0'])-h
    local = old['local_complete_bounds']
    require(all(F(row['complete_bound']) < target for row in local), 'Both original complete local rectangles remain below target')
    fallbacks = []
    for row in old['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target, 'Every original complete fallback remains below target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'candidate_target_gap': target-bound})
    cores = []
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error > 403, 'No terminal error is dropped and the problem remains unresolved')
        cores.append({'box': row['box'], 'unchanged_error': error, 'candidate_complete_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2
            and F(old['positive_denominator_lower_factor']) > 0
            and F(source['old_mass_coefficient'])-F(23, 42)*h > 0
            and target < F(old['candidate_K']), 'Complete positive division and strict global improvement')
    return prior.encode({'schema': 'erdos7-capped-slot-outer-comparison-v1', 'source_sha256': pins,
        'low_source_radius': F(old['low_source_radius']), 'low_residual_radius': floor,
        'wide_source_radius': F(old['wide_source_radius']), 'wide_residual_radius': F(old['wide_residual_radius']),
        'original_outer_slot_cutoff': cutoff, 'slot_loss_price': L,
        'old_slot_payment_at_residual_floor': 5*L*floor, 'new_slot_payment': L*cutoff,
        'marked_reserve_improvement': improvement_in_reserve,
        'old_K0': F(old['old_K0']), 'decrement_from_K0': h, 'candidate_K': target,
        'previous172_K': F(old['candidate_K']), 'improvement_over172': F(old['candidate_K'])-target,
        'marked_residual_coefficient': A-h-P, 'unmarked_residual_coefficient': A-h,
        'complete_outer_endpoints': rows, 'controlling_branches': controllers,
        'local_complete_bounds': local, 'fallbacks': fallbacks, 'complete_cores': cores,
        'original_fixed_outer_cost_count': old['original_fixed_outer_cost_count'],
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary full-domain refinement of172. The marked branch pays L times its original r cutoff, using the unsimplified155 reserve; no new marked theorem outside its domain. Both complete source rectangles, eleven outside endpoints, all eight fallbacks, both terminal errors, independent original labels and complete tails remain. No Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('capped_slot_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete capped-slot certificate')
    print('PASS: complete global comparison='+str(float(F(result['candidate_K'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
