#!/usr/bin/env python3
"""Join separate complete J-family errors to the full global source comparison."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_family_global_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/transport/actual_j_reserve_global_comparison.py': '8cf68751ecad78f1cba4f906da4301ad85b0fe2f03e24de71eabca9e862cd815', 'certificates/source_norms/actual_j_reserve_global_comparison.json': 'da4df4c150f87815ae541fb00d5ec9d6254509c62ed7c0e10f46e228c4ffa09b', 'frontier/joint_gap_denominator_escape.py': 'fd1febb46588bc7ffb9472e4741dcb3aae4a5411a3a9331afef7947b387f12de', 'certificates/source_norms/joint_gap_denominator_escape.json': '1da26e786818cc6f2c4c89d04cc100fc1dea4637a3fe5554e4224c0807749fae', 'frontier/j-source/j_face_alignment.py': 'a784f2de6cb88d9b6ae8cdce4d2fe7ad513354ea9d9971999df6cf1c781309eb', 'certificates/source_norms/j-source/j_face_alignment.json': '6874e71b0846d973fedd330f5a8a54bfa457b2cdfe896943db407b8d89bec611', 'frontier/j-source/j_source_labelwise_neighborhood.py': '7bc8cefd82701ec039284474ef62252191a5f0f923a2942f0ddf64cbff06e9a1', 'certificates/source_norms/j-source/j_source_labelwise_neighborhood.json': 'f53c4461ffef8816e989c24e01c254d280aacf767328ca0d15aea840b2bf0011', 'frontier/transport/extended_source_bridge_comparison.py': '4b9e21988e129c3aff849afefe563e92154cca7075e40eff5d20ae33418a403d', 'certificates/source_norms/extended_source_bridge_comparison.json': 'd38c7de4dc87e8467f4ee6e3a4ae3a71affccf652d88aa169e093b888e675451', 'frontier/wide_fresh_full_slot_source_comparison.py': '8b92c7eda87c06ca763d50015b5dd6078730cdb3c7af81aa8a46c989ba3f425d', 'certificates/source_norms/wide_fresh_full_slot_source_comparison.json': '7e8ba6cbd1fa404bf9274cd32e102fa40bf9b7bc7c4ad4c46c2b42b71a61a71a', 'frontier/j-source/j_family_error_reserve.py': '26f0b731e49d9adbf42d7779a35727299af6b0f63b9539dac957f9ea1785beaa', 'certificates/source_norms/j-source/j_family_error_reserve.json': '47c7a26d7a9268b3dc569c98a2eb95c4dd78912a13a8bd312ad7671cf1ff527f', 'profile-notes/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md': 'aea6209e78287b6d9b82e05abe96fc40f8ff6e995a2c8a3d93124151d0baf51f', 'profile-notes/49-full-linear-and-quadratic-carriers-refine-the-frontier.md': 'fb65fb2a313b8cc937a0f1c5ac0314c1fc1cda55c045e27ffe1c2a70d107c931'}


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


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical reader and completed proof inputs')
    io = module('actual_j_io', base/'certificate_io.py')
    read = lambda n: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(n+'.json')))
    old, joint, jface, jnear, wide, low, family = (read('actual_j_reserve_global_comparison'), read('joint_gap_denominator_escape'), read('j-source/j_face_alignment'), read('j-source/j_source_labelwise_neighborhood'), read('extended_source_bridge_comparison'), read('wide_fresh_full_slot_source_comparison'), read('j-source/j_family_error_reserve'))
    pins = dict(PINS)
    for data in (old, joint, jface, jnear, wide, low, family):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda n: module('actual_j_'+n, base/'frontier'/(n+'.py'))
    A, q, K0, H, g1, g2, eK, eJ, eB = (F(joint[k]) for k in (
        'signed_mass_coefficient', 'survival_mass_coefficient', 'old_K0', 'decrement_capacity',
        'first_escape_gap', 'next_escape_gap', 'K_denominator_payment',
        'J_denominator_payment', 'next_denominator_payment'))
    d, R = F(1, 2500), F(1, 100000)
    aH, etaH = H*eK, g2-H*eB
    far_reserve = etaH*d-(aH+etaH)*d*d
    far_payment = eJ-(eJ-eB)*d+(eK-eB)*d*d
    require(far_reserve > 0 and far_payment > 0, 'Positive paired far-J reserve and target slope')
    extra = far_reserve/far_payment
    require(extra > F(old['extra_decrement']), 'The larger actual J neighborhood gives a strict global improvement')
    h = H+extra
    target = K0-h
    require(q == F(23, 42) and H == g1/eJ and h > H and A-q*h > 0
            and K0-F(joint['old_offset'])-h > 0, 'A new target past the original J capacity, with positive true coefficients')

    # Extend the old paired layers by reconstructing the actual53 allocation.
    # No extension is inferred from the previous H-limited wrapper.
    source = module('actual_j_source', base/'verify_joint_frontier.py')
    allocated, control = load('allocated_seven_thresholds'), load('global_control_faces')
    old53, faces, survival, dictionary = (read(n) for n in (
        'allocated_seven_thresholds', 'global_control_faces', 'joint_survival_carriers', 'k_signed_gap_dictionary'))
    metadata = []
    for i, vertex in enumerate(source.vertices()):
        dat = source.data(vertex)
        metadata.append({'index': i, 's': dat[3], 'D': dat[4]})
    rows, stats = allocated.reconstruct(source, survival, metadata)
    require(encode(stats) == old53['allocation_statistics'] and len(rows) == 1296,
            'Fresh original allocated margins and their complete conditional digest')
    Kset = {(r['index'], r['carrier_index']) for r in faces['targets']['K']['zero_controls']}
    Jset = {(r['index'], r['carrier_index']) for r in faces['targets']['J']['zero_controls']}
    require(len(Kset) == 6 and len(Jset) == 18 and not Kset & Jset, 'Original disjoint K/J control sets')
    values, lookup = list(map(F, dictionary['rational_values'])), dictionary['lower_gap_value_indices']
    original, lower, payments = [], [], []
    for i, row in enumerate(rows):
        require(row['index'] == i and len(row['conditional']) == 18, 'Every original carrier row')
        for j, cond in enumerate(row['conditional']):
            require(tuple(cond['carrier']) == allocated.CARRIERS[j] == tuple(faces['carriers'][j]),
                    'Original source and carrier ordering')
            dc, margin, raw = cond['D_c'], cond['M'], row['s']
            gap = values[lookup[18*i+j]]
            payment = q*dc+margin
            require(0 < payment <= dc <= raw, 'Actual original lower denominator and survivor interval')
            original.extend(((i, j, 'D_c', gap), (i, j, 's', gap+A*(raw-dc))))
            lower.append((i, j, dc, raw, gap, payment))
            payments.append((i, j, dc, margin, payment))
    require(control.digest(original) == joint['complete_original_endpoint_table_sha256']
            and control.digest(payments) == joint['same_source_denominator_table_sha256'],
            'Every original gap remains paired with the same allocated denominator')
    layer_checks = []
    for decrement in (F(0), h):
        floors = (-decrement*eK, g1-decrement*eJ, g2-decrement*eB)
        slacks, outside_controls = [], []
        for i, j, dc, raw, gap, payment in lower:
            layer = 0 if (i, j) in Kset else 1 if (i, j) in Jset else 2
            slack = gap-decrement*payment-floors[layer]
            require(slack >= 0 and slack+(A-q*decrement)*(raw-dc) >= 0,
                    'Both mass endpoints of every paired row hold beyond H')
            slacks.append(slack)
            if layer == 2 and slack == 0:
                outside_controls.append((i, j))
        require(outside_controls == [(386, 14), (592, 13)], 'The same exact outside controllers after extension')
        layer_checks.append({'decrement': decrement, 'floors': floors,
                             'lower_checks': len(lower), 'upper_checks': len(lower),
                             'minimum_slack': min(slacks), 'outside_controllers': outside_controls})
    fK, fJ, fB = -h*eK, g1-h*eJ, g2-h*eB
    a, eta = fJ-fK, fB-fJ
    require(fK < fJ < 0 < fB and a > 0 and eta > 0, 'J floor is now negative and is retained honestly')
    Anew = A-q*h

    # The full local domains, not just isolated parameter points.
    require(tuple(F(low['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 20), F(1, 1000), F(1, 200))
            and tuple(F(wide['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 12), F(1, 3000), F(1, 600)), 'Both complete actual source rectangles')
    scale = 10**30

    def bracket(x):
        n = isqrt(x.numerator*scale*scale//x.denominator)
        lo, hi = F(n, scale), F(n+1, scale)
        require(lo*lo <= x < hi*hi and 0 <= lo <= 1, 'Integer-certified square-root enclosure')
        return lo, hi

    inner_endpoints = []
    for branch, left, right, residual in (
            ('low_outer', F(0), F(1, 20), F(1, 1000)),
            ('bridge_outer', F(1, 20), F(1, 12), F(1, 3000))):
        for side, sigma in (('left', left), ('right', right)):
            lo, hi = bracket(1-sigma)
            jcap = (1-lo)**2
            gap = fK*(1-sigma)+fB*sigma+(fJ-fB)*jcap+Anew*residual
            require(gap > 0, 'All inner complementary endpoints have strictly positive full signed margin')
            inner_endpoints.append({'branch': branch+'_'+side, 'sigma': sigma, 'residual_lower': residual,
                                    'sqrt_lower': lo, 'sqrt_upper': hi, 'margin_lower': gap})
    require(fK+fJ-2*fB < 0 and fJ-fB < 0, 'Concavity in sqrt(1-sigma) and correct J-mass substitution')

    # The outer region has x=qK<=11/12. Split at y=qJ=1-d.
    cap = F(11, 12)
    require(0 < d*d < cap and d+R < F(1, 1000), 'Exact J neighborhood inside the ordinary136 theorem domain')
    far_small = fJ+eta*d-(a+eta)*d*d
    far_split = fJ+2*eta*d-(a+2*eta)*d*d
    lo, hi = bracket(cap)
    far_large = fJ+2*eta*lo-(a+2*eta)*cap
    require(far_small == 0 and far_split > far_small and far_large > 0,
            'Every source outside the J neighborhood passes both concave subinterval endpoints')
    near_high = fJ-a*d*d+Anew*R
    require(near_high > 0, 'The same actual residual pays the entire negative J floor above R')
    jprovider = load('j-source/j_family_error_reserve')
    require(jprovider.calculate(base) == family, 'Reconstruct the complete197 family theorem and all its original source guards')
    family_bound = jprovider.reserve_bound(d, R)
    require(jprovider.encode(family_bound) == {k: v for k, v in next(
        r for r in family['complete_rectangles'] if F(r['source_radius']) == d and F(r['residual_radius']) == R).items()
        if k not in ('predecessor_complete_error', 'predecessor_reserve_lower', 'reserve_gain')},
        'The exact complete larger J-neighborhood theorem, without mixing separate source budgets')
    reserve = family_bound['old49_replacement_reserve_lower']
    require(reserve == F(499570949, 75937500000), 'The certified whole rectangular J reserve')
    weight = F(jface['direction40_weight'])
    engine = load('source_barrier_saturation').Experiment(base)
    require(weight == engine.weights[40] > 0 and F(jface['old49_replacement_reserve']) == F(79, 1944)
            and all(pins.get(p) == v for p, v in engine.pins.items()),
            'The actual original complete direction40 coefficient and same source closure')
    near_low = fJ-a*d*d+weight*reserve
    require(reserve > 0 and near_low > 0, 'One original identity reserve removes the J near-source obstruction')

    locals_out = []
    for name, data in (('wide_fresh_full_slot_source_comparison', low), ('extended_source_bridge_comparison', wide)):
        c, heads, par = data['comparison'], data['complete_heads'], data['parameters']
        indices = [r['index'] for r in heads['mean_costs']+heads['quadratic_costs']+c['simple_costs']]+[0, 16, 46, 47]
        bound, den, num, offset = (F(c[k]) for k in ('comparison_upper', 'denominator_at_mass_floor', 'signed_endpoint', 'offset'))
        require(sorted(indices) == c['all_original_indices'] == list(range(52))
                and den > 0 and F(c['remaining_S_coefficient']) > 0
                and bound == offset+num/den < target and F(par['rbar']) == 5*F(par['rho']),
                'All original52 local costs, full denominators and actual mass/slot ranges')
        locals_out.append({'source': name, 'source_radius': F(par['delta']), 'residual_radius': F(par['rho']),
                           'complete_bound': bound, 'candidate_target_margin': target-bound})
    fallbacks = [{'branch': r['branch'], 'complete_bound': F(r['complete_bound']),
                  'candidate_target_gap': target-F(r['complete_bound'])} for r in old['fallbacks']]
    cores = [{'box': r['box'], 'unchanged_error': F(r['unchanged_error']),
              'candidate_complete_gap': target+F(r['unchanged_error'])-403} for r in old['complete_cores']]
    require(len(fallbacks) == 8 and min(r['candidate_target_gap'] for r in fallbacks) > 0
            and len(cores) == 2 and min(r['candidate_complete_gap'] for r in cores) > 0
            and F(old['positive_denominator_lower_factor']) > 0, 'Every fallback and terminal error remains; problem unresolved')
    return encode({'schema': 'erdos7-j-family-global-comparison-v1', 'source_sha256': pins,
        'old_K0': K0, 'previous196_K': F(old['candidate_K']), 'candidate_K': target,
        'original_paired_decrement_capacity': H, 'extra_decrement': extra, 'decrement_from_K0': h,
        'far_J_reserve_at_H': far_reserve, 'far_J_extra_payment': far_payment,
        'improvement_over196': F(old['candidate_K'])-target,
        'original_allocation_conditional_sha256': stats['conditional_margin_sha256'],
        'complete_original_endpoint_table_sha256': control.digest(original),
        'same_source_denominator_table_sha256': control.digest(payments),
        'extended_layer_checks': layer_checks, 'target_floors': {'K': fK, 'J': fJ, 'outside': fB},
        'remaining_actual_residual_coefficient': Anew, 'sqrt_bracket_denominator': scale,
        'inner_complement_endpoints': inner_endpoints,
        'outer_K_mass_cap': cap, 'J_source_radius': d, 'J_residual_radius': R,
        'far_J_small_x_margin': far_small, 'far_J_split_margin': far_split,
        'far_J_large_x_margin': far_large, 'outer_sqrt_lower': lo, 'outer_sqrt_upper': hi,
        'near_J_high_residual_margin': near_high, 'complete_J_family_bound': family_bound,
        'J_identity_reserve': reserve, 'direction40_weight': weight,
        'near_J_low_residual_margin': near_low, 'local_complete_bounds': locals_out,
        'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary complete global comparison beyond the old paired-table J capacity. The original true-function coefficients are reweighted before Jensen, with every original allocated row checked at the new target. Both full local source rectangles and all complementary source cases are covered. In the actual J neighborhood only the original direction40 margin is replaced using197; its separate complete independent-label family errors and original positive weight remain. Every52 local cost, full denominator, eight fallbacks and both terminal errors remain. No Lean verification, actual-family sharpness or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true'); modes.add_argument('--check', action='store_true')
    args = parser.parse_args(); result = calculate(args.base)
    io = module('actual_j_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete family-reserve global comparison')
    print('PASS: complete J-family reserve and full source union; global K='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr); sys.exit(1)
