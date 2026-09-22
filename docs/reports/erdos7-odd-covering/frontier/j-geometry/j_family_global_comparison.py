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
CERTIFICATE = 'certificates/source_norms/j-geometry/j_family_global_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/source-budgets/actual_j_reserve_global_comparison.py': '73a5e33d21122050d93b95681cb81393fc182317025be0cd7afa8b914e75a8ca', 'certificates/source_norms/source-budgets/actual_j_reserve_global_comparison.json': 'ae43c59a6e923b7e6d1155d2d913426bea610fd9532a01756eb3a22dd79170fd', 'frontier/cover-geometry/joint_gap_denominator_escape.py': 'bc5bd10d49a0e1df10fac0a5f6e6f6f931e0a87808e587aca35fcc55bebad52f', 'certificates/source_norms/cover-geometry/joint_gap_denominator_escape.json': '414d035791892a6d9e8cf16e522b58e7257b99743e845ce5a882aa94bce783e5', 'frontier/j-geometry/j_face_alignment.py': '05074f0937efcb2cccc1a172e0717b89656f976d3e50543d31a27e7591b927ab', 'certificates/source_norms/j-geometry/j_face_alignment.json': '75433cab317fb492b5e8a9b36bc9b8d8671f5bcfe450cc7a2e37efe5378108d5', 'frontier/j-geometry/j_source_labelwise_neighborhood.py': '8c0936bf71a26897ac2156ec4878cb5695d816931264f924764e534436bacdca', 'certificates/source_norms/j-geometry/j_source_labelwise_neighborhood.json': 'e0332bb28d282bc9429cc135f74c232fb8d2a4df31416ed3edd2367184ba4902', 'frontier/source-budgets/extended_source_bridge_comparison.py': '2c40c799b23de126166ba8e95c942f36f27587896d536a2fece790b508ffe92a', 'certificates/source_norms/source-budgets/extended_source_bridge_comparison.json': '381ee12bc564ba3c36fb1ff1b14de9d237bff16c5bf7875fdae8e2bf6c66bea2', 'frontier/source-budgets/wide_fresh_full_slot_source_comparison.py': '4180ce2f7cb27179e7f8f10092d31c61f7da90e4c03623c07ff796c43f9a599d', 'certificates/source_norms/source-budgets/wide_fresh_full_slot_source_comparison.json': '31f20d1d614a6b961fe00642340a9fc3b5ac61d16862e02617337dabbbd8d427', 'frontier/j-geometry/j_family_error_reserve.py': '8f531511ef044a1dc881852ea502af42a49cc59036a39c134fe13eaf3412170b', 'certificates/source_norms/j-geometry/j_family_error_reserve.json': 'ab5043b757c5c79e11276bd7fc6b2cf9c9f36a530b9b59bbb6eaaa51bdbd578c', 'profile-notes/129-192/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md': '845d9a84f41391240f05f8c5be35cf074d6614abf1dfc493046e8619521f3945', 'profile-notes/001-064/49-full-linear-and-quadratic-carriers-refine-the-frontier.md': '8a34e4b32351d3c115d0f79fa6711b4971b15308a53c5be9bc15c75865a43427'}


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
    read = lambda n: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', n+'.json')))
    old, joint, jface, jnear, wide, low, family = (read(n) for n in (
        'actual_j_reserve_global_comparison', 'joint_gap_denominator_escape', 'j_face_alignment',
        'j_source_labelwise_neighborhood', 'extended_source_bridge_comparison',
        'wide_fresh_full_slot_source_comparison', 'j_family_error_reserve'))
    pins = dict(PINS)
    for data in (old, joint, jface, jnear, wide, low, family):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda n: module('actual_j_'+n, io.named_artifact(base/'frontier', n+'.py'))
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
    jprovider = load('j_family_error_reserve')
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
