#!/usr/bin/env python3
"""Complete global comparison with the enlarged certified K residual rectangle."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/expanded_bridge_global_comparison.json'
PINS = {
    'frontier/j-geometry/j_affine_global_comparison.py': 'f7a4b91d41640900c68461eaa64a7706c35bd4f3d9ed3d73381e05e494acd2fa',
    'certificates/source_norms/j-geometry/j_affine_global_comparison.json': '34c1b138d902232919cdcd9b40529277d56c02a9921ae2561f621c7ecc662b54',
    'frontier/comparison-bounds/expanded_bridge_residual_comparison.py': '587c298f3990161974eaee890ba26f153ad295e15747b9959aca3c063df4a6cb',
    'certificates/source_norms/comparison-bounds/expanded_bridge_residual_comparison.json': 'eef5e7aa20f28f5804cb0585baeff45b1191b7818a978e05760fbd58a7d780df',
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/j-geometry/j_aggregate_layer_global_comparison.py': 'cd50ae6d9165f254fe35dd3cadc3f15f02da79b2a32624ff7c0455662125cabd',
    'certificates/source_norms/j-geometry/j_aggregate_layer_global_comparison.json': 'c711a02b8ddfa20f9e8657ba7513b8e05ca0501c09142b46b6cb96dcfebc78b6',
    'frontier/j-geometry/j_affine_margin_reserve.py': '627dcee1ac3b667b4f7fa6ca40a724bb26bb0c415fe8da8409a2691b47557979',
    'certificates/source_norms/j-geometry/j_affine_margin_reserve.json': 'd01e44a1d4264e1a4d959848e21481dfa517b2d1a8683d026d382fefa2a9aa10',
    'frontier/moments-survival/wide_expanded_seven_survival.py': 'f34e659d2ac3070dc58bc7f54427beaae2edf34b36e1d7f7109ee2f7c8d4dce2',
    'certificates/source_norms/moments-survival/wide_expanded_seven_survival.json': '61260300e44a592bf87c6fcce57f4208a6ed63e1cf27d18937c6dbe71fa086ba',
}


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
        'j_aggregate_layer_global_comparison', 'three_layer_product_escape', 'j_face_alignment',
        'j_source_labelwise_neighborhood', 'extended_source_bridge_comparison',
        'wide_fresh_full_slot_source_comparison', 'j_affine_margin_reserve'))
    upgraded = read('wide_expanded_seven_survival')
    predecessor = read('j_affine_global_comparison')
    enlarged = read('expanded_bridge_residual_comparison')
    pins = dict(PINS)
    for data in (old, joint, jface, jnear, wide, low, family, upgraded, predecessor, enlarged):
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
    g3, eC = F(joint['third_escape_gap']), F(joint['third_denominator_payment'])
    d, R = F(1, 1112), F(317, 25000000)
    t0 = d/2
    far_reserve = -H*eK*t0*t0+2*(g3-H*eC)*t0*(1-t0)
    far_payment = eK*t0*t0+eJ*(1-t0)**2+2*eC*t0*(1-t0)
    require(far_reserve > 0 and far_payment > 0 and t0 == F(1, 2224),
            'Positive true four-layer J-alternative reserve and its own target payment')
    extra = far_reserve/far_payment
    require(extra > F(old['extra_decrement']), 'The aggregate exclusion improves the same complete J neighborhood')
    h = H+extra
    target = K0-h
    require(target < F(predecessor['candidate_K']), 'Strict improvement of the complete213 global bound')
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
    layer_data = read('k_next_escape_layers')
    Bset = {(r['index'], r['carrier_index']) for r in layer_data['next_layer_controls']}
    require(Bset == {(386, 14), (592, 13)} and not Bset & (Kset | Jset),
            'The original two next controls, disjoint from K and J')
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
        floors = (-decrement*eK, g1-decrement*eJ, g2-decrement*eB, g3-decrement*eC)
        slacks, outside_controls = [], []
        for i, j, dc, raw, gap, payment in lower:
            layer = 0 if (i, j) in Kset else 1 if (i, j) in Jset else 2 if (i, j) in Bset else 3
            slack = gap-decrement*payment-floors[layer]
            require(slack >= 0 and slack+(A-q*decrement)*(raw-dc) >= 0,
                    'Both mass endpoints of every paired row hold beyond H')
            slacks.append(slack)
            if layer == 3 and slack == 0:
                outside_controls.append((i, j))
        require(outside_controls == [(386, 15), (386, 16), (386, 17), (592, 15), (592, 16), (592, 17)],
                'The same six exact fourth-layer controls after extension')
        layer_checks.append({'decrement': decrement, 'floors': floors,
                             'lower_checks': len(lower), 'upper_checks': len(lower),
                             'minimum_slack': min(slacks), 'outside_controllers': outside_controls})
    fK, fJ, fB, fC = -h*eK, g1-h*eJ, g2-h*eB, g3-h*eC
    a, u, v = fJ-fK, fC-fB, fC-fJ
    require(fK < fJ < 0 < fB < fC and a > 0 and u > 0 and v > 0,
            'The negative J floor and all positive aggregate exclusion coefficients')
    Anew = A-q*h

    # The full local domains, not just isolated parameter points.
    require(tuple(F(low['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 20), F(1, 1000), F(1, 200))
            and tuple(F(wide['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 12), F(1, 3000), F(1, 600)), 'Both complete actual source rectangles')
    require(tuple(F(enlarged['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 12), F(1, 2300), F(1, 460)), 'Complete215 enlarged residual rectangle')
    scale = 10**30

    def bracket(x):
        n = isqrt(x.numerator*scale*scale//x.denominator)
        lo, hi = F(n, scale), F(n+1, scale)
        require(lo*lo <= x < hi*hi and 0 <= lo <= 1, 'Integer-certified square-root enclosure')
        return lo, hi

    inner_endpoints = []
    for branch, left, right, residual in (
            ('low_outer', F(0), F(1, 20), F(1, 1000)),
            ('bridge_outer', F(1, 20), F(1, 12), F(1, 2300))):
        for side, sigma in (('left', left), ('right', right)):
            lo, hi = bracket(1-sigma)
            jcap = (1-lo)**2
            for name, gap in (
                    ('B', fK*(1-sigma)+fB*sigma+Anew*residual),
                    ('J', fK*(1-sigma)+fC*sigma+(fJ-fC)*jcap+Anew*residual)):
                require(gap > 0, 'Both aggregate alternatives pass every full inner endpoint')
                inner_endpoints.append({'branch': branch+'_'+side, 'alternative': name,
                                        'sigma': sigma, 'residual_lower': residual,
                                        'sqrt_lower': lo, 'sqrt_upper': hi, 'margin_lower': gap})
    require(fK-fB < 0 and fK+fJ-2*fC < 0 and fJ-fC < 0,
            'Both complete alternatives are concave with correct signed root substitution')

    # The outer region has x=qK<=11/12. Split at y=qJ=1-d.
    cap = F(11, 12)
    require(0 < d*d < cap and d+R < F(1, 1000), 'Exact J neighborhood inside the ordinary136 theorem domain')
    require(t0*t0 < cap and (1-t0)**2 >= 1-d,
            'The exact J-complement transition1-sqrt(1-d) is at least d/2')
    far_B = fK*cap+fB*(1-cap)
    far_J_start = fK*t0*t0+fJ*(1-t0)**2+2*fC*t0*(1-t0)
    lo, hi = bracket(cap)
    far_J_end = fK*cap+fC*(1-cap)+(fJ-fC)*(1-lo)**2
    require(far_B > 0 and far_J_start == 0 and far_J_end > 0 and u+v > 0,
            'The aggregate far-J region passes all three complete concave endpoints')
    near_high = fJ-a*d*d+Anew*R
    require(near_high > 0, 'The same actual residual pays the entire negative J floor above R')
    jprovider = load('j_affine_margin_reserve')
    require(jprovider.calculate(base) == family,
            'Reconstruct212 affine source proof checks and every inherited197 guard and tail')
    error_provider = load('j_family_error_reserve')
    family_bound = jprovider.reserve_bound(d, R, error_provider)
    original_family = error_provider.reserve_bound(d, R)
    reserve = family_bound['old49_replacement_reserve_lower']
    require(family_bound['complete_zero7_error'] == original_family['complete_zero7_error']
            and reserve == F(79, 1944)-6*d-original_family['complete_zero7_error']
            == original_family['old49_replacement_reserve_lower']+48*d,
            'The general212 whole-rectangle theorem changes only the old49 source price')
    weight = F(jface['direction40_weight'])
    engine = load('source_barrier_saturation').Experiment(base)
    require(weight == engine.weights[40] > 0 and F(jface['old49_replacement_reserve']) == F(79, 1944)
            and all(pins.get(p) == v for p, v in engine.pins.items()),
            'The actual original complete direction40 coefficient and same source closure')
    near_low = fJ-a*d*d+weight*reserve
    require(reserve > 0 and near_low > 0, 'One original identity reserve removes the J near-source obstruction')

    locals_out = []
    original_terms = read('whole_quadratic_same_head')
    require('certificates/source_norms/moments-survival/whole_quadratic_same_head.json' in pins,
            'The original signed numerator coefficients remain pinned')
    require(len(upgraded['domains']) == 2, 'Exactly both complete208 local domains')
    for name, data in (('wide_fresh_full_slot_source_comparison', low), ('extended_source_bridge_comparison', wide)):
        previous, heads, par = data['comparison'], data['complete_heads'], data['parameters']
        matches = [row for row in upgraded['domains'] if row['source'] == name]
        require(len(matches) == 1, 'One independently certified complete208 local replacement')
        doc = matches[0]
        c = doc['comparison']
        indices = [r['index'] for r in heads['mean_costs']+heads['quadratic_costs']+c['simple_costs']]+[0, 16, 46, 47]
        bound, den, num, offset = (F(c[k]) for k in ('comparison_upper', 'denominator_at_mass_floor', 'signed_endpoint', 'offset'))
        require(doc['parameters'] == par and doc['guards'] == data['guards']
                and sorted(indices) == c['all_original_indices'] == list(range(52))
                and all(c[k] == previous[k] for k in ('cost_groups', 'simple_costs', 'heavy_costs',
                    'signed_endpoint', 'mass_coefficient', 'offset'))
                and all(c[k] == original_terms[k] for k in ('signed_mass_coefficient', 'complete_square_weight'))
                and num == F(c['signed_mass_coefficient'])*F(53, 360)
                            +sum(F(v) for v in c['cost_groups'].values()),
                'Every original52 numerator cost, signed mass, square and full-domain guard reconstructed')
        count_rows = doc['denominator_costs']
        require(len(count_rows) == 5
                and all(F(row['weight']) == (F(1, 7) if i < 4 else F(1, 6))
                        and row['hinge_coefficients'] == heads['denominator_costs'][i]['coefficients']
                        and F(row['uniform_upper']) == min(F(row['previous_upper']), F(row['scan']['upper']))
                        for i, row in enumerate(count_rows)),
                'The four original count blocks and separate AP13 complete bounds')
        loss = sum(F(row['weight'])*F(row['uniform_upper']) for row in count_rows)
        adopted = min(loss, F(heads['denominator_shared']['upper']))
        cE, H1 = F(1)-F(1, 614922), F(doc['complete_H1_upper'])
        require(H1 == F(data['complete_H1']['upper'])
                and loss == F(doc['separate_survival_loss_upper'])
                and adopted == F(doc['adopted_survival_loss_upper'])
                and F(doc['actual_survivor_mass_coefficient']) == cE
                and F(doc['actual_survivor_mass_floor']) == F(53, 360)
                and den == cE*F(53, 360)-adopted-H1/55902 > 0
                and F(c['remaining_S_coefficient']) == (bound-offset)*cE-F(c['mass_coefficient']) > 0
                and (target-offset)*cE-F(c['mass_coefficient']) > 0
                and bound == offset+num/den < target and F(par['rbar']) == 5*F(par['rho']),
                'Full208 denominator, complete tail payments and positive actual-S coefficient at the new target')
        locals_out.append({'source': name, 'proof': 'wide_expanded_seven_survival',
            'source_radius': F(par['delta']), 'residual_radius': F(par['rho']),
            'complete_bound': bound, 'candidate_target_margin': target-bound,
            'denominator_at_mass_floor': den, 'signed_numerator_at_mass_floor': num,
            'actual_S_coefficient_at_candidate': (target-offset)*cE-F(c['mass_coefficient']),
            'all_original_indices': sorted(indices), 'full_count_tail': doc['full_count_tail']})
    require(locals_out[0]['full_count_tail'] == locals_out[1]['full_count_tail'],
            'The same complete original count-tail law in both208 rectangles')
    enlarged_provider = load('expanded_bridge_residual_comparison')
    require(enlarged_provider.calculate(base) == enlarged,
            'Recompute215 whole-domain guards,3120 branch checks,26 complete objectives and52 costs')
    study = load('k_neighborhood_radius_study').Study(base)
    reconstructed = load('wide_expanded_seven_survival').original_numerator(study, enlarged)
    c, par, heads = enlarged['comparison'], enlarged['parameters'], enlarged['complete_heads']
    require(encode(reconstructed['cost_groups']) == c['cost_groups']
            and reconstructed['all_original_indices'] == list(range(52)),
            'Independent reconstruction of every transported numerator cost and signed term')
    bound, den, num, offset = (F(c[k]) for k in
        ('comparison_upper', 'denominator_at_mass_floor', 'signed_endpoint', 'offset'))
    cE, H1 = F(1)-F(1, 614922), F(enlarged['complete_H1']['upper'])
    require(len(heads['denominator_costs']) == 5
            and all(F(row['weight']) == (F(1, 7) if i < 4 else F(1, 6))
                    and row['coefficients'] == wide['complete_heads']['denominator_costs'][i]['coefficients']
                    for i, row in enumerate(heads['denominator_costs']))
            and den == cE*F(53, 360)-F(heads['denominator_shared']['upper'])-H1/55902 > 0
            and num == reconstructed['signed_endpoint']
            and offset == reconstructed['offset']
            and F(c['remaining_S_coefficient']) == (bound-offset)*cE-reconstructed['mass_coefficient'] > 0
            and (target-offset)*cE-reconstructed['mass_coefficient'] > 0
            and bound == offset+num/den < target,
            'Full transported denominator and every actual-S coefficient at the new global target')
    locals_out.append({'source': 'expanded_bridge_residual_comparison',
        'proof': 'expanded_bridge_residual_comparison',
        'source_radius': F(par['delta']), 'residual_radius': F(par['rho']),
        'complete_bound': bound, 'candidate_target_margin': target-bound,
        'denominator_at_mass_floor': den, 'signed_numerator_at_mass_floor': num,
        'actual_S_coefficient_at_candidate': (target-offset)*cE-reconstructed['mass_coefficient'],
        'all_original_indices': list(range(52)),
        'full_count_tail': locals_out[0]['full_count_tail'],
        'actual_survivor_mass_coefficient': cE,
        'complete_H1_tail_payment': H1/55902,
        'reused_original_head_evaluations': heads['reused_original_head_evaluations'],
        'finite_branch_transport_checks': heads['finite_branch_transport_checks']})
    fallbacks = [{'branch': r['branch'], 'complete_bound': F(r['complete_bound']),
                  'candidate_target_gap': target-F(r['complete_bound'])} for r in old['fallbacks']]
    cores = [{'box': r['box'], 'unchanged_error': F(r['unchanged_error']),
              'candidate_complete_gap': target+F(r['unchanged_error'])-403} for r in old['complete_cores']]
    require(len(fallbacks) == 8 and min(r['candidate_target_gap'] for r in fallbacks) > 0
            and len(cores) == 2 and min(r['candidate_complete_gap'] for r in cores) > 0
            and F(old['positive_denominator_lower_factor']) > 0, 'Every fallback and terminal error remains; problem unresolved')
    return encode({'schema': 'erdos7-expanded-bridge-global-comparison-v1', 'source_sha256': pins,
        'old_K0': K0, 'previous200_K': F(old['candidate_K']), 'candidate_K': target,
        'previous213_K': F(predecessor['candidate_K']),
        'improvement_over213': F(predecessor['candidate_K'])-target,
        'original_paired_decrement_capacity': H, 'extra_decrement': extra, 'decrement_from_K0': h,
        'far_J_reserve_at_H': far_reserve, 'far_J_extra_payment': far_payment,
        'conservative_J_transition_t': t0,
        'improvement_over200': F(old['candidate_K'])-target,
        'original_allocation_conditional_sha256': stats['conditional_margin_sha256'],
        'complete_original_endpoint_table_sha256': control.digest(original),
        'same_source_denominator_table_sha256': control.digest(payments),
        'extended_layer_checks': layer_checks, 'target_floors': {'K': fK, 'J': fJ, 'B': fB, 'outside': fC},
        'aggregate_product_constraint': 'sqrt(qK+qB)+sqrt(qJ)<=1',
        'aggregate_lower_in_sqrt_J': 'fB+(fK-fB)*x+2u*z-(u+v)*z^2, z=sqrt(qJ),u=fC-fB,v=fC-fJ',
        'remaining_actual_residual_coefficient': Anew, 'sqrt_bracket_denominator': scale,
        'inner_complement_endpoints': inner_endpoints,
        'outer_K_mass_cap': cap, 'J_source_radius': d, 'J_residual_radius': R,
        'far_J_B_endpoint': far_B, 'far_J_start_endpoint': far_J_start,
        'far_J_end_endpoint': far_J_end, 'outer_sqrt_lower': lo, 'outer_sqrt_upper': hi,
        'near_J_high_residual_margin': near_high, 'complete_J_family_bound': family_bound,
        'J_identity_reserve': reserve, 'direction40_weight': weight,
        'near_J_low_residual_margin': near_low, 'local_complete_bounds': locals_out,
        'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary complete global comparison using the aggregate K/next-layer square-root exclusion and215 enlarged full K residual rectangle. All four original paired layers are freshly checked at the new target before genuine-function Jensen. Both213 local rectangles remain certified by208, and the enlarged rectangle is independently reconstructed from215 with all52 costs. Both full inner alternatives, all three far-J endpoints and both near-J cases are covered. The actual old49 direction40 margin is replaced once using212, retaining every197 family error and infinite tail. The full denominator, eight fallbacks and both terminal errors remain. No Lean verification, actual-family sharpness or unrestricted Erdos7 resolution.'})


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
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete expanded-bridge global comparison certificate')
    print('PASS: all original paired endpoints,212 J reserve,208 domains and215 enlarged rectangle; global K='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr); sys.exit(1)
