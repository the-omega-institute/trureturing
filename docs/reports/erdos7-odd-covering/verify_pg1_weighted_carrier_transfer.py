#!/usr/bin/env python3
"""Exact PG1 carrier transfer by lost probability mass on one old45 shape.

Reconstruct every actual carrier orbit and every allowed old/digit map,
then compare the entire summary certificate. Uses NumPy and adjacent
canonical carrier modules. No optimizer, network or height search is used.
--write explicitly writes the certificate; default operation only compares.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import permutations, product
from pathlib import Path
import argparse
import importlib.util
import json

import numpy as np

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-weighted-carrier-transfer-v1'
SHAPE = 'root2_other_other_column'
SOURCES = ('mod3_conditioned_geometry_certificate.json',
           'original9_conditioned_geometry_certificate.json',
           'actual_deletion_profile_certificate.json',
           'carrier_dominance_certificate.json',
           'uniform_profile_box_certificate.json',
           'row_weighted_geometry_certificate.json')


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def module(name, directory):
    spec = importlib.util.spec_from_file_location(name, directory / (name + '.py'))
    require(spec is not None and spec.loader is not None, 'canonical carrier module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def evaluate(directory, expected_hashes=None):
    raw = {name: (directory / name).read_bytes() for name in SOURCES}
    hashes = {name: sha256(value).hexdigest() for name, value in raw.items()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'hash-bound canonical source certificates')
    source_data, original9, _, dominance, box, rowlaw = (json.loads(raw[name]) for name in SOURCES)
    source = next(c for c in source_data['cases'] if c['name'] == 'PG1')
    require(original9['source_sha256'] == hashes[SOURCES[0]]
            and original9['source_case'] == 'PG1', 'original9 source chain')
    require(rowlaw['geometry_sha256'] == hashes[SOURCES[2]]
            and rowlaw['uniform_box_sha256'] == hashes[SOURCES[4]], 'inherited row-law source chain')
    q0 = F(original9['result']['survival_lower'])
    G = F(original9['result']['Gamma_upper'])
    source_h2 = F(original9['result']['hinge2']['H2_upper'])
    source_mean = F(original9['result']['hinge2']['mean_upper'])
    require(q0 == F(25428074957, 48000000336)
            and G == F(492647095380812739054683, 14604022456869186140625),
            'fixed all-height PG1 survival and moment bounds')
    require(source_h2 == 3 and source_mean == 5
            and F(original9['result']['hinge2']['minimum_margin']) > 0,
            'same-law source hinge2 and mean observations')
    limit = q0 * (35-G) / 34
    den = source['weight_denominator']
    require(den == 1000000007 and 0 < limit < q0, 'positive bounded conditioning loss')
    scaled_limit = limit * den
    threshold = scaled_limit.numerator // scaled_limit.denominator
    geo = module('verify_seven_digit_classification', directory)
    dom = module('verify_carrier_dominance', directory)
    geometries = geo.read_geometries(directory / SOURCES[2])
    old_case = next(c for c in geometries if c['shape'] == SHAPE)
    old = old_case['old_points']
    require(old == source['old_points'], 'same old45 support')
    points = source['points']
    weights = source['weight_numerators']
    require(len(points) == len(weights) == 75 and len(set(points)) == 75
            and all(type(w) is int and w > 0 for w in weights)
            and sum(weights) == den
            and points == [x for x in range(315) if all(x % d != a for d, a in source['family'])]
            and all(x % 7 != 0 for x in points), 'actual positive PG1 probability')
    W = np.zeros((6, len(old)), dtype=np.int64)
    for x, w in zip(points, weights):
        W[x % 7 - 1, old.index(x % 45)] = w
    require(int(W.sum()) == den, 'complete point-weight matrix')
    # Before seven-digit assignment, old rows outside the target already
    # consume loss. Check the full normalized map class without filtering
    # for support containment or requiring a source stabilizer.
    old_actions = []
    for short, long, columns in product(permutations((1, 7)),
                                        permutations((2, 5, 8)),
                                        permutations((1, 2, 3, 4))):
        rows = dict(zip((1, 7, 2, 5, 8), short + long))
        cols = dict(zip((1, 2, 3, 4), columns))
        action = [(10 * rows.get(x % 9, x % 9)
                   + 36 * cols.get(x % 5, x % 5)) % 45 for x in range(45)]
        require(sorted(action) == list(range(45)), 'full normalized old45 bijection')
        old_actions.append(action)
    require(len(old_actions) == 288 and len({tuple(a) for a in old_actions}) == 288,
            'all normalized old maps, without a containment filter')
    row_weights = [sum(w for x, w in zip(points, weights) if x % 45 == a) for a in old]
    cross_shape = []
    for target_case in geometries:
        target_old = set(target_case['old_points'])
        scores = []
        for action in old_actions:
            loss = sum(w for a, w in zip(old, row_weights) if action[a] not in target_old)
            direct = sum(w for x, w in zip(points, weights) if action[x % 45] not in target_old)
            require(loss == direct, 'old-row loss equals literal source point loss')
            scores.append(loss)
        minimum = min(scores)
        within = sum(v <= threshold for v in scores)
        if target_case['shape'] == SHAPE:
            require(minimum == 0 and within == 12, 'only the source stabilizers meet the old-row budget')
        else:
            require(minimum > threshold, 'every other shape exceeds the fixed-source transfer budget')
        cross_shape.append({'shape': target_case['shape'], 'maps_checked': len(scores),
                            'minimum_loss_numerator': minimum, 'minimizing_map': old_actions[scores.index(minimum)],
                            'minimizer_count': scores.count(minimum), 'maps_within_budget': within,
                            'all_map_losses_sha256': geo.digest(scores)})
    maps = geo.old_maps(old)
    states, _, widths = geo.digit_union_states(old)
    require(len(states) == old_case['digit_union_states']
            and widths == old_case['independent_state_widths'], 'complete actual carrier domain')
    reps = dom.carrier_orbits(states, maps, geo)
    essential, cylinders = dom.essential_carriers(old, geo.MODULI)
    essential_reps = dom.carrier_orbits(essential, maps, geo)
    solve, targets, label_witness, _ = dom.resource_problem(essential_reps, cylinders)
    minimal = {s for s in essential_reps if solve(targets(s), 31) == sum(m.bit_count() for m in s)}
    old_report = next(c for c in dominance['cases'] if c['shape'] == SHAPE)
    require(len(essential) == old_report['essential_carriers']
            and geo.digest(sorted(essential)) == old_report['essential_carriers_sha256']
            and geo.digest(essential_reps) == old_report['essential_orbits_sha256']
            and len(minimal) == old_report['minimal_carrier_orbits']
            and geo.digest(sorted(minimal)) == old_report['minimal_orbits_sha256'],
            'independent canonical essential and minimal domains')
    all_masks = sorted({0} | {m for s in states for m in s})
    bits = np.array([[(m >> i) & 1 for i in range(len(old))] for m in all_masks], dtype=np.int64)
    mask_index = {m: i for i, m in enumerate(all_masks)}
    costs, counts = [], []
    for p in maps:
        mapped = np.zeros_like(W)
        mapped[:, p] = W
        costs.append((mapped @ bits.T).T)
        counts.append(((mapped > 0).astype(np.int64) @ bits.T).T)
    costs, counts = np.array(costs), np.array(counts)
    digit_maps = np.array(list(permutations(range(6))), dtype=np.int64)
    require(len(digit_maps) == 720 and len(maps) == 12, 'complete allowed maps')
    digits = np.arange(6, dtype=np.int64)
    big = den + 1
    require(75*big + den < 2**63, 'exact int64 weighted and cardinality objectives')
    rows = []
    example = None
    for state in reps:
        masks = state + (0,) * (6-len(state))
        ix = [mask_index[m] for m in masks]
        best, lex_best, detail = None, None, None
        for mi, p in enumerate(maps):
            value = costs[mi, ix].T[digits, digit_maps].sum(axis=1)
            count = counts[mi, ix].T[digits, digit_maps].sum(axis=1)
            pi = int(value.argmin())
            if best is None or int(value[pi]) < best:
                best = int(value[pi])
                detail = (mi, digit_maps[pi].tolist(), int(count[pi]))
            candidate = int((value + big*count).min())
            if lex_best is None or candidate < lex_best:
                lex_best = candidate
        require(best is not None and detail is not None and lex_best is not None, 'attained exact match')
        mincount, lex_weight = divmod(lex_best, big)
        mi, digit_map, loss_count = detail
        lost = [x for x in points if masks[digit_map[x % 7 - 1]] >> maps[mi][old.index(x % 45)] & 1]
        require(len(lost) == loss_count
                and sum(w for x, w in zip(points, weights) if x in lost) == best,
                'direct original75-point replay of selected minimum')
        orbit = {tuple(sorted(geo.image_mask(m, p) for m in state)) for p in maps}
        row = {'masks': list(state), 'orbit_size': len(orbit), 'essential': state in essential,
               'minimal': state in minimal, 'minimum_loss_numerator': best,
               'minimum_cardinality': mincount, 'least_loss_at_minimum_cardinality': lex_weight}
        rows.append(row)
        if example is None and state in minimal and 0 < best <= threshold:
            unions, assignment = label_witness(state)
            require(sorted(unions) == list(state), 'minimal original-label witness')
            available = list(range(len(state)))
            family = [list(pair) for pair in old_case['old_classes']] + [[7, 0]]
            for group in assignment:
                union = 0
                for label, mask in group:
                    union |= mask
                j = next(j for j in available if state[j] == union)
                available.remove(j)
                for label, mask in group:
                    co = geo.MODULI[label]
                    residue = next(a for a in range(co) if sum(1 << i for i, x in enumerate(old)
                                                              if x % co == a) == mask)
                    full = next(a for a in range(7*co) if a % co == residue and a % 7 == j+1)
                    family.append([7*co, full])
            family.sort()
            target = [x for x in range(315) if all(x % d != a for d, a in family)]
            direct = [x for x in range(315) if x % 45 in old and x % 7 != 0
                      and not (masks[x % 7 - 1] >> old.index(x % 45) & 1)]
            require(target == direct and len(family) == 11 and len({d for d, a in family}) == 11,
                    'actual target carrier with eleven distinct original moduli')
            inherited = 1 + (G-1)*q0/(q0-F(best, den))
            inherited_survival = (q0-F(best, den))/(1-F(best, den))
            inherited_factor = q0/(q0-F(best, den))
            require(inherited <= 35, 'strictly new minimal carrier meets target')
            example = {**row, 'original_low_family': family, 'target_points': target,
                       'source_old_map': list(maps[mi]), 'seven_digit_images': [j+1 for j in digit_map],
                       'lost_source_points': lost, 'source_point_loss': str(F(best, den)),
                       'target_low_weight_denominator': den-best,
                       'inherited_survival_lower': str(inherited_survival),
                       'inherited_mean_upper': str(1+(source_mean-1)*inherited_factor),
                       'inherited_H2_upper': str(source_h2*inherited_factor),
                       'inherited_Gamma_upper': str(inherited)}

    def tally(predicate):
        selected = [r for r in rows if predicate(r)]
        minimal_selected = [r['masks'] for r in selected if r['minimal']]
        return {'carrier_orbits': len(selected), 'carriers': sum(r['orbit_size'] for r in selected),
                'essential_carrier_orbits': sum(r['essential'] for r in selected),
                'essential_carriers': sum(r['orbit_size'] for r in selected if r['essential']),
                'minimal_carrier_orbits': len(minimal_selected),
                'minimal_carriers': sum(r['orbit_size'] for r in selected if r['minimal']),
                'carrier_orbits_sha256': geo.digest([r['masks'] for r in selected]),
                'minimal_carrier_orbits_sha256': geo.digest(minimal_selected)}

    zero = tally(lambda r: r['minimum_loss_numerator'] == 0)
    old_zero = dominance['PG1_support_coverage']
    require(zero['carrier_orbits'] == old_zero['covered_carrier_orbits']
            and zero['carriers'] == old_zero['covered_carriers']
            and zero['minimal_carrier_orbits'] == old_zero['covered_minimal_carrier_orbits']
            and zero['carrier_orbits_sha256'] == old_zero['covered_orbits_sha256'],
            'published complete zero-loss PG1 domain')
    require(max(weights) <= threshold, 'every single source point is below loss threshold')
    one = tally(lambda r: r['minimum_cardinality'] <= 1)
    two = tally(lambda r: r['minimum_cardinality'] <= 2
                and r['least_loss_at_minimum_cardinality'] <= threshold)
    weighted = tally(lambda r: r['minimum_loss_numerator'] <= threshold)
    require(example is not None, 'new minimal original-label example')
    pair_count = sum(weights[i] + weights[j] <= threshold for i in range(75) for j in range(i+1, 75))
    sorted_weights = sorted(weights)
    max_loss_points = max(k for k in range(76) if sum(sorted_weights[:k]) <= threshold)

    # Existing coverage of the other two shapes is inherited, not rerun as a
    # new moment calculation. Their prior overlap is explicitly subtracted.
    c2 = dominance['mod3_conditioned_support_coverage']['C2_support_coverage']
    bg = box['result']['actual_geometry']
    rc = rowlaw['result']['support_coverage']
    require(len({SHAPE, c2['shape'], box['result']['shape']}) == 3
            and rowlaw['result']['shape'] == box['result']['shape']
            and str(c2['target']) == str(box['target']) == str(rowlaw['target']) == '35',
            'three disjoint canonical shapes share target35')
    inherited_states = bg['covered_states'] + rc['covered_states'] - rc['overlap_box_states']
    inherited_orbits = bg['covered_orbits'] + rc['covered_orbits'] - rc['overlap_box_orbits']
    inherited_minimal = bg['covered_minimal_orbits'] + rc['additional_minimal_orbits']
    require(inherited_states == rc['union_states'] and inherited_orbits == rc['union_orbits'],
            'existing box and row-law overlap fully subtracted')
    total_minimal = sum(c['minimal_carrier_orbits'] for c in dominance['cases'])
    require(total_minimal == dominance['totals']['minimal_carrier_orbits'], 'full six-shape minimal total')
    def combined(pg1):
        count = pg1['minimal_carrier_orbits'] + c2['covered_minimal_carrier_orbits'] + inherited_minimal
        return {'covered_carriers': pg1['carriers'] + c2['covered_carriers'] + inherited_states,
                'covered_carrier_orbits': pg1['carrier_orbits'] + c2['covered_carrier_orbits'] + inherited_orbits,
                'covered_minimal_carrier_orbits': count,
                'remaining_minimal_carrier_orbits': total_minimal-count}
    result = {'shape': SHAPE, 'source_survival_lower': str(q0), 'source_Gamma_upper': str(G),
              'source_mean_upper': str(source_mean), 'source_H2_upper': str(source_h2),
              'target_Gamma': 35, 'loss_threshold': str(limit), 'weight_denominator': den,
              'integer_loss_threshold': threshold, 'admissible_single_points': len(weights),
              'normalized_old_map_domain': 'mod3 roots, absent mod9 child4, and mod5 column0 fixed; all288 remaining child/column permutations',
              'old_row_loss_by_shape': cross_shape,
              'uniform_survival_lower_at_loss_threshold': str((q0-limit)/(1-limit)),
              'admissible_unordered_pairs': pair_count, 'maximum_admissible_point_count': max_loss_points,
              'old_points': old, 'old_maps_sha256': geo.digest(sorted(maps)),
              'domain': {'carriers': len(states), 'carrier_orbits': len(reps),
                         'essential_carriers': len(essential), 'essential_carrier_orbits': len(essential_reps),
                         'minimal_carrier_orbits': len(minimal),
                         'carriers_sha256': geo.digest(sorted(states)), 'carrier_orbits_sha256': geo.digest(reps),
                         'minimal_carrier_orbits_sha256': geo.digest(sorted(minimal))},
              'zero_loss': zero, 'at_most_one_point': one, 'at_most_two_points': two,
              'all_weighted_threshold': weighted, 'all_matching_results_sha256': geo.digest(rows),
              'new_minimal_example': example,
              'inherited_other_shapes': [
                  {'shape': c2['shape'], 'carriers': c2['covered_carriers'],
                   'carrier_orbits': c2['covered_carrier_orbits'], 'minimal_orbits': c2['covered_minimal_carrier_orbits']},
                  {'shape': box['result']['shape'], 'carriers': inherited_states,
                   'carrier_orbits': inherited_orbits, 'minimal_orbits': inherited_minimal}],
              'combined_before': combined(zero), 'combined_after': combined(weighted),
              'scope': 'Complete weighted-loss matching only within the PG1 old45 shape; arbitrary finite higher357 heights and original labels follow by the stated conditioning argument. The combined count inherits separately certified target35 laws on two distinct old shapes. No unrestricted-prime continuation is asserted.'}
    return {'schema': SCHEMA, 'source_sha256': hashes, 'result': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE / 'pg1_weighted_carrier_transfer_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(args.certificate.read_text())
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        args.certificate.write_text(json.dumps(actual, indent=2) + '\n')
    else:
        require(actual == expected, 'complete exact weighted-carrier transfer certificate')
    print(json.dumps({key: actual['result'][key] for key in
                      ('all_weighted_threshold', 'combined_before', 'combined_after')}))


if __name__ == '__main__':
    main()
