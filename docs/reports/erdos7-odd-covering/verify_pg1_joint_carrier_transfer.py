#!/usr/bin/env python3
"""Replay four selected PG1 carrier transfers with one joint deletion.

For a source lift lambda, an arbitrary actual high survival event F, and
the low loss set S pulled back from the target, put A=F intersect S^c.
With b=1+1_(mod3=i)+1_(mod9=j) and f=35-b^2, the sufficient criterion is

  lambda(A) (E[L^2 | A]-35) <= U'_ij-35 + mu(f 1_S) + R(f mu 1_(S^c)).

The removed set is the disjoint union S and S^c intersect F^c. Thus there
is no second charge for S intersect F^c. U' and R retain complete tails.
This script checks all ten roots for four fixed carriers, their individual
12*720 matching minima, and original-label transport along all12 old maps.
It then reconstructs the carrier domain, checks support inclusion, and
replays weighted matching only on included targets to subtract old overlap.
Default: exact certificate replay. --write regenerates the certificate.
Requires Python3 and NumPy; all decision arithmetic is integer or Fraction.
"""
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import permutations, product
from pathlib import Path
import argparse
import json
import numpy as np

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-joint-carrier-transfer-v1'
INPUTS = ('mod3_conditioned_geometry_certificate.json',
          'original9_conditioned_geometry_certificate.json',
          'pg1_exact_zero_depth_certificate.json',
          'actual_deletion_profile_certificate.json',
          'pg1_weighted_carrier_transfer_certificate.json')
MODULES = ('verify_point_geometry', 'verify_seven_digit_classification',
           'verify_carrier_dominance')
# Fixed experiment inputs, not a new whole-domain or loss-tier enumeration.
SELECTED = ((2320, 4096, 4224, 25352, 44378),
            (2320, 4096, 25352, 48602),
            (2, 8456, 27416, 44378),
            (8, 25352, 33880, 44378))
ROOTS = [(i, j) for j in (1, 2, 5, 7, 8) for i in (1, 2)]
DIVISORS = (1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def module(name, directory):
    spec = spec_from_file_location(name, directory / (name + '.py'))
    require(spec is not None and spec.loader is not None, 'adjacent module loader')
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def old_extensions(old, maps):
    result = {}
    for short, long, columns in product(permutations((1, 7)),
                                        permutations((2, 5, 8)),
                                        permutations((1, 2, 3, 4))):
        rows = dict(zip((1, 7, 2, 5, 8), short + long))
        cols = dict(zip((1, 2, 3, 4), columns))
        action = [(10*rows.get(x % 9, x % 9) + 36*cols.get(x % 5, x % 5)) % 45
                  for x in range(45)]
        image = tuple(action[x] for x in old)
        result.setdefault(image, action)
    return [result[tuple(old[i] for i in p)] for p in maps]


def crt_map(old45, digits):
    return [(91*old45[x % 45] + 225*digits[x % 7]) % 315 for x in range(315)]


def check_map(action):
    require(len(action) == len(set(action)) == 315 and set(action) == set(range(315)),
            'full CRT bijection')
    # The prefix maps preserve every original modulus, not merely the carrier.
    # Keeping all subsequent p-adic digits gives the corresponding lift at
    # arbitrary heights; the mod9 prefix also preserves its mod3 parent.
    for d in DIVISORS:
        residues = [{action[x] % d for x in range(a, 315, d)} for a in range(d)]
        require(all(len(s) == 1 for s in residues)
                and len({next(iter(s)) for s in residues}) == d,
                'each original residue class preserved at modulus ' + str(d))


def transport_family(family, action):
    image = []
    for d, a in family:
        values = {action[x] % d for x in range(a, 315, d)}
        require(len(values) == 1, 'transported original class has one residue')
        image.append([d, next(iter(values))])
    image.sort()
    require(len(image) == len({d for d, _ in image}) == 11,
            'eleven distinct original low moduli after transport')
    return image


def complement(family):
    return [x for x in range(315) if all(x % d != a for d, a in family)]


def state_complement(state, old):
    masks = state + (0,)*(6-len(state))
    index = {x: i for i, x in enumerate(old)}
    return [x for x in range(315) if x % 45 in index and x % 7 != 0
            and not (masks[x % 7-1] >> index[x % 45] & 1)]


def realize(state, old, old_family, geo, dom):
    cylinders = dom.old_cylinders(old, geo.MODULI)
    solve, targets, witness, _ = dom.resource_problem([state], cylinders)
    deleted = sum(mask.bit_count() for mask in state)
    maximum = solve(targets(state), 31)
    require(maximum == deleted, 'selected carrier is support-minimal by the resource criterion')
    unions, assignment = witness(state)
    require(unions == state, 'selected state realized by all five mixed labels')
    family = [list(pair) for pair in old_family] + [[7, 0]]
    available = list(range(len(state)))
    for group in assignment:
        union = 0
        for _, mask in group:
            union |= mask
        digit_index = next(j for j in available if state[j] == union)
        available.remove(digit_index)
        for label, mask in group:
            cofactor = geo.MODULI[label]
            residue = next(a for a in range(cofactor)
                           if sum(1 << i for i, x in enumerate(old) if x % cofactor == a) == mask)
            full = next(a for a in range(7*cofactor)
                        if a % cofactor == residue and a % 7 == digit_index+1)
            family.append([7*cofactor, full])
    family.sort()
    require(len(family) == len({d for d, _ in family}) == 11,
            'actual eleven-label target family')
    require(complement(family) == state_complement(state, old),
            'literal original labels realize the selected carrier')
    return family, {'deleted_points': deleted, 'maximum_containing_deletion_points': maximum,
                    'mixed_label_assignment': assignment}


def match(state, old, points, weights, maps):
    masks = state + (0,)*(6-len(state))
    index = {x: i for i, x in enumerate(old)}
    best = None
    tested = 0
    for map_index, action in enumerate(maps):
        costs = [[sum(w for x, w in zip(points, weights)
                      if x % 7 == s and masks[j] >> action[index[x % 45]] & 1)
                  for j in range(6)] for s in range(1, 7)]
        for digits in permutations(range(6)):
            row = (sum(costs[s][digits[s]] for s in range(6)), map_index, digits)
            best = row if best is None or row < best else best
            tested += 1
    require(tested == 12*720 and best is not None, 'complete selected-carrier matching domain')
    loss, map_index, digits = best
    lost = [x for x in points
            if masks[digits[x % 7-1]] >> maps[map_index][index[x % 45]] & 1]
    require(sum(w for x, w in zip(points, weights) if x in lost) == loss,
            'literal minimizing loss witness')
    return loss, map_index, [0] + [d+1 for d in digits], lost, tested


def orbit_transports(state, family, source_map, source_points, lost, old, maps, extensions, geo):
    records, states = [], set()
    for map_index, (action, fullold) in enumerate(zip(maps, extensions)):
        images = [geo.image_mask(mask, action) for mask in state] + [0]*(6-len(state))
        order = sorted(range(6), key=lambda j: (images[j] == 0, images[j], j))
        digits = [0] + [order.index(j)+1 for j in range(6)]
        target_state = tuple(images[j] for j in order if images[j])
        states.add(target_state)
        transport = crt_map(fullold, digits)
        check_map(transport)
        target_family = transport_family(family, transport)
        target = complement(target_family)
        require(target == state_complement(target_state, old), 'transported normalized carrier')
        require(sorted(transport[x] for x in complement(family)) == target,
                'all actual target support points transported')
        composed = [transport[y] for y in source_map]
        require([x for x in source_points if composed[x] not in target] == lost,
                'orbit transport preserves exactly the original source loss set')
        records.append({'old_map_index': map_index, 'old_point_index_map': list(action),
                        'full_old45_map': fullold, 'seven_map_including_zero': digits,
                        'target_masks': list(target_state), 'original_target_low_family': target_family,
                        'source_to_orbit_map315_sha256': digest(composed)})
    require(len(records) == 12 and min(states) == state,
            'all twelve old maps and the selected canonical orbit representative')
    return records, states


def injection_witness(edges):
    def walk(remaining, used, chosen):
        if not remaining:
            return chosen
        j = min(remaining, key=lambda k: (edges[k] & ~used).bit_count())
        options = edges[j] & ~used
        while options:
            bit = options & -options
            options ^= bit
            result = walk([k for k in remaining if k != j], used | bit,
                          {**chosen, j: bit.bit_length()-1})
            if result is not None:
                return result
        return None
    return walk(list(range(len(edges))), 0, {})


def support_coverage(results, prior, geometry, old, points, weights, den, maps, extensions, geo, dom):
    states, _, widths = geo.digit_union_states(old)
    require(len(states) == geometry['digit_union_states']
            and widths == geometry['independent_state_widths'], 'complete actual carrier domain')
    reps = dom.carrier_orbits(states, maps, geo)
    require(len(states) == prior['domain']['carriers']
            and len(reps) == prior['domain']['carrier_orbits']
            and geo.digest(sorted(states)) == prior['domain']['carriers_sha256']
            and geo.digest(reps) == prior['domain']['carrier_orbits_sha256'],
            'reconstructed domain equals the previously certified weighted domain')
    threshold = prior['integer_loss_threshold']
    old_limit = F(prior['source_survival_lower'])*(35-F(prior['source_Gamma_upper']))/34
    scaled = old_limit*den
    require(threshold == scaled.numerator // scaled.denominator == 19730787,
            'unchanged published coverage threshold, distinct from the newer scalar tolerance')
    old_shape = next(r for r in prior['old_row_loss_by_shape'] if r['shape'] == geometry['shape'])
    require(old_shape['maps_within_budget'] == len(maps) == 12,
            'inherited exclusion of normalized old maps outside the stabilizer at the old budget')
    source_records, images = [], {}
    for source_index, row in enumerate(results):
        support = [x for x in points if x not in row['lost_source_points']]
        masks = tuple(sum(1 << i for i, a in enumerate(old)
                          if not any(x % 7 == digit and x % 45 == a for x in support))
                      for digit in range(1, 7))
        source_images = set()
        for map_index, action in enumerate(maps):
            ordered = tuple(geo.image_mask(mask, action) for mask in masks)
            normalized = tuple(sorted(mask for mask in ordered if mask))
            source_images.add(normalized)
            images.setdefault(normalized, (source_index, map_index, ordered))
        source_records.append({'source_index': source_index, 'lost_source_points': row['lost_source_points'],
                               'support_size': len(support), 'deletion_masks_by_source_digit': list(masks),
                               'normalized_deletion_masks': sorted(mask for mask in masks if mask),
                               'distinct_old_images': len(source_images)})
    used = {mask for state in reps for mask in state}
    image_rows = sorted(images.items())
    edge_tables = [{b: sum(1 << j for j, a in enumerate(ordered) if b & ~a == 0) for b in used}
                   for _, (_, _, ordered) in image_rows]
    covered, witnesses = [], {}
    for state in reps:
        for (_, (source_index, map_index, ordered)), edges in zip(image_rows, edge_tables):
            target_edges = [edges[b] for b in state]
            if not dom.injection(tuple(sorted(target_edges))):
                continue
            assignment = injection_witness(target_edges)
            require(assignment is not None, 'explicit six-digit support injection')
            remaining = [j for j in range(6) if j not in assignment.values()]
            assignment.update(zip(range(len(state), 6), remaining))
            digits = [0] + [next(j+1 for j, src in assignment.items() if src == s) for s in range(6)]
            transport = crt_map(extensions[map_index], digits)
            support = [x for x in points if x not in results[source_index]['lost_source_points']]
            target = set(state_complement(state, old))
            require(all(transport[x] in target for x in support),
                    'literal retained-source containment in the actual target carrier')
            covered.append(state)
            witnesses[state] = {'source_index': source_index, 'old_map_index': map_index,
                                'seven_map_including_zero': digits}
            break
    require(all(tuple(row['target_masks']) in covered for row in results),
            'the four direct target carriers occur in support coverage')
    cylinders = dom.old_cylinders(old, geo.MODULI)
    solve, targets, _, _ = dom.resource_problem(covered, cylinders)
    used_masks = sorted({0} | {mask for state in covered for mask in state})
    bits = np.array([[(m >> i) & 1 for i in range(len(old))] for m in used_masks], dtype=np.int64)
    mask_index = {m: i for i, m in enumerate(used_masks)}
    W = np.zeros((6, len(old)), dtype=np.int64)
    for x, w in zip(points, weights):
        W[x % 7-1, old.index(x % 45)] = w
    costs = []
    for action in maps:
        mapped = np.zeros_like(W)
        mapped[:, action] = W
        costs.append((mapped @ bits.T).T)
    digit_maps = np.array(list(permutations(range(6))), dtype=np.int64)
    digits = np.arange(6, dtype=np.int64)
    require(6*den < 2**63 and digit_maps.shape == (720, 6), 'exact subset matching arithmetic')
    rows = []
    for state in covered:
        ix = [mask_index[m] for m in state + (0,)*(6-len(state))]
        best = None
        for map_index, action in enumerate(maps):
            values = costs[map_index][ix].T[digits, digit_maps].sum(axis=1)
            at = int(values.argmin())
            candidate = (int(values[at]), map_index, tuple(map(int, digit_maps[at])))
            best = candidate if best is None or candidate < best else best
        loss, mi, dm = best
        masks = state + (0,)*(6-len(state))
        lost = [x for x in points if masks[dm[x % 7-1]] >> maps[mi][old.index(x % 45)] & 1]
        require(sum(w for x, w in zip(points, weights) if x in lost) == loss,
                'literal witness for included-target minimum weighted loss')
        maximum = solve(targets(state), 31)
        deleted = sum(m.bit_count() for m in state)
        require(maximum >= deleted, 'included carrier feasible in the resource problem')
        orbit = {tuple(sorted(geo.image_mask(m, action) for m in state)) for action in maps}
        rows.append({'masks': list(state), 'orbit_size': len(orbit),
                     'minimal': maximum == deleted, 'deleted_points': deleted,
                     'maximum_containing_deletion_points': maximum,
                     'minimum_loss_numerator': loss, 'previously_covered': loss <= threshold,
                     'support_containment_witness': witnesses[state]})

    def tally(selected):
        return {'carrier_orbits': len(selected), 'carriers': sum(r['orbit_size'] for r in selected),
                'minimal_carrier_orbits': sum(r['minimal'] for r in selected),
                'carrier_orbits_sha256': geo.digest([r['masks'] for r in selected]),
                'minimal_orbits_sha256': geo.digest([r['masks'] for r in selected if r['minimal']])}

    all_count = tally(rows)
    overlap = tally([r for r in rows if r['previously_covered']])
    additional = tally([r for r in rows if not r['previously_covered']])
    old_count = prior['all_weighted_threshold']
    merged = {key: old_count[key]+additional[key]
              for key in ('carrier_orbits', 'carriers', 'minimal_carrier_orbits')}
    before = prior['combined_after']
    after = {'covered_carriers': before['covered_carriers']+additional['carriers'],
             'covered_carrier_orbits': before['covered_carrier_orbits']+additional['carrier_orbits'],
             'covered_minimal_carrier_orbits': before['covered_minimal_carrier_orbits']+additional['minimal_carrier_orbits'],
             'remaining_minimal_carrier_orbits': before['remaining_minimal_carrier_orbits']-additional['minimal_carrier_orbits']}
    for key in ('carrier_orbits', 'carriers', 'minimal_carrier_orbits'):
        require(all_count[key] == overlap[key]+additional[key], 'old overlap subtracted once')
    return {'retained_source_supports': source_records, 'distinct_old_images': len(images),
            'reconstructed_target_domain': {'carrier_orbits': len(reps), 'carriers': len(states),
                                            'carrier_orbits_sha256': geo.digest(reps)},
            'matching_replayed_only_for_included_targets': len(rows),
            'matching_maps_per_included_target': 12*720,
            'included_targets': rows, 'support_covered': all_count, 'old_coverage_overlap': overlap,
            'additional_coverage': additional, 'previous_weighted_coverage': old_count,
            'merged_PG1_coverage': merged, 'inherited_other_shapes': prior['inherited_other_shapes'],
            'combined_before': before, 'combined_after': after,
            'scope': 'Each target contains a transported retained support of one of the four proved laws. The high event remains arbitrary, so the same law applies to every such target. Reconstruct all target representatives, but recompute weighted minima and minimality only on included targets. Previous weighted and other-shape totals are inherited from their hash-bound certificate; the additional count subtracts exact overlap with its original threshold.'}


def evaluate(directory, expected_hashes=None):
    raw = {name: (directory / name).read_bytes() for name in INPUTS}
    data = {name: json.loads(value) for name, value in raw.items()}
    source, original, exact, _, weighted = (data[name] for name in INPUTS)
    prerequisites = dict(exact['source_sha256'])
    for name, stamp in weighted['source_sha256'].items():
        require(name not in prerequisites or prerequisites[name] == stamp, 'compatible prerequisite source hashes')
        prerequisites[name] = stamp
    for name, stamp in prerequisites.items():
        require(Path(name).name == name and name.endswith('.json'), 'local prerequisite filename')
        value = (directory / name).read_bytes()
        require(sha256(value).hexdigest() == stamp, 'exact-zero prerequisite hash: ' + name)
        raw[name] = value
    for name in MODULES:
        raw[name + '.py'] = (directory / (name + '.py')).read_bytes()
    hashes = {name: sha256(value).hexdigest() for name, value in sorted(raw.items())}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'hash-bound certificates and replay implementations')
    require(original['source_sha256'] == hashes[INPUTS[0]]
            and original['source_case'] == 'PG1'
            and exact['schema'] == 'erdos7-pg1-exact-zero-depth-v1', 'unchanged certified PG1 source')
    require(weighted['schema'] == 'erdos7-pg1-weighted-carrier-transfer-v1'
            and weighted['result']['target_Gamma'] == 35
            and weighted['result']['shape'] == 'root2_other_other_column', 'inherited carrier-coverage source')
    pg, geo, dom = (module(name, directory) for name in MODULES)
    case = next(row for row in source['cases'] if row['name'] == 'PG1')
    points, old = case['points'], case['old_points']
    weights, den = case['weight_numerators'], case['weight_denominator']
    require(points == complement(case['family']) and len(points) == len(weights) == 75
            and len(case['family']) == len({d for d, _ in case['family']}) == 11
            and all(type(w) is int and w > 0 for w in weights)
            and sum(weights) == den == 1000000007, 'exact source law on its actual low carrier')
    q0 = F(original['result']['survival_lower'])
    ex = exact['result']
    require(q0 == F(ex['source_survival_lower']) > 0, 'same actual source survival lower bound')
    scalar_limit = q0*(35-F(ex['Gamma_upper']))/34
    integer_limit = (scalar_limit*den).numerator // (scalar_limit*den).denominator
    require(str(scalar_limit) == ex['target35_conditioning']['loss_limit']
            and integer_limit == ex['target35_conditioning']['integer_loss_limit'] == 20778236,
            'previous improved scalar conditioning threshold')
    source_rows = {(r['root3'], r['root9']): r for r in original['result']['records']}
    exact_rows = {(r['root3'], r['root9']): r for r in ex['records']}
    require(len(source_rows) == len(original['result']['records']) == 10
            and len(exact_rows) == len(ex['records']) == 10
            and set(source_rows) == set(exact_rows) == set(ROOTS)
            and all(F(exact_rows[k]['new_U']) <= F(source_rows[k]['U']) for k in ROOTS),
            'all ten inherited improved full-height square bounds')
    geometry = next(row for row in geo.read_geometries(directory / INPUTS[3])
                    if row['shape'] == 'root2_other_other_column')
    require(geometry['old_points'] == old, 'same canonical old45 shape')
    maps = geo.old_maps(old)
    require(len(maps) == 12, 'twelve same-shape old coordinate maps')
    extensions = old_extensions(old, maps)
    ds, _, _, rem, depths, _, _, outside = pg.coeffs((8, 5, 4))
    require(ex['depth_box'] == [8, 5, 4] and len(depths) == 270
            and ds == ex['tail_divisors']
            and list(map(str, outside)) == ex['complete_outside_square_coefficients'],
            'complete square tail retained in the source certificate')
    rem[ds.index(35)] -= F(1, 4)
    require(min(rem) >= 0, 'complete nonnegative remaining high357 deletion coefficients')
    x, w = np.array(points, dtype=np.int64), np.array(weights, dtype=np.int64)
    group = pg.group_setup({'survivors': points, 'points': old}, (9, 45), 35)
    cylinders = [np.array([x % d == a for a in sorted(set(map(int, x % d)))], dtype=np.int64)
                 for d in ds]
    results, all_states = [], set()
    for state in SELECTED:
        family, minimality = realize(state, old, geometry['old_classes'], geo, dom)
        loss, map_index, digits, lost, tested = match(state, old, points, weights, maps)
        require(loss > integer_limit and F(loss, den) < q0,
                'strictly beyond scalar budget with positive actual survival')
        fullold = extensions[map_index]
        transport = crt_map(fullold, digits)
        check_map(transport)
        target = complement(family)
        require([a for a in points if transport[a] not in target] == lost,
                'original-label target pullback equals selected low deletion')
        target_weights = {transport[a]: weight for a, weight in zip(points, weights) if a not in lost}
        require(set(target_weights) <= set(target) and sum(target_weights.values()) == den-loss,
                'normalized transported restriction of the unchanged source law')
        orbit, states = orbit_transports(state, family, transport, points, lost, old, maps, extensions, geo)
        require(not (states & all_states), 'the four selected old-map orbits are disjoint')
        all_states.update(states)
        bad = np.array([a in lost for a in points], dtype=bool)
        criteria = []
        for key in ROOTS:
            b = 1 + (x % 3 == key[0]).astype(np.int64) + (x % 9 == key[1]).astype(np.int64)
            cost = 35-b*b
            measure = w*cost*(~bad)
            require(int(cost.min()) > 0 and 48*sum(map(int, measure)) < 2**63,
                    'nonnegative joint deletion and safe integer arithmetic')
            best, _, domain = pg.group_oracle(measure, group)
            caps = [int((cy @ measure).max()) for cy in cylinders]
            high = F(best['value'], 48*den) + sum((r*F(c, den) for r, c in zip(rem, caps)), F())
            low = F(sum(int(weight)*int(c) for weight, c, hit in zip(w, cost, bad) if hit), den)
            value = F(exact_rows[key]['new_U'])-35+low+high
            require(value < 0, 'strict ten-root joint-deletion criterion')
            criteria.append({'root3': key[0], 'root9': key[1],
                             'new_source_U': exact_rows[key]['new_U'],
                             'low_deletion_cost': str(low), 'remaining_high_deletion_upper': str(high),
                             'group_numerator48': best['value'], 'cap_numerators': caps,
                             'criterion': str(value)})
        raw_survival = q0-F(loss, den)
        results.append({'target_masks': list(state), 'minimality': minimality,
                        'matching_maps_checked': tested, 'minimum_loss_numerator': loss,
                        'lost_source_points': lost, 'old_map_index': map_index,
                        'old_point_index_map': list(maps[map_index]), 'full_old45_map': fullold,
                        'seven_map_including_zero': digits, 'source_to_target_map315': transport,
                        'original_target_low_family': family, 'target_points': target,
                        'target_weight_numerators': [target_weights.get(a, 0) for a in target],
                        'target_weight_denominator': den-loss,
                        'raw_survival_lower': str(raw_survival),
                        'normalized_target_high_survival_lower': str(raw_survival / (1-F(loss, den))),
                        'criteria': criteria, 'maximum_criterion': str(max(F(r['criterion']) for r in criteria)),
                        'old_map_orbit_size': len(states), 'orbit_transports': orbit})
    require([r['old_map_orbit_size'] for r in results] == [6, 6, 12, 6], 'selected orbit sizes')
    coverage = support_coverage(results, weighted['result'], geometry, old, points, weights, den,
                                maps, extensions, geo, dom)
    return {'schema': SCHEMA, 'source_sha256': hashes,
            'result': {'shape': geometry['shape'], 'source_case': 'PG1',
                       'source_survival_lower': str(q0), 'source_weight_denominator': den,
                       'source_original_low_family': case['family'], 'source_points': points,
                       'source_weight_numerators': weights, 'source_old_points': old,
                       'target_Gamma': 35, 'previous_scalar_integer_loss_limit': integer_limit,
                       'depth_box': [8, 5, 4], 'tail_divisors': ds,
                       'remaining_high_deletion_coefficients': list(map(str, rem)),
                       'grouped_deletion_domain': domain,
                       'joint_criterion': "U'_ij-35+mu((35-b_ij^2)1_S)+R((35-b_ij^2)mu 1_(S^c)) <= 0",
                       'removed_set_partition': 'S disjoint-union (S^c intersect F^c)',
                       'selected_carriers': results, 'selected_orbits': len(results),
                       'selected_distinct_digit_quotient_states': len(all_states),
                       'selected_digit_quotient_states_sha256': digest(sorted(all_states)),
                       'support_coverage': coverage,
                       'scope': 'Four fixed support-minimal actual low315 carriers, and all12 same-shape old maps for each, under one transported restriction of the PG1 law and the same arbitrary actual high survival event. All ten original test roots, arbitrary finite physical heights, and complete high357 tails. Support containment extends these laws to the enumerated included targets, with old coverage overlap subtracted. No merger of source and target forbidden families, new cross-shape moment result, or unrestricted-prime resolution.'}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE / 'pg1_joint_carrier_transfer_certificate.json')
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
        require(actual == expected, 'complete deterministic certificate equality')
    rows = actual['result']['selected_carriers']
    print(json.dumps({'verified': True, 'selected_orbits': len(rows),
                      'orbit_sizes': [r['old_map_orbit_size'] for r in rows],
                      'minimum_loss_numerators': [r['minimum_loss_numerator'] for r in rows],
                      'maximum_criteria': [r['maximum_criterion'] for r in rows],
                      'coverage': actual['result']['support_coverage']['combined_after']}, sort_keys=True))


if __name__ == '__main__':
    main()
