#!/usr/bin/env python3
"""Extend the complete local comparison across the old outer-source bottleneck.

New source-radius guards justify every reused formula. New original-head
maxima are evaluated on this box; the existing narrower scans are not reused.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys
from time import perf_counter
from types import SimpleNamespace

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/expanded_source_complete_comparison.json'
HEAD_CERTIFICATE = 'certificates/source_norms/source-budgets/expanded_source_original_heads.json'
DELTA, RHO = F(1, 22), F(1, 20000)
EXPANDED_RHO = F(1, 15000)
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/pure_five_complete_face_comparison.py': '45c1b016e68eb5397a78a6540c4f8ee5287c214b6bb35625d4d0232224dd2314',
    'certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json': 'e0d124f375efa0567777973a2ba468d368285807aed054ada2e57727b896d4f2',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original proof input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def source_guards(study, par):
    d, rho, r = par['delta'], par['rho'], par['rbar']
    require(d == DELTA and rho in (RHO, EXPANDED_RHO) and r == 5*rho <= F(1, 3000), 'The new actual rectangles')
    require(F(1, 27) < F(41843898943, 10**12) < d < F(2, 27),
            'The new source radius crosses the old global strip and stays inside134')
    Delta = d/(4*(1-d))
    require(Delta == F(1, 84) < F(1, 18) and F(3, 4)+d/4 == F(67, 88) < F(4, 5)
            and r < F(1, 2500), 'Every actual source lies in the complete162 fixed-support slab')
    norms = study.get('exposed_concentration_prices').norm_bounds(d)
    D = norms['availability_Linfinity']
    h1, eta = F(1, 3)-d/18, F(1, 9)-d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-D)-2*r, (F(1, 6)-d/9)/5-r)
    require(min(gaps) >= F(241, 22500) > 0 and 0 < par['gap'] <= min(gaps),
            'All five actual first-label gaps and the same wrong-slot simplex remain valid')
    require(D <= Delta < F(1, 18) and F(1, 4)-3*d/4 > F(1, 20), 'Actual source/forcing guards')
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d}
    require(min(polynomials.values()) > 0,
            'All domain polynomials are positive; each decreases throughout[0,1/22]')
    # The only positive quadratic coefficient is in 3d²-23d+3.
    require(6*d-23 < 0, 'The remaining quadratic also decreases on the entire source interval')
    require(F(3, 5)-18*F(13, 1215) > 0, 'Retained-deep marker coefficients stay nonnegative')
    return {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
            'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
            'availability_upper': D, 'five_actual_gap_lowers': gaps,
            'minimum_actual_gap': min(gaps), 'common_wrong_slot_gap': par['gap'],
            'whole_interval_polynomial_lowers': polynomials,
            'fixed_support_slab_r_cutoff': F(1, 2500)}


def fresh_heads(study, par, pair, pins):
    uniform, cost, finite, capacity, affine, mean, outer = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'complete_off_face_cost', 'finite_source_face_transport',
         'broad_weighted_identity_source', 'shared_budget_affine_tail', 'joint_deep_mean_transport',
         'uniform_factorial_neighborhood'))
    face = cost.face_case(finite, study.source)
    point, _ = uniform.enlarged_point(face['point'], par)
    J = outer.UniformFactorialHead(study.factorial, study.tails, finite, face, par)
    Jrows = {layout: J.components(layout) for layout in mean.layouts()}
    base_rows = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    qvertices = finite.defect_vertices(par['gap'], par['gap'], par['rho'])
    eps = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cut = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
    cuts = sorted(set((cut, (10,)*4, (12,)*4)))
    pairtail = J.pairs['old_old_distinct']+pair['pair_upper']
    require(pairtail <= J.pairs['tail_distinct_pairs'], 'Complete158 pair categories retain the new box')
    rows = []

    def scan(index, coefficients, weight, theta=F(0)):
        record = finite.prepare(coefficients)
        a1 = record['coefficients'].get(1, F(0))
        objectives = tuple((layout, a1*ref-theta*Jrows[layout]['head_total'], tuple(a1*p for p in prices))
                           for layout, ref, prices in base_rows)
        vertices = [uniform.exhaustive_vertex(cost, finite, capacity, record, face, point, par, objectives, q)
                    for q in qvertices]
        supports = [study.quadratic.constant_support(uniform, record, par,
                    uniform.fixed_tail(affine, record, par, c), vertices, theta*pairtail) for c in cuts]
        row = {'index': index, 'coefficients': record['coefficients'], 'weight': weight,
               'factorial_tail_coefficient': theta, 'exhaustive_vertices': vertices,
               'selected_support': min(supports, key=lambda v: v['upper'])}
        rows.append(row)
        print('source1/22 original objective '+str(index)+': '+str(float(row['selected_support']['upper'])), flush=True)

    for row in study.den_prior['cost_results']:
        scan(row['name'], {int(k): F(v) for k, v in row['coefficients'].items()}, F(row['weight']))
    scan('H2', {2: F(1)}, F(1))
    for row in study.mean_prior['cost_results']:
        scan(row['index'], {int(k): F(v) for k, v in row['coefficients'].items()}, study.weights[row['index']])
    original = study.get('complete_off_face_quadratic_cost')
    targets = original.prepare_rows(study.source, study.get('whole_quadratic_same_head'), study.old, study.quadratic.INDICES)
    for row in targets:
        if row['index'] != 47:
            scan(row['index'], row['expansion']['hinge_coefficients'], study.weights[row['index']],
                 row['expansion']['factorial_tail_coefficient'])
    count = sum(v['original_head_evaluations'] for r in rows for v in r['exhaustive_vertices'])
    checks = sum(v['rational_comparisons'] for r in rows for v in r['exhaustive_vertices'])
    require(len(rows) == 26 and count == 9750000 and checks == 312,
            'All new26 original objectives, all common vertices and independent exact LP checks')
    return uniform.encode({'schema': 'erdos7-expanded-source-original-heads-v1', 'source_sha256': pins,
                           'parameters': par, 'objective_rows': rows, 'original_head_evaluations': count,
                           'independent_rational_comparisons': checks})


def expanded_joint_five(study, par, joint, guard):
    """Re-establish165's source-slot proof on the guard-checked larger interval."""
    d, rho = par['delta'], par['rho']
    require(guard['source_radius'] == d and guard['residual_radius'] == rho
            and min(guard['whole_interval_polynomial_lowers'].values()) > 0,
            'The extended domain proof is an explicit prerequisite')
    cbar, amin = F(2, 5)+13*d/90, (4-d)/5
    density = (F(0), cbar-amin*(F(1, 3)-d/18), cbar-amin*(F(1, 9)-d/18), cbar, cbar)
    hbar = F(1, 2)+d/18
    H = hbar-min(density[1:])
    require(all(0 < c < hbar for c in density[1:]), 'Positive actual restricted-source references')
    shallow = study.get('uniform_shallow_indicator_transport')
    rows = []
    for L, j in product((2, 3, 4), range(5)):
        one = shallow.one_label_bound((5, None, j), L, par)
        first = one['finite_transport']['finite_upper']-one['reference']+one['source_delta_price']*d
        prices = one['coordinate_prices']
        inside = max(prices[i] for i in (2, 3, 6))
        outside = max(*(prices[i] for i in (0, 1, 4, 5)), one['q_sum_price']/par['gap'])
        if j == 0:
            first = inside = outside = F(0)
        deep = max((11 if k == j else 7)*c/40 for k, c in enumerate(density))
        shared = joint.shared_error_maximum(study.factorial, rho, d/240, H, inside, outside)
        rows.append({'first_beta': L, 'first_slot': j, 'first_source_bound': first,
                     'deep_Bellman_upper': deep, 'shared_error': shared, 'upper': 3*first+deep+shared['upper']})
    return {'density_caps': density, 'raw_density_cap': hbar, 'common_error_envelope': H,
            'first_slot_rows': rows, 'joint_upper': max(r['upper'] for r in rows)}


def complete_comparison(study, par, slab, H1, square, heads):
    A, cE = F(53, 360), 1-F(1, 614922)
    cS, cQ, C0 = map(F, (study.old['signed_mass_coefficient'], study.old['complete_square_weight'], study.old['offset']))
    heavy = []
    for row in slab['heavy_bounds']:
        C, weight, margin, price = (F(row[k]) for k in ('barrier', 'weight', 'margin_lower', 'one_residual_price'))
        index = row['index']
        require(C == F(study.engine.thresholds[index]['constant']) and weight == study.weights[index],
                'The same original heavy costs and their complete fixed-support slab theorem')
        heavy.append({'index': index, 'weight': weight, 'barrier': C,
                      'endpoint_upper': C*A-margin+price*par['rho']})
    raw46 = study.square.retained_raw81(study.source, study.quadratic, study.old, study.read('k_face_complete_ratio'), par['delta'])
    raw47 = study.quadratic.retained_raw81_controller(study.source, study.old, par['delta'])
    simple = [{'index': r['index'], 'weight': F(r['weight']),
               'endpoint_upper': F(r['at_one'])*A+F(r['first_difference'])*H1['upper']
                 +F(r['second_curvature'])*heads['H2']['selected_support']['upper']}
              for r in study.simple_prior['radii'][0]['cost_results']]
    require(sum(F(r['weight'])*F(r['at_one']) for r in study.simple_prior['radii'][0]['cost_results'])
            == study.weights[40], 'Only row40 supplies a simple-cost unit-mass term')
    groups = {'mean11': heads['mean_shared']['upper'],
              'single28_at_mass_floor': sum(r['weight']*r['endpoint_upper'] for r in simple),
              'quadratic9': heads['quadratic_shared']['upper'],
              'raw81_first': raw46['outside_weight']*raw46['uniform_upper'],
              'raw81_second': raw47['weight']*raw47['uniform_upper'],
              'heavy2_fixed_support': sum(r['weight']*r['endpoint_upper'] for r in heavy),
              'square_at_mass_floor': cQ*(A+square['full_square_upper']-square['mass_upper'])}
    N = cS*A+sum(groups.values())
    denominator = cE*A-heads['denominator_shared']['upper']-H1['upper']/55902
    M = cS+sum(r['weight']*r['barrier'] for r in heavy)+study.weights[40]+cQ
    require(N > 0 and denominator > 0, 'Same actual-mass endpoint and positive complete denominator')
    target = C0+N/denominator
    remaining = (target-C0)*cE-M
    require(remaining > 0 and (target-C0)*denominator == N, 'Complete signed comparison for all actual S>=53/360')
    indices = [r['index'] for r in heads['mean_costs']+heads['quadratic_costs']+simple]+[0, 16, 46, 47]
    require(sorted(indices) == list(range(52)), 'All52 independent original tests, each once')
    return {'heavy_costs': heavy, 'cost_groups': groups, 'all_original_indices': sorted(indices),
            'simple_costs': simple, 'signed_endpoint': N, 'denominator_at_mass_floor': denominator,
            'mass_coefficient': M, 'remaining_S_coefficient': remaining, 'raw_s_coefficient': F(0),
            'offset': C0, 'comparison_upper': target, 'retained_raw81_first': raw46,
            'retained_raw81_second': raw47, 'target': F(509), 'target_margin': 509-target}


def transported_heads(study, oldpar, par, pair, scanned):
    """A uniform finite-LP perturbation, then complete new residual-tail support."""
    uniform, cost, finite, capacity, affine, mean, outer, portfolio = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'complete_off_face_cost', 'finite_source_face_transport',
         'broad_weighted_identity_source', 'shared_budget_affine_tail', 'joint_deep_mean_transport',
         'uniform_factorial_neighborhood', 'uniform_mean_cost_portfolio'))
    require(oldpar['delta'] == par['delta'] and oldpar['rho'] < par['rho'], 'Only the actual residual radius enlarges')
    face = cost.face_case(finite, study.source)
    oldpoint, _ = uniform.enlarged_point(face['point'], oldpar)
    point, _ = uniform.enlarged_point(face['point'], par)
    cap_diff = tuple(a-b for a, b in zip(point['caps'], oldpoint['caps']))
    require(min(cap_diff) >= 0 and point['budgets'] == oldpoint['budgets']
            and point['score'] == oldpoint['score'], 'Same finite LP groups and budgets, only capacities enlarge')
    oldJ = outer.UniformFactorialHead(study.factorial, study.tails, finite, face, oldpar)
    newJ = outer.UniformFactorialHead(study.factorial, study.tails, finite, face, par)
    Jdiff = [(layout, newJ.components(layout)['head_total']-oldJ.components(layout)['head_total'])
             for layout in mean.layouts()]
    factorial_increment = max(F(0), *(v for _, v in Jdiff))
    Jdigest = sha256(json.dumps(uniform.encode(Jdiff), separators=(',', ':')).encode()).hexdigest()
    oldmean = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, oldpar)
    newmean = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    require(oldmean == newmean, 'All layout-dependent mean references and seven prices are unchanged')
    maximum_prices = tuple(max(prices[j] for _, _, prices in newmean) for j in range(7))
    old_qvertices = finite.defect_vertices(oldpar['gap'], oldpar['gap'], oldpar['rho'])
    qvertices = finite.defect_vertices(par['gap'], par['gap'], par['rho'])
    require(len(qvertices) == len(old_qvertices) == 3
            and all(all(a <= b for a, b in zip(q0, q)) for q0, q in zip(old_qvertices, qvertices)),
            'Corresponding common-polytope vertices lie on the same three rays')
    eps = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cut = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
    cuts = sorted(set((cut, (10,)*4, (12,)*4)))
    pairtail = newJ.pairs['old_old_distinct']+pair['pair_upper']
    require(pairtail <= newJ.pairs['tail_distinct_pairs'], 'Every new-radius factorial pair and tail is retained')
    jobs, probe_count = [], 0

    def actual_branch(up, fc, layout, extra):
        B = up.load(layout)
        head = tuple(up.head[i, extra[i], B[i]] for i in range(25))
        lp = sum(up.capacity(head, group, budget) for group, budget in zip(cost.GROUPS, up.budgets))
        selected = 0
        for k, choices in enumerate(fc.operators, 1):
            selected += max(sum(weight*fc.inc[k, i, extra[i], B[i]] for i, weight in row) for row in choices)
        return F(lp, up.scale)+F(selected, fc.scale)

    for saved in scanned['objective_rows']:
        record = finite.prepare({int(k): F(v) for k, v in saved['coefficients'].items()})
        theta, a1 = F(saved['factorial_tail_coefficient']), record['coefficients'].get(1, F(0))
        require(theta >= 0 and a1 >= 0, 'The factorial and mean transport increments retain their upper-bound direction')
        vertices, transports = [], []
        for qi, (q0, q) in enumerate(zip(old_qvertices, qvertices)):
            oldv = saved['exhaustive_vertices'][qi]
            require(tuple(map(F, oldv['q'])) == q0, 'The exact independently enumerated old q vertex')
            oldup, newup = (cost.IntegerHead(finite, record, p, qq) for p, qq in ((oldpoint, q0), (point, q)))
            oldface, newface = (cost.IntegerHead(finite, record, face['point'], qq) for qq in (q0, q))
            normalized = lambda fc: tuple(tuple(tuple((i, F(w, fc.mass_scale)) for i, w in row)
                                               for row in choices) for choices in fc.operators)
            require(normalized(oldface) == normalized(newface), 'Every selected face-operator weight is unchanged')
            coefficient_max, coefficient_diff = [], []
            for i in range(25):
                allkeys = [(i, m, v) for m, v in product(range(3), range(1, 7))]
                coefficient_max.append(max(F(newup.head[k], newup.cost_scale) for k in allkeys))
                coefficient_diff.append(max(F(newup.head[k], newup.cost_scale)-F(oldup.head[k], oldup.cost_scale) for k in allkeys))
            require(min(coefficient_max) >= 0 and min(coefficient_diff) >= 0,
                    'All retained coefficient bounds and density changes are nonnegative')
            lp_change = sum(dc*c+oldc*dv for dc, c, oldc, dv in
                            zip(cap_diff, coefficient_max, oldpoint['caps'], coefficient_diff))
            selected_changes = []
            for k, choices in enumerate(oldface.operators, 1):
                increments = tuple(max(F(newface.inc[k, i, m, v], newface.cost_scale)
                                       -F(oldface.inc[k, i, m, v], oldface.cost_scale)
                                       for m, v in product(range(3), range(1, 7))) for i in range(25))
                require(min(increments) >= 0, 'Selected original increment changes remain nonnegative')
                selected_changes.append(max(sum(F(weight, oldface.mass_scale)*increments[i] for i, weight in row)
                                            for row in choices))
            selected_change = sum(selected_changes, F(0))
            oldres, newres = oldpar['rho']-oldpar['gap']*sum(q0), par['rho']-par['gap']*sum(q)
            require(F(oldv['residual']) == oldres and newres >= oldres >= 0, 'One actual residual at each corresponding vertex')
            shift = tuple(lp_change+selected_change+theta*factorial_increment
                          +a1*(newres-oldres)*p for p in maximum_prices)
            head_upper = tuple(F(v)+s for v, s in zip(oldv['head_maxima'], shift))
            for layout in uniform.PROBES:
                for root, slot, extra in newup.positive7:
                    change = actual_branch(newup, newface, layout, extra)-actual_branch(oldup, oldface, layout, extra)
                    require(change <= lp_change+selected_change,
                            'Independent complete finite branch respects the all-layout perturbation')
                    probe_count += 1
            vertices.append({'q': q, 'residual': newres, 'head_maxima': head_upper})
            transports.append({'old_q': q0, 'new_q': q, 'old_residual': oldres, 'new_residual': newres,
                               'finite_LP_increment': lp_change, 'selected_increment': selected_change,
                               'factorial_increment': theta*factorial_increment,
                               'seven_coordinate_increments': shift,
                               'old_original_head_digest': oldv['finite_objectives_sha256']})
        supports = [study.quadratic.constant_support(uniform, record, par,
                    uniform.fixed_tail(affine, record, par, c), vertices, theta*pairtail) for c in cuts]
        jobs.append({'index': saved['index'], 'name': str(saved['index']), 'weight': F(saved['weight']),
                     'coefficients': record['coefficients'], 'factorial_tail_coefficient': theta,
                     'transported_vertices': vertices, 'transport_proofs': transports,
                     'selected_support': min(supports, key=lambda r: r['upper'])})
    den = [r for r in jobs if isinstance(r['index'], str) and r['index'].startswith('AP')]
    H2 = next(r for r in jobs if r['index'] == 'H2')
    means = [r for r in jobs if isinstance(r['index'], int) and r['index'] < 41]
    quads = [r for r in jobs if isinstance(r['index'], int) and r['index'] >= 41]
    require(len(den) == 5 and len(means) == 11 and len(quads) == 9 and probe_count == 3120,
            'All26 original objectives transported, with3120 complete finite-branch checks')
    return {'denominator_costs': den, 'denominator_shared': portfolio.shared_maximum(den), 'H2': H2,
            'mean_costs': means, 'mean_shared': portfolio.shared_maximum(means),
            'quadratic_costs': quads, 'quadratic_shared': portfolio.shared_maximum(quads),
            'old_parameters': oldpar, 'parameters': par, 'cap_increments': cap_diff,
            'factorial_head_increment': factorial_increment, 'factorial_difference_digest': Jdigest,
            'factorial_layouts': len(Jdiff), 'mean_coordinate_price_maxima': maximum_prices,
            'complete_pair_upper': pairtail, 'finite_branch_transport_checks': probe_count,
            'reused_original_head_evaluations': scanned['original_head_evaluations'],
            'new_original_head_evaluations': 0}


def calculate(base, scan=False, write_heads=False):
    io = module('expanded_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json'))
    pins = {**prior['source_sha256'], **PINS}
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned full source '+path)
    study = module('expanded_study', base/'frontier/endpoint-bounds/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(p) == h for p, h in study.pins.items()), 'Full original comparison source closure')
    residual, wide, prices, pairs, joint = (study.get(n) for n in
        ('residual_shell_k_comparison', 'wide_k_signed_tail_comparison', 'exposed_concentration_prices',
         'seven_pair_source_prices', 'pure_five_complete_face_comparison'))
    pair = pairs.bounds(prices, pairs.raw_coefficients(study.factorial), DELTA)
    par = wide.parameters(study, DELTA, RHO)
    par['positive7'] = pair['Z_upper']
    guard = source_guards(study, par)
    H1 = residual.shallow_H1(study, par)
    square = study.square.uniform_square(par, SimpleNamespace(uniform_H1=lambda p: H1), study.factorial, study.tails)
    five = expanded_joint_five(study, par, joint, guard)
    old_pure = (next(r['weighted_upper'] for r in square['bounded_cylinders'] if r['modulus'] == 5)
                +next(r['upper'] for r in square['complete_weighted_tails'] if r['family'] == 'pure5'))
    saving = max(F(0), old_pure-five['joint_upper'])
    require(saving > 0, 'The actual joint pure-five estimate improves this larger source box')
    square = {**square, 'previous_full_square_upper': square['full_square_upper'],
              'old_pure_five_block': old_pure, 'joint_pure_five_block': five['joint_upper'],
              'joint_square_saving': saving, 'full_square_upper': square['full_square_upper']-saving,
              'zero7_pair_upper': square['zero7_pair_upper']-saving}
    if scan:
        started = perf_counter()
        scanned = fresh_heads(study, par, pair, pins)
        print('Fresh original heads elapsed_seconds='+str(perf_counter()-started), flush=True)
        if write_heads:
            io.write_certificate_text(base/HEAD_CERTIFICATE, json.dumps(scanned, indent=2)+'\n')
        else:
            require(scanned == json.loads(io.read_artifact_bytes(base/HEAD_CERTIFICATE)), 'Independent complete head replay')
    else:
        scanned = json.loads(io.read_artifact_bytes(base/HEAD_CERTIFICATE))
    require(scanned['source_sha256'] == pins, 'The newly measured original heads bind the exact current inputs')
    heads = residual.scan_heads(study, par, pair, scanned)
    slab = study.read('fixed_support_source_slab')
    result = complete_comparison(study, par, slab, H1, square, heads)
    print('Complete new source box K='+str(float(result['comparison_upper']))+
          '; target margin='+str(float(result['target_margin'])), flush=True)
    expanded_par = wide.parameters(study, DELTA, EXPANDED_RHO)
    expanded_par['positive7'] = pair['Z_upper']
    expanded_guard = source_guards(study, expanded_par)
    expanded_H1 = residual.shallow_H1(study, expanded_par)
    expanded_square = study.square.uniform_square(expanded_par,
        SimpleNamespace(uniform_H1=lambda p: expanded_H1), study.factorial, study.tails)
    expanded_five = expanded_joint_five(study, expanded_par, joint, expanded_guard)
    old_pure = (next(r['weighted_upper'] for r in expanded_square['bounded_cylinders'] if r['modulus'] == 5)
                +next(r['upper'] for r in expanded_square['complete_weighted_tails'] if r['family'] == 'pure5'))
    saving = max(F(0), old_pure-expanded_five['joint_upper'])
    require(saving > 0, 'Joint pure-five transport still improves the wider residual rectangle')
    expanded_square = {**expanded_square, 'previous_full_square_upper': expanded_square['full_square_upper'],
                       'old_pure_five_block': old_pure, 'joint_pure_five_block': expanded_five['joint_upper'],
                       'joint_square_saving': saving, 'full_square_upper': expanded_square['full_square_upper']-saving,
                       'zero7_pair_upper': expanded_square['zero7_pair_upper']-saving}
    expanded_heads = transported_heads(study, par, expanded_par, pair, scanned)
    expanded_result = complete_comparison(study, expanded_par, slab, expanded_H1, expanded_square, expanded_heads)
    require(expanded_result['comparison_upper'] < 509, 'The wider complete domain is sufficient for the global splice')
    print('Expanded rho1/15000 complete K='+str(float(expanded_result['comparison_upper'])), flush=True)
    pins[HEAD_CERTIFICATE] = sha256(io.read_artifact_bytes(base/HEAD_CERTIFICATE)).hexdigest()
    return study.uniform.encode({'schema': 'erdos7-expanded-source-complete-comparison-v1', 'source_sha256': pins,
                                  'parameters': par, 'guards': guard, 'complete_H1': H1,
                                  'joint_pure_five_transport': five, 'complete_square': square,
                                  'complete_heads': heads, 'comparison': result,
                                  'expanded_residual_comparison': {'parameters': expanded_par, 'guards': expanded_guard,
                                      'complete_H1': expanded_H1, 'complete_square': expanded_square,
                                      'joint_pure_five_transport': expanded_five, 'complete_heads': expanded_heads,
                                      'comparison': expanded_result},
                                  'scope': 'Ordinary complete actual-source bounds for both orientations, sigma<=1/22, rho<=1/15000, r<=1/3000. All52 independent original tests, actual S coefficient, five denominator objectives and every infinite tail remain. New source guards and9.75 million new original-head evaluations at rho1/20000, with312 independent rational LP checks; the wider residual uses proved coefficient/cap transport with3120 complete finite-branch checks. No unrestricted or full-global K claim, Lean verification or realization of relaxation maxima.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--scan', action='store_true', help='Re-evaluate all new-box original heads')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base, args.scan, args.write)
    io = module('expanded_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact expanded-source complete certificate')
    print('PASS: complete source radius1/22, residual1/15000; K='
          +result['expanded_residual_comparison']['comparison']['comparison_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
