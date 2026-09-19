#!/usr/bin/env python3
"""Transport a complete original-head scan while the source radius changes."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
from math import lcm
from types import SimpleNamespace
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/transported_source_complete_comparison.json'
DELTA, RHO = F(1, 18), F(1, 13000)
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/expanded_source_complete_comparison.py': 'faffa75e9f37987c5ceb7afc1eb4b1540e5fc067afcd78804ecf8067f2bb623c',
    'certificates/source_norms/expanded_source_complete_comparison.json': '6339942b05fd9b3540268fc76a5aa773a058fe863518bdd29829ce15bff5dfa7',
    'certificates/source_norms/expanded_source_original_heads.json': '0650365321b9d63ceb09ec2d63ef5b72cdf8765bb39fd3fe1bf7cc7c6669c4fd',
    'frontier/fixed_support_source_slab.py': '937399b0a0c88c650746a93c4456012692215bf65f80b7525aaefe29c94f9593',
    'certificates/source_norms/fixed_support_source_slab.json': 'e201842ea5c0db4179dfa1449ceb7196c4f8c6dbf35d54825f54d9fde0a16837',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable proof input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def source_guards(study, par):
    """All source, first-label, density and fixed-support guards are re-established."""
    d, rho, r = par['delta'], par['rho'], par['rbar']
    require(F(1, 22) <= d <= DELTA and 0 <= rho <= RHO and r == 5*rho < F(1, 2500),
            'The new rectangle and complete162 fixed-support slot-loss range')
    require(d < F(2, 27), 'The original134 cap and tail geometry domain')
    Delta = d/(4*(1-d))
    D = study.get('exposed_concentration_prices').norm_bounds(d)['availability_Linfinity']
    h1, eta = F(1, 3)-d/18, F(1, 9)-d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-D)-2*r, (F(1, 6)-d/9)/5-r)
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d}
    require(Delta <= F(1, 68) < F(1, 18) and F(3, 4)+d/4 <= F(55, 72) < F(4, 5)
            and D <= Delta and min(gaps) >= F(241, 22500) and 0 < par['gap'] <= min(gaps),
            'The actual source slab, all five first-label gaps and common residual simplex')
    require(min(polynomials.values()) > 0 and 6*d-23 < 0 and F(1, 4)-3*d/4 > F(1, 20),
            'Every decreasing source polynomial and first-label forcing condition is positive')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0, 'Every retained-deep marker remains nonnegative')
    return {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
            'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
            'availability_upper': D, 'five_actual_gap_lowers': gaps,
            'minimum_actual_gap': min(gaps), 'common_wrong_slot_gap': par['gap'],
            'whole_interval_polynomial_lowers': polynomials,
            'fixed_support_slab_r_cutoff': F(1, 2500), 'marker_coefficient_floor': F(11, 27)}


def transported_heads(study, oldpar, par, pair, scanned):
    """Transport capacities, budgets, density scores and the joint original head."""
    uniform, cost, finite, capacity, affine, mean, outer, portfolio = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'complete_off_face_cost', 'finite_source_face_transport',
         'broad_weighted_identity_source', 'shared_budget_affine_tail', 'joint_deep_mean_transport',
         'uniform_factorial_neighborhood', 'uniform_mean_cost_portfolio'))
    require(oldpar['delta'] <= par['delta'] and oldpar['rho'] <= par['rho'], 'Both source and residual radii enlarge')
    face = cost.face_case(finite, study.source)
    oldpoint, _ = uniform.enlarged_point(face['point'], oldpar)
    point, _ = uniform.enlarged_point(face['point'], par)
    cap_diff = tuple(max(F(0), a-b) for a, b in zip(point['caps'], oldpoint['caps']))
    budget_diff = tuple(max(F(0), a-b) for a, b in zip(point['budgets'], oldpoint['budgets']))
    require(sorted(i for group in cost.GROUPS for i in group) == list(range(25)),
            'Three nonoverlapping groups partition every finite LP variable')
    oldJ = outer.UniformFactorialHead(study.factorial, study.tails, finite, face, oldpar)
    newJ = outer.UniformFactorialHead(study.factorial, study.tails, finite, face, par)
    Jdiff = [(layout, newJ.components(layout)['head_total']-oldJ.components(layout)['head_total'])
             for layout in mean.layouts()]
    factorial_increment = max(F(0), *(v for _, v in Jdiff))
    Jdigest = sha256(json.dumps(uniform.encode(Jdiff), separators=(',', ':')).encode()).hexdigest()
    oldmean = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, oldpar)
    newmean = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    require(all(x[0] == y[0] == z[0] for x, y, z in zip(oldmean, newmean, Jdiff)), 'One original layout throughout the joint transport')
    oldmean_map = {ell: (ref, prices) for ell, ref, prices in oldmean}
    newmean_map = {ell: (ref, prices) for ell, ref, prices in newmean}
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
    joint_tables, joint_hashes, transport_cache = [], [], {}
    for q0, q in zip(old_qvertices, qvertices):
        oldres, newres = oldpar['rho']-oldpar['gap']*sum(q0), par['rho']-par['gap']*sum(q)
        rows = [(ell, jd, tuple(oldref-newref+newres*np-oldres*op for op, np in zip(oldprices, newprices)))
                for (ell, oldref, oldprices), (_, newref, newprices), (_, jd) in zip(oldmean, newmean, Jdiff)]
        scale = lcm(*(v.denominator for _, jd, prices in rows for v in (jd,)+prices))
        integers = [(ell, int(scale*jd), tuple(int(scale*p) for p in prices)) for ell, jd, prices in rows]
        joint_tables.append((scale, integers))
        joint_hashes.append(sha256(json.dumps([scale, integers], separators=(',', ':')).encode()).hexdigest())

    def same_layout_shift(a1, theta, qi):
        key = (a1, theta, qi)
        if key not in transport_cache:
            scale, rows = joint_tables[qi]
            factor = lcm(a1.denominator, theta.denominator)
            aa, tt = int(factor*a1), int(factor*theta)
            maxima, witnesses = [None]*7, [None]*7
            for ell, jd, prices in rows:
                for j, p in enumerate(prices):
                    value = tt*jd+aa*p
                    if maxima[j] is None or value > maxima[j]:
                        maxima[j], witnesses[j] = value, ell
            transport_cache[key] = (tuple(F(v, scale*factor) for v in maxima), witnesses)
        return transport_cache[key]

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
            require(tuple(map(F, oldv['q'])) == q0 and oldv['original_head_evaluations'] == 125000
                    and oldv['rational_comparisons'] == 4 and len(oldv['head_maxima']) == 7,
                    'The exact independently enumerated old q vertex and complete inventory')
            oldup, newup = (cost.IntegerHead(finite, record, p, qq) for p, qq in ((oldpoint, q0), (point, q)))
            oldface, newface = (cost.IntegerHead(finite, record, face['point'], qq) for qq in (q0, q))
            normalized = lambda fc: tuple(tuple(tuple((i, F(w, fc.mass_scale)) for i, w in row)
                                               for row in choices) for choices in fc.operators)
            require(normalized(oldface) == normalized(newface), 'Every selected face-operator weight is unchanged')
            coefficient_max, coefficient_diff = [], []
            for i in range(25):
                allkeys = [(i, m, v) for m, v in product(range(3), range(1, 7))]
                coefficient_max.append(max(F(newup.head[k], newup.cost_scale) for k in allkeys))
                coefficient_diff.append(max(F(0), *(F(newup.head[k], newup.cost_scale)-F(oldup.head[k], oldup.cost_scale) for k in allkeys)))
            require(min(coefficient_max) >= 0 and min(coefficient_diff) >= 0,
                    'All retained coefficient bounds and density changes are nonnegative')
            lp_change = sum(dc*c+oldc*dv for dc, c, oldc, dv in
                            zip(cap_diff, coefficient_max, oldpoint['caps'], coefficient_diff))
            budget_change = sum(db*max(coefficient_max[i] for i in group) for db, group in zip(budget_diff, cost.GROUPS))
            lp_change += budget_change
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
            joint_shift, joint_witnesses = same_layout_shift(a1, theta, qi)
            for j, ell in enumerate(joint_witnesses):
                ref0, prices0 = oldmean_map[ell]
                ref1, prices1 = newmean_map[ell]
                exact = theta*(newJ.components(ell)['head_total']-oldJ.components(ell)['head_total'])
                exact += a1*(ref0-ref1+newres*prices1[j]-oldres*prices0[j])
                require(exact == joint_shift[j], 'Rational reconstruction of every joint transport witness')
            shift = tuple(lp_change+selected_change+x for x in joint_shift)
            head_upper = tuple(F(v)+s for v, s in zip(oldv['head_maxima'], shift))
            for layout in uniform.PROBES:
                for root, slot, extra in newup.positive7:
                    change = actual_branch(newup, newface, layout, extra)-actual_branch(oldup, oldface, layout, extra)
                    require(change <= lp_change+selected_change,
                            'Independent complete finite branch respects the all-layout perturbation')
                    probe_count += 1
            vertices.append({'q': q, 'residual': newres, 'head_maxima': head_upper})
            transports.append({'old_q': q0, 'new_q': q, 'old_residual': oldres, 'new_residual': newres,
                               'finite_LP_increment': lp_change, 'group_budget_increment': budget_change,
                               'selected_increment': selected_change, 'joint_mean_factorial_increments': joint_shift,
                               'joint_mean_factorial_witnesses': joint_witnesses,
                               'separate_factorial_increment_bound': theta*factorial_increment,
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
            'factorial_layouts': len(Jdiff), 'group_budget_increments': budget_diff,
            'old_scores': oldpoint['score'], 'new_scores': point['score'],
            'joint_mean_factorial_difference_digests': joint_hashes,
            'complete_pair_upper': pairtail, 'finite_branch_transport_checks': probe_count,
            'reused_original_head_evaluations': scanned['original_head_evaluations'],
            'new_original_head_evaluations': 0}



def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('transported_source_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    prior = read('certificates/source_norms/expanded_source_complete_comparison.json')
    scanned = read('certificates/source_norms/expanded_source_original_heads.json')
    used = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent source closure: '+path)
        used[path] = pin
    for path, pin in used.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned proof input: '+path)
    study = module('transported_source_study', base/'frontier/k_neighborhood_radius_study.py').Study(base)
    require(all(used.get(p) == h for p, h in study.pins.items())
            and all(used.get(p) == h for p, h in scanned['source_sha256'].items()),
            'The entire original comparison and old scan bind their existing inputs')
    expanded, residual = study.get('expanded_source_complete_comparison'), study.get('residual_shell_k_comparison')
    oldpar = {k: tuple(map(F, v)) if isinstance(v, list) else F(v) for k, v in prior['parameters'].items()}
    require((oldpar['delta'], oldpar['rho']) == (F(1, 22), F(1, 20000))
            and scanned['parameters'] == study.uniform.encode(oldpar)
            and scanned['original_head_evaluations'] == 9750000
            and scanned['independent_rational_comparisons'] == 312,
            'The exact complete166 scan, not a reused narrower-source maximum')
    prices, pairs, joint = (study.get(n) for n in
        ('exposed_concentration_prices', 'seven_pair_source_prices', 'pure_five_complete_face_comparison'))
    pair = pairs.bounds(prices, pairs.raw_coefficients(study.factorial), DELTA)
    par = study.get('wide_k_signed_tail_comparison').parameters(study, DELTA, RHO)
    par['positive7'] = pair['Z_upper']
    guard = source_guards(study, par)
    H1 = residual.shallow_H1(study, par)
    square = study.square.uniform_square(par, SimpleNamespace(uniform_H1=lambda p: H1), study.factorial, study.tails)
    five = expanded.expanded_joint_five(study, par, joint, guard)
    old_pure = (next(r['weighted_upper'] for r in square['bounded_cylinders'] if r['modulus'] == 5)
                +next(r['upper'] for r in square['complete_weighted_tails'] if r['family'] == 'pure5'))
    saving = max(F(0), old_pure-five['joint_upper'])
    square = {**square, 'previous_full_square_upper': square['full_square_upper'],
              'old_pure_five_block': old_pure, 'joint_pure_five_block': five['joint_upper'],
              'joint_square_saving': saving, 'full_square_upper': square['full_square_upper']-saving,
              'zero7_pair_upper': square['zero7_pair_upper']-saving}
    heads = transported_heads(study, oldpar, par, pair, scanned)
    comparison = expanded.complete_comparison(study, par, study.read('fixed_support_source_slab'), H1, square, heads)
    require(comparison['comparison_upper'] < 509 and heads['new_original_head_evaluations'] == 0,
            'Complete larger-domain bound below509 without a new original-head scan')
    return study.uniform.encode({'schema': 'erdos7-transported-source-complete-comparison-v1',
            'source_sha256': used, 'parameters': par, 'guards': guard,
            'complete_H1': H1, 'joint_pure_five_transport': five, 'complete_square': square,
            'complete_heads': heads, 'comparison': comparison,
            'scope': 'Ordinary complete local theorem on both actual K orientations, sigma<=1/18, rho<=1/13000, r<=1/2600. All52 original independent costs, five complete denominator objectives, the same actual residual and actual S coefficient, and every infinite tail remain. A cap/budget/coefficient perturbation transports all166 original heads, with12500 same-layout mean/factorial corrections and3120 independent finite-branch checks. The162 fixed-support heavy theorem applies inside its original strict r cutoff. No new global K, unrestricted Erdos7 conclusion, Lean verification, fresh9.75m-head enumeration or actual attainment of the relaxed maxima.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('transported_source_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact transported-source complete certificate')
    comparison = result['comparison']
    print('PASS: source1/18, residual1/13000, actual r<=1/2600, all52 original tests and complete tails.')
    print('Complete comparison='+str(float(F(comparison['comparison_upper'])))+
          '; margin below509='+str(float(F(comparison['target_margin'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
