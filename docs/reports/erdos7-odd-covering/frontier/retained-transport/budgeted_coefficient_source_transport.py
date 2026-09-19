#!/usr/bin/env python3
"""Keep the old group budgets when pricing finite-head coefficient changes.

The stronger general transport extends the complete full-slot source
rectangle to rho1/940. All remaining source and tail bounds are rebuilt.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/budgeted_coefficient_source_transport.json'
DELTA, RHO = F(1, 26), F(1, 940)
TARGET = F(509289, 1000)
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/full_slot_radius_source_comparison.py': 'fac5400fa27868f790fae4d762488f52061a5ecbc580eacd406d65c00f7ce750',
    'certificates/source_norms/source-budgets/full_slot_radius_source_comparison.json': '19356548e96024d02fbd1c24f1d0138bde17c2f498c286ff478bade95d2753ff',
    'certificates/source_norms/source-budgets/full_slot_radius_source_heads.json': '9c917e5739bf52fe6c7ed87169373a2623c68b3cf08f579a2dec383a6a968dc7',
    'frontier/retained-transport/transported_source_complete_comparison.py': '361c6ba33a0d78abae5238656412a4caa8470f5a10ee1c9667245bb72c4bd8c2',
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


def parameters_and_guards(study):
    d, rho, r = DELTA, RHO, 5*RHO
    require(d == F(1, 26) < F(2, 27) and rho == F(1, 940) and r == F(1, 188),
            'The larger source rectangle with its full actual slot-loss range')
    total_loss = study.get('joint_concentration_loss_budget').total_loss_upper(d)
    Delta = total_loss/4
    D = study.get('exposed_concentration_prices').norm_bounds(d)['availability_Linfinity']
    h1, eta, hbar = F(1, 3)-d/18, F(1, 9)-d/18, F(1, 2)+d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-D)-2*r, (F(1, 6)-d/9)/5-r)
    gap = min(gaps)
    require(total_loss == F(1, 25) and Delta == F(1, 100) < F(1, 18)
            and D == F(3, 304) <= Delta and F(3, 4)+d/4 == F(79, 104) < F(4, 5),
            'Actual r=0 source lies inside162; exposed price bounds the same p+a+b')
    require(gap == F(151, 9165) > 0 and rho/gap == F(39, 604) < F(1, 5),
            'All five general first-label guards and their full common defect simplex')
    require(F(1, 4)-3*d/4 == F(23, 104) > F(1, 20),
            'The three first labels and their distinct slots are forced independently of r')
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d}
    require(min(polynomials.values()) > 0 and 6*d-23 < 0,
            'Every source domain polynomial stays positive throughout[0,1/26]')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0,
            'Original marked fixed-support dual coefficients remain nonnegative')
    par = study.get('wide_k_signed_tail_comparison').parameters(study, d, rho)
    par.update(rbar=r, gap=gap, v0=min(F(1, 20), Delta+2*r),
               v1=min(F(1, 10), Delta+r/h1))
    require(par['v0'] == F(97, 4700) and par['v1'] == F(3797, 145700),
            'Reconstructed full-r cap increments on the new source radius')
    P = max(hbar/(5*gap), F(65, 9))
    require(hbar/(5*gap) == F(11045, 1812) and P == F(65, 9)
            and P >= max(F(1), hbar/(5*gap)) and P >= 5*F(13, 9),
            'Same one-residual heavy price still pays every actual marker and slot motion')
    return par, {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
        'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
        'availability_upper': D, 'h1_lower': h1, 'first_beta_eta_lower': eta,
        'h_upper': hbar, 'five_actual_gap_lowers': gaps, 'minimum_actual_gap': gap,
        'common_wrong_slot_gap': gap, 'whole_interval_polynomial_lowers': polynomials,
        'heavy_residual_price_coefficient': P, 'heavy_slot_movement_coefficient': F(13, 9),
        'independent_r_cutoff': None}


def heavy_extension(study, guard):
    rows = []
    for old in study.read('fixed_support_source_slab')['heavy_bounds']:
        vmax = F(old['max_derivative'])
        row = {k: old[k] for k in ('index', 'barrier', 'weight', 'margin_lower')}
        row.update(max_derivative=vmax,
                   slot_movement_price=guard['heavy_slot_movement_coefficient']*vmax,
                   original_marker_price_upper=max(F(1),
                       guard['h_upper']/(5*guard['minimum_actual_gap']))*vmax,
                   one_residual_price=guard['heavy_residual_price_coefficient']*vmax)
        require(row['one_residual_price'] >= 5*row['slot_movement_price']
                and row['one_residual_price'] >= row['original_marker_price_upper'],
                'D r + P[rho-(r+r1)/5] <= P rho on the same actual residual')
        rows.append(row)
    require([r['index'] for r in rows] == [0, 16]
            and [r['one_residual_price'] for r in rows] == [F(12491905, 792792), F(18197065, 1459458)],
            'Both complete heavy tests retain their169 one-residual prices')
    return {'heavy_bounds': rows,
            'positive_r_proof': 'The162 r=0 fixed-support floors apply to the new source slab. General85/91 first-label and packing guards are independently re-established. The fixed correction loses at most(13/9)vmax*r. The original marker costs at mostmax(1,hbar/(5G))vmax per epsilon=rho-(r+r1)/5. Taking P=(65/9)vmax pays both with one rho; no old positive-r wrapper is invoked.'}


def refined_heads(study, oldpar, par, pair, scanned):
    """Replace the cap-only coefficient payment by its exact old-group support."""
    previous = study.get('transported_source_complete_comparison').transported_heads(
        study, oldpar, par, pair, scanned)
    uniform, cost, finite, capacity, affine, portfolio = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'complete_off_face_cost', 'finite_source_face_transport',
         'broad_weighted_identity_source', 'shared_budget_affine_tail', 'uniform_mean_cost_portfolio'))
    face = cost.face_case(finite, study.source)
    oldpoint, _ = uniform.enlarged_point(face['point'], oldpar)
    point, _ = uniform.enlarged_point(face['point'], par)
    require(sorted(i for group in cost.GROUPS for i in group) == list(range(25)),
            'The three disjoint old budgets cover all25 finite variables')
    oldvertices = finite.defect_vertices(oldpar['gap'], oldpar['gap'], oldpar['rho'])
    eps = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cut = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in
                zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
    cuts = sorted(set((cut, (10,)*4, (12,)*4)))
    jobs = (previous['denominator_costs']+[previous['H2']]
            +previous['mean_costs']+previous['quadratic_costs'])
    probes, supports, strict = 0, 0, 0

    def finite_value(up, fc, layout, extra):
        B = up.load(layout)
        head = tuple(up.head[i, extra[i], B[i]] for i in range(25))
        lp = sum(up.capacity(head, group, budget) for group, budget in zip(cost.GROUPS, up.budgets))
        selected = sum(max(sum(weight*fc.inc[k, i, extra[i], B[i]] for i, weight in row)
                           for row in choices) for k, choices in enumerate(fc.operators, 1))
        return F(lp, up.scale)+F(selected, fc.scale)

    for row in jobs:
        record = finite.prepare({int(k): F(v) for k, v in row['coefficients'].items()})
        for qi, vertex in enumerate(row['transported_vertices']):
            q0, q = oldvertices[qi], vertex['q']
            oldup = cost.IntegerHead(finite, record, oldpoint, q0)
            newup = cost.IntegerHead(finite, record, point, q)
            oldface = cost.IntegerHead(finite, record, face['point'], q0)
            newface = cost.IntegerHead(finite, record, face['point'], q)
            U, D = [], []
            for i in range(25):
                keys = [(i, m, v) for m, v in product(range(3), range(1, 7))]
                U.append(max(F(newup.head[k], newup.cost_scale) for k in keys))
                D.append(max(F(0), *(F(newup.head[k], newup.cost_scale)
                         -F(oldup.head[k], oldup.cost_scale) for k in keys)))
            trivial = sum(u*d for u, d in zip(oldpoint['caps'], D))
            group_rows = []
            for group, budget in zip(cost.GROUPS, oldpoint['budgets']):
                value, gamma = capacity.capacity_dual(D, oldpoint['caps'], budget, group)
                require(value == gamma*budget+sum(oldpoint['caps'][i]*max(D[i]-gamma, F(0)) for i in group),
                        'Exact old-group dual certificate for the coefficient increase')
                group_rows.append({'indices': group, 'budget': budget, 'dual_price': gamma, 'upper': value})
                supports += 1
            grouped = sum(g['upper'] for g in group_rows)
            require(F(0) <= grouped <= trivial, 'Old budget support improves its cap-only support')
            saving = trivial-grouped
            strict += int(saving > 0)
            proof = row['transport_proofs'][qi]
            cap_price = sum(max(F(0), a-b)*c for a, b, c in zip(point['caps'], oldpoint['caps'], U))
            budget_price = sum(max(F(0), a-b)*max(U[i] for i in group)
                               for a, b, group in zip(point['budgets'], oldpoint['budgets'], cost.GROUPS))
            require(proof['finite_LP_increment'] == cap_price+budget_price+trivial
                    and proof['group_budget_increment'] == budget_price,
                    'Replace exactly170 cap-only coefficient term, once')
            old_increment = proof['finite_LP_increment']
            proof.update(previous_finite_LP_increment=old_increment,
                         finite_LP_increment=cap_price+budget_price+grouped,
                         old_cap_only_coefficient_price=trivial,
                         old_grouped_coefficient_price=grouped,
                         coefficient_increase_bounds=tuple(D),
                         old_coefficient_group_supports=group_rows,
                         coefficient_budget_saving=saving)
            proof['seven_coordinate_increments'] = tuple(x-saving for x in proof['seven_coordinate_increments'])
            vertex['head_maxima'] = tuple(x-saving for x in vertex['head_maxima'])
            for layout in uniform.PROBES:
                for root, slot, extra in newup.positive7:
                    change = finite_value(newup, newface, layout, extra)-finite_value(oldup, oldface, layout, extra)
                    require(change <= proof['finite_LP_increment']+proof['selected_increment'],
                            'Independent full finite branch satisfies the stronger coefficient support')
                    probes += 1
        candidates = [study.quadratic.constant_support(uniform, record, par,
                      uniform.fixed_tail(affine, record, par, c), row['transported_vertices'],
                      row['factorial_tail_coefficient']*previous['complete_pair_upper']) for c in cuts]
        row['selected_support'] = min(candidates, key=lambda s: s['upper'])
    require(len(jobs) == 26 and supports == 234 and probes == 3120 and strict > 0,
            'All26 objectives,234 exact group supports and3120 stronger finite checks')
    previous.update(denominator_shared=portfolio.shared_maximum(previous['denominator_costs']),
                    mean_shared=portfolio.shared_maximum(previous['mean_costs']),
                    quadratic_shared=portfolio.shared_maximum(previous['quadratic_costs']),
                    old_group_coefficient_supports=supports, strict_coefficient_improvements=strict,
                    refined_finite_branch_checks=probes)
    return previous


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('full_slot_transport_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/full_slot_radius_source_comparison.json'))
    scanned = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/full_slot_radius_source_heads.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent prior proof closure '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    study = module('full_slot_transport_study', base/'frontier/endpoint-bounds/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(p) == h for p, h in study.pins.items())
            and all(pins.get(p) == h for p, h in scanned['source_sha256'].items()),
            'Complete original and169 fresh-head source closures')
    oldpar = {k: tuple(map(F, v)) if isinstance(v, list) else F(v) for k, v in prior['parameters'].items()}
    require(oldpar['delta'] == F(1, 27) and oldpar['rho'] == F(1, 1000) and oldpar['rbar'] == F(1, 200)
            and scanned['parameters'] == study.uniform.encode(oldpar)
            and scanned['original_head_evaluations'] == 9750000
            and scanned['independent_rational_comparisons'] == 312,
            'The exact169 full-slot original scan is the only head baseline')
    par, guard = parameters_and_guards(study)
    pairs, prices = study.get('seven_pair_source_prices'), study.get('exposed_concentration_prices')
    pair = pairs.bounds(prices, pairs.raw_coefficients(study.factorial), DELTA)
    par['positive7'] = pair['Z_upper']
    residual, complete = study.get('residual_shell_k_comparison'), study.get('expanded_source_complete_comparison')
    H1 = residual.shallow_H1(study, par)
    square = study.square.uniform_square(par, SimpleNamespace(uniform_H1=lambda p: H1), study.factorial, study.tails)
    five = complete.expanded_joint_five(study, par, study.get('pure_five_complete_face_comparison'), guard)
    old_pure = (next(r['weighted_upper'] for r in square['bounded_cylinders'] if r['modulus'] == 5)
                +next(r['upper'] for r in square['complete_weighted_tails'] if r['family'] == 'pure5'))
    saving = max(F(0), old_pure-five['joint_upper'])
    square = {**square, 'previous_full_square_upper': square['full_square_upper'],
              'old_pure_five_block': old_pure, 'joint_pure_five_block': five['joint_upper'],
              'joint_square_saving': saving, 'full_square_upper': square['full_square_upper']-saving,
              'zero7_pair_upper': square['zero7_pair_upper']-saving}
    heads = refined_heads(study, oldpar, par, pair, scanned)
    require(heads['group_budget_increments'] == (F(83, 1263600), F(1, 25272), F(1, 7800)),
            'All three changing group budgets are paid in the transport')
    heavy = heavy_extension(study, guard)
    result = complete.complete_comparison(study, par, heavy, H1, square, heads)
    require(result['comparison_upper'] < TARGET and heads['new_original_head_evaluations'] == 0,
            'Larger full-slot residual domain stays below509.289 with no additional original scan')
    return study.uniform.encode({'schema': 'erdos7-budgeted-coefficient-source-transport-v1', 'source_sha256': pins,
        'parameters': par, 'guards': guard, 'heavy_extension': heavy, 'complete_H1': H1,
        'complete_square': square, 'joint_pure_five_transport': five,
        'complete_heads': heads, 'comparison': result, 'application_target': TARGET,
        'application_target_margin': TARGET-result['comparison_upper'],
        'scope': 'Ordinary complete actual-source bound for both K orientations, sigma<=1/26 and rho<=1/940, with only the actual r<=5rho. Reuses169 fresh original heads through170 general cap/budget/coefficient transport strengthened by the exact old-group support of coefficient increases, independently proves the larger-domain first-label/gap/heavy guards, and reconstructs all52 independent costs, five denominator objectives and every infinite tail. No new global K bound, Lean verification, unrestricted Erdos7 result, fresh head scan or actual attainment of the relaxed maxima is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('full_slot_transport_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact larger full-slot source certificate')
    print('PASS: sigma1/26, rho1/940, no independent r cutoff; K='+result['comparison']['comparison_upper'])


if __name__ == '__main__':
    main()
