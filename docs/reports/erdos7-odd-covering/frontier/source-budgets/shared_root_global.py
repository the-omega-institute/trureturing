#!/usr/bin/env python3
"""Cost-scaled deep defects and shared root imbalance strengthen global K.

All alternatives concern the same original cost. One alternative per cost prevents
duplicate gain; complete tails and inherited comparison branches remain.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/shared_root_global.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/moments-survival/quadratic_marked_global.py': '1a08b16f36862c66c4e2b568a8a09ee2d296e3ddeb9e9eaad2a80ff4c8073626',
    'certificates/source_norms/moments-survival/quadratic_marked_global.json': 'f2dfcc7e37c71bb4e419273f99597db926e89da0e09b65f93800f87c8f364c4b',
    'frontier/source-budgets/shared_root_imbalance_payment.py': 'a7edda92e493cacfbd1b4665e03ef6fc0db7c8b1ef2febd17af4a1a609a4997a',
    'certificates/source_norms/source-budgets/shared_root_imbalance_payment.json': 'e00636fcfca0f68e632b19333e8d534c99006a2e5942ecac59f93f67f7138a5e',
    'frontier/source-budgets/fractional_deep_global.py': 'a3fcf9559712e1643138660217ca6c0a6c06d774ee523858a50661781ef2068f',
    'certificates/source_norms/source-budgets/fractional_deep_global.json': 'f44573cffb249ceb7ca492c533ea135e0bb5d301166540fa1d0b35fbc5a8659d',
}
OLD = (3, 4, 5, 6, 9, 11, 13, 14, 15, 19, 20, 21, 22, 25, 27,
       29, 30, 31, 34, 35, 37, 38, 39, 40, 42, 43, 45)
DEEP = tuple(i for i in range(46) if i not in OLD)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(PINS and 'certificate_io.py' in PINS, 'Completed source pins are required')
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('shared_root_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name)))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    old_marked = read('quadratic_marked_global.json')
    generic = read('shared_root_imbalance_payment.json')
    previous_global = read('fractional_deep_global.json')
    for prior in (old_marked, generic, previous_global):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited input')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    old = read('global_k_face_gain.json')
    escape = read('k_next_escape_layers.json')
    delta, rcut, decrease = F(1, 27), F(1, 520), F(39, 500)
    h1, eta_min, Delta = F(1, 3)-delta/6, F(1, 9)-delta/18, 3*delta/4
    guards = {'pure5': F(1, 10)-rcut, 'alpha': h1/5-rcut,
              'beta': eta_min/5-rcut, 'remaining': h1*(F(1, 10)-Delta)-2*rcut}
    gap, best_credit, qstar, wdeep = min(guards.values()), F(1, 50)-rcut/5, (1+delta)/5, (1-delta)/5
    require(0 < delta < F(1, 2) and Delta < F(1, 18)
            and 0 < rcut < min(F(1, 10), h1/5, eta_min/5)
            and gap == F(7499, 379080) and min(guards.values()) > 0,
            'Complete general source packing and distinct first-label guards')
    require(len(old_marked['cost_rows']) == len(generic['cost_rows']) == 46
            and old_marked['total_layout_cell_floor_checks'] == 23000,
            'All46 independently labelled complete costs and their original floors')
    generic_module = module('shared_root_generic', base/'frontier/source-budgets/shared_root_imbalance_payment.py')
    generic_fixed = generic_module.uniform_coefficients(generic['cost_rows'], delta, rcut)
    require(generic_fixed['G_lower'] == gap, 'The generic theorem uses identical source guards')
    rows = []
    for index, (previous, deep) in enumerate(zip(old_marked['cost_rows'], generic['cost_rows'])):
        require(previous['index'] == deep['index'] == index, 'Same cost order')
        C, weight, vmin, vmax = (F(previous[k]) for k in ('barrier', 'weight', 'vmin', 'vmax'))
        require(all(F(deep[k]) == F(previous[k]) for k in ('barrier', 'weight', 'vmin', 'vmax')),
                'Generic bridge applies to precisely the same barriers, weights and increments')
        quadratic = previous['quadratic']
        alpha, sigma = (F(6, 5), F(40, 3645)) if quadratic else (F(1), F(13, 1215))
        require(F(previous['alpha']) == alpha and F(deep['selected_deep_coefficient']) == sigma
                and sigma/5 == F(previous['deep_shift_coefficient']), 'Same full selected-deep family')
        old_credit = vmin*min((alpha-qstar)*gap, best_credit)-vmax*sigma/5
        old_penalty = max(vmax, vmin/(9*gap))
        new_credit = vmin*min(wdeep*gap, best_credit)
        new_penalty, imbalance = max(vmax, F(36, 25)*(vmax-vmin), vmin/(9*gap)), sigma*C/4
        fixed_row = generic_fixed['cost_rows'][index]
        require((new_credit, new_penalty, imbalance)
                == (fixed_row['g'], fixed_row['P'], fixed_row['escape_charge_coefficient']),
                'Independent reconstruction matches the general retained-deep interface')
        t_old = F(int(index in OLD))
        t_deep = F(int(index in DEEP))
        require((index in DEEP) == (new_credit > old_credit), 'Fixed selections choose one stronger zero-error credit')
        t_zero = 1-t_old-t_deep
        require(min(t_old, t_deep, t_zero) >= 0 and t_old+t_deep+t_zero == 1,
                'Fixed convex choices over old, retained-deep and zero for this cost')
        require(t_old == 0 or old_credit > 0, 'Every selected old gain is positive')
        require(new_credit > 0 and min(old_penalty, new_penalty) > 0,
                'Generic retained-deep gains and both residual penalties are positive')
        rows.append({'index': index, 'name': previous['name'], 'tuple': previous['tuple'],
                     'quadratic': quadratic, 'weight': weight, 'barrier': C, 'vmin': vmin, 'vmax': vmax,
                     'old_credit': old_credit, 'old_penalty': old_penalty,
                     'deep_credit': new_credit, 'deep_penalty': new_penalty,
                     'escape_penalty': imbalance,
                     'old_fraction': t_old, 'deep_fraction': t_deep, 'zero_fraction': t_zero,
                     'weighted_credit': weight*(t_old*old_credit+t_deep*new_credit),
                     'weighted_residual_penalty': weight*(t_old*old_penalty+t_deep*new_penalty),
                     'weighted_escape_penalty': weight*t_deep*imbalance})
    B = sum(row['weighted_credit'] for row in rows)
    P = sum(row['weighted_residual_penalty'] for row in rows)
    Q = sum(row['weighted_escape_penalty'] for row in rows)
    A0, Acur = F(old['signed_mass_coefficient']), F(old['new_mass_coefficient'])
    require(A0 >= Acur > P > 0 and B == F(292250583636758860113407141069, 14862421933958678536792310976000),
            'One actual residual pays every fraction once, with positive unused budget')
    gamma1, gamma2 = F(escape['first_positive_gap']), F(escape['gap_outside_JK_union'])
    concavity = gamma2-gamma1-F(11, 36)*decrease
    require(0 < gamma1 < gamma2 and concavity > 0, 'The joint escape polynomial remains concave')
    R = lambda s: -decrease/4+(gamma2-F(11, 36)*decrease)*s-concavity*s*s
    e_delta = F(1, 4)+F(11, 36)*delta
    margins = {'concentrated_small_r_zero_escape': B+R(0),
               'concentrated_small_r_at_delta': B-Q*delta+R(delta),
               'concentrated_large_r': Acur*rcut/5-decrease*e_delta,
               'outside_at_delta': R(delta), 'outside_at_one': R(1)}
    require(min(margins.values()) > 0, 'All five signed branch endpoint margins are strictly positive')
    K0 = F(old['old_K'])
    target = K0-decrease
    previous_target = F(previous_global['new_K'])
    require(previous_target-target == F(13, 1000) and target > 403,
            'New decrease counted once from the original K0')
    require(decrease > F(old_marked['scalar_template_decrement_upper']),
            'The retained-deep alternative leaves the old scalar template capacity')
    fallbacks, cores = [], []
    for row in old['fallbacks']:
        bound = F(row['bound'])
        require(bound < target, 'Every complete inherited fallback lies below the target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'target_gap': target-bound})
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(target+error > 403, 'The full terminal problem remains open')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2 and F(old['positive_survival_lower']) > 0
            and A0-F(23, 42)*decrease > 0, 'Complete branches, denominator and target sign')
    return {'schema': 'erdos7-shared-root-global-v1', 'source_sha256': used,
            'concentration_delta': delta, 'slot_loss_cutoff': rcut,
            'source_guards': guards, 'slot_gap_lower': gap, 'best_slot_credit_lower': best_credit,
            'shallow_density_upper': qstar, 'retained_source_coefficient': wdeep,
            'cost_rows': rows, 'fixed_old_indices': OLD, 'fixed_deep_indices': DEEP,
            'selected_cost_count': len(OLD)+len(DEEP),
            'weighted_credit': B, 'combined_residual_penalty': P, 'combined_escape_penalty': Q,
            'old_mass_coefficient': A0, 'conservative_mass_coefficient': Acur,
            'unused_residual_budget': Acur-P,
            'first_escape_gap': gamma1, 'next_escape_gap': gamma2,
            'escape_polynomial_negative_quadratic': concavity,
            'concentrated_denominator_upper': e_delta, 'signed_branch_margins': margins,
            'strict_margin_lower': min(margins.values()),
            'old_K0': K0, 'previous_K100': previous_target, 'decrease_from_K0': decrease,
            'new_K': target, 'improvement_over100': previous_target-target,
            'old_scalar_template_capacity': F(old_marked['scalar_template_decrement_upper']),
            'new_mass_coefficient': A0-F(23, 42)*decrease,
            'positive_denominator_lower_factor': F(old['positive_survival_lower']),
            'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary global comparison with one fixed alternative for each of46 costs, with the shared root-imbalance bound paying both root0 classes once. One residual and one source-escape coordinate pay all losses; no gains from the same cost are added. Independent original test residues, all infinite cofactor tails, original quadratic curvature, eight fallbacks and two full errors remain. No Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('shared_root_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact shared-root global certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: all46 fixed cost choices, cost-scaled deep defects, one root-imbalance charge, five signed margins and complete branches.')
    with localcontext() as context:
        context.prec = 34
        v = F(result['new_K'])
        print('Global K <= '+str(Decimal(v.numerator)/Decimal(v.denominator)))


if __name__ == '__main__':
    main()
