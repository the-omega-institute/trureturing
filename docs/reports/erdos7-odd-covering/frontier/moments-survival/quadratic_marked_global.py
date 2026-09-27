#!/usr/bin/env python3
"""Complete quadratic/linear marked costs with one actual residual budget.

The ordinary theorem keeps alpha=6/5 source payment and the original
curvature for the quadratic costs. Exact arithmetic includes polynomial
tails, independent layouts, joint source mass, escape and all fallbacks.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/quadratic_marked_global.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/product_escape_global.py': 'c7364768dee0ce136044a88d22cc20781a17343c39ac90de4b76b12215627575',
    'certificates/source_norms/source-budgets/product_escape_global.json': '4ab42b8d780ea9859ac41bc3b448a47bba5360023a2e434a2949d60a93f03a90',
}
CHOSEN = (3, 4, 5, 6, 9, 11, 12, 13, 14, 15, 19, 20, 21, 22, 25, 27,
          28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45)


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
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('quadratic_marker_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/source-budgets/product_escape_global.json')
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
        used[path] = pin
    old = read('certificates/source_norms/source-budgets/global_k_face_gain.json')
    linear = read('certificates/source_norms/source-budgets/weighted_marker_global.json')
    quadratic = read('certificates/source_norms/retained-transport/retained_quadratic_tests.json')
    frontier = read('certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    controls = read('certificates/source_norms/source-budgets/global_control_faces.json')
    escape = read('certificates/source_norms/endpoint-bounds/k_next_escape_layers.json')
    source = module('quadratic_marker_source', base/'verify_joint_frontier.py')
    schedule = module('quadratic_marker_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('quadratic_marker_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    layout = module('quadratic_marker_layout', base/'frontier/cover-geometry/layout_gap.py')
    specs, groups, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    require(len(specs) == 46 and len(source.BASES) == 10 and source.AC == F(2371, 2880),
            'All41 linear and five quadratic original costs with the old complete quadratic coefficient')

    delta, rcut, decrease = F(1, 44), F(1, 840), F(1, 20)
    qstar = (1+delta)/5
    h1, eta_min, Delta = F(1, 3)-delta/6, F(1, 9)-delta/18, 3*delta/4
    guards = {'pure5': F(1, 10)-rcut, 'alpha': h1/5-rcut,
              'beta': eta_min/5-rcut, 'remaining': h1*(F(1, 10)-Delta)-2*rcut}
    gap, best_credit = min(guards.values()), F(1, 50)-rcut/5
    require(0 < delta < F(1, 2) and Delta < F(1, 18)
            and rcut < min(F(1, 10), h1/5, eta_min/5) and gap == F(8, 385),
            'General packing, distinct first labels and exact positive gap')
    require(sum(F(1, 3**a) for a in range(3, 7)) == F(40, 729)
            and F(40, 729)/25 == F(8, 3645) and F(40, 729)+F(1, 1458) == F(1, 18)
            and F(13, 243)/25 == F(13, 6075) and F(13, 243)+F(1, 486) == F(1, 18),
            'Complete selected deep shifts and unchanged infinite remainders')

    rows, total_floors, total_prefix = [], 0, 0
    for index, spec in enumerate(specs):
        is_quad = index >= 41
        alpha, deep = (F(6, 5), F(8, 3645)) if is_quad else (F(1), F(13, 6075))
        tag, zero = spec['tag'], spec['zero']
        f = lambda v: source.zero5_cost(tag, v)
        psi = lambda v: source.zero5_cost(zero, v)
        fm, pm = source.zero5_cost_metadata(tag), source.zero5_cost_metadata(zero)
        require(fm[0] == pm[0] == (2 if is_quad else 1) and pm[1] == alpha*fm[1]
                and spec['cofactor_count'] == (6 if is_quad else 5), 'Original degree, source payment and cofactor count')
        entrance = max(3, fm[3], pm[3])
        increments, source_increments = [], []
        for v in range(1, entrance+2):
            vf, vp = f(v+1)-f(v), psi(v+1)-psi(v)
            require(0 <= vf and alpha*vf <= vp, 'Every finite-prefix source increment pays alpha copies')
            if increments:
                require(increments[-1] <= vf, 'Convexity through the polynomial entrance')
            if v >= entrance:
                require(f(v) == fm[1]*v**fm[0]+fm[2] and psi(v) == pm[1]*v**pm[0]+pm[2]
                        and vp == alpha*vf, 'Complete polynomial tails retain the exact source multiplier')
            increments.append(vf)
            source_increments.append(vp)
            total_prefix += 1
        vmin, vmax = increments[0], increments[2]
        curve_record = None
        if is_quad:
            ci, norm = index-41, quadratic['norms'][index-41]
            require(spec['tuple'] == norm['tuple'], 'Same original quadratic tuple')
            C, weight = F(norm['C']), source.AC
            exact_zero, exact_psi, curve, _, curve_record = schedule.psi_record(source, layout, tuple(spec['tuple']))
            require(exact_zero == zero and all(exact_psi(v) == psi(v) for v in range(1, entrance+3)),
                    'Same selected source in the full curvature formula')
            old_curve = norm['curvature_record']
            require(curve == F(old_curve['curvature']) and curve_record['mean'] == F(old_curve['mean'])
                    and all(value == F(old_curve['low_product_atoms'][str(n)])
                            for n, value in curve_record['low_product_atoms'].items()), 'Original curvature and all low product atoms retained')
            require([psi(v+1)-psi(v)-alpha*(f(v+1)-f(v)) for v in range(1, 5)]
                    == list(map(F, norm['payment_increment_margins'])), 'Published quadratic source payment recovered')
        else:
            saved = linear['cost_rows'][index]
            C, weight = F(saved['barrier']), F(saved['weight'])
            require(spec['tuple'] == saved['tuple'] and spec['name'] == saved['name']
                    and vmin == F(saved['vmin']) and vmax == F(saved['vmax']), 'Same41 linear costs and complete old weights')
        require(vmax > 0 and 0 <= vmin <= vmax and weight > 0, 'Positive denominator for cost-specific residual coefficient')
        floors = 0
        for b, c5 in product(source.BASES, repeat=2):
            for cell in range(5):
                v = f(b[cell]+1)-f(b[cell])
                k, t = C-f(b[cell]), c5[cell]*v
                require(vmin <= v <= vmax and 0 <= t-v <= t <= k,
                        'Nonnegative old and marked floors for every independent layout and cell')
                require(k/4-t/5 >= k/20 >= 0 and 0 <= v/5 <= vmax/5,
                        'The deep cap and its marked translation remain nonnegative')
                floors += 1
        total_floors += floors
        credit = min((alpha-qstar)*gap, best_credit)
        gain, penalty = vmin*credit-vmax*deep, max(vmax, vmin/(9*gap))
        require(penalty >= vmax and penalty >= vmin/(9*gap)
                and penalty <= vmax*max(F(1), F(1, 9)/gap), 'One cost-specific charge dominates both actual errors')
        rows.append({'index': index, 'name': spec['name'], 'tuple': spec['tuple'], 'quadratic': is_quad,
                     'alpha': alpha, 'selected_cofactor_count': spec['cofactor_count'], 'barrier': C, 'weight': weight,
                     'vmin': vmin, 'vmax': vmax, 'minimum_source_credit': credit, 'deep_shift_coefficient': deep,
                     'gain_before_residual': gain, 'residual_penalty': penalty, 'chosen': gain > 0,
                     'curvature_record': curve_record, 'retained_curvature_factor': F(4, 25) if is_quad else None,
                     'finite_prefix_and_tail': {'entrance': entrance, 'cost_increments': increments,
                                                'source_increments': source_increments, 'cost_metadata': fm,
                                                'source_metadata': pm}, 'layout_cell_floor_checks': floors})
    chosen = [r for r in rows if r['chosen']]
    require(tuple(r['index'] for r in chosen) == CHOSEN and total_floors == 23000,
            'Fixed28 linear and four quadratic gains with all23000 layout-cell checks')
    for block in frontier['frontier']['row_blocks']:
        for oldrow in block:
            require(len(oldrow['linear_directions']) == 41 and len(oldrow['quadratic_directions']) == 5,
                    'Complete old conditional direction inventory')
            for row, direction in zip(rows, oldrow['linear_directions']+oldrow['quadratic_directions']):
                require(F(direction['constant']) == row['barrier'] and direction['tuple'] == row['tuple'],
                        'Every new marked inequality retains the same old conditional barrier')
                if not row['quadratic']:
                    require(F(direction['weight']) == row['weight'], 'The complete linear coefficient is unchanged')

    vertices = list(source.vertices())
    raw_masses = [source.data(v)[3] for v in vertices]
    require(len(vertices) == 1296 and min(raw_masses) == F(1, 4) and max(raw_masses) == F(5, 9),
            'The complete raw source mass interval')
    union = []
    for kind, count in (('K', 6), ('J', 18)):
        zero_controls = controls['targets'][kind]['zero_controls']
        require(len(zero_controls) == count, 'Complete zero-control set: '+kind)
        for control in zero_controls:
            require(raw_masses[control['index']] == F(control['raw_mass']) == F(1, 4),
                    'Both K and J controls have the same small source mass')
            union.append({'kind': kind, 'index': control['index'], 'carrier': control['carrier'], 'raw_mass': F(1, 4)})
    gamma1, gamma2 = F(escape['first_positive_gap']), F(escape['gap_outside_JK_union'])
    residual_escape = gamma2-gamma1-F(11, 36)*decrease
    require(0 < gamma1 < gamma2 and residual_escape > 0, 'Joint J/K mass keeps the outside polynomial concave')
    E = lambda sigma: F(1, 4)+F(11, 36)*sigma
    R = lambda sigma: -decrease/4+(gamma2-F(11, 36)*decrease)*sigma-residual_escape*sigma*sigma
    require(R(0) == -decrease/4 and R(1) == gamma1-decrease/4,
            'Same joint mass and escape polynomial at both endpoints')
    B = sum(r['weight']*r['gain_before_residual'] for r in chosen)
    penalty = sum(r['weight']*r['residual_penalty'] for r in chosen)
    # Capacity of this scalar sufficient criterion only: dropping every
    # other guard enlarges its possible decrement, not the actual K range.
    ideal_rows = [{'index': r['index'], 'weighted_positive_gain': r['weight']*max(F(0),
                   r['vmin']*(F(1, 50) if r['quadratic'] else F(4, 225))
                   -r['vmax']*r['deep_shift_coefficient'])} for r in rows]
    ideal_gain = sum(r['weighted_positive_gain'] for r in ideal_rows)
    require(ideal_gain == F(10115878772922446403539237, 705718040548845134700489600)
            and decrease < 4*ideal_gain < F(3, 50), 'Exact ideal capacity of the scalar marked template')
    A0, Acur = F(old['signed_mass_coefficient']), F(old['new_mass_coefficient'])
    require(A0 >= Acur > penalty > 0, 'All32 marked inequalities charge the same actual residual once')
    margins = {'concentrated_small_slot_loss': B-decrease*E(delta),
               'concentrated_large_slot_loss': Acur*rcut/5-decrease*E(delta),
               'outside_near_endpoint': R(delta), 'outside_far_endpoint': R(1)}
    require(min(margins.values()) > 0, 'All actual source/carrier branches have strictly positive margin')
    K0, K93 = F(old['old_K']), F(previous['new_K'])
    target = K0-decrease
    require(403 < target < K93 < K0 and target > source.WHOLE_CONST
            and A0-F(23, 42)*decrease > 0, 'Target decreases once from K0 with the same positive sign branch')
    fallbacks, cores = [], []
    for row in old['fallbacks']:
        bound = F(row['bound'])
        require(target > bound, 'Every complete fallback remains below the new target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'new_gap': target-bound})
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(target+error > 403, 'Both full terminal comparisons remain open')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2 and F(old['positive_survival_lower']) > 0,
            'Complete branch split and positive actual comparison denominator')
    return {'schema': 'erdos7-quadratic-marked-global-v1', 'source_sha256': used,
            'concentration_delta': delta, 'slot_loss_cutoff': rcut, 'carrier_density_upper': qstar,
            'source_guards': guards, 'slot_gap_lower': gap, 'best_slot_credit_lower': best_credit,
            'cost_rows': rows, 'chosen_cost_indices': CHOSEN, 'chosen_cost_count': len(chosen),
            'chosen_linear_count': sum(not r['quadratic'] for r in chosen),
            'chosen_quadratic_count': sum(r['quadratic'] for r in chosen),
            'total_layout_cell_floor_checks': total_floors, 'total_prefix_increment_checks': total_prefix,
            'weighted_gain_before_residual': B, 'combined_residual_penalty': penalty,
            'conservative_mass_coefficient': Acur, 'positive_remaining_mass_coefficient': Acur-penalty,
            'JK_union_raw_mass_controls': union, 'all_source_vertex_count': len(vertices),
            'joint_denominator_constant': F(1, 4), 'joint_denominator_outside_union_coefficient': F(11, 36),
            'joint_denominator_statement': 'E <= 1/4+(11/36)*(1-qK-qJ)',
            'outside_linear_coefficient': gamma2-F(11, 36)*decrease,
            'outside_negative_quadratic_coefficient': residual_escape,
            'concentrated_denominator_upper': E(delta), 'signed_branch_margins': margins,
            'new_signed_margin_lower': min(margins.values()), 'old_K0': K0, 'previous_K93': K93,
            'decrease_from_K0': decrease, 'new_K': target, 'improvement_over93': K93-target,
            'new_mass_coefficient': A0-F(23, 42)*decrease,
            'scalar_template_ideal_cost_gains': ideal_rows,
            'scalar_template_ideal_gain': ideal_gain,
            'scalar_template_decrement_upper': 4*ideal_gain,
            'scalar_template_additional_decrement_upper': 4*ideal_gain-decrease,
            'scalar_template_scope': 'Upper capacity of this fixed vmin/vmax, scalar packing and positive-subset sufficient criterion only. Not a lower bound on actual K; vector and other changed comparisons are outside its scope.',
            'positive_denominator_lower_factor': F(old['positive_survival_lower']),
            'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary quadratic and linear marked-source theorem using all original event payments, unchanged quadratic curvature and complete exponent tails. A fixed28 linear/four quadratic set shares one actual residual budget and the same K/J product mass. All original test layouts remain independent. The target is recomputed once from K0; eight fallbacks and two full errors remain. No Lean verification, sharpness or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('quadratic_marker_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact quadratic marked-global certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: all46 marked costs,32 fixed gains, polynomial tails, joint mass and complete global branches.')
    with localcontext() as context:
        context.prec = 34
        value = F(result['new_K'])
        print('Global K <= '+str(Decimal(value.numerator)/Decimal(value.denominator)))


if __name__ == '__main__':
    main()
