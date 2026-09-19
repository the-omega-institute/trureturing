#!/usr/bin/env python3
"""All46 marked costs replace their fixed deep charge by actual defects.

The generic tied-root comparison includes all ten root/cell baselines,
including nonnested labels. Uniform coefficient vectors retain the full
source payment, complete cofactor tails, curvature and one residual.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/tied_root_deep_payment.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/moments-survival/quadratic_marked_global.py': '71c7b94fa6ca7748481d9415363552402e21dcfdd755c78781dbeffe121d905f',
    'certificates/source_norms/moments-survival/quadratic_marked_global.json': 'ef92b42ce4cc28f7a8d3e9cca5628bb30dd7f3bb9cd3f49fa2bb7dd7cbebcd37',
}
ROOT = (0, 0, 1, 1, 1)
QMIN, D1MAX, ROOT_GAP = F(25, 36), F(5, 9), F(5, 36)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def digest(value):
    return sha256(json.dumps(encode(value), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def generic_cone_check(bases):
    """All allowed low cost data are a nonnegative combination of five rays."""
    labels = [(root, cell) for root in range(2) for cell in range(5)]
    require(tuple(tuple(1+int(ROOT[i] == root)+int(i == cell) for i in range(5))
                  for root, cell in labels) == bases, 'All ten original root/cell baselines, without nesting restriction')
    require(sum(ROOT[cell] != root for root, cell in labels) == 5, 'Five of the ten baselines are nonnested')
    rays = []
    for coordinate in range(5):
        x = [F(0)]*5
        x[coordinate] = F(1)
        f1, v1, step2, step3, slack = x
        f2, f3, f4 = f1+v1, f1+2*v1+step2, f1+3*v1+2*step2+step3
        values = (F(0), f1, f2, f3, f4)
        barrier = f3+3*(v1+step2+step3)+slack
        rays.append((values, barrier))
    rows = []
    for bi, b in enumerate(bases):
        root_low = min((0, 1), key=lambda i: (b[i], i))
        level = b[root_low]
        require(level in (1, 2) and abs(b[0]-b[1]) <= 1, 'The two root0 baselines are equal or adjacent')
        if level == 2:
            require(max(b[2:]) <= level, 'Root0-selected baselines include the nonnested root1-cell case')
        else:
            require(min(b[2:]) >= 2, 'Root1-selected baselines include the nonnested root0-cell case')
        for ci, c5 in enumerate(bases):
            require(min(c5) >= 1 and max(c5) <= 3, 'Only component bounds of the independent second layout are used')
            unsafe = [i for i in range(5) if b[i] > level]
            comparisons = []
            for cell in unsafe:
                coefficients = []
                for values, barrier in rays:
                    v = [values[b[i]+1]-values[b[i]] for i in range(5)]
                    low_shifted = QMIN*(barrier-values[level])-(c5[root_low]-1)*v[root_low]/5
                    high_d = QMIN if cell < 2 else D1MAX
                    high_shifted = high_d*(barrier-values[b[cell]])-(c5[cell]-1)*v[cell]/5
                    coefficients.append(low_shifted-high_shifted)
                require(min(coefficients) >= 0, 'Universal nonnegative cost-cone coefficients for every unsafe shifted candidate')
                comparisons.append({'cell': cell, 'coefficients': coefficients})
            rows.append({'baseline_index': bi, 'positive5_layout_index': ci, 'low_root_cell': root_low,
                         'minimum_root_baseline': level, 'unsafe_comparisons': comparisons})
    require(len(rows) == 100, 'Every pair of original layouts is included in the generic proof')
    return {'cone_coordinates': ['f1', 'v1', 'v2-v1', 'v3-v2', 'C-f3-3v3'],
            'original_labels': labels, 'nonnested_baseline_count': 5, 'layout_pair_count': len(rows),
            'unsafe_comparison_count': sum(len(row['unsafe_comparisons']) for row in rows),
            'coefficient_checks': 5*sum(len(row['unsafe_comparisons']) for row in rows),
            'coefficient_rows': rows,
            'statement': 'For tied d0=d1=q>=25/36 and root1 d<=5/9: max(z+v/5)-max(z)<=min(v0,v1)/5.'}


def uniform_coefficients(cost_rows, delta, rcut):
    """Valid fixed lower-credit and upper-penalty vectors, without a global claim."""
    delta, rcut = F(delta), F(rcut)
    require(0 <= delta <= F(2, 27) and 0 <= rcut, 'The concentrated region lies in the proved broad slab')
    h1, eta_min, Delta = F(1, 3)-delta/6, F(1, 9)-delta/18, 3*delta/4
    guards = (F(1, 10)-rcut, h1/5-rcut, eta_min/5-rcut,
              h1*(F(1, 10)-Delta)-2*rcut)
    gap = min(guards)
    require(gap > 0 and rcut < min(F(1, 10), h1/5, eta_min/5), 'General packing and all first-slot guards')
    wdeep, best_credit = (1-delta)/5, F(1, 50)-rcut/5
    credit = min(wdeep*gap, best_credit)
    require(credit > 0, 'Uniform positive marked-source credit')
    rows = []
    for row in cost_rows:
        vmin, vmax, barrier = map(F, (row['vmin'], row['vmax'], row['barrier']))
        count = row['selected_cofactor_count']
        sigma = sum(F(1, 3**a) for a in range(3, count+1))/5
        P, Q = max(barrier, vmin/(9*gap)), sigma*barrier
        require(barrier >= 3*vmax and P >= barrier >= vmax, 'One penalty pays deep capacity and union loss')
        rows.append({'index': row['index'], 'name': row['name'], 'tuple': row['tuple'],
                     'weight': F(row['weight']), 'barrier': barrier, 'vmin': vmin, 'vmax': vmax,
                     'selected_cofactor_count': count, 'source_multiplier': F(count, 5),
                     'selected_deep_coefficient': sigma, 'g': vmin*credit, 'P': P, 'Q': Q,
                     'escape_charge_coefficient': Q/4})
    return {'delta': delta, 'r_upper_inclusive': rcut, 'four_gap_guards': guards, 'G_lower': gap,
            'remaining_hole_coefficient': wdeep, 'best_slot_credit_lower': best_credit,
            'uniform_source_credit': credit, 'cost_rows': rows,
            'weighted_g_sum': sum(row['weight']*row['g'] for row in rows),
            'weighted_P_sum': sum(row['weight']*row['P'] for row in rows),
            'weighted_Q_sum': sum(row['weight']*row['Q'] for row in rows),
            'comparison': 'd_i>=m_i_old+[g_i-P_i*(rho-r/5)-Q_i*chi]_+; chi<=b<=sigma_escape/4, r is the actual best-slot loss.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('tied_deep_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/moments-survival/quadratic_marked_global.json')
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
        used[path] = pin
    prior_module = module('tied_deep_previous', base/'frontier/moments-survival/quadratic_marked_global.py')
    require(encode(prior_module.calculate(base)) == previous, 'All46 source payments, polynomial tails, original curvature and floor checks revalidated')
    source = module('tied_deep_source', base/'verify_joint_frontier.py')
    schedule = module('tied_deep_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('tied_deep_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    generic = generic_cone_check(source.BASES)
    geometry = {'root0_availability_lower': QMIN, 'root1_availability_upper': D1MAX,
                'root_availability_gap': ROOT_GAP,
                'missing_mass_payment_vmax_factor': F(36, 125),
                'root1_payment_vmax_factor': F(36, 25)}
    require(QMIN-D1MAX == ROOT_GAP and F(1, 5)/QMIN == F(36, 125)
            and F(1, 5)/ROOT_GAP == F(36, 25) < 3, 'The barrier coefficient dominates both parts of the actual-capacity defect')
    adapted = []
    for index, (spec, row) in enumerate(zip(specs, previous['cost_rows'])):
        require(index == row['index'] and spec['tuple'] == row['tuple'] and spec['name'] == row['name'],
                'The complete original46-cost inventory and order')
        values = tuple(source.zero5_cost(spec['tag'], v) for v in range(1, 5))
        increments = tuple(values[j+1]-values[j] for j in range(3))
        C = F(row['barrier'])
        cone = (values[0], increments[0], increments[1]-increments[0], increments[2]-increments[1],
                C-values[2]-3*increments[2])
        require(min(cone) >= 0 and increments[0] == F(row['vmin']) and increments[2] == F(row['vmax'])
                and C >= 3*increments[2] and increments[0] > 0, 'Every original cost belongs to the generic cone with positive first increment')
        tests = []
        for witness in generic['coefficient_rows']:
            bi, ci = witness['baseline_index'], witness['positive5_layout_index']
            b, c5 = source.BASES[bi], source.BASES[ci]
            v = tuple(increments[b[j]-1] for j in range(5))
            k = tuple(C-values[b[j]-1] for j in range(5))
            avail = (QMIN, QMIN, D1MAX, D1MAX, D1MAX)
            z = tuple(k[j]*avail[j]-c5[j]*v[j]/5 for j in range(5))
            shifted = tuple(z[j]+v[j]/5 for j in range(5))
            low = witness['low_root_cell']
            margins = []
            for comparison in witness['unsafe_comparisons']:
                cell = comparison['cell']
                expansion = sum(x*y for x, y in zip(cone, comparison['coefficients']))
                require(expansion == shifted[low]-shifted[cell] >= 0,
                        'Each original cost instantiates the generic nonnegative comparison exactly')
                margins.append(expansion)
            shift = max(shifted)-max(z)
            require(0 <= shift <= min(v[0], v[1])/5 and shift <= max(v)/5,
                    'Every original branch obeys the tied-root shift at the worst comparison geometry')
            tests.append({'baseline': bi, 'positive5_layout': ci, 'shift': shift,
                          'root_increment_cap': min(v[0], v[1])/5, 'unsafe_margins': margins})
        count = row['selected_cofactor_count']
        sigma = sum(F(1, 3**a) for a in range(3, count+1))/5
        tail = F(1, 5*3**(count+1))/(1-F(1, 3))
        require(count in (5, 6) and sigma+tail == F(1, 90)
                and F(count, 5)-F(2, 5)-F(count-2, 5) == 0,
                'Entire selected and unselected pure3 tails and the exact source/density cancellation')
        adapted.append({'index': index, 'name': row['name'], 'tuple': row['tuple'], 'barrier': C,
                        'weight': F(row['weight']), 'vmin': increments[0], 'vmax': increments[2],
                        'low_values': values, 'increments': increments, 'generic_cone_coordinates': cone,
                        'layout_pair_checks': len(tests), 'all_layout_checks_sha256': digest(tests),
                        'minimum_tied_shift_slack': min(r['root_increment_cap']-r['shift'] for r in tests),
                        'selected_cofactor_count': count, 'selected_deep_coefficient': sigma,
                        'complete_remaining_mass_tail': tail, 'curvature_record': row['curvature_record'],
                        'source_payment_multiplier': F(count, 5)})
    require(len(adapted) == 46 and sum(row['layout_pair_checks'] for row in adapted) == 4600,
            'All46 costs and all100 independently labelled layout pairs')
    default = uniform_coefficients(previous['cost_rows'], F(1, 44), F(1, 840))
    require(len(default['cost_rows']) == 46 and all(row['g'] > 0 for row in default['cost_rows']),
            'Positive uniform g for every original cost, without a fixed deep subtraction')
    return {'schema': 'erdos7-tied-root-deep-payment-v1', 'source_sha256': used,
            'generic_tied_root': generic, 'slab_geometry': geometry, 'cost_rows': adapted,
            'total_original_layout_pair_checks': 4600,
            'source_checks_reused': {'prefix_increment_checks': previous['total_prefix_increment_checks'],
                                     'layout_cell_floor_checks': previous['total_layout_cell_floor_checks']},
            'actual_deep_bridge': 'Q_D-P_deep>=-C*Edeep-sigma_deep*C*chi',
            'shared_budget': 'Edeep+(E5-r/5)+omega<=rho-r/5',
            'imbalance_bound': 'chi=abs(beta0-beta1)<=b<=sigma_escape/4',
            'general_gain': 'g_i=vmin_i*min(((1-delta)/5)*G,m/5)',
            'general_residual_coefficient': 'P_i=max(C_i,vmin_i*m/G)',
            'general_imbalance_coefficient': 'Q_i=sigma_deep_i*C_i',
            'uniform_default': default,
            'scope': 'Ordinary generic tied-root and full infinite-family actual-capacity proof, with all46 exact cost adaptations. Nonnested original test labels, old curvature and complete tails retained. Coefficient vectors are an interface with one shared actual residual and explicit root imbalance. They are not independent budgets, additive gains over prior marked estimates, or a new global K/Lean/unrestricted Erdos7 result.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('tied_deep_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact generic tied-root/deep-payment certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: generic nonnested tied-root cone, all46 costs and4600 layout pairs, full tail coefficients and one shared residual.')
    print('Uniform g is positive for all46 costs. No global K improvement is inferred.')


if __name__ == '__main__':
    main()
