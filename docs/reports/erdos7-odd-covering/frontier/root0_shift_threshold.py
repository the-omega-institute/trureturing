#!/usr/bin/env python3
"""Root0 derivative order gives a strict shift threshold and zero imbalance remainder.

The exact peak of a valid piecewise upper envelope pays every root0
label with its own actual capacity defect, including bounded-chi use.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/root0_shift_threshold.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/shared_root_imbalance_payment.py': '9dab691f5ca6a1f64d58b096f96fe03c44b04c4513fbf8081221ee73b9cbc57e',
    'certificates/source_norms/shared_root_imbalance_payment.json': '2e1e8e0398737ffbf1f87d8a59ec86b82931f2dce75667e2d3c7bdc517f37c59',
}
ROOT = (0, 0, 1, 1, 1)
THRESHOLD_FACTOR = F(89, 180)


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


def root0_case(low, high, high_barrier, chi_upper=None):
    """Exact peak of min((high-low)/5,[k*chi-tau]+) / chi."""
    low, high, kh = F(low), F(high), F(high_barrier)
    require(0 < low <= high and kh > 0, 'Positive convex increments and high-cell barrier')
    tau, gap = THRESHOLD_FACTOR*low, (high-low)/5
    onset, peak_at = tau/kh, (tau+gap)/kh
    global_peak = kh*gap/(tau+gap)
    require(global_peak == kh*(high-low)/(high+F(53, 36)*low), 'Closed-form peak coefficient')
    if chi_upper is None:
        peak = global_peak
    else:
        chi_upper = F(chi_upper)
        require(chi_upper >= 0, 'Nonnegative actual imbalance bound')
        peak = F(0) if chi_upper == 0 else (
            max(F(0), kh-tau/chi_upper) if chi_upper <= peak_at else global_peak)
    require(0 <= peak <= global_peak <= kh, 'Bounded envelope never exceeds its unbounded peak')
    require(kh*onset == tau and kh*peak_at-tau == gap and global_peak*peak_at == gap,
            'Exact onset and intersection of the two positive envelope branches')
    return {'low_increment': low, 'high_increment': high, 'high_cell_barrier': kh,
            'threshold_offset': tau, 'shift_gap_cap': gap,
            'onset_imbalance': onset, 'ratio_peak_imbalance': peak_at,
            'unbounded_capacity_coefficient': global_peak,
            'chi_upper': chi_upper, 'capacity_coefficient': peak}


def cost_penalties(row, chi_upper=None):
    C, vmin, vmax = map(F, (row['barrier'], row['vmin'], row['vmax']))
    values, increments = tuple(map(F, row['low_values'])), tuple(map(F, row['increments']))
    require(len(values) == 4 and len(increments) == 3 and increments[0] == vmin
            and increments[2] == vmax and C >= values[2]+3*vmax, 'Same original low cost and barrier')
    cases = [root0_case(increments[m-1], increments[m], C-values[m], chi_upper) for m in (1, 2)]
    missing, root1 = F(36, 125)*vmax, F(36, 25)*(vmax-vmin)
    root0 = max(case['capacity_coefficient'] for case in cases)
    kappa = max(missing, root1, root0)
    require(kappa <= C and max(vmax, kappa) == max(vmax, root1, root0),
            'Zero-remainder capacity coefficient and the unchanged union coefficient')
    return {'root0_cases': cases, 'root0_capacity_penalty': root0,
            'missing_mass_penalty': missing, 'root1_penalty': root1,
            'deep_capacity_penalty': kappa, 'marked_base_penalty': max(vmax, kappa)}


def uniform_coefficients(cost_rows, delta, rcut, use_concentration_bound=True):
    """Inclusive r cutoff; use chi<=delta/4 by default, or the unbounded peak."""
    delta, rcut = F(delta), F(rcut)
    require(0 <= delta <= F(2, 27) and rcut >= 0, 'Concentrated broad-slab source region')
    h1, eta_min = F(1, 3)-delta/6, F(1, 9)-delta/18
    guards = (F(1, 10)-rcut, h1/5-rcut, eta_min/5-rcut,
              h1*(F(1, 10)-3*delta/4)-2*rcut)
    G = min(guards)
    require(G > 0 and rcut < min(F(1, 10), h1/5, eta_min/5), 'All packing and original first-label guards')
    source_credit = min((1-delta)*G/5, F(1, 50)-rcut/5)
    require(source_credit > 0, 'Positive common retained source credit')
    chi_upper = delta/4 if use_concentration_bound else None
    rows = []
    for row in cost_rows:
        penalties = cost_penalties(row, chi_upper)
        vmin, vmax, C = map(F, (row['vmin'], row['vmax'], row['barrier']))
        P = max(penalties['marked_base_penalty'], vmin/(9*G))
        rows.append({'index': row['index'], 'name': row['name'], 'tuple': row['tuple'],
                     'weight': F(row['weight']), 'barrier': C, 'vmin': vmin, 'vmax': vmax,
                     **penalties, 'g': vmin*source_credit, 'P': P, 'Q': F(0),
                     'escape_charge_coefficient': F(0)})
    return {'delta': delta, 'r_upper_inclusive': rcut, 'chi_upper': chi_upper,
            'four_gap_guards': guards, 'G_lower': G, 'uniform_source_credit': source_credit,
            'cost_rows': rows,
            'weighted_g_sum': sum(row['weight']*row['g'] for row in rows),
            'weighted_P_sum': sum(row['weight']*row['P'] for row in rows),
            'weighted_Q_sum': F(0),
            'root0_zero_penalty_count': sum(row['root0_capacity_penalty'] == 0 for row in rows),
            'comparison': 'd_i>=m_i_old+[g_i-P_i*(rho-r/5)]_+; no separate chi or source-escape charge.'}


def layout_audit(bases):
    require(len(bases) == 10 and tuple(tuple(1+int(ROOT[l] == r)+int(l == j) for l in range(5))
            for r in range(2) for j in range(5)) == bases, 'All10 original nonnested root/cell baselines')
    rows = []
    for bi, b in enumerate(bases):
        for ci, c5 in enumerate(bases):
            require(abs(c5[0]-c5[1]) <= 1, 'Independent second-layout root0 entries differ by at most one')
            if b[0] == b[1]:
                require((b[0] == 2 and max(b[2:]) <= 2) or (b[0] == 1 and min(b[2:]) >= 2),
                        'Equal root0 derivatives have no positive shift excess')
                rows.append({'baseline': bi, 'second_layout': ci, 'shape': 'equal', 'root0_level': b[0]})
                continue
            low = min((0, 1), key=lambda l: b[l])
            high = 1-low
            require(b[high] == b[low]+1 and b[high] == max(b), 'High root0 derivative is globally maximal')
            cv, cd = 1-c5[low]+c5[high], c5[high]-1
            require(min(cv, cd) >= 0, 'v-((c_low-1)*v-(c_high-1)*w) is a nonnegative convex-increment combination')
            rows.append({'baseline': bi, 'second_layout': ci, 'shape': 'adjacent',
                         'low_cell': low, 'high_cell': high, 'low_level': b[low],
                         'correction_slack_coefficients': [cv, cd]})
    require(len(rows) == 100, 'All independent original layout pairs')
    return rows


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('root0_threshold_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/shared_root_imbalance_payment.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
        used[path] = pin
    shared = module('root0_threshold_previous', base/'frontier/shared_root_imbalance_payment.py')
    require(encode(shared.calculate(base)) == previous, 'Prior tied-root source, cost floors and complete tails revalidated')
    source = module('root0_threshold_source', base/'verify_joint_frontier.py')
    layouts = layout_audit(source.BASES)
    require(F(25, 36)-F(1, 5) == THRESHOLD_FACTOR, 'Exact strict threshold from the original c5 root relation')
    adapted = []
    checks = 0
    for row in previous['cost_rows']:
        values, ds = tuple(map(F, row['low_values'])), tuple(map(F, row['increments']))
        for layout in layouts:
            if layout['shape'] == 'adjacent':
                m = layout['low_level']
                low, high = layout['low_cell'], layout['high_cell']
                c5 = source.BASES[layout['second_layout']]
                v, w = ds[m-1], ds[m]
                correction = (c5[low]-1)*v-(c5[high]-1)*w
                cv, cd = layout['correction_slack_coefficients']
                require(v-correction == cv*v+cd*(w-v) >= 0, 'All original cost/layout correction inequalities')
            checks += 1
        require(F(row['selected_deep_coefficient'])+F(row['complete_remaining_mass_tail']) == F(1, 90),
                'Every complete selected and unselected pure3 mass tail remains')
        adapted.append({**row, 'zero_remainder_penalties': cost_penalties(row)})
    require(len(adapted) == 46 and checks == 4600, 'Complete original cost and independent-layout inventory')
    bounded = uniform_coefficients(adapted, F(1, 27), F(1, 520))
    unbounded = uniform_coefficients(adapted, F(1, 27), F(1, 520), False)
    old_fixed = shared.uniform_coefficients(previous['cost_rows'], F(1, 27), F(1, 520))
    for b, u, old in zip(bounded['cost_rows'], unbounded['cost_rows'], old_fixed['cost_rows']):
        require(b['g'] == u['g'] == old['g'] and b['P'] <= u['P'] and b['Q'] == u['Q'] == 0,
                'Same source credit, smaller bounded-range penalty, zero separate imbalance')
    return {'schema': 'erdos7-root0-shift-threshold-v1', 'source_sha256': used,
            'layout_checks': layouts, 'total_original_layout_checks': checks,
            'source_checks_reused': previous['source_checks_reused'], 'cost_rows': adapted,
            'threshold_factor': THRESHOLD_FACTOR,
            'pointwise_envelope': 'For low/high root0 increments v,w: [s_shift-v/5]+ <= min((w-v)/5,[k_h*chi-(89/180)*v]+). Positive excess requires the low-derivative cell to be nonmaximal in availability.',
            'unbounded_root0_coefficient': 'k_h*(w-v)/(w+(53/36)*v)',
            'deep_bridge': 'Q_D-P_D>=-kappa_zero*E_D, with no chi remainder.',
            'shared_budget': 'E_D+(E5-r/5)+omega<=rho-r/5',
            'uniform_at103_bounded': bounded, 'uniform_at103_unbounded': unbounded,
            'scope': 'Ordinary source-slab theorem with exact upper-envelope peaks. These coefficients need not minimize actual costs and their aggregate residual charge need not fit a global consumer. Independent original labels, all infinite tails, source curvature and one actual residual retained. No new global K, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('root0_threshold_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact root0 threshold and envelope certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: all46 costs, all100 original layout pairs, strict root0 thresholds, exact envelope peaks and complete tails.')
    print('The actual deep bridge has zero separate imbalance remainder; no global improvement is inferred.')


if __name__ == '__main__':
    main()
