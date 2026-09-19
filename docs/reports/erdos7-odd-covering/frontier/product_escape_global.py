#!/usr/bin/env python3
"""Joint product escape and source mass lower the complete global K bound.

The public weighted-marker theorem is evaluated at fixed rational guards.
The source/carrier product controls both escape and the denominator. All
old infinite cost tails, independent labels and fallback branches remain.
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
CERTIFICATE = 'certificates/source_norms/product_escape_global.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/weighted_marker_global.py': 'f4b7e272c9f98ee9445dccaefdbe8d4b088d78d6aaf4b85385260cf4d349db9e',
    'certificates/source_norms/weighted_marker_global.json': '8ca7b3bb7036a563019ca310019a2ea8f7dee57e479ba1af6318b61d2c0372d8',
    'frontier/k_next_escape_layers.py': 'f17140e366688960a1dcd04e3c72287c9acbeace1c865f0d1905a0d8d051a5b1',
    'certificates/source_norms/k_next_escape_layers.json': '68e181fcd4bb06953a03688260c8d426ee34c607bc73a5b5b8e49ee94fab00a8',
}


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
    io = module('product_escape_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    marker = read('certificates/source_norms/weighted_marker_global.json')
    escape = read('certificates/source_norms/k_next_escape_layers.json')
    for predecessor in (marker, escape):
        for path, pin in predecessor['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited input')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    old = read('certificates/source_norms/global_k_face_gain.json')
    gamma1 = F(escape['first_positive_gap'])
    gamma2 = F(escape['gap_outside_JK_union'])
    require(0 < gamma1 < gamma2 and gamma1 == F(old['gamma_K']), 'Same original signed comparison')
    # These constants are fixed independently of the actual source and tests.
    delta, rcut, decrease = F(2, 125), F(1, 1250), F(1, 30)
    w = 1-(1+delta)/5
    h1, eta_min, Delta = F(1, 3)-delta/6, F(1, 9)-delta/18, 3*delta/4
    guards = {'pure5': F(1, 10)-rcut, 'alpha': h1/5-rcut,
              'beta': eta_min/5-rcut, 'remaining': h1*(F(1, 10)-Delta)-2*rcut}
    gap = min(guards.values())
    require(0 < delta < F(1, 2) and Delta <= F(1, 18) and min(guards.values()) > 0
            and rcut < min(F(1, 10), h1/5, eta_min/5), 'All general packing and first-label guards')
    min_credit = min(w*gap, F(1, 50)-rcut/5)
    c = max(F(1), F(1, 9)/gap)
    require(gap == F(239, 11250), 'The exact common source gap')
    rows = []
    for index, row in enumerate(marker['cost_rows']):
        require(index == row['index'] and row['layout_cell_floor_checks'] == 500,
                'All old branches retain their proved marked floor')
        vmin, vmax, weight = F(row['vmin']), F(row['vmax']), F(row['weight'])
        require(0 <= vmin <= vmax and weight > 0, 'Positive comparison weights and convex increments')
        gain = vmin*min_credit-vmax*F(13, 6075)
        rows.append({'index': index, 'name': row['name'], 'tuple': row['tuple'], 'weight': weight,
                     'vmin': vmin, 'vmax': vmax, 'gain_before_residual': gain,
                     'residual_penalty': vmax*c, 'chosen': gain > 0})
    chosen = [r for r in rows if r['chosen']]
    require(len(rows) == 41 and len(chosen) == 28
            and marker['total_layout_cell_floor_checks'] == 20500, 'All41 complete costs and28 fixed positive gains')
    B = sum(r['weight']*r['gain_before_residual'] for r in chosen)
    penalty = sum(r['weight']*r['residual_penalty'] for r in chosen)
    A0, Acur = F(old['signed_mass_coefficient']), F(old['new_mass_coefficient'])
    require(A0 >= Acur > penalty > 0, 'One signed mass term absorbs all28 penalties together')
    E = lambda sigma: F(1, 4)+F(11, 36)*sigma
    Q = lambda sigma: gamma2*sigma-(gamma2-gamma1)*sigma*sigma
    require(Q(0) == 0 and Q(1) == gamma1 and E(0) == F(1, 4) and E(1) == F(5, 9),
            'Exact joint escape and denominator endpoints')
    # Q-hE is concave; its minimum on [delta,1] is at an endpoint.
    margins = {'concentrated_small_slot_loss': B-decrease*E(delta),
               'concentrated_large_slot_loss': Acur*rcut/5-decrease*E(delta),
               'outside_near_endpoint': Q(delta)-decrease*E(delta),
               'outside_far_endpoint': Q(1)-decrease*E(1)}
    require(min(margins.values()) > 0, 'Every actual source/carrier and slot-loss branch is strictly positive')
    K0, K90 = F(old['old_K']), F(marker['new_K'])
    target = K0-decrease
    require(403 < target < K90 < K0 and A0-F(23, 42)*decrease > 0,
            'Improvement starts once from K0 and retains the signed mass orientation')
    fallbacks, cores = [], []
    for row in old['fallbacks']:
        bound = F(row['bound'])
        require(target > bound, 'Every complete old fallback remains below the target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'new_gap': target-bound})
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(target+error > 403, 'Full terminal comparison remains open')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2 and F(old['positive_survival_lower']) > 0,
            'Complete old split and positive actual denominator')
    return {'schema': 'erdos7-product-escape-global-v1', 'source_sha256': used,
            'concentration_delta': delta, 'slot_loss_cutoff': rcut, 'source_loss_coefficient': w,
            'source_guards': guards, 'slot_gap_lower': gap, 'minimum_source_credit': min_credit,
            'common_residual_coefficient': c, 'cost_rows': rows,
            'chosen_cost_indices': [r['index'] for r in chosen], 'chosen_cost_count': len(chosen),
            'weighted_gain_before_residual': B, 'combined_residual_penalty': penalty,
            'conservative_mass_coefficient': Acur, 'positive_remaining_mass_coefficient': Acur-penalty,
            'escape_linear_coefficient': gamma2, 'escape_negative_quadratic_coefficient': gamma2-gamma1,
            'denominator_constant': F(1, 4), 'denominator_escape_coefficient': F(11, 36),
            'concentrated_denominator_upper': E(delta), 'outside_interval': [delta, F(1)],
            'signed_branch_margins': margins, 'new_signed_margin_lower': min(margins.values()),
            'old_K0': K0, 'previous_K90': K90, 'decrease_from_K0': decrease,
            'new_K': target, 'improvement_over90': K90-target,
            'new_mass_coefficient': A0-F(23, 42)*decrease,
            'positive_denominator_lower_factor': F(old['positive_survival_lower']),
            'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary global comparison using the same product weights for K/J exclusion, source mass and all28 retained linear marked gains. Complete independent original tests, infinite tails, eight fallbacks and two terminal errors remain. No prior target gain is added again; no new quadratic or deep-event gain is assumed. No Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('product_escape_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact product-escape global certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: joint product escape, denominator,28 weighted gains and all complete branches.')
    with localcontext() as context:
        context.prec = 32
        value = F(result['new_K'])
        print('Global K <= '+str(Decimal(value.numerator)/Decimal(value.denominator)))


if __name__ == '__main__':
    main()
