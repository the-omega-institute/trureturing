#!/usr/bin/env python3
"""Fresh complete original heads on source radius2/27 and residual1/13000."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter
from types import SimpleNamespace

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/wide_source_bridge_comparison.json'
HEAD_CERTIFICATE = 'certificates/source_norms/source-budgets/wide_source_bridge_heads.json'
DELTA, RHO = F(2, 27), F(1, 13000)
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/expanded_source_complete_comparison.py': 'd5eaeb60aa63d06c8b0d515079d51f7dc76444d91182ef1ac9a286ffe184b50b',
    'frontier/source-budgets/wide_fresh_full_slot_source_comparison.py': 'f4cb79e71f5092d0eeca452aba9bbb31e9fc8ea929685cbdfa462ea269cd19d9',
    'frontier/source-budgets/fixed_support_source_slab.py': '90ed2e911d98d325688cb3b2891510c881fc90a7df686e8fd50548d651aa35a9',
    'certificates/source_norms/source-budgets/fixed_support_source_slab.json': '63b2b9e3959f43f95abedeb956e9e0dc03596670ded5c175f25d1e318677967d',
    'frontier/comparison-bounds/pure_five_complete_face_comparison.py': '45c1b016e68eb5397a78a6540c4f8ee5287c214b6bb35625d4d0232224dd2314',
    'certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json': 'e0d124f375efa0567777973a2ba468d368285807aed054ada2e57727b896d4f2',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original proof provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def parameters_and_guards(study):
    d, rho, r = DELTA, RHO, 5*RHO
    require(d == F(2, 27) and rho == F(1, 13000) and r == F(1, 2600),
            'The complete source rectangle stays in the original134 domain')
    loss = study.get('joint_concentration_loss_budget').total_loss_upper(d)
    Delta = loss/4
    availability = study.get('exposed_concentration_prices').norm_bounds(d)['availability_Linfinity']
    h1, eta, hbar = F(1, 3)-d/18, F(1, 9)-d/18, F(1, 2)+d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-availability)-2*r, (F(1, 6)-d/9)/5-r)
    gap = min(gaps)
    require(loss == F(2, 25) and Delta == F(1, 50) < F(1, 18)
            and availability == F(3, 154) <= Delta
            and F(3, 4)+d/4 == F(83, 108) < F(4, 5),
            'Every actual source lies in the original162 zero-slot-loss slab')
    require(gap == F(13277, 631800) > 0 and rho/gap == F(243, 66385) < F(1, 5)
            and F(1, 4)-3*d/4 == F(7, 36) > F(1, 20),
            'All five actual packing gaps, first-label forcing and one shared defect simplex')
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d}
    require(tuple(polynomials.values()) == (F(19, 27), F(1448, 729), F(30478, 729),
                                            F(319, 243), F(1076, 729))
            and min(polynomials.values()) > 0 and 6*d-23 < 0,
            'Every decreasing source and tail-domain polynomial is positive on[0,2/27]')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0,
            'The original marked fixed-support coefficients remain nonnegative')
    par = study.get('wide_k_signed_tail_comparison').parameters(study, d, rho)
    par.update(rbar=r, gap=gap, v0=min(F(1, 20), Delta+2*r),
               v1=min(F(1, 10), Delta+r/h1))
    require(par['v0'] == F(27, 1300) and par['v1'] == F(4403, 208000)
            and par['budget_increments'] == (F(83, 24300), F(1, 486), F(1, 150)),
            'The full new-source caps and all three joint-loss budgets are rebuilt')
    price = max(hbar/(5*gap), F(65, 9))
    require(hbar/(5*gap) == F(63700, 13277) and price == F(65, 9)
            and price >= max(F(1), hbar/(5*gap)) and price >= 5*F(13, 9),
            'One actual residual pays both original heavy marker and slot motion')
    return par, {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
        'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
        'availability_upper': availability, 'h1_lower': h1, 'first_beta_eta_lower': eta,
        'h_upper': hbar, 'five_actual_gap_lowers': gaps, 'minimum_actual_gap': gap,
        'common_wrong_slot_gap': gap, 'whole_interval_polynomial_lowers': polynomials,
        'heavy_residual_price_coefficient': price, 'heavy_slot_movement_coefficient': F(13, 9),
        'independent_r_cutoff': None}


def calculate(base, scan=False, write_heads=False):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('source_bridge_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    previous = read('certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json')
    pins = dict(PINS)
    for path, pin in previous['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent complete source closure '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    study = module('source_bridge_study', base/'frontier/endpoint-bounds/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'Complete original source providers')
    par, guard = parameters_and_guards(study)
    pairs, prices = study.get('seven_pair_source_prices'), study.get('exposed_concentration_prices')
    pair = pairs.bounds(prices, pairs.raw_coefficients(study.factorial), DELTA)
    par['positive7'] = pair['Z_upper']
    complete, residual = study.get('expanded_source_complete_comparison'), study.get('residual_shell_k_comparison')
    H1 = residual.shallow_H1(study, par)
    square = study.square.uniform_square(par, SimpleNamespace(uniform_H1=lambda p: H1), study.factorial, study.tails)
    five = complete.expanded_joint_five(study, par, study.get('pure_five_complete_face_comparison'), guard)
    old_pure = (next(row['weighted_upper'] for row in square['bounded_cylinders'] if row['modulus'] == 5)
                +next(row['upper'] for row in square['complete_weighted_tails'] if row['family'] == 'pure5'))
    saving = max(F(0), old_pure-five['joint_upper'])
    square = {**square, 'previous_full_square_upper': square['full_square_upper'],
              'old_pure_five_block': old_pure, 'joint_pure_five_block': five['joint_upper'],
              'joint_square_saving': saving, 'full_square_upper': square['full_square_upper']-saving,
              'zero7_pair_upper': square['zero7_pair_upper']-saving}
    if scan:
        started = perf_counter()
        scanned = complete.fresh_heads(study, par, pair, pins)
        print('Source2/27 fresh original heads elapsed_seconds='+str(perf_counter()-started), flush=True)
        if write_heads:
            io.write_certificate_text(base/HEAD_CERTIFICATE, json.dumps(scanned, indent=2)+'\n')
        else:
            require(scanned == read(HEAD_CERTIFICATE), 'Independent complete original-head replay')
    else:
        scanned = read(HEAD_CERTIFICATE)
    require(scanned['source_sha256'] == pins and scanned['parameters'] == study.uniform.encode(par)
            and scanned['original_head_evaluations'] == 9750000
            and scanned['independent_rational_comparisons'] == 312,
            'The exact new source rectangle and all26 complete original objectives')
    heads = residual.scan_heads(study, par, pair, scanned)
    heavy = study.get('wide_fresh_full_slot_source_comparison').heavy_extension(study, guard)
    result = complete.complete_comparison(study, par, heavy, H1, square, heads)
    require(result['all_original_indices'] == list(range(52))
            and result['denominator_at_mass_floor'] > 0 and result['remaining_S_coefficient'] > 0,
            'Every original independent cost and the complete signed actual-mass comparison')
    pins[HEAD_CERTIFICATE] = sha256(io.read_artifact_bytes(base/HEAD_CERTIFICATE)).hexdigest()
    return study.uniform.encode({'schema': 'erdos7-wide-source-bridge-comparison-v1', 'source_sha256': pins,
        'parameters': par, 'guards': guard, 'heavy_extension': heavy, 'complete_H1': H1,
        'complete_square': square, 'joint_pure_five_transport': five, 'complete_heads': heads,
        'comparison': result,
        'scope': 'Ordinary complete actual-source comparison in both K orientations for sigma<=2/27 and rho<=1/13000, with the full actual r<=5rho. All source/gap/heavy guards are established on this rectangle. Every one of9.75 million original heads is newly evaluated with312 independent rational LP checks; all52 independent costs, five denominator objectives, actual mass and every infinite tail remain. No domain beyond2/27, coverage of a slanted residual region, new global K, actual-family attainment, Lean verification or unrestricted Erdos7 resolution is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--scan', action='store_true', help='Recompute every original head on this source rectangle')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base, args.scan, args.write)
    io = module('source_bridge_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact fresh source2/27 complete-comparison certificate')
    print('PASS: fresh source2/27, residual1/13000, full actual slot domain; K='
          +str(float(F(result['comparison']['comparison_upper']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
