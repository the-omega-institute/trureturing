#!/usr/bin/env python3
"""Remove the independent best-slot loss cutoff from a complete local bound.

The actual r <= 5 rho bound is retained. Positive actual packing gaps
justify the larger slot domain, and fresh original heads use its caps.
"""
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
CERTIFICATE = 'certificates/source_norms/full_slot_radius_source_comparison.json'
HEAD_CERTIFICATE = 'certificates/source_norms/full_slot_radius_source_heads.json'
DELTA, RHO = F(1, 27), F(1, 1000)
PINS = {
    'frontier/expanded_source_complete_comparison.py': 'faffa75e9f37987c5ceb7afc1eb4b1540e5fc067afcd78804ecf8067f2bb623c',
    'frontier/fixed_support_source_slab.py': '937399b0a0c88c650746a93c4456012692215bf65f80b7525aaefe29c94f9593',
    'certificates/source_norms/fixed_support_source_slab.json': 'e201842ea5c0db4179dfa1449ceb7196c4f8c6dbf35d54825f54d9fde0a16837',
    'frontier/pure_five_complete_face_comparison.py': '519cd2c0c0163f80e7cb996fc43d8acb7ee202922eefd437365f247194af1986',
    'certificates/source_norms/pure_five_complete_face_comparison.json': '44912cf01714336a093ffda2a0289a301ff4d69422f8af7465640cd2bc059f45',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable proof input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def parameters_and_guards(study):
    d, rho, r = DELTA, RHO, 5*RHO
    require(d == F(1, 27) and rho == F(1, 1000) and r == F(1, 200),
            'Full actual slot-loss domain of the new complete comparison')
    total_loss = study.get('joint_concentration_loss_budget').total_loss_upper(d)
    Delta = total_loss/4
    D = study.get('exposed_concentration_prices').norm_bounds(d)['availability_Linfinity']
    h1, eta, hbar = F(1, 3)-d/18, F(1, 9)-d/18, F(1, 2)+d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-D)-2*r, (F(1, 6)-d/9)/5-r)
    gap = min(gaps)
    require(Delta == F(1, 104) < F(1, 18) and D == F(3, 316) <= Delta
            and F(3, 4)+d/4 == F(41, 54) < F(4, 5),
            'Actual sources lie inside162 r=0 source slab; availability has its own exposed bound')
    require(gap == F(817, 48600) > 0 and rho/gap < F(1, 5),
            'All five actual first-label gaps remain positive at the full slot endpoint')
    require(F(1, 4)-3*d/4 > F(1, 20),
            'First labels5,15,45 and their distinct slots are forced before any r bound')
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d}
    require(min(polynomials.values()) > 0 and 6*d-23 < 0,
            'Every reused domain polynomial is positive throughout[0,delta]')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0,
            'All fixed-support marked-source dual coefficients stay nonnegative')
    # The old constructor supplies only delta-dependent ratios, densities,
    # tails and common source budgets. Its narrow r/gap/caps are replaced.
    par = study.get('wide_k_signed_tail_comparison').parameters(study, d, rho)
    par.update(rbar=r, gap=gap, v0=min(F(1, 20), Delta+2*r),
               v1=min(F(1, 10), Delta+r/h1))
    require(par['v0'] == F(51, 2600) and par['v1'] == F(10343, 418600),
            'The full enlarged Q caps, not the narrower old rbar caps')
    price_coefficient = max(hbar/(5*gap), F(65, 9))
    require(price_coefficient == F(65, 9)
            and price_coefficient >= max(F(1), hbar/(5*gap))
            and price_coefficient >= 5*F(13, 9),
            'One residual price pays both marked defects and positive-r slot movement')
    return par, {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
                 'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
                 'availability_upper': D, 'five_actual_gap_lowers': gaps,
                 'minimum_actual_gap': gap, 'common_wrong_slot_gap': gap,
                 'whole_interval_polynomial_lowers': polynomials,
                 'heavy_residual_price_coefficient': price_coefficient,
                 'heavy_slot_movement_coefficient': F(13, 9),
                 'independent_r_cutoff': None}


def heavy_extension(study, guard):
    slab = study.read('fixed_support_source_slab')
    rows = []
    for original in slab['heavy_bounds']:
        vmax = F(original['max_derivative'])
        row = {k: original[k] for k in ('index', 'barrier', 'weight', 'margin_lower')}
        row.update(max_derivative=vmax,
                   slot_movement_price=guard['heavy_slot_movement_coefficient']*vmax,
                   original_marker_price_upper=max(F(1),
                       (F(1, 2)+DELTA/18)/(5*guard['minimum_actual_gap']))*vmax,
                   one_residual_price=guard['heavy_residual_price_coefficient']*vmax)
        require(row['one_residual_price'] >= 5*row['slot_movement_price']
                and row['one_residual_price'] >= row['original_marker_price_upper'],
                'D r + P epsilon <= P rho for epsilon=rho-(r+r1)/5')
        rows.append(row)
    require([r['index'] for r in rows] == [0, 16], 'Exactly the two full heavy cost margins')
    return {'heavy_bounds': rows,
            'positive_r_proof': 'Keep162 r=0 floors and fixed supports. General85/91 marker identities hold because the five actual gaps and forced labels are re-established. Non-H Q cap movement costs at most(13/9)vmax*r; the H movement is smaller. The remaining same-measure epsilon=rho-(r+r1)/5 is nonnegative. P=max(hbar/(5G),65/9)vmax pays both effects once.'}


def inputs(base):
    io = module('full_slot_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/pure_five_complete_face_comparison.json'))
    pins = {**prior['source_sha256'], **PINS}
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin,
                'Pinned complete proof input '+path)
    study = module('full_slot_study', base/'frontier/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(p) == h for p, h in study.pins.items()), 'Full original source closure')
    return io, study, pins


def calculate(base, scan=False, write_heads=False):
    io, study, pins = inputs(base)
    par, guard = parameters_and_guards(study)
    extension = study.get('expanded_source_complete_comparison')
    residual = study.get('residual_shell_k_comparison')
    pairs, prices = study.get('seven_pair_source_prices'), study.get('exposed_concentration_prices')
    pair = pairs.bounds(prices, pairs.raw_coefficients(study.factorial), DELTA)
    par['positive7'] = pair['Z_upper']
    H1 = residual.shallow_H1(study, par)
    square = study.square.uniform_square(par, SimpleNamespace(uniform_H1=lambda p: H1), study.factorial, study.tails)
    five = extension.expanded_joint_five(study, par, study.get('pure_five_complete_face_comparison'), guard)
    old_pure = (next(r['weighted_upper'] for r in square['bounded_cylinders'] if r['modulus'] == 5)
                +next(r['upper'] for r in square['complete_weighted_tails'] if r['family'] == 'pure5'))
    saving = max(F(0), old_pure-five['joint_upper'])
    require(saving > 0, 'Complete joint pure-five bound improves the full-r source box')
    square = {**square, 'previous_full_square_upper': square['full_square_upper'],
              'old_pure_five_block': old_pure, 'joint_pure_five_block': five['joint_upper'],
              'joint_square_saving': saving, 'full_square_upper': square['full_square_upper']-saving,
              'zero7_pair_upper': square['zero7_pair_upper']-saving}
    if scan:
        started = perf_counter()
        scanned = extension.fresh_heads(study, par, pair, pins)
        print('Full-slot original heads elapsed_seconds='+str(perf_counter()-started), flush=True)
        if write_heads:
            io.write_certificate_text(base/HEAD_CERTIFICATE, json.dumps(scanned, indent=2)+'\n')
        else:
            require(scanned == json.loads(io.read_artifact_bytes(base/HEAD_CERTIFICATE)),
                    'Independent complete full-slot head replay')
    else:
        scanned = json.loads(io.read_artifact_bytes(base/HEAD_CERTIFICATE))
    require(scanned['source_sha256'] == pins, 'Fresh heads bind the complete unchanged proof input closure')
    heads = residual.scan_heads(study, par, pair, scanned)
    heavy = heavy_extension(study, guard)
    result = extension.complete_comparison(study, par, heavy, H1, square, heads)
    require(result['comparison_upper'] < 509, 'Complete comparison sufficient for the global splice')
    pins[HEAD_CERTIFICATE] = sha256(io.read_artifact_bytes(base/HEAD_CERTIFICATE)).hexdigest()
    return study.uniform.encode({'schema': 'erdos7-full-slot-radius-source-comparison-v1',
        'source_sha256': pins, 'parameters': par, 'guards': guard,
        'heavy_extension': heavy, 'complete_H1': H1, 'complete_square': square,
        'joint_pure_five_transport': five, 'complete_heads': heads, 'comparison': result,
        'scope': 'Ordinary complete actual-source bound for both K orientations, sigma<=1/27 and rho<=1/1000. The only slot-loss bound is the globally valid r<=5rho. All52 independent original tests, the actual S coefficient, five denominator objectives and every infinite tail remain. No unrestricted Erdos7 solution, Lean verification, global K conclusion or realization of relaxation extrema is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--scan', action='store_true', help='Re-evaluate every new-domain original head')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base, args.scan, args.write)
    io = module('full_slot_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact complete full-slot source certificate')
    print('PASS: no independent r cutoff; complete K='+result['comparison']['comparison_upper'])


if __name__ == '__main__':
    main()
