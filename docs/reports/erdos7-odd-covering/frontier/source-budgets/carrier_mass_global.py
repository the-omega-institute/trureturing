#!/usr/bin/env python3
"""Use the carrier-averaged mass and its actual residual in global K.

The same46 fixed choices from103 remain. The new denominator bound charges
the target decrement to the existing residual exactly once.
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
CERTIFICATE = 'certificates/source_norms/source-budgets/carrier_mass_global.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/shared_root_global.py': '180c427d0f4df1bb5851a42a66cbdd8b03469e13d7612fc4ab485991528bde13',
    'certificates/source_norms/source-budgets/shared_root_global.json': '84d4bd1b65b66600ec0368ddc4850dbd6d9d36fbb2f6a3c8ddbcdd8aa60a8a5f',
    'frontier/source-budgets/carrier_mass_residual_bound.py': '0478f224ae2d59dcd4e0f7d9d0c4b23eca7c6bd632bd6ffb12bce5420fd5ef16',
    'certificates/source_norms/source-budgets/carrier_mass_residual_bound.json': 'f43db53a004d7d9b3a6c8b298609256e128a8cc0435987e3bb14d5216cc0627b',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
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


def calculate(base):
    require('certificate_io.py' in PINS, 'Completed source pins')
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('carrier_global_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name)))
    previous, mass = read('shared_root_global.json'), read('carrier_mass_residual_bound.json')
    for prior in (previous, mass):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited source')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    old_module = module('carrier_global_previous', base/'frontier/source-budgets/shared_root_global.py')
    require(encode(old_module.calculate(base)) == previous, 'Recompute all46 complete cost choices and their common budget')
    mass_module = module('carrier_global_mass', base/'frontier/source-budgets/carrier_mass_residual_bound.py')
    require(encode(mass_module.calculate(base)) == mass, 'Recompute the source mass interface and its projection identities')
    delta, rcut, decrease = F(1, 27), F(1, 520), F(3, 25)
    require(F(previous['concentration_delta']) == delta and F(previous['slot_loss_cutoff']) == rcut,
            'Identical concentrated source region and packing guards')
    B, P, Q = (F(previous[k]) for k in ('weighted_credit', 'combined_residual_penalty', 'combined_escape_penalty'))
    rows = previous['cost_rows']
    require(len(rows) == 46 and B == sum(F(r['weighted_credit']) for r in rows)
            and P == sum(F(r['weighted_residual_penalty']) for r in rows)
            and Q == sum(F(r['weighted_escape_penalty']) for r in rows), 'All46 cost contributions are counted once')
    a, b, c = (F(mass[k]) for k in ('S0_upper_constant', 'S0_upper_sigma_coefficient', 'E_upper_rho_coefficient'))
    require((a, b, c) == (F(53, 360), F(5, 9), F(1)), 'One actual residual in the complete denominator')
    A0, Acur = F(previous['old_mass_coefficient']), F(previous['conservative_mass_coefficient'])
    available = Acur-decrease*c
    require(A0 >= Acur and available > P > 0, 'The denominator decrement and all cost losses share one residual')
    gamma1, gamma2 = F(previous['first_escape_gap']), F(previous['next_escape_gap'])
    curvature = gamma2-gamma1
    far_curvature = curvature-F(11, 36)*decrease
    require(0 < delta < F(1, 2) and 0 < gamma1 < gamma2 and far_curvature > 0,
            'Both source-escape polynomials are concave on their stated intervals')
    W = lambda s: gamma2*s-curvature*s*s-decrease*(a+b*s)
    R = lambda s: -decrease/4+(gamma2-F(11, 36)*decrease)*s-far_curvature*s*s
    margins = {'concentrated_small_r_zero_escape': B+W(0),
               'concentrated_small_r_at_delta': B-Q*delta+W(delta),
               'concentrated_large_r': available*rcut/5-decrease*(a+b*delta),
               'middle_at_delta': W(delta), 'middle_limit_at_half': W(F(1, 2)),
               'far_at_half': R(F(1, 2)), 'far_at_one': R(1)}
    require(len(margins) == 7 and min(margins.values()) > 0,
            'All seven signed margins are strictly positive; the half endpoint of W is only its continuous extension')
    require(mass_module.boundS0(delta) == a+b*delta and mass_module.boundE(delta, rcut/5) == a+b*delta+rcut/5,
            'The new denominator uses the proved interface inside its open-half domain')
    K0, before = F(previous['old_K0']), F(previous['new_K'])
    target = K0-decrease
    require(before-target == F(21, 500) and target > 403, 'Full decrement counted once from K0; unrestricted comparison remains open')
    fallbacks, cores = [], []
    for row in previous['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target, 'Every complete fallback remains below the target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'target_gap': target-bound})
    for row in previous['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error > 403, 'Both full terminal errors retained')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': target+error-403})
    denominator_lower = F(previous['positive_denominator_lower_factor'])
    require(len(fallbacks) == 8 and len(cores) == 2 and denominator_lower > 0
            and A0-F(23, 42)*decrease > 0, 'Complete inherited branches, positive division and target coefficient')
    return {'schema': 'erdos7-carrier-mass-global-v1', 'source_sha256': used,
            'concentration_delta': delta, 'slot_loss_cutoff': rcut,
            'source_guards': previous['source_guards'], 'slot_gap_lower': F(previous['slot_gap_lower']),
            'fixed_old_indices': previous['fixed_old_indices'], 'fixed_deep_indices': previous['fixed_deep_indices'],
            'selected_cost_count': len(rows), 'weighted_credit': B,
            'combined_residual_penalty': P, 'combined_escape_penalty': Q,
            'S0_upper_constant': a, 'S0_upper_sigma_coefficient': b, 'E_upper_rho_coefficient': c,
            'old_mass_coefficient': A0, 'conservative_mass_coefficient': Acur,
            'residual_after_denominator_charge': available, 'unused_residual_budget': available-P,
            'first_escape_gap': gamma1, 'next_escape_gap': gamma2,
            'middle_negative_quadratic': curvature, 'far_negative_quadratic': far_curvature,
            'near_denominator_without_residual_upper': a+b*delta,
            'signed_branch_margins': margins, 'strict_margin_lower': min(margins.values()),
            'old_K0': K0, 'previous_K103': before, 'decrease_from_K0': decrease,
            'new_K': target, 'improvement_over103': before-target,
            'new_mass_coefficient': A0-F(23, 42)*decrease,
            'positive_denominator_lower_factor': denominator_lower, 'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary global comparison using E<=53/360+5*sigma/9+rho for sigma<1/2 and the same actual rho as all46 cost losses. Retains103 fixed choices, original source guards, independent original residues, all infinite tails, eight complete fallbacks and two full errors. At sigma>=1/2 only the original global denominator is used. No Lean verification, optimality or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('carrier_global_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact carrier-mass global certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: one actual mass/residual relation, all46 inherited choices, seven signed margins and complete branches.')
    with localcontext() as context:
        context.prec = 34
        value = F(result['new_K'])
        print('Global K <= '+str(Decimal(value.numerator)/Decimal(value.denominator)))


if __name__ == '__main__':
    main()
