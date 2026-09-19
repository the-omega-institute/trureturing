#!/usr/bin/env python3
"""Complete source radius1/12, residual1/2300 comparison by certified transport."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/expanded_bridge_residual_comparison.json'
DELTA, RHO = F(1, 12), F(1, 2300)
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/transport/extended_source_bridge_comparison.py': '4b9e21988e129c3aff849afefe563e92154cca7075e40eff5d20ae33418a403d',
    'certificates/source_norms/extended_source_bridge_comparison.json': 'd38c7de4dc87e8467f4ee6e3a4ae3a71affccf652d88aa169e093b888e675451',
    'frontier/expanded_source_complete_comparison.py': 'faffa75e9f37987c5ceb7afc1eb4b1540e5fc067afcd78804ecf8067f2bb623c',
    'frontier/wide_fresh_full_slot_source_comparison.py': '8b92c7eda87c06ca763d50015b5dd6078730cdb3c7af81aa8a46c989ba3f425d',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable proof provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def parameters_and_guards(study):
    """Prove the whole new rectangle directly, without changing195's wrapper."""
    d, rho, r = DELTA, RHO, 5*RHO
    require(d == F(1, 12) < F(1, 2) and rho == F(1, 2300),
            'General106 covers both orientations of the actual source')
    loss = study.get('joint_concentration_loss_budget').total_loss_upper(d)
    Delta = loss/4
    availability = study.get('exposed_concentration_prices').norm_bounds(d)['availability_Linfinity']
    h1, eta, hbar = F(1, 3)-d/18, F(1, 9)-d/18, F(1, 2)+d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-availability)-2*r, (F(1, 6)-d/9)/5-r)
    gap = min(gaps)
    require(loss == F(1, 11) and Delta == F(1, 44) < F(1, 18)
            and availability == F(3, 136) <= Delta
            and F(3, 4)+d/4 == F(37, 48) < F(4, 5),
            'General153/156 source and117/162 zero-residual packing guards')
    require(gap > 0 and rho/gap < F(1, 5)
            and F(1, 4)-3*d/4 == F(3, 16) > F(1, 20),
            'All five actual packing gaps, first labels and the full defect simplex')
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d,
                   'first_cell_below_reference': 4-5*d-3*d*d,
                   'other_cells_below_reference': 1-d-d*d}
    require(min(polynomials.values()) > 0 and 6*d-23 < 0 and 8-15*d > 0
            and 3-2*d > 0 and 1-d > 0,
            'Source-ratio, maximizing-cell and domination polynomials on[0,1/12]')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0,
            'All original fixed-support marker coefficients stay positive')
    v0, v1 = min(F(1, 20), Delta+2*r), min(F(1, 10), Delta+r/h1)
    require(F(3, 20)+v0 <= F(1, 5) and F(1, 10)+v1 <= F(1, 5),
            'Both enlarged Q pre-cap tables stay inside the original slot range')
    par = {'delta': d, 'rho': rho, 'rbar': r, 'h1min': h1, 'v0': v0, 'v1': v1,
           'gap': gap, 'tbar': 2*(1+d)/(1-4*d),
           'Cbar': (F(3, 4)+d/4)/(F(1, 5)-3*d/8), 'kbar': (6-d)/(3-2*d),
           'budget_increments': ((3+d)*loss/72, d/36, loss/12),
           'c': (F(7, 10)+d/4, F(2, 5)+13*d/90, F(4, 15)+d/15, F(4, 45)+d/45),
           'H': (F(1, 20)+21*d/20-d*d/5, F(1, 10)+(19*d+2*d*d)/90,
                 F(1, 15)+d/9, F(1, 45)+d/30-d*d/360)}
    require((par['tbar'], par['Cbar'], par['kbar']) == (F(13, 4), F(370, 81), F(71, 34))
            and par['Cbar'] >= 1+par['tbar'] and par['Cbar'] >= par['kbar']
            and min(par['c']+par['H']) > 0, 'Complete positive source and error envelopes')
    root0 = F(1, 9)+par['budget_increments'][0]+par['budget_increments'][1]
    root1, maxn = F(5, 36)+loss/12, F(1, 12)+d/36
    require(root0 <= root1 and F(1, 36)+par['budget_increments'][0] <= maxn
            and F(1, 18)+loss/36 <= maxn, 'All root and cell dominance comparisons')
    price = max(hbar/(5*gap), F(65, 9))
    require(price == F(65, 9) and price >= max(F(1), hbar/(5*gap))
            and price >= 5*F(13, 9), 'One actual residual pays every heavy marker and slot movement')
    return par, {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
        'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
        'availability_upper': availability, 'h1_lower': h1, 'first_beta_eta_lower': eta,
        'h_upper': hbar, 'five_actual_gap_lowers': gaps, 'minimum_actual_gap': gap,
        'common_wrong_slot_gap': gap, 'whole_interval_polynomial_lowers': polynomials,
        'heavy_residual_price_coefficient': price, 'heavy_slot_movement_coefficient': F(13, 9),
        'independent_r_cutoff': None,
        'domain_proof': 'All source envelopes increase with sigma through1/12 and all packing gaps decrease with the same actual r through5/2300. The source polynomials are positive throughout[0,1/12]. The new full residual rectangle independently satisfies the original source, slot, marker, selected-operator, factorial and infinite-tail conditions.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('expanded_bridge_io', base/'certificate_io.py')
    read = lambda n: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(n+'.json')))
    old = read('extended_source_bridge_comparison')
    pins = dict(PINS)
    for path, pin in old['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent complete predecessor closure '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    study = module('expanded_bridge_study', base/'frontier/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'Complete original source providers')
    bridge = study.get('transport/extended_source_bridge_comparison')
    oldpar, oldguard = bridge.parameters_and_guards(study)
    pair = bridge.source_pair_bounds(study, DELTA)
    oldpar['positive7'] = pair['Z_upper']
    require(study.uniform.encode(oldpar) == old['parameters']
            and study.uniform.encode(oldguard) == old['guards'], 'Exactly the certified predecessor rectangle')
    par, guard = parameters_and_guards(study)
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
    scanned = read('extended_source_bridge_heads')
    head_path = 'certificates/source_norms/extended_source_bridge_heads.json'
    require(pins.get(head_path) == sha256(io.read_artifact_bytes(base/head_path)).hexdigest()
            and scanned['source_sha256'] == {p: h for p, h in old['source_sha256'].items() if p != head_path}
            and scanned['parameters'] == study.uniform.encode(oldpar)
            and scanned['original_head_evaluations'] == 9750000
            and scanned['independent_rational_comparisons'] == 312,
            'The exact312-check,9750000-head predecessor certificate supplies every old upper')
    heads = complete.transported_heads(study, oldpar, par, pair, scanned)
    require(heads['finite_branch_transport_checks'] == 3120
            and heads['reused_original_head_evaluations'] == 9750000
            and heads['new_original_head_evaluations'] == 0,
            'Uniform all-layout perturbation with3120 independent rational branch checks')
    heavy = study.get('wide_fresh_full_slot_source_comparison').heavy_extension(study, guard)
    result = complete.complete_comparison(study, par, heavy, H1, square, heads)
    require(result['all_original_indices'] == list(range(52))
            and result['denominator_at_mass_floor'] > 0 and result['remaining_S_coefficient'] > 0
            and 403 < result['comparison_upper'] < F(507),
            'Complete52-cost, all-tail actual-mass comparison on the enlarged rectangle')
    return study.uniform.encode({'schema': 'erdos7-expanded-bridge-residual-comparison-v1',
        'source_sha256': pins, 'parameters': par, 'guards': guard, 'heavy_extension': heavy,
        'complete_H1': H1, 'complete_square': square, 'joint_pure_five_transport': five,
        'complete_heads': heads, 'comparison': result,
        'predecessor_parameters': oldpar,
        'scope': 'Ordinary complete actual-source bound in both K orientations for sigma<=1/12 and rho<=1/2300, including the whole actual r<=5rho range. Every old original head is transported by the uniform coefficient/capacity perturbation theorem. All52 independent costs, five denominator objectives, the same signed actual mass and every infinite tail remain. No local endpoint alone substitutes for a domain theorem. No global conclusion, Lean verification, actual-family attainment or unrestricted Erdos7 resolution is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('expanded_bridge_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact complete expanded-residual certificate')
    print('PASS: full source1/12 and residual1/2300; complete52 costs; K='
          +str(float(F(result['comparison']['comparison_upper']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
