#!/usr/bin/env python3
"""Fresh complete original heads on source radius1/12 and residual1/3000."""
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
CERTIFICATE = 'certificates/source_norms/source-budgets/extended_source_bridge_comparison.json'
HEAD_CERTIFICATE = 'certificates/source_norms/source-budgets/extended_source_bridge_heads.json'
DELTA, RHO = F(1, 12), F(1, 3000)
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
    """Independent source-domain proof; no old radius wrapper is invoked."""
    d, rho, r = DELTA, RHO, 5*RHO
    require(d == F(1, 12) < F(1, 2) and rho == F(1, 3000) and r == F(1, 600),
            'The original106 orientation theorem covers the new actual source domain')
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
            'General153/156 concentration, general117 packing and original162 zero-r slab')
    require(gaps == (F(59, 600), F(173, 2700), F(53, 2700), F(16367, 734400), F(161, 5400))
            and gap == F(53, 2700) > 0 and rho/gap == F(9, 530) < F(1, 5)
            and F(1, 4)-3*d/4 == F(3, 16) > F(1, 20),
            'Five general actual packing guards, first labels and full actual-r defect simplex')
    polynomials = {'carrier_ratio': 1-4*d, 'shallow_C_minus_1_t': 6-49*d-70*d*d,
                   'shallow_C_minus_k': 42-35*d*d,
                   'pure3_maximizing_cell': 3*d*d-23*d+3,
                   'root0_below_root1_reference': 2-7*d-d*d,
                   'first_cell_below_reference': 4-5*d-3*d*d,
                   'other_cells_below_reference': 1-d-d*d}
    require(tuple(polynomials.values()) == (F(2, 3), F(103, 72), F(6013, 144), F(53, 48),
                                            F(203, 144), F(57, 16), F(131, 144))
            and min(polynomials.values()) > 0 and 6*d-23 < 0
            and 8-15*d > 0 and 3-2*d > 0 and 1-d > 0,
            'Explicit whole-interval domain proof for134,152,157,158 on[0,1/12]')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0,
            'All original fixed-support marker coefficients remain positive')
    v0, v1 = min(F(1, 20), Delta+2*r), min(F(1, 10), Delta+r/h1)
    require(v0 == F(43, 1650) and v1 == F(2171, 78100)
            and F(3, 20)+v0 <= F(1, 5) and F(1, 10)+v1 <= F(1, 5),
            'Both new Q pre-cap tables stay in the original valid slot range')
    # These are the original pointwise formulas, with each domain condition
    # established above. The older public radius-limited constructors are not
    # called or modified to assert an extension they did not prove.
    par = {'delta': d, 'rho': rho, 'rbar': r, 'h1min': h1, 'v0': v0, 'v1': v1,
           'gap': gap, 'tbar': 2*(1+d)/(1-4*d),
           'Cbar': (F(3, 4)+d/4)/(F(1, 5)-3*d/8), 'kbar': (6-d)/(3-2*d),
           'budget_increments': ((3+d)*loss/72, d/36, loss/12),
           'c': (F(7, 10)+d/4, F(2, 5)+13*d/90, F(4, 15)+d/15, F(4, 45)+d/45),
           'H': (F(1, 20)+21*d/20-d*d/5, F(1, 10)+(19*d+2*d*d)/90,
                 F(1, 15)+d/9, F(1, 45)+d/30-d*d/360)}
    require((par['tbar'], par['Cbar'], par['kbar']) == (F(13, 4), F(370, 81), F(71, 34))
            and par['Cbar'] >= 1+par['tbar'] and par['Cbar'] >= par['kbar']
            and par['budget_increments'] == (F(37, 9504), F(1, 432), F(1, 132))
            and min(par['c']+par['H']) > 0,
            'Full source ratios, cap budgets and positive complete reference/error envelopes')
    root0 = F(1, 9)+par['budget_increments'][0]+par['budget_increments'][1]
    root1, maxn = F(5, 36)+loss/12, F(1, 12)+d/36
    require(root0 <= root1 and F(1, 36)+par['budget_increments'][0] <= maxn
            and F(1, 18)+loss/36 <= maxn,
            'All157 root and cell dominance comparisons are independently re-established')
    price = max(hbar/(5*gap), F(65, 9))
    require(hbar/(5*gap) == F(545, 106) and price == F(65, 9)
            and price >= max(F(1), hbar/(5*gap)) and price >= 5*F(13, 9),
            'The full new r range uses one actual residual for heavy marker and slot motion')
    return par, {'source_radius': d, 'residual_radius': rho, 'actual_r_upper': r,
        'joint_source_Delta_upper': Delta, 'source_z_upper': F(3, 4)+d/4,
        'availability_upper': availability, 'h1_lower': h1, 'first_beta_eta_lower': eta,
        'h_upper': hbar, 'five_actual_gap_lowers': gaps, 'minimum_actual_gap': gap,
        'common_wrong_slot_gap': gap, 'whole_interval_polynomial_lowers': polynomials,
        'heavy_residual_price_coefficient': price, 'heavy_slot_movement_coefficient': F(13, 9),
        'independent_r_cutoff': None,
        'domain_proof': '106 applies for sigma<1/2. General153/156 replaces the obsolete coarse Delta<=3delta/4 cutoff by Delta<=delta/(4(1-delta)). General117 guards and162 zero-r slab then hold. Every additional134/152/157/158 source-ratio, reference and domination polynomial is positive throughout[0,1/12]. Full original cap, selected-operator, mean, factorial and infinite-tail derivations apply with these source bounds.'}


def source_pair_bounds(study, delta):
    """Extend158 by its pointwise source proof and156 price-gap criterion."""
    d = F(delta)
    require(0 <= d <= F(1, 12) and 2-7*d-d*d > 0,
            'Root0 reference stays below5/36 throughout the independently proved interval')
    raw = study.get('seven_pair_source_prices').raw_coefficients(study.factorial)
    matrix = ((F(1, 12), F(1, 8), F(1, 36), (5+d)/72, F(1, 72), F(0)),
              (F(1, 12), F(1, 12), F(1, 36), F(1, 72), F(0), F(0)),
              (F(0), F(1, 36), F(0), F(0), F(0), F(0)),
              (F(0), F(1, 4), F(0), F(0), F(0), F(0)),
              (F(0), F(0), F(0), F(1, 18), F(0), F(0)),
              (F(0),)*6, (F(0),)*6, (F(0),)*6)
    pZ = tuple(sum(raw['positive7_complement'][j]*matrix[j][i] for j in range(8)) for i in range(6))
    pF = tuple(sum(raw['pair'][j]*matrix[j][i] for j in range(8)) for i in range(6))
    require(pZ == (F(1, 420), F(3, 280), F(1, 1260), F(4, 3150), F(0), F(0))
            and pF == (F(1, 36), F(13, 180), F(1, 108), (146+5*d)/10800, F(1, 2160), F(0)),
            'Original complete seven-tail price vectors reconstructed before bounding')
    require(F(1, 420) <= (1-F(1, 12))*F(3, 280)
            and F(1, 36) <= (1-F(1, 12))*F(13, 180)
            and (146+5*F(1, 12))/10800 < F(1, 36),
            'Both price-gap criteria hold uniformly through1/12, with unchanged second prices')
    prices = study.get('exposed_concentration_prices')
    z, pair = prices.price_record(pZ, d), prices.price_record(pF, d)
    require(z['corner_criterion'] and pair['corner_criterion']
            and z['sorted_indices'][0] == pair['sorted_indices'][0] == 1
            and z['upper'] == 3*d/280 and pair['upper'] == 13*d/180,
            '156 supports the same actual six-loss vector on the enlarged domain')
    return {'delta': d, 'source_price_matrix': matrix, 'Z_price': z, 'pair_price': pair,
            'Z_upper': F(779, 12600)+z['upper'], 'pair_upper': F(103, 180)+pair['upper']}


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
    pair = source_pair_bounds(study, DELTA)
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
        print('Source1/12 fresh original heads elapsed_seconds='+str(perf_counter()-started), flush=True)
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
    return study.uniform.encode({'schema': 'erdos7-extended-source-bridge-comparison-v1', 'source_sha256': pins,
        'parameters': par, 'guards': guard, 'heavy_extension': heavy, 'complete_H1': H1,
        'complete_square': square, 'joint_pure_five_transport': five, 'complete_heads': heads,
        'comparison': result,
        'scope': 'Ordinary complete actual-source comparison in both K orientations for sigma<=1/12 and rho<=1/3000, with full actual r<=5rho. An independent enlarged-domain proof re-establishes all source/gap/heavy/reference/tail and six-loss price conditions; no radius-limited predecessor wrapper is modified or invoked beyond its domain. Every one of9.75 million original heads is newly evaluated with312 independent rational LP checks; all52 independent costs, five denominator objectives, actual mass and every infinite tail remain. No global complementary-region join, actual-family attainment, Lean verification or unrestricted Erdos7 resolution is asserted.'})


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
                'Exact fresh source1/12 complete-comparison certificate')
    print('PASS: fresh source1/12, residual1/3000, full actual slot domain; K='
          +str(float(F(result['comparison']['comparison_upper']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
