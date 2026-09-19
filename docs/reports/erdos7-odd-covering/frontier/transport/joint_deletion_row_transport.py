#!/usr/bin/env python3
"""Transport the E3/E5 and three common-survivor link families together.

Only the stated883 constraint residuals are priced. This is not a complete
retained-LP objective, off-face K comparison or covering theorem.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/joint_deletion_row_transport.json'
PINS = {
    'frontier/transport/selected_deletion_mask_row_transport.py': '5a1ac7bfc00bf04edc27ec4b87e2fd232eaa989cc6e50edad1536f10ae7b1ae9',
    'certificates/source_norms/retained-transport/selected_deletion_mask_row_transport.json': '9a77f9d4394aec0324a5317df77b6560e7c8e49251c9631b05b1a1d686c121c5',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original provider')
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


def row_inventory(lp, wi):
    require(len(lp.rows) == 4726 and len(lp.equalities) == 55, 'Unchanged223 branch dimensions')
    coarse, root1 = [], {}
    cursor = 536
    for cell in range(25):
        expected = {825+cell: F(1), 850+cell: F(1)}
        for mask in range(16):
            k = 16*cell+mask
            require(lp.rows[132+k] == {425+k: F(1), k: -F(wi[cell], 5)}
                    and lp.rhs[132+k] == 0, 'Four hundred old survivor links')
            expected[k], expected[425+k] = -F(wi[cell], 5), F(1)
        require(lp.rows[cursor] == expected and lp.rhs[cursor] == 0, 'Twenty-five joint coarse deletion links')
        coarse.append(cursor)
        cursor += 1
        if cell//5 >= 2:
            require(lp.rows[cursor] == {825+cell: F(1)} and lp.rhs[cursor] == 0, 'Fifteen E3 root1 zero rows')
            root1[cell] = cursor
            cursor += 1
    require(cursor == 576, 'All coarse and zero rows accounted for')
    q = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))
    for s in range(5):
        require(lp.equalities[6+s] == {825+s: F(1), 830+s: F(1)} and lp.erhs[6+s] == q[s]/90,
                'The five E3 equality rows include root0 only')
        require(lp.rows[576+s] == {830+s: -F(1)} and lp.rhs[576+s] == -q[s]/135,
                'Five original27 cell1 lower rows')
    return coarse, root1


def price_record(record, parameters, caps, budgets, bridge, e5, inventory):
    coarse_rows, root1_rows = inventory
    y = {int(k): F(v) for k, v in record['nonzero_inequality_duals'].items()}
    z = list(map(F, record['equality_duals']))
    get = lambda index: y.get(index, F(0))
    require(len(z) == 55 and all(v >= 0 for v in y.values()), 'Actual signed223 dual prices')
    alpha, beta = z[6:11], [get(576+s) for s in range(5)]
    gamma = {(c, s): get(root1_rows[5*c+s]) for c in range(2, 5) for s in range(5)}
    slots = range(1, 5)  # P is an exact empty actual source slot.
    xi = max([F(0)]+[beta[s]-alpha[s] for s in slots])
    chi = max([F(0)]+[-alpha[s] for s in slots])
    bad0 = max(beta[s] for s in slots)
    bad1 = max([F(0)]+[gamma[c, s]-alpha[s]+beta[s] for c in range(2, 5) for s in slots])
    later = max([F(0)]+[gamma[c, s]-alpha[s] for c in range(2, 5) for s in slots])
    tbar, Cbar = parameters['tbar'], parameters['Cbar']
    L27 = xi+max((Cbar-1)*bad0, tbar*bad1)
    Lge4 = chi+tbar*later
    # The full original27 projection can only improve the good-part reference.
    old0 = max([F(0)]+[xi+alpha[s] for s in slots])
    old1 = max(xi+gamma[c, s] for c in range(2, 5) for s in slots)
    require(bad0 <= old0 and bad1 <= old1
            and L27 <= xi+max((Cbar-1)*old0, tbar*old1), 'Signed full-projection domination')
    k = [alpha[s]/90-beta[s]/135 for s in range(5)]
    source_gains = [max(F(0), k[3]), max(F(0), k[3]-k[1]), max(F(0), k[3]-k[2])]
    d, rho, gap = (parameters[name] for name in ('delta', 'rho', 'gap'))
    delta_upper = 3*d/(4*(3-2*d))
    q_source = min(d/4*sum(source_gains), delta_upper*max(source_gains))
    h_slot_price = 10*max(F(0), k[3]-k[4])
    pure_source = q_source+d*(xi/360+chi/720)
    # All three link families test the same W and the same raw atom.
    merged = dict(y)
    for cell in range(25):
        for mask in range(16):
            atom = 16*cell+mask
            merged[596+atom] = get(596+atom)+get(132+atom)+get(coarse_rows[cell])
    packed = dict(record)
    packed['nonzero_inequality_duals'] = {str(index): str(value) for index, value in merged.items() if value}
    old = e5.price_record(packed, parameters, caps)
    signed = e5.signed_price_record(packed, parameters, caps, budgets, bridge, old)
    primitive = dict(signed['primitive_prices'])
    primitive['shallow_five_shifted_defect'] += h_slot_price
    primitive['pure_three_27_defect'] = L27
    primitive['pure_three_later_defect'] = Lge4
    require(len(primitive) == 7 and min(primitive.values()) >= 0, 'One seven-coordinate nonnegative price vector')
    largest = max(primitive.values())
    vertices = []
    for row in signed['triangle_vertices']:
        q5, q15 = row['q']
        value = d*signed['source_price']+pure_source+row['raw_transport']+(rho-gap*(q5+q15))*largest
        require(value >= 0 and rho-gap*(q5+q15) >= 0, 'One residual after the common wrong-slot budget')
        vertices.append({'q': [q5, q15], 'raw_transport': row['raw_transport'],
                         'raw_primal_dual': row['raw_primal_dual'], 'joint_row_error_upper': value})
    return {'E3_equality_prices': alpha, 'E3_lower_prices': beta,
            'E3_positive_projection_prices': [xi, chi], 'E3_bad_carrier_prices': [bad0, bad1, later],
            'E3_source_gains': source_gains, 'E3_q_source_upper': q_source,
            'E3_source_upper': pure_source, 'E3_H_shifted_price': h_slot_price,
            'E5_source_price': signed['source_price'], 'primitive_prices': primitive,
            'common_link_atom_price_maxima': old['cell_mask_price_maxima'],
            'remaining_residual_price': largest, 'triangle_vertices': vertices,
            'joint_row_error_upper': max(row['joint_row_error_upper'] for row in vertices)}


def calculate(base):
    io = module('joint_rows_io', base/'certificate_io.py')
    read = lambda rel: json.loads(io.read_artifact_bytes(base/rel))
    parent = read('certificates/source_norms/retained-transport/selected_deletion_mask_row_transport.json')
    pins = dict(parent['source_sha256'])
    for path, pin in PINS.items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited source')
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    e5 = module('joint_rows_e5', base/'frontier/transport/selected_deletion_mask_row_transport.py')
    retained = module('joint_rows_retained', base/'frontier/transport/retained135_heavy_comparison.py')
    prior = read('certificates/source_norms/retained-transport/retained135_heavy_comparison.json')
    bank = retained.decode_dual_bank(prior['encoded_rational_duals'])
    require(len(bank) == 2060, 'All published223 rational duals')
    head = retained.retained135_head_class(base)(base)
    inventories = []
    for lp in head.branch_lps.values():
        e5.check_row_meanings(lp, head.common.wi)
        inventories.append(row_inventory(lp, head.common.wi))
    require(all(value == inventories[0] for value in inventories), 'Both original nested/disjoint branches share these row meanings')
    study = module('joint_rows_study', base/'frontier/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'Same guarded whole-domain providers')
    output = []
    for domain, provider in zip(parent['domains'], (study.get('wide_fresh_full_slot_source_comparison'), study.get('transport/extended_source_bridge_comparison')), strict=True):
        name = domain['source_domain']
        par, guards = provider.parameters_and_guards(study)
        doc = read('certificates/source_norms/'+name+'.json')
        require(encode(guards) == doc['guards'] and par['delta'] == F(domain['delta'])
                and par['rho'] == F(domain['rho']) and par['gap'] == F(domain['gap']), 'The same two208 source domains')
        d = par['delta']
        require(par['tbar'] == 2*(1+d)/(1-4*d)
                and par['Cbar'] == (F(3,4)+d/4)/(F(1,5)-3*d/8), 'Established uniform original-label spill ratios')
        caps, budgets = [list(map(F, domain[name])) for name in ('raw_caps', 'raw_budgets')]
        require(encode(caps) == doc['complete_heads']['uniform_caps']
                and encode(budgets) == doc['complete_heads']['uniform_budgets'], 'Fixed raw feasible set')
        priced = {key: price_record(record, par, caps, budgets, head.bridge, e5, inventories[0])
                  for key, record in bank.items()}
        maximum = max(row['joint_row_error_upper'] for row in priced.values())
        controllers = []
        for row in prior['heavy_results']:
            controllers.append({'cost': row['index'], 'branches': {
                branch: {'dual_key': key, 'joint_row_transport': priced[key]}
                for branch, key in row['scan']['maximizing_witness']['nested_disjoint_dual_keys'].items()}})
        output.append({'source_domain': name, 'delta': d, 'rho': par['rho'], 'gap': par['gap'],
                       'dual_count': len(bank), 'joint_row_error_maximum': maximum,
                       'all_priced_rows_sha256': sha256(json.dumps(encode(priced), sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
                       'maximizing_dual_keys': [key for key in sorted(priced) if priced[key]['joint_row_error_upper'] == maximum],
                       'complete_heavy_controllers': controllers})
    return encode({'schema': 'erdos7-joint-deletion-row-transport-v1', 'source_sha256': pins,
                   'included_constraints': {'E5_totals': 5, 'marked_marginals': 8, 'fixed_H': 5,
                       'E5_forbidden_slots': 15, 'mask_links': 400, 'old_survivor_links': 400,
                       'coarse_deletion_links': 25, 'E3_root1_zero': 15, 'E3_root0_equalities': 5,
                       'E3_cell1_lower': 5}, 'priced_constraint_count': 883, 'exact_aggregation_rows': 25,
                   'domains': output,
                   'scope': 'Only883 old E3/E5 and shared-link row residuals. One common actual measure and residual. Raw/selected margins, scalar mass/caps, retained135/125, complete tails, pruning and whole-objective transportation remain. No complete off-face K or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_rows_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact joint row-transport certificate')
    for row in result['domains']:
        print(row['source_domain']+': partial883-row error='+str(float(F(row['joint_row_error_maximum'])))+'.')
    print('PASS: one signed budget for E3/E5 and all three common-link families; other off-face obligations remain.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
