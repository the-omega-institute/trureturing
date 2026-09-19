#!/usr/bin/env python3
"""Price five E5 constraint groups on two established source neighborhoods.

This computes a contribution to dual transport, not an off-face LP bound.
The remaining constraints and objective/tail changes are not included.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/selected_deletion_mask_row_transport.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/retained-transport/retained135_heavy_comparison.py': '16decabc92c504ef15a12ce7efff65786625d79dd3608049f182b1d355cdde36',
    'certificates/source_norms/retained-transport/retained135_heavy_comparison.json': 'fb5abfd3bc05a85881a1556a6c9cd314f42bcf860982ae4f08c225859ed32578',
    'certificates/source_norms/source-budgets/wide_fresh_full_slot_source_comparison.json': 'f5fa0d812a9a5330585948683fa9e93dc4a405a7e2d962973cb189b0ae1f3a04',
    'certificates/source_norms/source-budgets/extended_source_bridge_comparison.json': '537a33d2748503601eee5ceefd41a47af5a1248f23535271aca614099fb5ac05',
    'frontier/endpoint-bounds/k_neighborhood_radius_study.py': '67cc9b5ab2f930baca853be93cb5ffa91b779fde1aeb75895ac5dacf5fe99a9c',
    'frontier/source-budgets/wide_fresh_full_slot_source_comparison.py': 'f4cb79e71f5092d0eeca452aba9bbb31e9fc8ea929685cbdfa462ea269cd19d9',
    'frontier/source-budgets/extended_source_bridge_comparison.py': '1f5901ff36605fea35633bc05251820dafe0911f9da50777a6f1bcbab2fb905a',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source provider')
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


def price_record(record, parameters, caps):
    """Apply227's one-budget bound to the actual signed prices of these rows."""
    y = {int(k): F(v) for k, v in record['nonzero_inequality_duals'].items()}
    z = list(map(F, record['equality_duals']))
    require(len(z) == 55 and all(v >= 0 for v in y.values()), 'Canonical223 price signs and dimensions')
    T = max(abs(z[i]) for i in range(11, 16))
    M = max(abs(z[i]) for i in range(46, 54))
    H = max(abs(z[i]) for i in range(16, 21))
    S = max(y.get(i, F(0)) for i in range(581, 596))
    cell_prices = [max(y.get(596+16*cell+mask, F(0)) for mask in range(16)) for cell in range(25)]
    Q = max(cell_prices)
    d, rho, gap = (parameters[k] for k in ('delta', 'rho', 'gap'))
    kappa = parameters['kbar']
    hbar, h0bar, h1min, etamin = F(1, 2)+d/18, F(1, 6)+d/18, F(1, 3)-d/18, F(1, 9)-d/18
    require(0 <= d <= F(1, 12) and rho >= 0 and gap > 0 and h1min > h0bar > 0 and etamin > 0,
            'The established source neighborhood has positive root and packing gaps')
    require(kappa == h1min/(h1min-h0bar), 'The same root-spill ratio')
    beta_p = max(h0bar/h1min, hbar/etamin-1)
    beta_a = max(F(1, 3)/etamin-1, kappa-1)
    primitive_prices = {'slot_loss_over_five': 5*H, 'pure_deep_five_defect': T+2*M+beta_p*S,
                        'alpha_deep_five_defect': (2*kappa-1)*(T+2*M)+beta_a*S, 'union_overlap': Q}
    L = max(primitive_prices.values())
    C = T/600+M/450+H/45+sum(caps[i]*cell_prices[i] for i in range(5, 25))/5
    B5 = sum(caps[i]*cell_prices[i] for i in range(4, 25, 5))
    B15 = sum(caps[i]*cell_prices[i] for i in range(14, 25, 5))
    vertices = ((F(0), F(0)), (rho/gap, F(0)), (F(0), rho/gap))
    values = [d*C+q5*B5+q15*B15+(rho-gap*(q5+q15))*L for q5, q15 in vertices]
    bound = d*C+rho*max(L, B5/gap, B15/gap)
    require(bound == max(values) and min(values) >= 0, 'Exact one-residual affine budget identity')
    return {'price_suprema': {'row_totals': T, 'marked_marginals': M, 'fixed_H': H,
                             'forbidden_slots': S, 'mask_links': Q},
            'cell_mask_price_maxima': cell_prices, 'root_spill_upper': kappa,
            'support_ratios': {'pure': beta_p, 'alpha': beta_a}, 'primitive_prices': primitive_prices,
            'source_price': C, 'wrong_slot_prices': [B5, B15], 'remaining_residual_price': L,
            'triangle_values': values, 'five_group_error_upper': bound}


def signed_price_record(record, parameters, caps, budgets, bridge, coarse):
    """Keep the signs of the same equality rows and the common raw-source LP."""
    y = {int(k): F(v) for k, v in record['nonzero_inequality_duals'].items()}
    z = list(map(F, record['equality_duals']))
    phi = []
    for c in range(5):
        marked = (F(0), F(0)) if c == 0 else (z[46+2*(c-1)], z[47+2*(c-1)])
        phi.append([z[11+c]+a*marked[0]+b*marked[1] for a in (0, 1) for b in (0, 1)])
    # All four bit pairs contain both nested and disjoint actual geometries.
    A5 = max(F(0), -min(v for row in phi for v in row))
    A15 = max(F(0), -min(v for row in phi[2:] for v in row))
    B15 = max(F(0), max(v for row in phi[:2] for v in row))
    S = max(y.get(581+3*c+s, F(0)) for c in range(5) for s in (1, 2))
    H = z[16:21]
    L0 = max(F(0), -min(H[:2]))
    L1 = max(F(0), -min(H[2:]))
    kappa = coarse['root_spill_upper']
    bp, ba = (coarse['support_ratios'][k] for k in ('pure', 'alpha'))
    cell_prices = coarse['cell_mask_price_maxima']
    primitive = {'shallow_five_shifted_defect': 5*L0,
                 'shallow_alpha_shifted_defect': 5*max(L1-L0, F(0)),
                 'pure_deep_five_defect': A5+bp*S,
                 'alpha_deep_five_defect': A15+(kappa-1)*(A15+B15)+ba*S,
                 'union_overlap': max(cell_prices)}
    L = max(primitive.values())
    C0 = z[11]/100+H[0]/5
    CU = max(-F(1+int(c >= 2), 100)*v-H[c]/5 for c in range(1, 5) for v in phi[c])
    source_price = max(F(0), C0+max(F(0), CU))/18
    d, rho, gap = (parameters[k] for k in ('delta', 'rho', 'gap'))
    vertices = ((F(0), F(0)), (rho/gap, F(0)), (F(0), rho/gap))
    records = []
    for q5, q15 in vertices:
        coefficients = [u*(d/5*int(i//5 != 0)+q5*int(i % 5 == 4)
                            +q15*int(i//5 >= 2 and i % 5 == 4)) for i, u in enumerate(cell_prices)]
        raw, witnesses = bridge.lp_bound(coefficients, caps, budgets)
        value = d*source_price+raw+(rho-gap*(q5+q15))*L
        records.append({'q': [q5, q15], 'raw_transport': raw, 'raw_primal_dual': witnesses,
                        'five_group_error_upper': value})
    upper = max(row['five_group_error_upper'] for row in records)
    return {'ternary_coefficient_values': phi, 'primitive_prices': primitive,
            'source_price': source_price, 'remaining_residual_price': L,
            'triangle_vertices': records, 'five_group_error_upper': upper,
            'accepted_five_group_error_upper': min(upper, coarse['five_group_error_upper'])}


def check_row_meanings(lp, wi):
    require(len(lp.rows) == 4726 and len(lp.equalities) == 55 and lp.mask_links == list(range(596, 996)),
            'Exact223 constraint inventory')
    eta = (F(1, 18),)+(F(1, 9),)*4
    for c in range(5):
        require(lp.equalities[11+c] == {850+5*c+s: F(1) for s in range(5)}
                and lp.erhs[11+c] == eta[c]*(1+int(c >= 2))/100, 'Five original E5 row totals')
        require(lp.equalities[16+c] == {16*(5*c+4)+m: F(1) for m in range(16)}
                and lp.erhs[16+c] == eta[c]/5, 'Five original fixed-H rows')
        for s in range(3):
            require(lp.rows[581+3*c+s] == {850+5*c+s: F(1)} and lp.rhs[581+3*c+s] == 0,
                    'Fifteen original forbidden-slot rows')
    for cell in range(25):
        for mask in range(16):
            k = 16*cell+mask
            require(lp.rows[596+k] == {875+k: F(1), 425+k: F(1), k: -F(wi[cell], 5)}
                    and lp.rhs[596+k] == 0, 'Four hundred original common-mask rows')
        require(lp.equalities[21+cell] == {850+cell: F(-1), **{875+16*cell+m: F(1) for m in range(16)}}
                and lp.erhs[21+cell] == 0, 'Aggregation remains exact and needs no error price')
    for c in range(1, 5):
        for offset, (bit, group, ratio) in enumerate(((1, 1, F(1, 3)), (3, 3, F(1, 9)))):
            row = {lp.lambda_groups[group][c]: -eta[c]*(1+int(c >= 2))*ratio/100,
                   **{875+16*(5*c+s)+m: F(1) for s in range(5) for m in range(16) if m & (1 << bit)}}
            require(lp.equalities[46+2*(c-1)+offset] == row and lp.erhs[46+2*(c-1)+offset] == 0,
                    'Eight independently marked original ternary marginals')


def calculate(base):
    io = module('e5_row_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior = read('retained135_heavy_comparison')
    domain_names = ('wide_fresh_full_slot_source_comparison', 'extended_source_bridge_comparison')
    domains = [read(name) for name in domain_names]
    pins = dict(PINS)
    for data in [prior]+domains:
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent published source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    retained = module('e5_row_retained', base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank = retained.decode_dual_bank(prior['encoded_rational_duals'])
    head = retained.retained135_head_class(base)(base)
    for lp in head.branch_lps.values():
        check_row_meanings(lp, head.common.wi)
    study = module('e5_row_study', base/'frontier/endpoint-bounds/k_neighborhood_radius_study.py').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'The same complete source providers')
    raw = [v for row in head.bridge.source_tables(2)[1] for v in row]
    output = []
    for name, doc in zip(domain_names, domains):
        par, guards = study.get(name).parameters_and_guards(study)
        require(encode(guards) == doc['guards'], 'Rechecked established whole-domain source guards')
        caps = list(map(F, doc['complete_heads']['uniform_caps']))
        expected = []
        for i, cap in enumerate(raw):
            c, s = divmod(i, 5)
            excluded = s == 0 or (s == 1 and c >= 2) or (s == 2 and c == 2)
            delta = F(0) if excluded or c != 0 else par['delta']/90
            if not excluded and s == 3:
                delta += par['v0']/18 if c == 0 else par['v0']/9 if c == 1 else par['v1']/9
            expected.append(cap+delta)
        require(caps == expected and len(caps) == 25, 'The original208 uniform raw-source capacities')
        budgets = list(map(F, doc['complete_heads']['uniform_budgets']))
        require(budgets == [a+b for a, b in zip(head.bridge.GROUP_MASSES, par['budget_increments'])],
                'The same three complete source-group budgets')
        priced = {key: price_record(record, par, caps) for key, record in bank.items()}
        signed = {key: signed_price_record(record, par, caps, budgets, head.bridge, priced[key])
                  for key, record in bank.items()}
        maximum = max(row['accepted_five_group_error_upper'] for row in signed.values())
        controllers = []
        for row in prior['heavy_results']:
            keys = row['scan']['maximizing_witness']['nested_disjoint_dual_keys']
            controllers.append({'cost': row['index'], 'branches': {
                branch: {'dual_key': key, 'row_transport': priced[key], 'signed_row_transport': signed[key]}
                for branch, key in keys.items()}})
        output.append({'source_domain': name, 'delta': par['delta'], 'rho': par['rho'], 'gap': par['gap'],
                       'raw_caps': caps, 'raw_budgets': budgets, 'dual_count': len(bank),
                       'coarse_five_group_error_maximum': max(row['five_group_error_upper'] for row in priced.values()),
                       'five_group_error_maximum': maximum,
                       'maximizing_dual_keys': [key for key in sorted(signed)
                                               if signed[key]['accepted_five_group_error_upper'] == maximum],
                       'complete_heavy_controllers': controllers})
    return encode({'schema': 'erdos7-selected-deletion-mask-row-transport-v1', 'source_sha256': pins,
                   'included_constraints': {'E5_totals': 5, 'marked_marginals': 8, 'fixed_H': 5,
                                            'forbidden_slots': 15, 'mask_links': 400},
                   'exact_aggregation_rows': 25, 'domains': output,
                   'scope': 'Five E5 row groups only, with one actual source and one residual budget. Prices are evaluated on all2060 existing223 rational duals, not a new off-face objective certificate. Other inherited216 constraints, retained135/125 constraints, pruning candidates, objective and complete-tail changes remain separate obligations. No new K comparison, global improvement, Lean verification or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('e5_row_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact five-group row-transport prices')
    for row in result['domains']:
        print(row['source_domain']+': five-group error maximum='+str(float(F(row['five_group_error_maximum'])))+'.')
    print('PASS: actual E5 row-transport prices; remaining off-face obligations are not included.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
