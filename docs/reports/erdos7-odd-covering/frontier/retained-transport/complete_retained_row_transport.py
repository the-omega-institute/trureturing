#!/usr/bin/env python3
"""Transport every row of the two retained135/125 dual banks.

This prices the complete LP constraint residual, not the infinite tails,
pruned alternatives, or the complete off-face52-cost comparison.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/complete_retained_row_transport.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/retained-transport/retained_pair_row_transport.py': '0baf4c40d0a715cad65e4b753609f5a231624b42c318d0d9020ae26c5ba27080', 'certificates/source_norms/retained-transport/retained_pair_row_transport.json': '2e6ef022a71cce9b2123e09667cfd68e8c6b14f15209b7a93c7667b29ba3c313', 'frontier/retained-transport/retained135125_survival_comparison.py': 'a44c625195c6edd91d5f66af2d9d717370660d02c65be3fd03930a13e7be4b88', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '2b3a347050126d9b40697b78d3f02cfb727c8bffc321fbbbdd1a18eec6590da1'}


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def complete_inventory(lp, original, bridge, wi, old_inventory, added_inventory):
    """Account for all7163 inequalities and56 equalities without overlaps."""
    require(lp.rows[:len(original.rows)] == original.rows and lp.rhs[:len(original.rhs)] == original.rhs
            and lp.equalities[:len(original.equalities)] == original.equalities
            and lp.erhs[:len(original.erhs)] == original.erhs,
            'Every inherited raw/survivor/deletion row retains its original meaning')
    face = [v for row in bridge.source_tables(2)[1] for v in row]
    for cell in range(25):
        require(lp.rows[cell] == {16*cell+m: F(1) for m in range(16)}
                and lp.rhs[cell] == face[cell], 'Original raw-node cap')
    for j, group in enumerate(bridge.GROUPS):
        require(lp.rows[25+j] == {16*c+m: F(1) for c in group for m in range(16)}
                and lp.rhs[25+j] == bridge.GROUP_MASSES[j], 'Original raw-group budget')
    require(lp.equalities[4] == {425+k: F(1) for k in range(400)}
            and lp.erhs[4] == F(53, 360)
            and lp.equalities[5] == {k: F(1) for k in range(400)}
            and lp.erhs[5] == F(1, 4), 'Both signed actual mass equalities')
    coarse, root1 = old_inventory
    profiles, states = added_inventory
    moving_profiles = {profiles[5*c+3][0] for c in range(5)} | {profiles[s][1] for s in range(1, 5)}
    old_moving_profiles = ({28+s for s in range(1, 5)} | {78+s for s in range(1, 5)}
                          | {start+5*c+3 for start in (53, 103) for c in range(5)})
    moving = set(range(28)) | old_moving_profiles | set(range(132, 532)) | set(coarse)
    moving |= set(root1.values()) | set(range(576, 996)) | moving_profiles | {3448}
    moving |= {i for rows in states for i in rows}
    zero_price = set(range(532, 536))
    exact = set(range(28, 132))-old_moving_profiles
    exact |= {996, 3447} | set(range(3449, 7163))
    for cell, rows in enumerate(profiles):
        exact |= set(rows)-moving_profiles
        for mask in range(16):
            start = 997+98*cell+2+6*mask
            exact |= {start, start+1}
    require(not (moving & exact or moving & zero_price or exact & zero_price)
            and moving | exact | zero_price == set(range(7163)), 'Exhaustive disjoint inequality inventory')
    eq_moving = {5} | set(range(6, 21)) | set(range(46, 54))
    eq_exact = set(range(4)) | set(range(21, 46)) | {54, 55}
    require(not (eq_moving & eq_exact) and eq_moving | eq_exact | {4} == set(range(56)),
            'Exhaustive equality inventory with the measured zero survivor price')
    return {'inequalities': {'transported': len(moving), 'exact': len(exact), 'zero_price': len(zero_price)},
            'equalities': {'transported': len(eq_moving), 'exact': len(eq_exact), 'zero_price': 1}}


def price_record(record, inherited, parameters, caps, budgets, bridge):
    """Add raw caps, profiles and positive raw mass before the shared support."""
    y = {int(k): F(v) for k, v in record['nonzero_inequality_duals'].items()}
    z = list(map(F, record['equality_duals']))
    get = lambda i: y.get(i, F(0))
    require(len(z) == 56 and all(0 <= i < 7163 and v >= 0 for i, v in y.items()), 'Canonical complete dual')
    require(all(get(i) == 0 for i in range(532, 536)) and z[4] == 0 and z[5] >= 0,
            'This bank has zero old survivor-cap and survivor-mass prices; nonnegative raw mass')
    d, rho, gap = [parameters[k] for k in ('delta', 'rho', 'gap')]
    profiles = [d/450*max(get(start+s) for s in range(1, 5)) for start in (28, 78)]
    profiles += [max(parameters['v0' if c < 2 else 'v1']*get(start+5*c+3)/den
                     for c in range(5)) for start, den in ((53, 27), (103, 81))]
    source = F(inherited['combined_source_upper'])+sum(profiles)
    node = list(map(F, inherited['common_raw_node_prices']))
    primitive = {k: F(v) for k, v in inherited['primitive_prices'].items()}
    require(len(node) == 25 and len(primitive) == 7 and min(primitive.values()) >= 0, 'One existing joint field')
    base_prices = [get(i)+get(25+(0 if i < 5 else 1 if i < 10 else 2))+z[5] for i in range(25)]
    face = [v for row in bridge.source_tables(2)[1] for v in row]
    face_subtraction = sum(get(i)*face[i] for i in range(25))
    face_subtraction += sum(get(25+j)*v for j, v in enumerate(bridge.GROUP_MASSES))+z[5]/4
    vertices, witnesses = [], []
    for q5, q15 in ((F(0), F(0)), (rho/gap, F(0)), (F(0), rho/gap)):
        coefficients = [base_prices[i]+node[i]*(d/5*int(i//5 != 0)+q5*int(i%5 == 4)
                            +q15*int(i//5 >= 2 and i%5 == 4)) for i in range(25)]
        raw, witness = bridge.lp_bound(coefficients, caps, budgets)
        raw -= face_subtraction
        residual = rho-gap*(q5+q15)
        require(residual >= 0, 'Only the common residual is spent')
        # raw and the complete residual upper may legitimately be negative.
        value = source+raw+residual*max(primitive.values())
        vertices.append({'q': [q5, q15], 'signed_raw_transport': raw, 'complete_row_error_upper': value})
        witnesses.append(witness)
    return {'combined_source_upper': source, 'old_profile_source_uppers_25_75_27_81': profiles,
            'raw_base_prices': base_prices, 'raw_face_subtraction': face_subtraction, 'raw_mass_price': z[5],
            'primitive_prices': primitive, 'common_raw_node_prices': node,
            'common_atom_fields_sha256': inherited['common_atom_fields_sha256'], 'triangle_vertices': vertices,
            'complete_row_error_upper': max(row['complete_row_error_upper'] for row in vertices)}, witnesses


def calculate(base):
    require(PINS, 'Final audited source pins are required')
    io = module('complete_retained_io', base/'certificate_io.py')
    read = lambda rel: json.loads(io.read_artifact_bytes(base/rel))
    parent, heavy, survival = [read(io.named_artifact(base/'certificates/source_norms', name + '.json').relative_to(base).as_posix()) for name in (
        'retained_pair_row_transport', 'retained135125_heavy_comparison', 'retained135125_survival_comparison')]
    pins = dict(PINS)
    for doc in (parent, heavy, survival):
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('complete_retained_'+name, io.named_artifact(base/'frontier', name+'.py'))
    partial, exact, pair = map(load, ('retained_pair_row_transport', 'retained135_heavy_comparison', 'retained135125_heavy_comparison'))
    bridge, old, e5 = map(load, ('k_face_common_seven_hinges', 'joint_deletion_row_transport', 'selected_deletion_mask_row_transport'))
    banks = {'heavy': exact.decode_dual_bank(heavy['encoded_rational_duals'], 7163, 56),
             'survival': exact.decode_dual_bank(survival['rational_duals'], 7163, 56)}
    require([len(banks[k]) for k in ('heavy', 'survival')] == [6292, 2792], 'All9084 original rational certificates')
    pre, _, density, descendant = bridge.source_tables(2)
    wi = [int(5*w) for row in density for w in row]
    raw = load('joint_selected_source_comparison').RawSelectedLP(bridge)
    original = load('retained_deletion_heavy_comparison').RetainedDeletionLP(raw, wi)
    inventories, counts = [], []
    for branch in ('nested', 'disjoint'):
        oldlp = exact.lp_class(base)(original, wi, pre, branch)
        lp = pair.lp_class(base)(original, wi, pre, descendant, branch)
        require(lp.specification() == heavy['branch_lps'][branch] == survival['branch_lps'][branch], 'Same original branch matrix')
        require(lp.rows[:997] == oldlp.rows[:997] and lp.rhs[:997] == oldlp.rhs[:997]
                and lp.equalities[:54] == oldlp.equalities[:54] and lp.erhs[:54] == oldlp.erhs[:54],
                'All old222/223 row meanings are unchanged')
        e5.check_row_meanings(oldlp, wi)
        inventory = old.row_inventory(oldlp, wi), partial.new_inventory(lp, pre, descendant, wi)
        inventories.append(inventory)
        counts.append(complete_inventory(lp, original, bridge, wi, *inventory))
    require(inventories[0] == inventories[1] and counts[0] == counts[1], 'Both geometric alternatives fully accounted for')
    study = load('k_neighborhood_radius_study').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'Same source-domain guards')
    output = []
    for domain in parent['domains']:
        name = domain['source_domain']
        par, guards = study.get(name).parameters_and_guards(study)
        source = read(io.named_artifact(base/'certificates/source_norms', name + '.json').relative_to(base).as_posix())
        require(encode(guards) == source['guards'] and all(F(domain[k]) == par[k] for k in ('delta', 'rho', 'gap')),
                'The same208 domain and its complete guards')
        caps, budgets = [list(map(F, domain[k])) for k in ('raw_caps', 'raw_budgets')]
        require(encode(caps) == source['complete_heads']['uniform_caps']
                and encode(budgets) == source['complete_heads']['uniform_budgets'], 'Unchanged fixed raw feasible set')
        inherited_bank = partial.decode_price_bank(domain['encoded_price_bank'])
        require(set(inherited_bank) == set(banks['heavy']), 'Every229 heavy record is present')
        results = {}
        for kind, bank in banks.items():
            priced, maximum, maximum_keys, keep = {}, None, [], {}
            positive_mass = 0
            for number, (key, record) in enumerate(sorted(bank.items()), 1):
                if kind == 'heavy':
                    inherited = inherited_bank[key]
                else:
                    inherited, _ = partial.price_record(record, par, caps, budgets, bridge, old, e5, *inventories[0])
                result, witness = price_record(record, inherited, par, caps, budgets, bridge)
                priced[key] = result
                positive_mass += F(record['equality_duals'][5]) > 0
                value = result['complete_row_error_upper']
                if maximum is None or value > maximum:
                    maximum, maximum_keys, keep = value, [key], {key: witness}
                elif value == maximum:
                    maximum_keys.append(key)
                    keep[key] = witness
                if number % 1000 == 0:
                    print(name+' '+kind+': '+str(number)+'/'+str(len(bank))+' complete row prices.', flush=True)
            packed = partial.encode_price_bank(priced)
            require(partial.decode_price_bank(packed) == encode(priced), 'Every complete row record restored without loss')
            results[kind] = {'dual_count': len(bank), 'positive_raw_mass_prices': positive_mass,
                'zero_raw_mass_prices': len(bank)-positive_mass, 'zero_old_survivor_cap_prices': 4*len(bank),
                'zero_survivor_mass_prices': len(bank), 'complete_row_error_maximum': maximum,
                'maximizing_dual_keys': maximum_keys, 'encoded_price_bank': packed,
                'maximizing_raw_primal_dual_witnesses': keep}
        output.append({'source_domain': name, 'delta': par['delta'], 'rho': par['rho'], 'gap': par['gap'],
                       'raw_caps': caps, 'raw_budgets': budgets, 'banks': results})
    return encode({'schema': 'erdos7-complete-retained-row-transport-v1', 'source_sha256': pins,
                   'constraint_inventory': counts[0], 'domains': output,
                   'scope': 'All7163 inequalities and56 equalities of every6292 heavy and2792 survival fixed dual are transported or accounted for exactly. Raw caps, group budgets, positive raw mass and link-density errors use one raw support; all deletion errors use one W and one seven-coordinate residual. Complete infinite tails, pruned alternatives and the52-cost consumer are separate. No complete off-face/global K, Lean verification or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('complete_retained_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete row-transport certificate')
    for domain in result['domains']:
        for kind, bank in domain['banks'].items():
            print(domain['source_domain']+' '+kind+': row error='+str(float(F(bank['complete_row_error_maximum']))))
    print('PASS: complete retained-row transportation; whole tails and pruning remain separate.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
