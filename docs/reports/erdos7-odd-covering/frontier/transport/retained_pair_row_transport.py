#!/usr/bin/env python3
"""Merge2493 old-deletion and retained135/125 row residuals on one budget.

The remaining inherited constraints, tails and complete consumer are separate.
No original head/projection scan or numerical optimizer is run here.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/retained_pair_row_transport.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/transport/joint_deletion_row_transport.py': '22eea33556056edb038580598002e32c74d4cfa9297a6c07c4bfc2ae34469d3d', 'certificates/source_norms/retained-transport/joint_deletion_row_transport.json': '6c5585a5f885caeebb906f28dd5152aba9ee943d9771b8649f23637b83a17cfc', 'frontier/transport/retained135125_heavy_comparison.py': '5e7a8bdd7ee1e93afd3115c80a8792d0afbf035ac50be715cf69631b75c70ff5', 'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': '98195f65f9d5acc4a27b8275952488b928e5204c56871e9a41cf4f32cf0e4ff6', 'profile-notes/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': 'cbe1fc88855354bd58e7a11ff22574bd8f9f9f94dceb57612c3ac8b1d943df17', 'profile-notes/transport/195-the-complete-source-comparison-extends-beyond-the-old-radius-domain.md': '4ce83eb8dce7127273b13d431f23d608eed3e152218a6eaf57406c60e339b991', 'profile-notes/transport/208-the-expanded-seven-survival-bound-covers-both-wide-source-domains.md': '9beb7e1c7eb5b006d896927b536d4a85a2b11b39ad16025941907762a31ad5e2', 'profile-notes/transport/225-two-original-tests-share-the-complete-retained-bridge.md': 'c0fb6383f17d2e9550481b98c64796eff4e9c2ef2b323b456911a1610047dfaf', 'profile-notes/transport/227-the-actual-deletion-mask-rows-have-one-off-face-error-budget.md': '5f755984495bf3a0229f60c597b6454beed932fe6113a93884e7f74e4c0ef29b'}


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


def _hash(value):
    return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def encode_price_bank(bank):
    """Keep every field; intern rational strings and share the record structure."""
    bank = encode(bank)
    require(isinstance(bank, dict) and bank and all(_hash(key) for key in bank), 'Canonical nonempty price bank')
    template, flattened, rationals = None, [], set()
    for key, record in sorted(bank.items()):
        require(isinstance(record, dict) and _hash(record.get('common_atom_fields_sha256')), 'Complete price record and field hash')
        values = []

        def shape(value, path=()):
            if path == ('common_atom_fields_sha256',):
                return '$hash'
            if isinstance(value, dict):
                return {k: shape(v, path+(k,)) for k, v in value.items()}
            if isinstance(value, list):
                return [shape(v, path+(i,)) for i, v in enumerate(value)]
            require(isinstance(value, str) and str(F(value)) == value, 'Canonical rational field')
            index = len(values)
            values.append(value)
            return index

        current = shape(record)
        if template is None:
            template = current
        require(current == template, 'One complete common field structure')
        rationals.update(values)
        flattened.append((key, record['common_atom_fields_sha256'], values))
    table = sorted(rationals)
    indices = {value: str(i) for i, value in enumerate(table)}
    return {'codec': 'retained-price-template-rationals-v1', 'template': template,
            'field_count': len(flattened[0][2]), 'record_count': len(flattened),
            'rational_table': [' '.join(table[i:i+128]) for i in range(0, len(table), 128)],
            'rows': [key+' '+digest+' '+','.join(indices[v] for v in values)
                     for key, digest, values in flattened]}


def decode_price_bank(encoded):
    """Return dual_key -> original complete record, including its W-field hash."""
    require(isinstance(encoded, dict) and set(encoded) == {
        'codec', 'template', 'field_count', 'record_count', 'rational_table', 'rows'}
        and encoded['codec'] == 'retained-price-template-rationals-v1', 'Exact price codec fields')
    count, template = encoded['field_count'], encoded['template']
    require(type(count) is int and count > 0 and isinstance(template, dict)
            and template.get('common_atom_fields_sha256') == '$hash', 'Complete field template')
    leaves, hashes = [], []

    def validate(value, path=()):
        if isinstance(value, dict):
            for k, v in value.items():
                require(isinstance(k, str), 'String record key')
                validate(v, path+(k,))
        elif isinstance(value, list):
            for i, v in enumerate(value):
                validate(v, path+(i,))
        elif value == '$hash':
            hashes.append(path)
        else:
            require(type(value) is int, 'Integer rational-field address')
            leaves.append(value)

    validate(template)
    require(leaves == list(range(count)) and hashes == [('common_atom_fields_sha256',)],
            'Every rational field exactly once and one independent hash column')
    blocks = encoded['rational_table']
    require(isinstance(blocks, list) and blocks and all(isinstance(row, str) for row in blocks), 'Nonempty rational table')
    pieces = [row.split(' ') for row in blocks]
    require(all(len(row) == 128 for row in pieces[:-1]) and 1 <= len(pieces[-1]) <= 128, 'Canonical rational table blocks')
    table = [v for row in pieces for v in row]
    require(table == sorted(set(table)) and all(str(F(v)) == v for v in table), 'Unique canonical rational strings')
    rows = encoded['rows']
    require(type(encoded['record_count']) is int and encoded['record_count'] > 0
            and isinstance(rows, list) and len(rows) == encoded['record_count'], 'Every complete record is present')
    result, used, previous = {}, set(), ''
    for row in rows:
        require(isinstance(row, str), 'Canonical encoded row')
        pieces = row.split(' ')
        require(len(pieces) == 3, 'Independent key, hash and numerical columns')
        key, digest, packed = pieces
        require(_hash(key) and _hash(digest) and previous < key, 'Sorted unique dual keys and exact field hashes')
        tokens = packed.split(',')
        require(len(tokens) == count and all(v and v.isascii() and v.isdecimal()
                and str(int(v)) == v for v in tokens), 'Canonical complete rational index vector')
        vector = list(map(int, tokens))
        require(all(0 <= i < len(table) for i in vector), 'Every rational index in range')
        used.update(vector)

        def restore(value):
            if isinstance(value, dict):
                return {k: restore(v) for k, v in value.items()}
            if isinstance(value, list):
                return [restore(v) for v in value]
            return digest if value == '$hash' else table[vector[value]]

        result[key] = restore(template)
        previous = key
    require(used == set(range(len(table))), 'No unused rational table data')
    return result


def new_inventory(lp, pre, descendant, wi):
    require(lp.nvars == 3705 and len(lp.rows) == 7163 and len(lp.equalities) == 56,
            'Complete original225 dimensions')
    profile, state_rows = [], []
    for cell in range(25):
        c, s = divmod(cell, 5)
        start = 997+98*cell
        expected = {3675+cell: -pre[c][s]/27,
                    **{1275+400*a+16*cell+m: F(1) for a in (0, 2) for m in range(16)}}
        other = {3700+s: -descendant[c][s]/125,
                 **{1275+400*a+16*cell+m: F(1) for a in (1, 2) for m in range(16)}}
        require(lp.rows[start:start+2] == [expected, other] and lp.rhs[start:start+2] == [0, 0],
                'Both independent normalized raw profile rows')
        profile.append((start, start+1))
        for mask in range(16):
            k, row = 16*cell+mask, start+2+6*mask
            require(lp.rows[row] == {k: F(-1), **{1275+400*a+k: F(1) for a in range(3)}}
                    and lp.rows[row+1] == {425+k: F(-1), **{2475+400*a+k: F(1) for a in range(3)}},
                    'Both marked partitions remain exact')
            complement = {425+k: F(1), k: -F(wi[cell], 5)}
            for a in range(3):
                x, y = 1275+400*a+k, 2475+400*a+k
                require(lp.rows[row+2+a] == {y: F(1), x: -F(wi[cell], 5)},
                        'Each explicit actual survivor state')
                complement[y], complement[x] = F(-1), F(wi[cell], 5)
            require(lp.rows[row+5] == complement and lp.rhs[row:row+6] == [0]*6,
                    'The complement is the fourth actual state')
            state_rows.append(tuple(range(row+2, row+6)))
    for row, states, cap in ((3447, (0, 2), F(1, 135)), (3448, (1, 2), F(2, 625))):
        require(lp.rows[row] == {2475+400*a+k: F(1) for a in states for k in range(400)}
                and lp.rhs[row] == cap, 'Both original scalar survivor rows')
    for j, (label, states) in enumerate(((135, (0, 2)), (125, (1, 2)))):
        for bit, old in enumerate((25, 27, 75, 81)):
            row = 3449+4*j+bit
            require(lp.rows[row] == {1275+400*a+16*cell+m: F(1) for a in states
                    for cell in range(25) for m in range(16) if m & (1 << bit)}
                    and lp.rhs[row] == F(1, lcm(label, old)), 'Exact independent CRT row')
    require(lp.rows[3457] == {2075+k: F(1) for k in range(400)} and lp.rhs[3457] == F(1, 3375)
            and lp.unit_rows == list(range(3458, 7163)), 'Joint raw event and every unit row')
    for k, row in enumerate(lp.unit_rows):
        require(lp.rows[row] == {k: F(1)} and lp.rhs[row] == 1, 'An actual unit cap')
    require(lp.equalities[54:] == [{k: F(1) for k in range(3675, 3700)},
                                   {k: F(1) for k in range(3700, 3705)}]
            and lp.erhs[54:] == [1, 1], 'The retained profiles stay independent')
    return profile, state_rows


def price_record(record, parameters, caps, budgets, bridge, old_provider, e5, old_inventory, added_inventory):
    """Keep one raw field and one W field until the final shared-simplex maximum."""
    require(len(record['equality_duals']) == 56, 'All original225 equality prices')
    # The old routines read only eq0..53; their existing API expects one unused55th entry.
    adapter = {**record, 'equality_duals': record['equality_duals'][:55]}
    inherited = old_provider.price_record(adapter, parameters, caps, budgets, bridge, e5, old_inventory)
    prices = {int(k): F(v) for k, v in record['nonzero_inequality_duals'].items()}
    require(all(0 <= k < 7163 and v >= 0 for k, v in prices.items()), 'Canonical nonnegative225 row prices')
    get = lambda i: prices.get(i, F(0))
    profile, states = added_inventory
    coarse, _ = old_inventory
    d, rho, gap = [parameters[k] for k in ('delta', 'rho', 'gap')]
    theta = get(3448)
    # Each retained profile is its own simplex. Only five Q rows and four cell0 rows move.
    profile135 = max(get(profile[5*c+3][0])*parameters['v0' if c < 2 else 'v1']/27 for c in range(5))
    profile125 = d/2250*max(get(profile[s][1]) for s in range(1, 5))
    c125 = theta*479*d/90000
    raw_prices, overlap = [F(0)]*25, F(0)
    field_digest = sha256()
    for atom, rows in enumerate(states):
        cell = atom//16
        old_links = get(132+atom)+get(596+atom)+get(coarse[cell])
        joint = [old_links+get(row) for row in rows]
        raw_prices[cell] = max(raw_prices[cell], *joint)
        wfield = [value+(theta if state in (1, 2) else 0) for state, value in enumerate(joint)]
        overlap = max(overlap, *wfield)
        field_digest.update(json.dumps(encode([atom, joint, wfield]), separators=(',', ':')).encode())
    require(all(a >= b for a, b in zip(raw_prices, inherited['common_link_atom_price_maxima'])),
            'Combine the old and new atom fields before taking node maxima')
    primitive = dict(inherited['primitive_prices'])
    old_overlap = primitive['union_overlap']
    primitive['union_overlap'] = overlap
    primitive['pure_three_27_defect'] += theta
    primitive['pure_three_later_defect'] += theta
    require(len(primitive) == 7 and overlap >= old_overlap and min(primitive.values()) >= 0,
            'The one common W and all seven nonnegative primitive prices')
    largest = max(primitive.values())
    source = d*inherited['E5_source_price']+inherited['E3_source_upper']+profile135+profile125+c125
    vertices, witnesses = [], []
    for q5, q15 in ((F(0), F(0)), (rho/gap, F(0)), (F(0), rho/gap)):
        coefficients = [u*(d/5*int(cell//5 != 0)+q5*int(cell % 5 == 4)
                          +q15*int(cell//5 >= 2 and cell % 5 == 4)) for cell, u in enumerate(raw_prices)]
        raw, witness = bridge.lp_bound(coefficients, caps, budgets)
        residual = rho-gap*(q5+q15)
        value = source+raw+residual*largest
        require(residual >= 0 and value >= 0, 'One nonnegative residual after wrong-slot spending')
        vertices.append({'q': [q5, q15], 'raw_transport': raw, 'joint_row_error_upper': value})
        witnesses.append(witness)
    result = {'E3_source_upper': inherited['E3_source_upper'], 'E5_source_price': inherited['E5_source_price'],
              'profile_source_uppers': [profile135, profile125], 'retained125_cap_price': theta,
              'retained125_source_upper': c125, 'combined_source_upper': source,
              'primitive_prices': primitive, 'remaining_residual_price': largest,
              'common_raw_node_prices': raw_prices, 'common_atom_fields_sha256': field_digest.hexdigest(),
              'triangle_vertices': vertices, 'joint_row_error_upper': max(row['joint_row_error_upper'] for row in vertices)}
    return result, witnesses


def complete_tail_checks():
    N3, N9, D, h, h1, em = map(F, ('5/36', '1/12', '3/4', '1/2', '1/3', '1/9'))
    C = N3+N9+D/18+(h+h1+em)/4+F(1, 72)
    seven = C/5-F(6, 35)*(N3+h/5+N9+h1/5)-F(6, 245)*(N3+h/5)
    coefficients = [F(1, 245), F(1, 35), F(1, 90), F(53, 4900), F(11, 700), F(1, 20)]
    require(seven == sum(a*v for a, v in zip(coefficients, (N3, N9, D, h, h1, em)))+F(1, 360)
            == F(2669, 88200), 'Complete positive six-projection tail and exact face specialization')
    five = [F(7, 10)/3**5/(1-F(1, 3)), F(2, 5)/5**4/(1-F(1, 5)),
            F(4, 15)/5**3/(1-F(1, 5)), F(4, 45)/5**2/(1-F(1, 5)), F(7, 1080)]
    require(sum(five) == F(7579, 405000) and F(1, 72)-F(1, 135) == F(7, 1080)
            and F(13, 90)/125+F(1, 240) == F(479, 90000), 'Complete punctured tails and125 source slope')
    return {'zero7_omitted_depths_t_ge2': {'pure3': [3, 4], 'pure5': [2, 3], 'root5': [2], 'cell5': []},
            'remaining_mixed_cap': F(7, 1080), 'face_zero7_t_ge2': sum(five),
            'positive7_coefficient_order': ['N3', 'N9', 'D', 'h', 'h1', 'max_eta'],
            'positive7_coefficients': coefficients, 'positive7_constant': F(1, 360),
            'face_positive7': seven, 'included_in_priced_row_error': False}


def calculate(base):
    require(PINS, 'Pinned source closure')
    io = module('pair_rows_io', base/'certificate_io.py')
    read = lambda rel: json.loads(io.read_artifact_bytes(base/rel))
    parent = read('certificates/source_norms/retained-transport/joint_deletion_row_transport.json')
    prior = read('certificates/source_norms/retained-transport/retained135125_heavy_comparison.json')
    pins = dict(PINS)
    for doc in (parent, prior):
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent logical source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('pair_rows_'+name, base/'frontier'/(name+'.py'))
    bridge = load('k_face_common_seven_hinges')
    old_provider, e5 = load('transport/joint_deletion_row_transport'), load('transport/selected_deletion_mask_row_transport')
    exact, pair = load('transport/retained135_heavy_comparison'), load('transport/retained135125_heavy_comparison')
    bank = exact.decode_dual_bank(prior['encoded_rational_duals'], 7163, 56)
    require(len(bank) == 6292, 'Every6292 published225 rational dual')
    pre, _, density, descendant = bridge.source_tables(2)
    wi = [int(5*w) for row in density for w in row]
    raw = load('transport/joint_selected_source_comparison').RawSelectedLP(bridge)
    original = load('transport/retained_deletion_heavy_comparison').RetainedDeletionLP(raw, wi)
    inventories = []
    for branch in ('nested', 'disjoint'):
        oldlp = exact.lp_class(base)(original, wi, pre, branch)
        newlp = pair.lp_class(base)(original, wi, pre, descendant, branch)
        require(newlp.rows[:997] == oldlp.rows[:997] and newlp.rhs[:997] == oldlp.rhs[:997]
                and newlp.equalities[:54] == oldlp.equalities[:54] and newlp.erhs[:54] == oldlp.erhs[:54],
                'Every inherited222 row and equality is unchanged in225')
        require(newlp.specification() == prior['branch_lps'][branch], 'Bound to the certified225 matrix')
        e5.check_row_meanings(oldlp, wi)
        inventories.append((old_provider.row_inventory(oldlp, wi), new_inventory(newlp, pre, descendant, wi)))
    require(inventories[0] == inventories[1], 'Both original geometries have the same priced row meanings')
    old_inventory, added_inventory = inventories[0]
    study = load('k_neighborhood_radius_study').Study(base)
    require(all(pins.get(path) == pin for path, pin in study.pins.items()), 'Same guarded source providers')
    domains = []
    for domain, provider in zip(parent['domains'], (study.get('wide_fresh_full_slot_source_comparison'), study.get('transport/extended_source_bridge_comparison')), strict=True):
        name = domain['source_domain']
        par, guards = provider.parameters_and_guards(study)
        doc = read('certificates/source_norms/'+name+'.json')
        require(encode(guards) == doc['guards'] and par['delta'] == F(domain['delta'])
                and par['rho'] == F(domain['rho']) and par['gap'] == F(domain['gap']), 'The same208 whole-domain guards')
        caps, budgets = [list(map(F, doc['complete_heads'][key])) for key in ('uniform_caps', 'uniform_budgets')]
        expected = []
        face = [v for row in bridge.source_tables(2)[1] for v in row]
        for i, cap in enumerate(face):
            c, s = divmod(i, 5)
            excluded = s == 0 or (s == 1 and c >= 2) or (s == 2 and c == 2)
            addition = F(0) if excluded or c != 0 else par['delta']/90
            if not excluded and s == 3:
                addition += par['v0']/18 if c == 0 else par['v0']/9 if c == 1 else par['v1']/9
            expected.append(cap+addition)
        require(caps == expected and budgets == [a+b for a, b in zip(bridge.GROUP_MASSES, par['budget_increments'])],
                'Unchanged fixed raw capacities and group budgets')
        priced, witness_bank = {}, {}
        controller_keys = {key for row in prior['heavy_results']
                           for key in row['scan']['maximizing_witness']['nested_disjoint_dual_keys'].values()}
        maximum, maximum_keys = F(-1), []
        for number, (key, record) in enumerate(sorted(bank.items()), 1):
            result, witnesses = price_record(record, par, caps, budgets, bridge,
                                             old_provider, e5, old_inventory, added_inventory)
            priced[key] = result
            value = result['joint_row_error_upper']
            if key in controller_keys or value >= maximum:
                witness_bank[key] = witnesses
            if value > maximum:
                maximum, maximum_keys = value, [key]
            elif value == maximum:
                maximum_keys.append(key)
            if number % 1000 == 0:
                print(name+': priced '+str(number)+'/'+str(len(bank))+' original duals.', flush=True)
        keep = controller_keys | set(maximum_keys)
        encoded_prices = encode_price_bank(priced)
        require(decode_price_bank(encoded_prices) == encode(priced),
                'Lossless recovery of every complete priced record and field hash')
        controllers = [{'cost': row['index'], 'branches': {
            branch: {'dual_key': key, 'joint_row_transport': priced[key]}
            for branch, key in row['scan']['maximizing_witness']['nested_disjoint_dual_keys'].items()}}
            for row in prior['heavy_results']]
        domains.append({'source_domain': name, 'delta': par['delta'], 'rho': par['rho'], 'gap': par['gap'],
                        'raw_caps': caps, 'raw_budgets': budgets, 'dual_count': len(bank),
                        'joint_row_error_maximum': maximum, 'maximizing_dual_keys': maximum_keys,
                        'complete_heavy_controllers': controllers, 'encoded_price_bank': encoded_prices,
                        'selected_raw_primal_dual_witnesses': {key: witness_bank[key] for key in sorted(keep)}})
    return encode({'schema': 'erdos7-retained-pair-row-transport-v2', 'source_sha256': pins,
                   'inherited_priced_constraints': 883, 'added_priced_constraints': 1610,
                   'added_constraint_classes': {'moving_profile_rows': 9, 'state_density_rows': 1600, 'retained125_cap': 1},
                   'added_zero_error_inequalities': 4556, 'exact_added_profile_equalities': 2,
                   'exact_old_aggregation_rows': 25, 'priced_constraint_count': 2493,
                   'complete_tail_interface': complete_tail_checks(), 'domains': domains,
                   'scope': 'One common raw-source field, one W field and one seven-coordinate residual for883 old deletion/link rows and1610 moving retained135/125 rows. Every6292 original225 dual is priced on both208 domains. Other inherited raw/selected constraints, signed mass, all tails and pruning still require compatible complete transport. No complete off-face or global K, Lean verification or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('pair_rows_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact combined2493-row certificate')
    for row in result['domains']:
        print(row['source_domain']+': partial2493-row error='+str(float(F(row['joint_row_error_maximum'])))+'.')
    print('PASS: all6292 duals share the merged raw/W fields and seven-coordinate budget; complete transport remains.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
