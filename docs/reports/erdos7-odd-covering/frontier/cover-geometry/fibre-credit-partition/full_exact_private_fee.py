"""One fixed full-P evaluation of the 2017 old supports not evaluated in145/146.

Only saved146/145/144 JSON is read. Saved146 joint P products and positive
individual factors supply same-cell subset quotients. The nineteen earlier
P support fees and separate shallow G_P are reused without optimization.
No primitive product, K fee, producer, control, source search or continuation
is evaluated. Head depth blocks and same-address free root sums stay fixed.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys


HEADS = (5, 7)
PRIVATE = (11, 13, 17, 19, 23, 29, 31, 37, 41)
ROOTS = (1, 2)
CASES = ('FC110', 'FC131')
FULL_MASK = (1 << len(PRIVATE)) - 1
CELL_ORDER = tuple((r, i, j) for r in ROOTS for i in range(5) for j in range(7))
HEAD_CLASSES = ((), (5,), (7,), (5, 7))
BLOCKS = {
    (): ((),), (5,): ((0,), (1,)), (7,): ((0,), (1,)),
    (5, 7): ((0, 0), (1, 0), (0, 1), (1, 1)),
}
ADDRESSES = {
    (): ((),), (5,): tuple((i,) for i in range(5)),
    (7,): tuple((j,) for j in range(7)),
    (5, 7): tuple((i, j) for i in range(5) for j in range(7)),
}
TABLE_HASHES = {
    'FC110': '5540ef30fbf02147b4c4687e80e4e617b96cdd58f41a706b8a3f460793ce0a70',
    'FC131': '7ff231d7a8c95f0a7bc9e5181fd4c7099e816f985403325fdd608dd176ce37c6',
}
INPUT146_SHA256 = '5fa2dd84a74f115d1e78bab45dbe2ea29f187470504303727028b17121233cad'
INPUT145_SHA256 = '4ae73a9a4e17120630602fbef88ffccdc74f34a33ad3f7ac878c633c656aaa04'
INPUT144_SHA256 = 'bad5b8c850742e0bb7277ea316bf5e96dc06f963317a28033cc6ed8e1ebb06bb'
INPUT143_SHA256 = 'f500e063cf43ffee76f9d749644c8eeed8d78a47b66904aad42f609a45b312b1'
SCORES_SHA256 = '4e824f35c5f921cdacee1cb462cf3387f5524978e859c65460e45cb3fcb5f8c4'
DESIGN_SHA256 = '9b7c69c7ff5aad753456b83c78c0b6e53cb5b9fe6354efe2532e4fcb66866f00'
CHECKS = 0


def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def read_pinned(path, expected):
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    require(actual == expected, 'pinned saved input identity: ' + str(path))
    return json.loads(raw), {
        'file': str(path), 'sha256': actual,
        'hash_role': 'saved input identity, not mathematical premise',
    }


def head_key(heads):
    return ','.join(str(h) for h in heads) if heads else 'none'


def build_cap_cache():
    # This complete supported-private depth coefficient is shared by the tables.
    caps = [F(1)]
    updates = 0
    for mask in range(1, FULL_MASK + 1):
        bit = mask & -mask
        index = bit.bit_length() - 1
        caps.append(caps[mask ^ bit] / (PRIVATE[index] - 2))
        updates += 1
    require(updates == 511 and len(caps) == 512, 'one fixed supported-cap cache')
    return caps, updates


def read_joint_source(case146):
    records = case146['joint_cells']
    indexed = {(v['root'], v['head5_row'], v['head7_row']): v for v in records}
    require(len(records) == 70 and set(indexed) == set(CELL_ORDER),
            'exactly the seventy fixed physical root/head cells')
    w = {r: {h: [None] * h for h in HEADS} for r in ROOTS}
    products, factors = [], []
    for r, i, j in CELL_ORDER:
        cell = indexed[r, i, j]
        for h, row, field in ((5, i, 'head5_mass'), (7, j, 'head7_mass')):
            value = F(cell[field])
            if w[r][h][row] is None:
                w[r][h][row] = value
            require(w[r][h][row] == value, 'one physical row law across the other head coordinate')
        raw_factors = cell['private_factors']
        require(tuple(v['private_prime'] for v in raw_factors) == PRIVATE,
                'all and only nine fixed private factors at this same cell')
        p = [F(v['P']) for v in raw_factors]
        require(all(0 < value <= 1 for value in p), 'saved P factors are strictly positive')
        full_product = F(cell['P_product'])
        require(0 < full_product <= 1, 'saved full P product is positive')
        # Its nine-factor identity is reused from the audited saved146 artifact.
        # No primitive multiplication and no K field is used here.
        products.append(full_product)
        factors.append(p)
    for r in ROOTS:
        for h in HEADS:
            c_h = F(h - 1, h - 2)
            require(all(value is not None and value >= 0 for value in w[r][h]),
                    'complete nonnegative head row law')
            require(all(value == 0 or F(1, h) <= value <= c_h / h for value in w[r][h]),
                    'fixed canonical live-row bounds')
            require(all(min(c_h / h, value) == value for value in w[r][h]),
                    'head depth one uses its row mass once')
            require(all(min(c_h / (h * h), value)
                        == c_h / (h * h) * int(value > 0) for value in w[r][h]),
                    'head tail saturates at depth two with exact zero masks')
    return w, products, factors


def build_quotient_cache(products, factors):
    quotients = [products]
    updates = 0
    for mask in range(1, FULL_MASK + 1):
        bit = mask & -mask
        index = bit.bit_length() - 1
        previous = quotients[mask ^ bit]
        values = []
        for cell_index in range(70):
            value = previous[cell_index] / factors[cell_index][index]
            require(0 < value <= 1, 'same-cell unsupported product quotient lies in (0,1]')
            values.append(value)
            updates += 1
        quotients.append(values)
    require(updates == 35770 and len(quotients) == 512,
            'fixed quotient-cache operation count')
    require(all(value == 1 for value in quotients[FULL_MASK]),
            'empty unsupported-private product is exactly one')
    return quotients, updates


def read_cached19(case145, case146):
    pairs = case145['pair_supports']
    indexed = {(v['head'], v['private_prime']): v for v in pairs}
    require(len(pairs) == 18 and set(indexed) == {(h, q) for h in HEADS for q in PRIVATE},
            'exactly the eighteen earlier deep head/private P supports')
    cached = []
    sum_f = sum_s = F()
    for h in HEADS:
        for q in PRIVATE:
            pair = indexed[h, q]
            p = pair['coefficients']['P']
            fee_f, fee_s = F(p['free_pair_fee']), F(p['selected_pair_fee'])
            require(fee_f >= 0 and fee_s >= 0, 'cached complete pair fees are nonnegative')
            require(F(pair['supported_private_cap_sum']) == F(1, q - 2)
                    and F(pair['complete_head_tail_factor']) == F(1, h * (h - 2)),
                    'cached pair retains its complete original depth domains')
            cached.append({
                'supported_heads': [h], 'private_primes': [q],
                'head_depth_lower': 2, 'private_depth_lower': 1,
                'free_fee_P': str(fee_f), 'selected_fee_P': str(fee_s), 'read_from': '145',
            })
            sum_f += fee_f
            sum_s += fee_s
    require(sum_f == F(case145['deep_pair_totals']['P']['free'])
            and sum_s == F(case145['deep_pair_totals']['P']['selected']),
            'adding saved pair fees reproduces the saved P aggregate without optimization')
    pair57 = case146['single_support_57_totals']['P']
    fee57_f, fee57_s = F(pair57['free']), F(pair57['selected'])
    require(fee57_f >= 0 and fee57_s >= 0, 'cached two-head P coefficient is nonnegative')
    cached.append({
        'supported_heads': [5, 7], 'private_primes': [],
        'head_depth_lower': 1, 'free_fee_P': str(fee57_f),
        'selected_fee_P': str(fee57_s), 'read_from': '146',
    })
    require(len(cached) == 19, 'all nineteen cached P supports are read once')
    return cached, sum_f + fee57_f, sum_s + fee57_s


def integrate_head_tables(w, outside, counts):
    tables = {heads: {} for heads in ((), (5,), (7,))}
    for r in ROOTS:
        offset = (r - 1) * 35
        t5 = [sum((w[r][7][j] * outside[offset + i * 7 + j] for j in range(7)), F())
              for i in range(5)]
        t7 = [sum((w[r][5][i] * outside[offset + i * 7 + j] for i in range(5)), F())
              for j in range(7)]
        t0 = sum((w[r][5][i] * t5[i] for i in range(5)), F())
        counts['head_weighted_summands'] += 75
        tables[()][r], tables[(5,)][r], tables[(7,)][r] = [t0], t5, t7
    return tables


def evaluate_support(heads, mask, supported_cap, table, w, counts):
    addresses = ADDRESSES[heads]
    d = {5: F(1, 15), 7: F(1, 35)}
    block_results = []
    support_f = support_s = F()
    class_counts = counts['by_heads'][head_key(heads)]
    for alpha in BLOCKS[heads]:
        depth_weight = F(1)
        for h, is_deep in zip(heads, alpha):
            if is_deep:
                depth_weight *= d[h]
        values = {}
        for r in ROOTS:
            root_values = []
            for index, address in enumerate(addresses):
                head_factor = F(1)
                for h, row, is_deep in zip(heads, address, alpha):
                    head_factor *= F(int(w[r][h][row] > 0)) if is_deep else w[r][h][row]
                value = table[r][index] * head_factor / 2
                require(value >= 0, 'root/address candidate is nonnegative')
                root_values.append(value)
                counts['root_address_candidates'] += 1
                class_counts['root_address_candidates'] += 1
            values[r] = root_values
        # One physical supported-head address is kept before the two roots are added.
        free_values = [values[1][index] + values[2][index] for index in range(len(addresses))]
        free_max = max(free_values)
        selected_max = max(value for r in ROOTS for value in values[r])
        counts['free_address_sums'] += len(addresses)
        class_counts['free_address_sums'] += len(addresses)
        counts['prescribed_maxima'] += 2
        class_counts['prescribed_maxima'] += 2
        counts['depth_blocks'] += 1
        class_counts['depth_blocks'] += 1
        fee_f = supported_cap * depth_weight * free_max
        fee_s = supported_cap * depth_weight * selected_max
        support_f += fee_f
        support_s += fee_s
        block_results.append({
            'deep_tail_bits_in_head_order': list(alpha), 'depth_weight': str(depth_weight),
            'free_same_address_max': str(free_max), 'selected_root_address_max': str(selected_max),
            'free_block_fee': str(fee_f), 'selected_block_fee': str(fee_s),
            'free_maximizing_addresses': [list(address) for index, address in enumerate(addresses)
                                           if free_values[index] == free_max],
            'selected_maximizing_addresses': [
                {'root': r, 'head_rows': list(address)} for r in ROOTS
                for index, address in enumerate(addresses) if values[r][index] == selected_max
            ],
        })
    counts['new_supports'] += 1
    class_counts['new_supports'] += 1
    return {
        'supported_heads': list(heads), 'private_mask': mask,
        'supported_private_primes': [q for index, q in enumerate(PRIVATE) if mask & (1 << index)],
        'head_depth_lower': 1, 'private_depth_lower': 1,
        'complete_supported_private_cap': str(supported_cap),
        'free_fee_P': str(support_f), 'selected_fee_P': str(support_s),
        'blocks': block_results,
    }, support_f, support_s


def evaluate_case(name, case146, case145, case144, caps):
    require(F(case146['saved_score_J']) == F(case145['saved_score_J']) == F(case144['saved_score_J']),
            'same original J retained in all three saved cases')
    require(F(case146['saved_full_selected_S']) == F(case145['saved_full_selected_S'])
            == F(case144['saved_selected_fee_S']), 'same original selected total')
    g_p = F(case144['G_P'])
    require(g_p == F(case146['saved_shallow_G_P']) == F(case145['saved_shallow_G_P']),
            'separate shallow G_P is read unchanged')
    cached, cached_f, cached_s = read_cached19(case145, case146)
    w, products, factors = read_joint_source(case146)
    quotients, quotient_updates = build_quotient_cache(products, factors)
    count_keys = ('new_supports', 'depth_blocks', 'root_address_candidates',
                  'free_address_sums', 'prescribed_maxima')
    counts = {key: 0 for key in count_keys}
    counts['head_weighted_summands'] = 0
    counts['by_heads'] = {head_key(heads): {key: 0 for key in count_keys} for heads in HEAD_CLASSES}
    support_results = []
    contraction_records = [None] * (FULL_MASK + 1)
    rest_f = rest_s = F()
    for mask in range(1, FULL_MASK + 1):
        outside = quotients[mask]
        if mask.bit_count() >= 2:
            tables = integrate_head_tables(w, outside, counts)
            # Store each shared contraction once, not again in each support/block.
            contraction_records[mask] = {
                'T0': [str(tables[()][r][0]) for r in ROOTS],
                'T5': [[str(v) for v in tables[(5,)][r]] for r in ROOTS],
                'T7': [[str(v) for v in tables[(7,)][r]] for r in ROOTS],
            }
            for heads in ((), (5,), (7,)):
                result, fee_f, fee_s = evaluate_support(heads, mask, caps[mask], tables[heads], w, counts)
                support_results.append(result)
                rest_f += fee_f
                rest_s += fee_s
        # For both supported heads there is no unsupported-head integration.
        table57 = {r: outside[(r - 1) * 35:r * 35] for r in ROOTS}
        result, fee_f, fee_s = evaluate_support((5, 7), mask, caps[mask], table57, w, counts)
        support_results.append(result)
        rest_f += fee_f
        rest_s += fee_s
    expected = {
        'none': (502, 502, 1004, 502, 1004),
        '5': (502, 1004, 10040, 5020, 2008),
        '7': (502, 1004, 14056, 7028, 2008),
        '5,7': (511, 2044, 143080, 71540, 4088),
    }
    for key, expected_values in expected.items():
        require(tuple(counts['by_heads'][key][field] for field in count_keys) == expected_values,
                'fixed class-specific support/block/address counts: ' + key)
    require(tuple(counts[key] for key in count_keys) == (2017, 4554, 168180, 84090, 9108)
            and counts['head_weighted_summands'] == 75300 and len(support_results) == 2017,
            'complete prescribed new-support operation counts')
    old_rest = case146['old_inventory_replacement']
    old_rest_f, old_rest_s = F(old_rest['unchanged2017_free_fee']), F(old_rest['unchanged2017_selected_fee'])
    require(0 <= rest_f <= old_rest_f and 0 <= rest_s <= old_rest_s,
            'new P support totals do not exceed saved unchanged2017 K totals')
    total_f, total_s = cached_f + rest_f, cached_s + rest_s
    a_bar = F(case146['saved_group_mass'])
    old_margin = F(case146['new146_margin'])
    require(old_margin == a_bar - cached_f - old_rest_f - F(3, 2) * (cached_s + old_rest_s) - g_p / 2,
            'cached nineteen fees and saved2017 fees reproduce the same146 source accounting')
    gain_f, gain_s = old_rest_f - rest_f, old_rest_s - rest_s
    gain = gain_f + F(3, 2) * gain_s
    margin = a_bar - total_f - F(3, 2) * total_s - g_p / 2
    require(margin == old_margin + gain and gain >= 0 and old_margin > 0,
            'entire gain is the exact remaining-support replacement on one positive source')
    sign = 'positive' if margin > 0 else ('negative' if margin < 0 else 'zero')
    return {
        'case': name, 'saved_group_mass_Abar': str(a_bar), 'saved_shallow_G_P': str(g_p),
        'cached19_free_P': str(cached_f), 'cached19_selected_P': str(cached_s),
        'cached19_support_fees': cached,
        'new2017_free_P': str(rest_f), 'new2017_selected_P': str(rest_s),
        'saved2017_free_K': str(old_rest_f), 'saved2017_selected_K': str(old_rest_s),
        'full_free_P': str(total_f), 'full_selected_P': str(total_s),
        'gain_free': str(gain_f), 'gain_selected': str(gain_s),
        'weighted_margin_gain': str(gain), 'strict_gain': gain > 0,
        'saved146_margin': str(old_margin), 'new148_margin': str(margin), 'margin_sign': sign,
        'head_weights': {str(r): {str(h): [str(v) for v in w[r][h]] for h in HEADS} for r in ROOTS},
        'new_support_results': support_results,
        'outside_P_quotients_by_supported_private_mask': [[str(v) for v in row] for row in quotients],
        'quotient_format': 'mask-indexed arrays0..511; entries follow the top-level joint_cell_order; mask0 is the saved seed',
        'head_contractions_by_supported_private_mask': contraction_records,
        'contraction_format': 'null for masks of size below2; T0/T5/T7 use top-level root_order, then physical head-row order where present',
        'evaluation_counts': {
            **counts, 'same_cell_quotient_updates': quotient_updates,
            'primitive_products_formed': 0, 'cached_P_support_fees_reevaluated': 0,
            'K_support_fees_evaluated': 0, 'old_full_K_fee_evaluations': 0,
        },
        'interpretation': 'exact value of a full-P upper allowance on the same source; supported-cylinder, maxima and union-bound slack remain',
    }


def check_provenance(data146, data145, data144):
    require(all(set(data['cases']) == set(CASES) for data in (data146, data145, data144)),
            'exactly the two fixed source cases')
    require(data146['saved145_input']['sha256'] == INPUT145_SHA256
            and data145['saved_P_rows_input']['sha256'] == INPUT144_SHA256
            and data145['saved_K_rows_input']['sha256'] == INPUT143_SHA256,
            'saved computational dependency identities')
    require(data146['saved_scores_input']['sha256'] == SCORES_SHA256
            and data145['saved_J_F_S_input']['sha256'] == SCORES_SHA256
            and data144['saved_scores_input']['sha256'] == SCORES_SHA256,
            'same original saved score source without reading its producer')
    for name in CASES:
        require(data146['table_inputs'][name]['sha256']
                == data144['table_inputs'][name]['sha256'] == TABLE_HASHES[name],
                'same original primitive identity, carried by saved provenance only')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--saved146', type=Path, required=True)
    parser.add_argument('--saved145', type=Path, required=True)
    parser.add_argument('--saved144', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(bool(sys.flags.isolated) and bool(sys.flags.no_site)
            and bool(sys.flags.dont_write_bytecode), 'run only with python3 -I -S -B')
    require(args.output.is_absolute()
            and args.output.parent.resolve() == Path('/tmp').resolve()
            and args.output.name.startswith('e7_batch148_'),
            'output is an explicit batch148 path directly under /tmp')
    require(not args.output.exists(), 'refuse to overwrite a prior result')
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    data146, provenance146 = read_pinned(args.saved146, INPUT146_SHA256)
    data145, provenance145 = read_pinned(args.saved145, INPUT145_SHA256)
    data144, provenance144 = read_pinned(args.saved144, INPUT144_SHA256)
    check_provenance(data146, data145, data144)
    caps, cap_updates = build_cap_cache()
    cases = {}
    for name in CASES:
        cases[name] = evaluate_case(name, data146['cases'][name], data145['cases'][name],
                                    data144['cases'][name], caps)
        print(json.dumps({
            'event': 'case_complete', 'case': name, 'margin_sign': cases[name]['margin_sign'],
            'strict_gain': cases[name]['strict_gain'],
            'margin_decimal_display': float(F(cases[name]['new148_margin'])),
        }), flush=True)
    margins = [F(v['new148_margin']) for v in cases.values()]
    both_positive = all(value > 0 for value in margins)
    reserve = min(margins) / 2 if both_positive else None
    old_reserve = F(data146['common_reserve_if_both_positive'])
    require(both_positive and reserve >= old_reserve,
            'the same-source sharpening preserves the already proved common reserve')
    result = {
        'scope': 'new P evaluation of exactly2017 old supports, plus19 cached P support fees and unchanged separate shallow G_P',
        'source_contract': 'same full-target136 reference or138/141 exact head-row target/common-transport extension; no arbitrary compensated137/139 source',
        'evidence': 'ordinary per-original bridge and exact fixed saved-data arithmetic; no Lean claim',
        'design_sha256': DESIGN_SHA256,
        'consumer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'saved146_input': provenance146, 'saved145_input': provenance145, 'saved144_input': provenance144,
        'private_prime_order': list(PRIVATE), 'root_order': list(ROOTS),
        'joint_cell_order': [list(v) for v in CELL_ORDER],
        'complete_supported_private_caps_by_mask': [str(v) for v in caps],
        'shared_supported_cap_updates': cap_updates,
        'quotient_rule': 'O[0]=saved joint P; O[m]=O[m without least set bit]/same-cell P_q; no source measure is normalized by this division',
        'free_rule': 'add both roots at one physical supported-head address before maximizing, separately in each exact depth block',
        'selected_rule': 'one root/address maximum in each depth block; all positive ternary heights have multiplier3/2',
        'formula': 'M148=Abar-F_fullP-(3/2)*S_fullP-G_P/2',
        'gain_identity': 'M148-M146=(remaining2017_K_free-new2017_P_free)+(3/2)*(remaining2017_K_selected-new2017_P_selected)',
        'normalization': 'saved limiting signatures are evaluated; finite b_q,N stays inside finite P, while supported private depth sums use b_q,infinity',
        'primitive_products_formed': 0, 'primitive_tables_read': False,
        'cached19_P_support_fees_reevaluated': 0, 'K_support_fees_evaluated': 0,
        'producer_or_controls_executed': False, 'continuation_executed': False,
        'no_parameter_search': True, 'cases': cases,
        'both_margins_positive': both_positive,
        'common_reserve_if_both_positive': str(reserve) if reserve is not None else None,
        'saved146_common_reserve': str(old_reserve),
        'reserve_rule': 'one half of the smaller positive limiting margin; a corresponding finite threshold follows by convergence, no numeric threshold is computed',
        'raw_Xi_scope': 'unchanged raw bounds by domination by the same R_N; a changed mass does not inherit Top_h84 or any saved continuation',
        'remaining_exclusions': 'further pure ternary powers, unpaid higher-ternary singleton classes, unrestricted head incidences, unrestricted prime support and the middle-prime continuation gap',
        'remaining_slack': 'supported-cylinder caps, address maxima and deletion-union overlap; full-P is not the actual deletion union',
        'execution': {
            'python': sys.version.split()[0], 'isolated': bool(sys.flags.isolated),
            'site_disabled': bool(sys.flags.no_site),
            'bytecode_disabled': bool(sys.flags.dont_write_bytecode),
        },
        'checks': CHECKS,
    }
    # Store shared quotient/contraction witnesses and block maxima, not duplicate candidates.
    with args.output.open('x') as stream:
        json.dump(result, stream, separators=(',', ':'))
        stream.write('\n')
    print(json.dumps({
        'event': 'output_written', 'output': str(args.output), 'checks': CHECKS,
        'both_margins_positive': both_positive,
    }), flush=True)


if __name__ == '__main__':
    main()
