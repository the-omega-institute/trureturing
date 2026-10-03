"""One fixed evaluation of the old single support {5,7} with exact P factors.

Each pinned table contributes 70 joint root/head cells with K/P nine-factor
products, four exact depth blocks, and 16 prescribed maxima. Free labels
retain the SAME physical pair of head rows across roots before maximizing.
No other support is evaluated, no producer is imported, and no continuation
or parameter/depth/phase search runs. Saved145 supplies all earlier savings.
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
KINDS = ('K', 'P')
BLOCKS = ((0, 0), (1, 0), (0, 1), (1, 1))
CASES = ('FC110', 'FC131')
INPUTS = {
    'FC110': ('first_layer_witness',
              '5540ef30fbf02147b4c4687e80e4e617b96cdd58f41a706b8a3f460793ce0a70'),
    'FC131': ('bounded_joint_result',
              '7ff231d7a8c95f0a7bc9e5181fd4c7099e816f985403325fdd608dd176ce37c6'),
}
SCORES_SHA256 = '4e824f35c5f921cdacee1cb462cf3387f5524978e859c65460e45cb3fcb5f8c4'
SAVED145_SHA256 = '4ae73a9a4e17120630602fbef88ffccdc74f34a33ad3f7ac878c633c656aaa04'
SAVED143_SHA256 = 'f500e063cf43ffee76f9d749644c8eeed8d78a47b66904aad42f609a45b312b1'
SAVED144_SHA256 = 'bad5b8c850742e0bb7277ea316bf5e96dc06f963317a28033cc6ed8e1ebb06bb'
DESIGN_SHA256 = '5b78dd1ec044fdd3bc207fc2d895ba29afaa23d4c6d8728921451f525482fcef'
CHECKS = 0


def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def read_pinned(path, expected):
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    require(actual == expected, 'pinned input identity: ' + str(path))
    return json.loads(raw), {
        'file': str(path), 'sha256': actual,
        'hash_role': 'saved input identity, not mathematical premise',
    }


def product(values):
    value = F(1)
    for factor in values:
        value *= factor
    return value


def source_rows(name, source):
    require(tuple(source['private_primes']) == PRIVATE, 'fixed private prime order')
    if INPUTS[name][0] == 'bounded_joint_result':
        require(source['gamma'] == '1/2'
                and 'final_rows' in source and 'final_masks' in source,
                'fixed bounded-result schema and root weight')
    else:
        require(all(key in source for key in
                    ('first_layer_star', 'common_rows', 'masks', 'objectives')),
                'fixed first-layer schema')
    w = {r: {h: [F(v) for v in source['head_weights'][str(r)][str(h)]]
             for h in HEADS} for r in ROOTS}
    arrays = {
        r: {h: [[F(v) for v in row] for row in source['arrays'][str(r)][str(h)]]
            for h in HEADS} for r in ROOTS
    }
    counts = {r: {h: {} for h in HEADS} for r in ROOTS}
    for h in HEADS:
        common = [F(v) for v in source['common_head_laws'][str(h)]]
        require(len(common) == h and sum(common, F()) == 1,
                'common physical head law')
        c_h = F(h - 1, h - 2)
        for r in ROOTS:
            losses = [F(v) for v in source['head_star_losses'][str(r)][str(h)]]
            require(len(w[r][h]) == len(losses) == h,
                    'head-row dimensions')
            require(all(0 <= loss <= mass <= c_h / h and mass - loss == row
                        for mass, loss, row in zip(common, losses, w[r][h])),
                    'exact same-root surviving row weights')
            require(all(row == 0 or F(1, h) <= row <= c_h / h for row in w[r][h]),
                    'live rows support the fixed saturation threshold two')
            require(all(min(c_h / h, row) == row for row in w[r][h]),
                    'shallow depth-one cap equals the actual row mass')
            require(all(min(c_h / (h * h), row)
                        == c_h / (h * h) * int(row > 0) for row in w[r][h]),
                    'depth-two cap saturates on precisely the live rows')
            require(len(arrays[r][h]) == len(PRIVATE)
                    and all(len(row) == h for row in arrays[r][h]),
                    'conditional group array dimensions')
    for qi, q in enumerate(PRIVATE):
        b_q = F(1, q - 2)
        for h in HEADS:
            raw = source['private_sources'][str(q)][str(h)]
            free = [F(v) for v in raw['free']]
            selected = {r: [F(v) for v in raw['selected_increment'][str(r)]] for r in ROOTS}
            require(len(free) == h and all(len(selected[r]) == h for r in ROOTS),
                    'raw named-role row dimensions')
            require(all(v in (0, b_q) for v in free) and sum(free, F()) == b_q,
                    'one globally fixed free named role')
            require(all(v in (0, b_q) for r in ROOTS for v in selected[r])
                    and sum((v for r in ROOTS for v in selected[r]), F()) == b_q,
                    'one globally fixed selected named role')
            for r in ROOTS:
                g = 1 - int(r == 2) * b_q
                loads = [free[i] + selected[r][i] for i in range(h)]
                require(all(g * arrays[r][h][qi][i] == loads[i] for i in range(h)),
                        'conditional arrays reconstruct the actual named-role load')
                numbers = [v / b_q for v in loads]
                require(all(v.denominator == 1 and 0 <= v <= 2 for v in numbers),
                        'full active-role counts are integral')
                counts[r][h][q] = [int(v) for v in numbers]
    return w, arrays, counts


def joint_cells(w, arrays, counts):
    matrices = {kind: {r: {} for r in ROOTS} for kind in KINDS}
    records = []
    product_count = factor_count = 0
    for r in ROOTS:
        epsilon = int(r == 2)
        for i in range(5):
            for j in range(7):
                factors = {kind: [] for kind in KINDS}
                factor_records = []
                for qi, q in enumerate(PRIVATE):
                    b_q = F(1, q - 2)
                    g = 1 - epsilon * b_q
                    x, y = arrays[r][5][qi][i], arrays[r][7][qi][j]
                    k_value, p_value = g * (1 - max(x, y)), g * (1 - x - y)
                    n5, n7 = counts[r][5][q][i], counts[r][7][q][j]
                    require(k_value == 1 - (epsilon + max(n5, n7)) * b_q
                            and p_value == 1 - (epsilon + n5 + n7) * b_q,
                            'same-cell K/P normalization from full named-role counts')
                    require(0 < p_value <= k_value <= g,
                            'positive full-target factor below the old K allowance')
                    factors['K'].append(k_value)
                    factors['P'].append(p_value)
                    factor_records.append({'private_prime': q, 'K': str(k_value), 'P': str(p_value)})
                for kind in KINDS:
                    require(len(factors[kind]) == 9, 'all nine private primes are unsupported')
                    matrices[kind][r][i, j] = product(factors[kind])
                    product_count += 1
                    factor_count += len(factors[kind])
                require(0 < matrices['P'][r][i, j] <= matrices['K'][r][i, j],
                        'pointwise full private product domination')
                records.append({
                    'root': r, 'head5_row': i, 'head7_row': j,
                    'head5_mass': str(w[r][5][i]), 'head7_mass': str(w[r][7][j]),
                    'K_product': str(matrices['K'][r][i, j]),
                    'P_product': str(matrices['P'][r][i, j]),
                    'private_factors': factor_records,
                })
    require(len(records) == 70 and product_count == 140 and factor_count == 1260,
            'only the fixed one-support joint products are formed')
    return matrices, records, product_count, factor_count


def depth_blocks(w, matrices, saved_score):
    d = {h: F(1, h * (h - 2)) for h in HEADS}
    for h in HEADS:
        require(F(h - 1, h - 2) * F(1, h * h) / (1 - F(1, h)) == d[h],
                'saturated complete head tail begins at exponent two')
    blocks = []
    maxima_count = root_candidate_count = free_candidate_count = 0
    for alpha, beta in BLOCKS:
        values = {kind: {r: {} for r in ROOTS} for kind in KINDS}
        root_records = []
        for r in ROOTS:
            for i in range(5):
                l5 = w[r][5][i] if alpha == 0 else F(int(w[r][5][i] > 0))
                for j in range(7):
                    l7 = w[r][7][j] if beta == 0 else F(int(w[r][7][j] > 0))
                    for kind in KINDS:
                        values[kind][r][i, j] = matrices[kind][r][i, j] * l5 * l7 / 2
                        root_candidate_count += 1
                    require(0 <= values['P'][r][i, j] <= values['K'][r][i, j],
                            'same-root block candidate domination')
                    root_records.append({
                        'root': r, 'head5_row': i, 'head7_row': j,
                        'head5_factor': str(l5), 'head7_factor': str(l7),
                        'X_K': str(values['K'][r][i, j]),
                        'X_P': str(values['P'][r][i, j]),
                    })
        if (alpha, beta) == (0, 0):
            # These are already formed shallow-shallow terms, not new private products.
            root_masses = {r: sum(values['P'][r].values(), F()) for r in ROOTS}
            require(sum(root_masses.values(), F()) == F(saved_score['weighted_group_residual']),
                    'joint P cells belong to the same saved full-target source')
            require(all(2 * root_masses[r] == F(saved_score['root_group_residuals'][str(r)])
                        for r in ROOTS), 'same-source root mass normalization')
        weight = (d[5] if alpha else F(1)) * (d[7] if beta else F(1))
        coefficients = {}
        for kind in KINDS:
            free_rows = [
                {'head5_row': i, 'head7_row': j,
                 'same_pair_root_sum': str(values[kind][1][i, j] + values[kind][2][i, j])}
                for i in range(5) for j in range(7)
            ]
            free_max = max(F(v['same_pair_root_sum']) for v in free_rows)
            selected_max = max(values[kind][r][i, j]
                               for r in ROOTS for i in range(5) for j in range(7))
            maxima_count += 2
            free_candidate_count += len(free_rows)
            coefficients[kind] = {
                'free_same_pair_max': str(free_max), 'selected_root_pair_max': str(selected_max),
                'free_block_fee': str(weight * free_max),
                'selected_block_fee': str(weight * selected_max),
                'free_maximizing_addresses': [
                    {'head5_row': v['head5_row'], 'head7_row': v['head7_row']}
                    for v in free_rows if F(v['same_pair_root_sum']) == free_max
                ],
                'selected_maximizing_addresses': [
                    {'root': r, 'head5_row': i, 'head7_row': j}
                    for r in ROOTS for i in range(5) for j in range(7)
                    if values[kind][r][i, j] == selected_max
                ],
                'free_candidates': free_rows,
            }
        require(F(coefficients['P']['free_block_fee']) <= F(coefficients['K']['free_block_fee'])
                and F(coefficients['P']['selected_block_fee'])
                <= F(coefficients['K']['selected_block_fee']),
                'both block fee replacements lower the old allowance')
        blocks.append({
            'head5_block': 'shallow' if alpha == 0 else 'deep_tail',
            'head7_block': 'shallow' if beta == 0 else 'deep_tail',
            'alpha': alpha, 'beta': beta, 'depth_weight': str(weight),
            'coefficients': coefficients, 'paired_root_candidates': root_records,
        })
    require(len(blocks) == 4 and maxima_count == 16
            and root_candidate_count == 560 and free_candidate_count == 280,
            'fixed four-block evaluation counts')
    return blocks, maxima_count, root_candidate_count, free_candidate_count


def evaluate(name, source, saved_score, old145):
    require(saved_score['recognized_schema'] == INPUTS[name][0]
            and saved_score['witness_sha256'] == INPUTS[name][1]
            and saved_score['gamma'] == '1/2', 'same saved table, schema and root weight')
    require(all(saved_score['head_tail_start_at_lower_one'][str(h)] == 2 for h in HEADS),
            'saved min-cap head tails saturate at depth two')
    saved = saved_score['modes']['head_min']
    j, total_f, total_s = (F(saved[key]) for key in ('score', 'free', 'selected'))
    group_mass = F(saved_score['weighted_group_residual'])
    require(j == group_mass - total_f - total_s, 'saved J decomposes on this full-target source')
    require(j == F(old145['saved_score_J']) and total_f == F(old145['saved_full_free_F'])
            and total_s == F(old145['saved_full_selected_S']), 'same original totals in saved145')
    require(old145['evaluation_counts']['paired_root_rows'] == 216
            and old145['evaluation_counts']['prescribed_maxima'] == 72,
            'saved145 is the prescribed eighteen-support replacement')
    w, arrays, counts = source_rows(name, source)
    matrices, cells, product_count, factor_count = joint_cells(w, arrays, counts)
    blocks, maxima_count, root_count, free_count = depth_blocks(w, matrices, saved_score)
    totals57 = {
        kind: {
            label: sum((F(v['coefficients'][kind][label + '_block_fee']) for v in blocks), F())
            for label in ('free', 'selected')
        } for kind in KINDS
    }
    bucket = saved_score['by_supported_heads']['5,7']
    require(bucket['support_count'] == 512, 'two-head aggregate is not the isolated support')
    remaining2018 = {label: F(old145['unchanged_other_2018_support_fees'][label])
                     for label in ('free', 'selected')}
    for label, old_total in (('free', total_f), ('selected', total_s)):
        require(remaining2018[label] == old_total - F(old145['deep_pair_totals']['K'][label]),
                'saved remaining2018 supports exclude exactly the old eighteen K pair fees')
        require(0 <= totals57['P'][label] <= totals57['K'][label]
                <= F(bucket['head_min'][label]), 'identified support fits the two-head aggregate')
        require(totals57['K'][label] <= remaining2018[label],
                'identified support is still contained in the untouched2018-support inventory')
    delta_f = totals57['K']['free'] - totals57['P']['free']
    delta_s = totals57['K']['selected'] - totals57['P']['selected']
    saving = delta_f + F(3, 2) * delta_s
    old_delta_f, old_delta_s = F(old145['DeltaF']), F(old145['DeltaS'])
    g_p = F(old145['saved_shallow_G_P'])
    old_margin = F(old145['new145_margin'])
    require(old_margin == j - (total_s + g_p) / 2 + old_delta_f + F(3, 2) * old_delta_s,
            'saved145 margin keeps its exact earlier source and inventory')
    margin = old_margin + saving
    new_f, new_s = total_f - old_delta_f - delta_f, total_s - old_delta_s - delta_s
    require(margin == group_mass - new_f - F(3, 2) * new_s - g_p / 2,
            'new bound replaces precisely nineteen old supports on one source')
    require(new_f >= 0 and new_s >= 0 and saving >= 0,
            'remaining upper fees and new improvement are nonnegative')
    sign = 'positive' if margin > 0 else ('negative' if margin < 0 else 'zero')
    return {
        'saved_score_J': str(j), 'saved_full_free_F': str(total_f),
        'saved_full_selected_S': str(total_s), 'saved_group_mass': str(group_mass),
        'saved_shallow_G_P': str(g_p), 'saved145_margin': str(old_margin),
        'saved145_DeltaF': str(old_delta_f), 'saved145_DeltaS': str(old_delta_s),
        'single_support_57_totals': {
            kind: {label: str(value) for label, value in subtotal.items()}
            for kind, subtotal in totals57.items()
        },
        'DeltaF57': str(delta_f), 'DeltaS57': str(delta_s),
        'weighted_saving_DeltaF57_plus_3_over_2_DeltaS57': str(saving),
        'new146_margin': str(margin), 'margin_sign': sign,
        'old_inventory_replacement': {
            'original_supports': 2036, 'earlier_replaced_supports': 18,
            'newly_replaced_supports': 1, 'total_replaced_supports': 19,
            'unchanged_supports': 2017,
            'unchanged2017_free_fee': str(remaining2018['free'] - totals57['K']['free']),
            'unchanged2017_selected_fee': str(remaining2018['selected'] - totals57['K']['selected']),
            'revised_full_free_fee': str(new_f), 'revised_full_selected_fee': str(new_s),
        },
        'joint_cells': cells, 'depth_blocks': blocks,
        'evaluation_counts': {
            'target_supports': 1, 'joint_root_head_cells': len(cells),
            'nine_factor_products_K_and_P': product_count,
            'scalar_private_factors_K_and_P': factor_count,
            'depth_blocks': len(blocks), 'prescribed_maxima': maxima_count,
            'root_pair_candidates_K_and_P': root_count,
            'same_pair_free_candidates_K_and_P': free_count,
            'other_support_evaluations': 0, 'old_full_fee_evaluations': 0,
        },
        'interpretation': (
            'positive limit gives a new sufficiently-large finite threshold under the same full-target source and declared inventory'
            if margin > 0 else
            'negative limit blocks this stronger sufficient allowance at sufficiently large finite depths; no actual covering is established'
            if margin < 0 else
            'zero limit leaves finite-depth positivity unsettled'
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first-table', type=Path, required=True)
    parser.add_argument('--second-table', type=Path, required=True)
    parser.add_argument('--saved-scores', type=Path, required=True)
    parser.add_argument('--saved145', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(bool(sys.flags.isolated) and bool(sys.flags.no_site)
            and bool(sys.flags.dont_write_bytecode), 'run only with python3 -I -S -B')
    require(args.output.is_absolute()
            and args.output.parent.resolve() == Path('/tmp').resolve()
            and args.output.name.startswith('e7_batch146_'),
            'output has an explicit batch146 path directly under /tmp')
    require(not args.output.exists(), 'refuse to overwrite a previous evaluation')
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    scores, scores_provenance = read_pinned(args.saved_scores, SCORES_SHA256)
    saved145, saved145_provenance = read_pinned(args.saved145, SAVED145_SHA256)
    require(len(scores['results']) == 2 and set(saved145['cases']) == set(CASES),
            'exactly the two fixed cases')
    require(saved145['saved_J_F_S_input']['sha256'] == SCORES_SHA256
            and saved145['saved_K_rows_input']['sha256'] == SAVED143_SHA256
            and saved145['saved_P_rows_input']['sha256'] == SAVED144_SHA256,
            'saved145 preserves the declared score and earlier candidate provenance')
    cases, inputs = {}, {}
    for index, name, path in ((0, 'FC110', args.first_table), (1, 'FC131', args.second_table)):
        source, provenance = read_pinned(path, INPUTS[name][1])
        inputs[name] = provenance
        cases[name] = evaluate(name, source, scores['results'][index], saved145['cases'][name])
        print(json.dumps({
            'event': 'case_complete', 'case': name,
            'margin_sign': cases[name]['margin_sign'],
            'margin_decimal_display': float(F(cases[name]['new146_margin'])),
        }), flush=True)
    margins = [F(v['new146_margin']) for v in cases.values()]
    both_positive = all(value > 0 for value in margins)
    reserve = min(margins) / 2 if both_positive else None
    result = {
        'scope': 'replace exactly old support{5,7}, all head exponents>=1 and all ternary heights; retain saved145 changes and saved144 shallow G_P',
        'source_contract': 'one full-target direct-Haar source136 or exact head-row target/common-transport extensions138/141; not arbitrary compensated137/139 sources',
        'evidence': 'ordinary same-source bridge and fixed exact arithmetic; no Lean claim',
        'design_sha256': DESIGN_SHA256,
        'consumer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'table_inputs': inputs, 'saved_scores_input': scores_provenance,
        'saved145_input': saved145_provenance,
        'formula': 'M146=M145+(F57_K-F57_P)+(3/2)*(S57_K-S57_P)',
        'depth_blocks': '00 shallow/shallow,10 deep/shallow,01 shallow/deep,11 deep/deep; weights1,1/15,1/35,1/525',
        'free_rule': 'sum both roots at the same physical(head5row,head7row), then maximize that pair separately in each depth block',
        'selected_rule': 'one root/head-pair maximum separately in each depth block',
        'private_rule': 'all nine private coordinates unsupported; no supported-private b_infinity factor',
        'normalization': 'limiting table is evaluated here; the finite-source bridge uses finite b_q,N inside every P/K factor',
        'old_eight_factor_cell_reuse': 'unavailable:143/144 recorded row contractions, not cell values; only this support receives new joint products',
        'old_full_fee_recomputed': False, 'other_supports_evaluated': 0,
        'producer_or_controls_executed': False, 'continuation_executed': False,
        'no_parameter_search': True, 'cases': cases,
        'both_margins_positive': both_positive,
        'common_reserve_if_both_positive': str(reserve) if reserve is not None else None,
        'reserve_rule': 'half of the smaller positive limiting margin only when both are positive; requires a new common finite threshold',
        'raw_Xi_scope': 'unchanged comparison for the same full-target reference by domination; no transfer to arbitrary source laws or changed-mass Top_h84 continuation',
        'remaining_exclusions': 'pure ternary powers, singleton nonternary supports, unrestricted head incidences and unrestricted prime support; unrestricted Erdős7 remains open',
        'execution': {
            'python': sys.version.split()[0], 'isolated': bool(sys.flags.isolated),
            'site_disabled': bool(sys.flags.no_site),
            'bytecode_disabled': bool(sys.flags.dont_write_bytecode),
        },
        'checks': CHECKS,
    }
    with args.output.open('x') as stream:
        stream.write(json.dumps(result, indent=2) + '\n')
    print(json.dumps({
        'event': 'output_written', 'output': str(args.output), 'checks': CHECKS,
        'both_margins_positive': both_positive,
    }), flush=True)


if __name__ == '__main__':
    main()
