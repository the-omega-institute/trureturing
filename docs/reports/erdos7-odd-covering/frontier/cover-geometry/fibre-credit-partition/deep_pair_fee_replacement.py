"""One fixed saved-data evaluation of the eighteen deep-head pair fee replacements.

Reads saved143 K rows, saved144 P rows and saved J/F/S totals only.
Per table: 216 paired root/row records and 72 prescribed maxima.
Zero new private cell products, producer imports, depth enumerations,
controls, phase choices, parameter scans, or continuation calculations.
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
INPUTS = {
    'FC110': ('first_layer_witness',
              '5540ef30fbf02147b4c4687e80e4e617b96cdd58f41a706b8a3f460793ce0a70'),
    'FC131': ('bounded_joint_result',
              '7ff231d7a8c95f0a7bc9e5181fd4c7099e816f985403325fdd608dd176ce37c6'),
}
K_SHA256 = 'f500e063cf43ffee76f9d749644c8eeed8d78a47b66904aad42f609a45b312b1'
P_SHA256 = 'bad5b8c850742e0bb7277ea316bf5e96dc06f963317a28033cc6ed8e1ebb06bb'
SCORES_SHA256 = '4e824f35c5f921cdacee1cb462cf3387f5524978e859c65460e45cb3fcb5f8c4'
DESIGN_SHA256 = '9acb1d921c1566ab6bc66d82e500695f2d6f01b42d186a73a1aaea2a8f806fa2'
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


def pair_index(case):
    entries = case['pair_supports']
    indexed = {(v['head'], v['private_prime']): v for v in entries}
    require(len(entries) == 18
            and set(indexed) == {(h, q) for h in HEADS for q in PRIVATE},
            'exactly eighteen distinct fixed head/private pair supports')
    return indexed


def row_index(pair, h):
    entries = pair['candidates']
    indexed = {(v['root'], v['row']): v for v in entries}
    require(len(entries) == 2 * h
            and set(indexed) == {(r, i) for r in ROOTS for i in range(h)},
            'complete fixed physical root/head-row registry')
    return indexed


def evaluate(name, k_case, p_case, saved_score):
    require(saved_score['recognized_schema'] == INPUTS[name][0]
            and saved_score['witness_sha256'] == INPUTS[name][1],
            'saved J/F/S refers to the same fixed witness')
    require(saved_score['gamma'] == '1/2', 'fixed saved root weights')
    saved = saved_score['modes']['head_min']
    j, total_f, total_s = (F(saved[key]) for key in ('score', 'free', 'selected'))
    require(j == F(k_case['saved_score']) == F(p_case['saved_score_J'])
            and total_s == F(k_case['saved_selected_fee']) == F(p_case['saved_selected_fee_S']),
            'all three saved inputs retain the identical old J and S')
    k_pairs, p_pairs = pair_index(k_case), pair_index(p_case)
    pair_results = []
    row_count = maxima_count = 0
    free_candidate_count = selected_candidate_count = 0
    for h in HEADS:
        for q in PRIVATE:
            k_pair, p_pair = k_pairs[h, q], p_pairs[h, q]
            k_rows, p_rows = row_index(k_pair, h), row_index(p_pair, h)
            values = {kind: {r: {} for r in ROOTS} for kind in ('K', 'P')}
            paired_rows = []
            for r in ROOTS:
                for i in range(h):
                    old, new = k_rows[r, i], p_rows[r, i]
                    w = F(old['row_mass'])
                    require(w == F(new['row_mass']) and w >= 0,
                            'identical nonnegative physical head-row mass')
                    c_k, c_p = F(old['selected_candidate']), F(new['selected_candidate_P'])
                    t_k, t_p = F(old['unsupported_sum_T']), F(new['unsupported_sum_P'])
                    require(c_k == F(new['saved_selected_candidate_K']),
                            'P result retains exactly this saved K candidate')
                    require(t_k >= 0 and t_p >= 0
                            and c_k == w * t_k / 2 and c_p == w * t_p / 2,
                            'saved shallow candidates equal w times saved gamma-T')
                    require(0 <= c_p <= c_k, 'saved same-address P candidate is bounded by K')
                    if w > 0:
                        v_k, v_p = c_k / w, c_p / w
                        require(v_k == t_k / 2 and v_p == t_p / 2,
                                'live-row quotient recovers gamma-T exactly')
                    else:
                        require(c_k == 0 and c_p == 0, 'zero head row has zero shallow candidates')
                        v_k, v_p = F(), F()
                    require(0 <= v_p <= v_k, 'masked deep-head P coefficient is bounded by K')
                    values['K'][r][i], values['P'][r][i] = v_k, v_p
                    paired_rows.append({
                        'root': r, 'row': i, 'row_mass': str(w),
                        'saved_C_K': str(c_k), 'saved_C_P': str(c_p),
                        'masked_V_K': str(v_k), 'masked_V_P': str(v_p),
                    })
                    row_count += 1

            b_q = F(1, q - 2)
            head_tail = F(1, h * (h - 2))
            require(F(h - 1, h - 2) * F(1, h * h) / (1 - F(1, h)) == head_tail,
                    'complete head-depth tail begins exactly at exponent two')
            require(F(k_pair['b_q']) == b_q
                    and F(p_pair['supported_private_cap_sum']) == b_q,
                    'complete supported-private cap factor is unchanged')
            coefficients = {}
            for kind in ('K', 'P'):
                # One physical head row is used before adding its two root values.
                free_rows = [{
                    'row': i,
                    'same_row_root_sum': str(values[kind][1][i] + values[kind][2][i]),
                } for i in range(h)]
                free_max = max(F(v['same_row_root_sum']) for v in free_rows)
                selected_max = max(values[kind][r][i] for r in ROOTS for i in range(h))
                maxima_count += 2
                free_candidate_count += h
                selected_candidate_count += 2 * h
                coefficients[kind] = {
                    'free_same_row_max': str(free_max),
                    'selected_live_max': str(selected_max),
                    'free_pair_fee': str(b_q * head_tail * free_max),
                    'selected_pair_fee': str(b_q * head_tail * selected_max),
                    'free_maximizing_rows': [v['row'] for v in free_rows
                                             if F(v['same_row_root_sum']) == free_max],
                    'selected_maximizing_addresses': [
                        {'root': r, 'row': i} for r in ROOTS for i in range(h)
                        if values[kind][r][i] == selected_max
                    ],
                    'free_candidates': free_rows,
                }
            require(F(coefficients['K']['selected_live_max']) == F(k_pair['zeta_live_max'])
                    and F(coefficients['K']['selected_pair_fee'])
                    == F(k_pair['old_deep_pair_selected_fee']),
                    'recovered selected K term equals the saved old deep-pair term')
            delta_f = F(coefficients['K']['free_pair_fee']) - F(coefficients['P']['free_pair_fee'])
            delta_s = F(coefficients['K']['selected_pair_fee']) - F(coefficients['P']['selected_pair_fee'])
            require(delta_f >= 0 and delta_s >= 0, 'both pair replacements lower an upper allowance')
            pair_results.append({
                'head': h, 'private_prime': q,
                'supported_private_cap_sum': str(b_q), 'complete_head_tail_factor': str(head_tail),
                'coefficients': coefficients,
                'free_fee_saving': str(delta_f), 'selected_fee_saving': str(delta_s),
                'weighted_all_height_saving': str(delta_f + F(3, 2) * delta_s),
                'paired_root_rows': paired_rows,
            })

    require(row_count == 216 and maxima_count == 72
            and free_candidate_count == 216 and selected_candidate_count == 432,
            'fixed saved-row and prescribed-maxima evaluation counts')
    totals = {
        kind: {
            label: sum((F(v['coefficients'][kind][label + '_pair_fee'])
                        for v in pair_results), F())
            for label in ('free', 'selected')
        } for kind in ('K', 'P')
    }
    require(0 <= totals['P']['free'] <= totals['K']['free'] <= total_f,
            'identified free pair summands fit within saved complete free fee')
    require(0 <= totals['P']['selected'] <= totals['K']['selected'] <= total_s,
            'identified selected pair summands fit within saved complete selected fee')
    delta_f = totals['K']['free'] - totals['P']['free']
    delta_s = totals['K']['selected'] - totals['P']['selected']
    saving = delta_f + F(3, 2) * delta_s
    old_margin = F(p_case['new_margin_J_minus_half_S_plus_G_P'])
    g_p = F(p_case['G_P'])
    require(old_margin == j - (total_s + g_p) / 2,
            'saved144 margin retains the old fee and the same new shallow allowance')
    margin = old_margin + saving
    require(margin == j - (total_s + g_p) / 2 + delta_f + F(3, 2) * delta_s,
            'only identified deep-pair allowances are replaced in the same-source margin')
    require(saving == sum((F(v['weighted_all_height_saving']) for v in pair_results), F()),
            'total improvement equals the sum of the eighteen disjoint pair savings')
    sign = 'positive' if margin > 0 else ('negative' if margin < 0 else 'zero')
    return {
        'saved_score_J': str(j), 'saved_full_free_F': str(total_f),
        'saved_full_selected_S': str(total_s), 'saved_shallow_G_P': str(g_p),
        'deep_pair_totals': {
            kind: {label: str(value) for label, value in subtotal.items()}
            for kind, subtotal in totals.items()
        },
        'unchanged_other_2018_support_fees': {
            'free': str(total_f - totals['K']['free']),
            'selected': str(total_s - totals['K']['selected']),
        },
        'DeltaF': str(delta_f), 'DeltaS': str(delta_s),
        'weighted_saving_DeltaF_plus_3_over_2_DeltaS': str(saving),
        'saved144_margin': str(old_margin), 'new145_margin': str(margin),
        'margin_sign': sign, 'pair_supports': pair_results,
        'evaluation_counts': {
            'paired_root_rows': row_count, 'prescribed_maxima': maxima_count,
            'free_same_row_candidates_K_and_P': free_candidate_count,
            'selected_root_row_candidates_K_and_P': selected_candidate_count,
            'new_private_cell_products': 0, 'old_full_fee_evaluations': 0,
        },
        'interpretation': (
            'positive limit gives a new sufficiently-large finite threshold under the fixed full-target source and inventory contract'
            if margin > 0 else
            'negative limit blocks this stronger sufficient allowance for sufficiently large finite depths; no actual covering is established'
            if margin < 0 else
            'zero limit leaves finite-depth positivity unsettled'
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--saved-k-rows', type=Path, required=True)
    parser.add_argument('--saved-p-rows', type=Path, required=True)
    parser.add_argument('--saved-scores', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(bool(sys.flags.isolated) and bool(sys.flags.no_site)
            and bool(sys.flags.dont_write_bytecode), 'run only with python3 -I -S -B')
    require(args.output.is_absolute()
            and args.output.parent.resolve() == Path('/tmp').resolve()
            and args.output.name.startswith('e7_batch145_'),
            'output is an explicit batch145 path directly under /tmp')
    require(not args.output.exists(), 'refuse to overwrite a saved evaluation')
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    k_data, k_provenance = read_pinned(args.saved_k_rows, K_SHA256)
    p_data, p_provenance = read_pinned(args.saved_p_rows, P_SHA256)
    scores, scores_provenance = read_pinned(args.saved_scores, SCORES_SHA256)
    require(set(k_data['cases']) == set(p_data['cases']) == set(CASES)
            and len(scores['results']) == 2, 'exactly the two fixed table cases')
    require(k_data['saved_scores_input']['sha256'] == SCORES_SHA256
            and p_data['saved_scores_input']['sha256'] == SCORES_SHA256
            and p_data['saved_K_comparison_input']['sha256'] == K_SHA256,
            'saved results share the declared inputs')
    cases = {}
    for index, name in enumerate(CASES):
        require(k_data['table_inputs'][name]['sha256']
                == p_data['table_inputs'][name]['sha256'] == INPUTS[name][1],
                'same physical source table in both saved candidate files')
        cases[name] = evaluate(name, k_data['cases'][name], p_data['cases'][name],
                               scores['results'][index])
        print(json.dumps({
            'event': 'case_complete', 'case': name,
            'margin_sign': cases[name]['margin_sign'],
            'margin_decimal_display': float(F(cases[name]['new145_margin'])),
        }), flush=True)
    margins = [F(v['new145_margin']) for v in cases.values()]
    both_positive = all(value > 0 for value in margins)
    reserve = min(margins) / 2 if both_positive else None
    result = {
        'scope': 'replace only the eighteen old deep-head pair supports h^a*q^e, a>=2, e>=1; new144 shallow G_P unchanged; remaining2018 old supports unchanged',
        'source_contract': 'one full-target reference from136 or exact head-row target extensions138/141; excludes arbitrary compensated137/139 references',
        'evidence': 'ordinary exact fee bridge and arithmetic on saved candidates; no Lean claim',
        'design_sha256': DESIGN_SHA256,
        'consumer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'saved_K_rows_input': k_provenance, 'saved_P_rows_input': p_provenance,
        'saved_J_F_S_input': scores_provenance,
        'recovery': 'V=C/w on positive rows, V=0 on zero rows',
        'free_rule': 'max over one physical head row after summing its two root V values',
        'selected_rule': 'one root/head-row maximum',
        'formula': 'M145=M144+(F_K_pair-F_P_pair)+(3/2)*(S_K_pair-S_P_pair)',
        'complete_head_depth_factor': '1/[h(h-2)] for a>=2',
        'complete_private_depth_factor': 'b_q,infinity=1/(q-2)',
        'old_full_fee_recomputed': False, 'new_private_cell_products': 0,
        'producer_or_controls_executed': False, 'continuation_executed': False,
        'no_parameter_search': True, 'cases': cases,
        'both_margins_positive': both_positive,
        'common_reserve_if_both_positive': str(reserve) if reserve is not None else None,
        'reserve_rule': 'one half of the smaller limiting margin, only if both are positive; a new common finite threshold is required',
        'continuation_boundary': 'raw Xi bounds persist by domination; saved Top_h84 initialization and continuation do not transfer to a changed mass',
        'remaining_exclusions': 'pure ternary powers, singleton nonternary supports, unrestricted head incidences and unrestricted prime support',
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
