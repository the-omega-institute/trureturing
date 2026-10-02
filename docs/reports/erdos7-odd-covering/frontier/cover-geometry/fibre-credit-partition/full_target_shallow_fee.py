"""One fixed exact evaluation of the full-target high-ternary shallow fee.

For each of the two pinned tables: 630 shared eight-factor cells,
216 root/row candidates and 18 pair maxima. Only the newly admitted
3^t*h*q^e labels (t>=2, e>=1, h in {5,7}) use exact unsupported P.
Old F/S are saved inputs. No producer, controls, continuation, depth
scan, table search, phase change, repository import or Lean claim.
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
INPUTS = {
    'FC110': ('first_layer_witness',
              '5540ef30fbf02147b4c4687e80e4e617b96cdd58f41a706b8a3f460793ce0a70'),
    'FC131': ('bounded_joint_result',
              '7ff231d7a8c95f0a7bc9e5181fd4c7099e816f985403325fdd608dd176ce37c6'),
}
SCORES_SHA256 = '4e824f35c5f921cdacee1cb462cf3387f5524978e859c65460e45cb3fcb5f8c4'
SAVED_K_SHA256 = 'f500e063cf43ffee76f9d749644c8eeed8d78a47b66904aad42f609a45b312b1'
BRIDGE_SHA256 = 'c336c389a0bf453dd8d4573e065915cf23bc83ec6cd0db15ee8028a743ad8493'
CHECKS = 0


def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def read_pinned(path, digest):
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    require(actual == digest, 'pinned input identity: ' + str(path))
    return json.loads(raw), {
        'file': str(path), 'sha256': actual,
        'hash_role': 'saved input identity, not mathematical premise',
    }


def product(values):
    result = F(1)
    for value in values:
        result *= value
    return result


def table_data(name, source):
    if INPUTS[name][0] == 'bounded_joint_result':
        require(source['gamma'] == '1/2', 'fixed root weight')
        require('final_rows' in source and 'final_masks' in source,
                'bounded-result schema')
    else:
        require(all(k in source for k in
                    ('first_layer_star', 'common_rows', 'masks', 'objectives')),
                'first-layer schema')
    require(tuple(source['private_primes']) == PRIVATE, 'fixed private order')
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
        cap = F(h - 1, h * (h - 2))
        for r in ROOTS:
            losses = [F(v) for v in source['head_star_losses'][str(r)][str(h)]]
            require(len(w[r][h]) == h and len(losses) == h,
                    'physical head-row dimensions')
            require(all(0 <= loss <= mass <= cap and mass - loss == row
                        for mass, loss, row in zip(common, losses, w[r][h])),
                    'head rows equal common law minus same-root star loss')
            require(all(min(cap, row) == row for row in w[r][h]),
                    'supported head depth-one min cap equals its row weight')
            require(len(arrays[r][h]) == len(PRIVATE)
                    and all(len(row) == h for row in arrays[r][h]),
                    'conditional projection dimensions')

    for qi, q in enumerate(PRIVATE):
        b = F(1, q - 2)
        for h in HEADS:
            record = source['private_sources'][str(q)][str(h)]
            free = [F(v) for v in record['free']]
            selected = {
                r: [F(v) for v in record['selected_increment'][str(r)]]
                for r in ROOTS
            }
            require(len(free) == h and all(len(selected[r]) == h for r in ROOTS),
                    'raw named-role row dimensions')
            require(all(v in (0, b) for v in free) and sum(free, F()) == b,
                    'one free named role has one fixed physical row')
            require(all(v in (0, b) for r in ROOTS for v in selected[r])
                    and sum((v for r in ROOTS for v in selected[r]), F()) == b,
                    'one selected named role has one fixed root and physical row')
            for r in ROOTS:
                g = 1 - (r == 2) * b
                raw = [free[i] + selected[r][i] for i in range(h)]
                require(all(g * arrays[r][h][qi][i] == raw[i] for i in range(h)),
                        'g times conditional array equals raw named-role load')
                n = [v / b for v in raw]
                require(all(v.denominator == 1 and 0 <= v <= 2 for v in n),
                        'full active-role counts are integers between zero and two')
                counts[r][h][q] = [int(v) for v in n]

    p = {r: {} for r in ROOTS}
    entry_count = 0
    for r in ROOTS:
        epsilon = int(r == 2)
        for qi, q in enumerate(PRIVATE):
            b = F(1, q - 2)
            g = 1 - epsilon * b
            matrix = []
            for i5 in range(5):
                row = []
                for i7 in range(7):
                    from_arrays = g * (1 - arrays[r][5][qi][i5]
                                       - arrays[r][7][qi][i7])
                    n5 = counts[r][5][q][i5]
                    n7 = counts[r][7][q][i7]
                    from_counts = 1 - (epsilon + n5 + n7) * b
                    require(from_arrays == from_counts,
                            'exact full-target P normalization on the same cell')
                    require(0 < from_counts <= g,
                            'positive normalized full-target private mass')
                    row.append(from_counts)
                    entry_count += 1
                matrix.append(row)
            p[r][q] = matrix
    require(entry_count == 630, 'exactly 630 scalar P entries per table')
    return w, p


def evaluate(name, source, saved_score, saved_k):
    require(saved_score['recognized_schema'] == INPUTS[name][0],
            'matching saved J/S schema')
    require(saved_score['witness_sha256'] == INPUTS[name][1],
            'matching saved J/S source identity')
    require(saved_score['gamma'] == '1/2', 'saved J/S root weight')
    j = F(saved_score['modes']['head_min']['score'])
    s = F(saved_score['modes']['head_min']['selected'])
    require(j == F(saved_k['saved_score']) and s == F(saved_k['saved_selected_fee']),
            'saved old comparison uses identical J and S')
    w, p = table_data(name, source)
    expected_pairs = {(h, q) for h in HEADS for q in PRIVATE}
    old_pairs = {(v['head'], v['private_prime']): v for v in saved_k['pair_supports']}
    require(len(saved_k['pair_supports']) == 18 and set(old_pairs) == expected_pairs,
            'saved K comparison has the same eighteen numerical pair supports')

    # Build each unsupported-private product once, then reuse it for both heads.
    matrices = {q: {} for q in PRIVATE}
    cell_count = factor_count = 0
    for q in PRIVATE:
        for r in ROOTS:
            matrix = []
            for i5 in range(5):
                row = []
                for i7 in range(7):
                    factors = [p[r][private][i5][i7]
                               for private in PRIVATE if private != q]
                    require(len(factors) == 8, 'eight unsupported private coordinates')
                    row.append(product(factors))
                    cell_count += 1
                    factor_count += len(factors)
                matrix.append(row)
            matrices[q][r] = matrix

    pairs = []
    row_count = 0
    for h in HEADS:
        other = 7 if h == 5 else 5
        for q in PRIVATE:
            old_pair = old_pairs[h, q]
            old_candidates = {(v['root'], v['row']): v for v in old_pair['candidates']}
            require(len(old_pair['candidates']) == 2 * h
                    and set(old_candidates) == {(r, i) for r in ROOTS for i in range(h)},
                    'saved comparison retains every physical root/row address')
            candidates = []
            for r in ROOTS:
                matrix = matrices[q][r]
                for i in range(h):
                    row_sum = sum((w[r][other][k]
                                   * (matrix[i][k] if h == 5 else matrix[k][i])
                                   for k in range(other)), F())
                    value = w[r][h][i] * row_sum / 2
                    old_candidate = old_candidates[r, i]
                    require(w[r][h][i] == F(old_candidate['row_mass']),
                            'comparison keeps the identical supported head row mass')
                    old_value = F(old_candidate['selected_candidate'])
                    require(0 <= value <= old_value,
                            'new same-address P candidate does not exceed saved K candidate')
                    candidates.append({
                        'root': r, 'row': i, 'row_mass': str(w[r][h][i]),
                        'unsupported_sum_P': str(row_sum),
                        'selected_candidate_P': str(value),
                        'saved_selected_candidate_K': str(old_value),
                    })
                    row_count += 1
            b_max = max(F(v['selected_candidate_P']) for v in candidates)
            b_q = F(1, q - 2)
            require(F(q - 1, q - 2) * F(1, q) / (1 - F(1, q)) == b_q,
                    'complete supported-private cap sum uses limiting b')
            g_pair = b_q * b_max
            old_b_max = F(old_pair['B_max'])
            old_g_pair = F(old_pair['G_pair'])
            require(b_max <= old_b_max and g_pair <= old_g_pair,
                    'new pair allowance does not exceed saved K allowance')
            pairs.append({
                'head': h, 'private_prime': q, 'supported_private_cap_sum': str(b_q),
                'B_P_max': str(b_max), 'G_P_pair': str(g_pair),
                'saved_B_K_max': str(old_b_max), 'saved_G_K_pair': str(old_g_pair),
                'G_pair_saving': str(old_g_pair - g_pair),
                'maximizing_addresses': [
                    {'root': v['root'], 'row': v['row']} for v in candidates
                    if F(v['selected_candidate_P']) == b_max
                ],
                'candidates': candidates,
            })

    require(len(pairs) == 18 and row_count == 216
            and cell_count == 630 and factor_count == 5040,
            'fixed eighteen-pair evaluation counts')
    total_p = sum((F(v['G_P_pair']) for v in pairs), F())
    total_k = F(saved_k['G'])
    margin = j - (s + total_p) / 2
    old_margin = F(saved_k['new_margin_J_minus_half_S_plus_G'])
    require(0 <= total_p <= total_k, 'total new fee does not exceed saved old fee')
    require(old_margin == j - (s + total_k) / 2,
            'saved old margin has the same score and selected fee')
    require(margin - old_margin == (total_k - total_p) / 2,
            'all margin improvement is precisely the newly avoided fee enlargement')
    sign = 'positive' if margin > 0 else ('negative' if margin < 0 else 'zero')
    return {
        'saved_score_J': str(j), 'saved_selected_fee_S': str(s),
        'G_P': str(total_p), 'saved_G_K': str(total_k),
        'G_P_by_head': {
            str(h): str(sum((F(v['G_P_pair']) for v in pairs if v['head'] == h), F()))
            for h in HEADS
        },
        'additional_high_ternary_fee_G_P_over_2': str(total_p / 2),
        'new_margin_J_minus_half_S_plus_G_P': str(margin),
        'saved_old_margin': str(old_margin),
        'margin_gain': str(margin - old_margin), 'margin_sign': sign,
        'pair_supports': pairs,
        'evaluation_counts': {
            'pair_supports': len(pairs), 'row_candidates': row_count,
            'shared_eight_factor_cells': cell_count,
            'scalar_P_factors_in_cell_products': factor_count,
            'scalar_P_table_entries': 630,
        },
        'interpretation': (
            'positive limit gives a new sufficiently-large finite threshold under the full-target source contract'
            if margin > 0 else
            'negative limit blocks this stronger additive allowance at sufficiently large finite depths; no actual covering is established'
            if margin < 0 else
            'zero limit leaves finite-depth positivity unsettled'
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first-table', type=Path, required=True)
    parser.add_argument('--second-table', type=Path, required=True)
    parser.add_argument('--saved-scores', type=Path, required=True)
    parser.add_argument('--saved-k-fees', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(bool(sys.flags.isolated) and bool(sys.flags.no_site)
            and bool(sys.flags.dont_write_bytecode), 'run only with python3 -I -S -B')
    require(args.output.is_absolute()
            and args.output.parent.resolve() == Path('/tmp').resolve()
            and args.output.name.startswith('e7_batch144_'),
            'result must have an explicit batch144 path directly under /tmp')
    require(not args.output.exists(), 'refuse to overwrite a previous result')
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    scores, scores_provenance = read_pinned(args.saved_scores, SCORES_SHA256)
    saved_k, saved_k_provenance = read_pinned(args.saved_k_fees, SAVED_K_SHA256)
    require(len(scores['results']) == 2 and set(saved_k['cases']) == set(INPUTS),
            'only the two declared fixed tables')
    require(saved_k['saved_scores_input']['sha256'] == SCORES_SHA256,
            'saved K result used the same pinned J/S input')

    inputs, cases = {}, {}
    for name, path, score in (
            ('FC110', args.first_table, scores['results'][0]),
            ('FC131', args.second_table, scores['results'][1])):
        require(saved_k['table_inputs'][name]['sha256'] == INPUTS[name][1],
                'saved K result used the same pinned table')
        source, provenance = read_pinned(path, INPUTS[name][1])
        inputs[name] = provenance
        cases[name] = evaluate(name, source, score, saved_k['cases'][name])
        print(json.dumps({
            'event': 'case_complete', 'case': name,
            'margin_sign': cases[name]['margin_sign'],
            'G_P_decimal_display': float(F(cases[name]['G_P'])),
            'margin_decimal_display': float(F(cases[name]['new_margin_J_minus_half_S_plus_G_P'])),
        }), flush=True)

    margins = [F(v['new_margin_J_minus_half_S_plus_G_P']) for v in cases.values()]
    both_positive = all(v > 0 for v in margins)
    reserve = min(margins) / 2 if both_positive else None
    result = {
        'scope': 'new labels3^t*h*q^e with t>=2, e>=1, h in{5,7}, on each fixed full-target reference; old F/S and numerical inventory remain fixed',
        'source_contract': '136 direct-Haar full targets, or 138/141 exact head-row targets; not arbitrary 137/139 compensated sources',
        'evidence': 'ordinary proved fee bridge plus exact fixed-table limiting arithmetic; no Lean claim',
        'bridge_design_sha256': BRIDGE_SHA256,
        'consumer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'table_inputs': inputs, 'saved_scores_input': scores_provenance,
        'saved_K_comparison_input': saved_k_provenance,
        'formula': 'G_P=sum_q b_q,infinity*(B5q+B7q); B=max_(root,row)(w_head/2)*sum_other w_other*product_(private!=q)Pbar',
        'normalization': 'finite source Pbar uses b_q,N, supported cap sum uses b_q,infinity; this consumer evaluates only the prescribed limiting table',
        'ternary_height_tail_factor': '1/2',
        'old_full_fee_recomputed': False, 'old_K_fee_recomputed': False,
        'producer_or_controls_executed': False, 'continuation_executed': False,
        'no_parameter_search': True, 'cases': cases,
        'both_margins_positive': both_positive,
        'common_reserve_if_both_positive': str(reserve) if reserve is not None else None,
        'reserve_rule': 'one half of the smaller limiting margin, only if both are positive; a new finite threshold is required',
        'continuation_boundary': 'raw Xi bounds persist by domination; saved Top_h84 initialization and continuation are not reused at changed mass',
        'remaining_scope': 'pure ternary powers, singleton nonternary supports, unrestricted head incidences and primes outside the declared inventory remain excluded',
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
        'event': 'output_written', 'output': str(args.output),
        'checks': CHECKS, 'both_margins_positive': both_positive,
    }), flush=True)


if __name__ == '__main__':
    main()
