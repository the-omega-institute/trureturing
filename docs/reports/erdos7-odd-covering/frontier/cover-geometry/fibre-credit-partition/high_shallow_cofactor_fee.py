"""One fixed two-table evaluation of the missing high-ternary shallow fee G.

Analytic depth sums only:18 pair supports,216 row candidates and1260
8-factor cell products per table. Read saved primitive rows and J/S;
no repository import, producer, controls, continuation or parameter scan.
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
    'FC110': ('first_layer_witness', '5540ef30fbf02147b4c4687e80e4e617b96cdd58f41a706b8a3f460793ce0a70'),
    'FC131': ('bounded_joint_result', '7ff231d7a8c95f0a7bc9e5181fd4c7099e816f985403325fdd608dd176ce37c6'),
}
SCORES_SHA256 = '4e824f35c5f921cdacee1cb462cf3387f5524978e859c65460e45cb3fcb5f8c4'
DESIGN_SHA256 = '731e7f362c896f174790d2e4b7d506b94e1408e0eea787624c928a7d21189231'
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
    return json.loads(raw), {'file': str(path), 'sha256': actual,
                            'hash_role': 'saved input identity, not mathematical premise'}


def product(values):
    out = F(1)
    for value in values:
        out *= value
    return out


def table_data(name, source):
    schema = INPUTS[name][0]
    if schema == 'bounded_joint_result':
        require(source['gamma'] == '1/2', 'fixed saved root weight')
        require('final_rows' in source and 'final_masks' in source, 'bounded-result schema')
    else:
        require(all(k in source for k in ('first_layer_star', 'common_rows', 'masks', 'objectives')),
                'first-layer schema')
    require(tuple(source['private_primes']) == PRIVATE, 'fixed private order')
    w = {r: {h: [F(v) for v in source['head_weights'][str(r)][str(h)]]
             for h in HEADS} for r in ROOTS}
    arrays = {r: {h: [[F(v) for v in row] for row in source['arrays'][str(r)][str(h)]]
                  for h in HEADS} for r in ROOTS}
    g = {r: {q: F(1) if r == 1 else F(1) - F(1, q - 2) for q in PRIVATE} for r in ROOTS}
    for h in HEADS:
        common = [F(v) for v in source['common_head_laws'][str(h)]]
        require(len(common) == h and sum(common, F()) == 1, 'common physical head law')
        c = F(h - 1, h - 2)
        for r in ROOTS:
            loss = [F(v) for v in source['head_star_losses'][str(r)][str(h)]]
            require(len(w[r][h]) == h and len(loss) == h, 'fixed physical row dimensions')
            require(all(0 <= a <= c / h and 0 <= b <= a and a - b == z
                        for a, b, z in zip(common, loss, w[r][h])),
                    'row weights equal common law minus same-root star loss')
            require(all(z == 0 or F(1, h) <= z <= c / h for z in w[r][h]),
                    'every live row is between1/h and limiting depth-one cap')
            require(all(min(c / h, z) == z for z in w[r][h]), 'depth-one min cap equals w')
            require(len(arrays[r][h]) == len(PRIVATE)
                    and all(len(row) == h for row in arrays[r][h]), 'projection dimensions')
    for qi, q in enumerate(PRIVATE):
        for h in HEADS:
            record = source['private_sources'][str(q)][str(h)]
            free = [F(v) for v in record['free']]
            selected = {r: [F(v) for v in record['selected_increment'][str(r)]] for r in ROOTS}
            require(len(free) == h and all(len(selected[r]) == h for r in ROOTS),
                    'same-source raw projection row dimensions')
            for r in ROOTS:
                require(all(g[r][q] * arrays[r][h][qi][i] == free[i] + selected[r][i]
                            for i in range(h)), 'g times conditional array equals raw common-source mass')
                require(all(0 <= a <= 1 for a in arrays[r][h][qi]), 'conditional projection range')
    return w, arrays, g


def evaluate(name, source, old):
    require(old['recognized_schema'] == INPUTS[name][0], 'matching saved score schema')
    require(old['witness_sha256'] == INPUTS[name][1], 'matching saved score source identity')
    require(old['gamma'] == '1/2', 'same saved score root weight')
    w, arrays, g = table_data(name, source)
    j = F(old['modes']['head_min']['score'])
    s = F(old['modes']['head_min']['selected'])
    pairs = []
    row_count = cell_count = factor_count = 0
    for h in HEADS:
        other = 7 if h == 5 else 5
        for q in PRIVATE:
            candidates = []
            for r in ROOTS:
                for i in range(h):
                    row_sum = F()
                    for other_row in range(other):
                        i5, i7 = (i, other_row) if h == 5 else (other_row, i)
                        factors = []
                        for qi, private in enumerate(PRIVATE):
                            if private == q:
                                continue
                            conditional_max = max(arrays[r][5][qi][i5], arrays[r][7][qi][i7])
                            factor = g[r][private] * (1 - conditional_max)
                            require(0 <= factor <= g[r][private], 'unsupported-private raw K factor range')
                            factors.append(factor)
                        require(len(factors) == 8, 'exactly the unsupported eight private coordinates')
                        row_sum += w[r][other][other_row] * product(factors)
                        cell_count += 1
                        factor_count += len(factors)
                    value = w[r][h][i] * row_sum / 2
                    candidates.append({'root': r, 'row': i, 'row_mass': str(w[r][h][i]),
                                       'unsupported_sum_T': str(row_sum),
                                       'selected_candidate': str(value)})
                    row_count += 1
            b_value = max(F(c['selected_candidate']) for c in candidates)
            live = [c for c in candidates if F(c['row_mass']) > 0]
            require(bool(live), 'live head rows exist')
            zeta = max(F(c['unsupported_sum_T']) / 2 for c in live)
            pair_g = F(1, q - 2) * b_value
            pair_e = F(1, q - 2) * zeta / (h * (h - 2))
            require((h - 2) * pair_e <= pair_g <= (h - 1) * pair_e,
                    'missing shallow fee versus already paid deep-head pair tail')
            # The two depth sums are closed rational identities, not loops over depth.
            c_q = F(q - 1, q - 2)
            require(c_q * F(1, q) / (1 - F(1, q)) == F(1, q - 2),
                    'complete supported-private geometric depth sum')
            c_h = F(h - 1, h - 2)
            require(c_h * F(1, h*h) / (1 - F(1, h)) == F(1, h*(h-2)),
                    'complete previously paid deep-head selected pair factor')
            pairs.append({'head': h, 'private_prime': q, 'b_q': str(F(1, q - 2)),
                          'B_max': str(b_value), 'G_pair': str(pair_g),
                          'zeta_live_max': str(zeta), 'old_deep_pair_selected_fee': str(pair_e),
                          'lower_from_old_pair': str((h - 2) * pair_e),
                          'upper_from_old_pair': str((h - 1) * pair_e),
                          'maximizing_addresses': [
                              {'root': c['root'], 'row': c['row']} for c in candidates
                              if F(c['selected_candidate']) == b_value],
                          'candidates': candidates})
    require(len(pairs) == 18, 'exactly eighteen omitted shallow pair supports')
    require(row_count == 216 and cell_count == 1260 and factor_count == 10080,
            'predeclared bounded formula evaluation counts')
    total_g = sum((F(pair['G_pair']) for pair in pairs), F())
    margin = j - (s + total_g) / 2
    old_all_height_margin = j - s / 2
    require(margin == old_all_height_margin - total_g / 2,
            'same-table source score with precisely the new missing fee')
    by_head = {str(h): str(sum((F(pair['G_pair']) for pair in pairs if pair['head'] == h), F()))
               for h in HEADS}
    sign = 'positive' if margin > 0 else ('negative' if margin < 0 else 'zero')
    return {
        'saved_score': str(j), 'saved_selected_fee': str(s),
        'old_all_height_margin': str(old_all_height_margin),
        'G': str(total_g), 'G_by_head': by_head, 'additional_high_ternary_fee_G_over_2': str(total_g/2),
        'new_margin_J_minus_half_S_plus_G': str(margin), 'margin_sign': sign,
        'absolute_gap_to_zero': str(abs(margin)),
        'pair_supports': pairs,
        'evaluation_counts': {'pair_supports': len(pairs), 'row_candidates': row_count,
                              'eight_factor_cells': cell_count, 'scalar_K_factors': factor_count},
        'interpretation': (
            'strict positive limit yields a sufficiently-large finite-source margin under the declared contract'
            if margin > 0 else
            'strict negative limit obstructs this additive certificate at sufficiently large finite depths; not actual coverage'
            if margin < 0 else
            'zero limit leaves finite-depth positivity undecided'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first-table', type=Path, required=True)
    parser.add_argument('--second-table', type=Path, required=True)
    parser.add_argument('--saved-scores', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    if args.output.exists():
        raise RuntimeError('refusing to overwrite a prior result; one designated run only')
    scores, score_provenance = read_pinned(args.saved_scores, SCORES_SHA256)
    require(len(scores['results']) == 2, 'exactly the two saved score cases')
    inputs, cases = {}, {}
    for name, path, old in (('FC110', args.first_table, scores['results'][0]),
                            ('FC131', args.second_table, scores['results'][1])):
        source, provenance = read_pinned(path, INPUTS[name][1])
        inputs[name] = provenance
        cases[name] = evaluate(name, source, old)
        print(json.dumps({'event': 'case_complete', 'case': name,
                          'margin_sign': cases[name]['margin_sign'],
                          'G_decimal_display': float(F(cases[name]['G'])),
                          'margin_decimal_display': float(F(cases[name]['new_margin_J_minus_half_S_plus_G']))}), flush=True)
    positive = all(F(c['new_margin_J_minus_half_S_plus_G']) > 0 for c in cases.values())
    reserve = min(F(c['new_margin_J_minus_half_S_plus_G']) for c in cases.values()) / 2 if positive else None
    result = {
        'scope': 'FC647-FC648 omitted labels3^t*h*q^e, t>=2, e>=1, on each fixed canonical head table; pure3 powers and singleton supports still excluded',
        'evidence': 'ordinary analytic depth-sum identities and exact fixed-table arithmetic; no Lean claim',
        'design_sha256': DESIGN_SHA256,
        'consumer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'table_inputs': inputs, 'saved_scores_input': score_provenance,
        'formula': 'G=sum_q b_q*(B5q+B7q), B=max_(root,headrow)(w_head/2)*sum_(otherheadrow)w_other*product_(private!=q)K',
        'ternary_height_tail_factor': '1/2',
        'no_parameter_search': True, 'producer_or_controls_executed': False,
        'continuation_executed': False, 'old_full_fee_recomputed': False,
        'actual_zero_fee_case': 'if a new nonternary cylinder lies in an already avoided original free group hole, its actual R_N intersection is empty; arbitrary phases need not satisfy containment',
        'negative_margin_next_gap': 'same-source grouped-hole/high-label joint hit masses; no moment or clipping scan',
        'cases': cases, 'both_margins_positive': positive,
        'common_reserve_if_both_positive': str(reserve) if reserve is not None else None,
        'execution': {'python': sys.version.split()[0], 'isolated': bool(sys.flags.isolated),
                      'site_disabled': bool(sys.flags.no_site), 'bytecode_disabled': bool(sys.flags.dont_write_bytecode)},
        'checks': CHECKS,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'event': 'output_written', 'output': str(args.output),
                      'checks': CHECKS, 'both_margins_positive': positive}), flush=True)


if __name__ == '__main__':
    main()
