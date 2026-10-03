"""Exact two-row phase reconstruction and seven-term convexification gap.

The carrier is an explicitly selected two-row subcarrier, not the repository's
75-row survivor set. No claim about the full 372-slot problem follows.
"""
from fractions import Fraction as F
import json
from math import prod
from pathlib import Path
import argparse

D = (3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315)
S = (3, 5, 7, 15, 21, 35, 105)
X = (0, 105)
CORE75 = ((3, 0), (5, 0), (7, 0), (9, 4), (15, 11), (21, 8),
          (35, 9), (45, 1), (63, 1), (105, 59), (315, 179))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def crt_old_new(d, a, prime, root):
    result = a + d * (((root - a) * pow(d, -1, prime)) % prime)
    need(0 <= result < d * prime and result % d == a
         and result % prime == root, 'CRT phase reconstruction')
    return result


def make_dictionary(prime, old_phases, roots):
    return [{'old_modulus': d, 'old_phase': old_phases[d],
             'outside_prime': prime, 'outside_root': roots[d],
             'actual_modulus': d * prime,
             'actual_phase': crt_old_new(d, old_phases[d], prime, roots[d])}
            for d in D]


def row_counts(dictionary, prime):
    hits, actual_deletions, survivors = [], [], []
    for x in X:
        active = [row for row in dictionary if x % row['old_modulus'] == row['old_phase']]
        removed = {row['outside_root'] for row in active} - {0}
        hits.append(len(active))
        actual_deletions.append(len(removed))
        # Independently check the numerical APs at every complete x/prime CRT point.
        alive = []
        for root in range(prime):
            point = crt_old_new(315, x, prime, root)
            bad = root == 0 or any(point % row['actual_modulus'] == row['actual_phase']
                                  for row in dictionary)
            if not bad:
                alive.append(root)
        survivors.append(alive)
        need(prime - 1 - len(active) == len(alive),
             'This literal dictionary realizes hit counts as distinct live-root deletions')
    return hits, actual_deletions, survivors


def kappa(d):
    saturation = ((3,) if d % 9 == 0 else ()) + tuple(p for p in (5, 7) if d % p == 0)
    return prod((F(p, p - 1) for p in saturation), start=F(1)) - 1


def calculate():
    old_a = {d: 0 if d in S or d == 9 else 1 for d in D}
    old_b = dict(old_a)
    old_b[9] = 6
    old_13 = {d: 0 for d in D}
    old_13.update({63: 42, 315: 105})
    roots_11 = {d: j + 1 for j, d in enumerate(S)}
    roots_11.update({9: 8, 45: 8, 63: 9, 315: 10})
    roots_13 = {d: j + 1 for j, d in enumerate(S)}
    roots_13.update({9: 8, 45: 9, 63: 8, 315: 9})
    dict_a = make_dictionary(11, old_a, roots_11)
    dict_b = make_dictionary(11, old_b, roots_11)
    dict_13 = make_dictionary(13, old_13, roots_13)
    ha, da, alive_a = row_counts(dict_a, 11)
    hb, db, alive_b = row_counts(dict_b, 11)
    h13, d13, alive_13 = row_counts(dict_13, 13)
    need(ha == da == [8, 7] and hb == db == [7, 8]
         and h13 == d13 == [9, 9], 'Literal hit and root-count vectors')
    for dictionary in (dict_a, dict_b):
        labels = [11, 13] + [row['actual_modulus'] for row in dictionary + dict_13]
        need(len(labels) == len(set(labels)) == 24 and all(m > 1 and m % 2 for m in labels),
             'One pairwise-distinct odd family, including the pure classes')
    coefficients = [kappa(d) + 1 for d in S]
    total = sum(coefficients, F(0))
    need(coefficients == [F(1), F(5, 4), F(7, 6), F(5, 4), F(7, 6), F(35, 24), F(35, 24)]
         and total == F(35, 4), 'Seven-term saturated coefficients')
    need(all(x % d == 0 for x in X for d in S), 'Each retained old cell contains both rows')
    # Endpoint row coefficients of F_A(p) and F_B(p), u=(p,1-p).
    ca = (total / 6, total / 9)
    cb = (total / 9, total / 6)
    actual = min(ca)
    hull = total / (F(5, 2) * 3)
    common = sum(ca, F(0)) / 2
    need(actual == F(35, 36) < 1 < hull == F(7, 6) < common == F(175, 144),
         'Exact strict actual/hull/common gap')
    need(ca[0] - ca[1] == cb[1] - cb[0] > 0,
         'Opposite linear slopes force the common optimum at p=1/2')
    # For a convex load state theta*A+(1-theta)*B,
    # V=total/(3*max(3-theta,2+theta)).  The two arguments sum to 5;
    # max>=5/2, with equality at theta=1/2.  This proves the entire hull max.
    need(F(3) + F(2) == 5 and F(3) - F(1, 2) == F(2) + F(1, 2) == F(5, 2),
         'Exact full-hull optimum certificate')
    # The omitted (d=5,J=empty) slot has kappa(5)=1/4 and cap=1.
    # Even the actual endpoint states therefore fail the full envelope.
    full_lower = actual + kappa(5)
    need(full_lower == F(11, 9) > 1, 'No vertex-positivity claim for the full 372-slot functional')
    need(all(10 in alive for alive in alive_a + alive_b + alive_13),
         'A common live outside root exists for these retained query cells')
    # A legitimate completed core dictionary with residue 1 at every d
    # retains both selected rows; it does NOT have exactly X as survivor set.
    core_survivors = [x for x in range(315) if all(x % d != 1 for d in D)]
    need(set(X) < set(core_survivors), 'Two-row carrier is a supported subcarrier only')
    actual75 = [x for x in range(315) if all(x % d != a for d, a in CORE75)]
    need(len(actual75) == 75 and not set(X).intersection(actual75),
         'The current literal 75-row source excludes both example rows')
    return {
        'carrier': X, 'divisor_labels': D, 'retained_old_labels': S,
        'pure_classes': [[11, 0], [13, 0]],
        'state_A_prime11_dictionary': dict_a,
        'state_B_prime11_dictionary': dict_b,
        'common_prime13_dictionary': dict_13,
        'state_A_hits': ha, 'state_B_hits': hb, 'common_prime13_hits': h13,
        'state_A_live_roots': alive_a, 'state_B_live_roots': alive_b,
        'common_prime13_live_roots': alive_13,
        'actual_root_deletion_equals_hit_count_on_selected_rows': True,
        'seven_coefficients': coefficients, 'coefficient_sum': total,
        'state_A_cost_coefficients': ca, 'state_B_cost_coefficients': cb,
        'maximum_actual_state_optimum': actual, 'maximum_convex_hull_optimum': hull,
        'best_common_row_law_cost': common,
        'full_envelope_endpoint_cost_lower': full_lower,
        'supporting_core_phases': [[d, 1] for d in D],
        'supporting_core_survivor_count': len(core_survivors),
        'selected_rows_are_the_full_core_survivor_set': False,
        'comparison_75_source_core': CORE75,
        'comparison_75_source_survivor_count': len(actual75),
        'selected_rows_belong_to_current_75_source': False,
        'counterexample_scope': 'Seven-term subfunctional on a two-row supported carrier. '
        'Refutes a general vertexwise-to-hull positivity implication, not '
        'the current 75-row/full372 universal feasibility question.',
        'lean_verification': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        retained = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == retained, 'Retained result agrees with exact recomputation')
    print(json.dumps(result, indent=2))
