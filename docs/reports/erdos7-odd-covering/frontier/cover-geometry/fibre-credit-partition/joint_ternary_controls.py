"""Exact controls for the explicitly restricted squarefree-pair proof.

This is not an unrestricted covering-system search or Lean verification.
All paths are explicit and no filesystem discovery is performed.
"""

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import prod
from pathlib import Path


CHECKS = 0


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def fixed_certificates():
    primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    thresholds = (0, 6, 5, 3, 3, 3, 3, 3, 3, 3, 3)
    expected = (Fraction(1, 486), Fraction(1, 81), Fraction(1, 24),
                Fraction(2, 45), Fraction(5, 72), Fraction(1, 15),
                Fraction(7, 144), Fraction(4, 63), Fraction(1, 20),
                Fraction(5, 99))
    rows = []
    charges = []
    for i, (q, h) in enumerate(zip(primes, thresholds)):
        if i == 0:
            continue
        denominator = q - h * i
        check(denominator > 0, 'positive threshold denominator')
        charge = Fraction(3 * i, 2 * (3 ** h) * denominator)
        check(charge == expected[i - 1], 'independent fixed table entry')
        rows.append({'prime': q, 'indegree_bound': i, 'threshold': h,
                     'charge': str(charge)})
        charges.append(charge)
    total = sum(charges, Fraction(0))
    delta = Fraction(1, 2) - total
    check(total == Fraction(672449, 1496880), 'fixed bad-mass total')
    check(delta == Fraction(75991, 1496880) and delta > 0,
          'eleven-prime positive mass')
    period = prod(primes)
    check(period == 50708377254535, 'squarefree private period')
    full_bound = delta / period
    check(full_bound == Fraction(75991, 75904355744768350800),
          'full Haar normalization')
    odd_tail = Fraction(1, 81) / (1 - Fraction(1, 3))
    check(odd_tail == Fraction(1, 54), 'odd-integer geometric tail from 11')
    degenerate_total = Fraction(1, 3) + Fraction(1, 9) + odd_tail
    check(degenerate_total == Fraction(25, 54), 'two-degenerate bad mass')
    check(Fraction(1, 2) - degenerate_total == Fraction(1, 27),
          'two-degenerate good mass')
    return {'rows': rows, 'bad_mass_upper': str(total),
            'good_ternary_lower': str(delta), 'private_period': period,
            'full_Haar_lower_for_displayed_primes': str(full_bound),
            'two_degenerate_bad_mass_upper': str(degenerate_total),
            'two_degenerate_good_ternary_lower': '1/27'}


def enumerate_actual_family(case):
    primes = (5, 7, 11)
    height = 3
    ternary_period = 3 ** height
    private_period = prod(primes)
    edges = list(combinations(range(3), 2)) if case < 2 else [(0, 1), (1, 2)]
    originals = []
    for i, j in edges:
        for k in range(height + 1):
            if case == 2 and (i + k) % 3 == 0:
                continue
            ternary = (1 if case == 0 else 2 * k + i + 2 * j + case) % (3 ** k)
            ri = (k + j + case) % primes[i]
            rj = (2 * k + i + 2 * case) % primes[j]
            originals.append((k, i, j, ternary, ri, rj))
    pure = [(1, 0), (2, 4)]
    numerical_labels = [3 ** k * primes[i] * primes[j]
                        for k, i, j, _, _, _ in originals]
    numerical_labels += [3 ** k for k, _ in pure]
    check(len(numerical_labels) == len(set(numerical_labels)),
          'actual numerical labels stay distinct')
    incoming = [len({i for _, i, j, _, _, _ in originals if j == v})
                for v in range(3)]
    points = list(product(*(range(q) for q in primes)))
    actual_count = 0
    integral_count_bound = Fraction(0)
    good_count = 0
    allowed_t = []
    bad_counts = [0, 0, 0]
    counts_at_t = {}
    for t in range(ternary_period):
        active = [row for row in originals if t % (3 ** row[0]) == row[3]]
        counts = [sum(row[2] == v for row in active) for v in range(3)]
        counts_at_t[t] = counts
        surviving_private = sum(
            all(not (x[i] == ri and x[j] == rj)
                for _, i, j, _, ri, rj in active)
            for x in points)
        sequential_count = prod(max(q - c, 0) for q, c in zip(primes, counts))
        check(surviving_private >= sequential_count,
              'actual private count dominates sequential extension count')
        if any(t % (3 ** k) == a for k, a in pure):
            continue
        allowed_t.append(t)
        actual_count += surviving_private
        integral_count_bound += Fraction(sequential_count, private_period * ternary_period)
        good_count += all(c < q for c, q in zip(counts, primes))
        for v in range(3):
            bad_counts[v] += counts[v] >= primes[v]
    actual_mass = Fraction(actual_count, ternary_period * private_period)
    good_mass = Fraction(good_count, ternary_period)
    check(actual_mass >= integral_count_bound >= good_mass / private_period,
          'full joint Haar integral and good-fibre count normalization')
    beta_sum = Fraction(0)
    for v, d in enumerate(incoming):
        if d == 0:
            check(bad_counts[v] == 0, 'zero indegree has no bad fibre')
            continue
        bounds = []
        for h in range((primes[v] - 1) // d + 1):
            actual_tail = sum(
                sum(t % (3 ** k) == a for t in allowed_t)
                for k, _, j, a, _, _ in originals if j == v and k >= h)
            z = Fraction(actual_tail, ternary_period)
            bound = z / (primes[v] - h * d)
            check(Fraction(bad_counts[v], ternary_period) <= bound,
                  'actual-prefix Markov budget')
            check(z <= Fraction(3 * d, 2 * 3 ** h),
                  'actual tail below geometric inventory enlargement')
            bounds.append(bound)
        beta_sum += min(Fraction(len(allowed_t), ternary_period), *bounds)
    check(good_mass >= Fraction(len(allowed_t), ternary_period) - beta_sum,
          'union of bad ternary sets needs no independence')
    return {'case': case, 'pair_labels': len(originals), 'pure3_labels': len(pure),
            'full_grid_size': ternary_period * private_period,
            'actual_survivor_count': actual_count,
            'actual_Haar_survivor': str(actual_mass),
            'integrated_sequential_lower': str(integral_count_bound),
            'actual_good_ternary_mass': str(good_mass)}


def actual_dead_fibre():
    pairs = list(product(range(5), range(7)))
    height = len(pairs)
    active_pairs = set()
    actual_mass = Fraction(1, 3)  # root 2; root 0 is the pure3 original.
    sequential_mass = Fraction(1, 3)
    good_mass = Fraction(1, 3)
    for depth, pair in enumerate(pairs, 1):
        active_pairs.add(pair)
        # Exact shell around t=1: first mismatch after this depth, or final cylinder.
        shell = Fraction(1, 3 ** depth) if depth == height else Fraction(2, 3 ** (depth + 1))
        survivor_count = sum((a, b) not in active_pairs for a, b in pairs)
        lower_count = 5 * max(7 - depth, 0)
        check(survivor_count >= lower_count, 'nested actual pair-family fibre bound')
        actual_mass += shell * Fraction(survivor_count, 35)
        sequential_mass += shell * Fraction(lower_count, 35)
        if depth < 7:
            good_mass += shell
    check(len(active_pairs) == 35 and survivor_count == 0, 'deepest fibre is dead')
    formula = Fraction(2, 3) - (1 - Fraction(1, 3 ** 35)) / 70
    check(actual_mass == formula > 0, 'exact globally phased dead-fibre example')
    check(good_mass == Fraction(2, 3) - Fraction(1, 3 ** 7), 'exact bad ternary cylinder')
    check(actual_mass >= sequential_mass >= good_mass / 35,
          'dead fibres do not invalidate the global positive bound')
    return {'private_primes': [5, 7], 'pair_labels': 35, 'pure3_labels': 1,
            'deepest_ternary_height': 35, 'deepest_private_survivors': 0,
            'actual_Haar_survivor': str(actual_mass),
            'integrated_sequential_lower': str(sequential_mass),
            'good_ternary_mass': str(good_mass)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = {'scope': 'pure3 and squarefree nonternary pairs only; ordinary exact controls',
              'fixed_certificates': fixed_certificates(),
              'actual_finite_families': [enumerate_actual_family(i) for i in range(3)],
              'actual_dead_fibre': actual_dead_fibre()}
    result['exact_checks'] = CHECKS
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'exact_checks': CHECKS, 'output': str(args.output)}))


if __name__ == '__main__':
    main()
