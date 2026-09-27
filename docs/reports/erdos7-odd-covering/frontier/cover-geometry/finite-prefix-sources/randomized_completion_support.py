#!/usr/bin/env python3
"""Exact constants for randomized completion with full original survivor support.

The countable probability argument, source-uniformity and measure transport are
ordinary proof premises described in the companion note. No geometry rerun or
Lean certification is performed. Checks remain active under Python -O.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
import json
from math import prod
from pathlib import Path

SEED_SHA = '2ff88432077332183296e76c9119791e6fa6e05cbf8476454489069c249f2e63'
RELATIVE_LEDGER_SHA = '35bce0fade7fe0fb1b98b37193d3c4ba30e2c2a7a8ebdd34d99c24166d53a2bc'
PRIMES = (3, 5, 7, 11, 13, 17, 19)
MIXED = (15, 21, 35, 45, 63, 75, 105, 165)
CAPS = (Q(3, 2), Q(5, 3), Q(3, 2), Q(2), Q(9, 5))

def need(ok, why):
    if not ok:
        raise ValueError(why)

def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value

def finite_completion_control():
    original = {3: 0, 9: 0, 27: 2}
    selected = (3, 9, 27)
    states = [(Q(1), {})]
    for m in selected:
        updated = []
        for weight, completed in states:
            free = [a for a in range(m)
                    if all(a % d != phase for d, phase in completed.items() if m % d == 0)]
            choices = [original[m]] if original[m] in free else free
            for a in choices:
                updated.append((weight/len(choices), {**completed, m: a}))
        states = updated
    need(len(states) == 20 and sum((w for w, _ in states), Q(0)) == 1,
         'finite adaptive completion total probability')
    original_covered = {x for x in range(27) if any(x % m == a for m, a in original.items())}
    original_survivors = set(range(27))-original_covered
    preserved = {x: Q(0) for x in range(27)}
    weight_counts = {}
    for weight, completed in states:
        covered = {x for x in range(27) if any(x % m == a for m, a in completed.items())}
        need(original_covered <= covered, 'each finite completion preserves original coverage')
        weight_counts[str(weight)] = weight_counts.get(str(weight), 0)+1
        for x in set(range(27))-covered:
            preserved[x] += weight
    need(weight_counts == {'1/6': 5, '1/90': 15}, 'adaptive completion weights')
    need(len(original_survivors) == 17, 'finite original survivor count')
    need({preserved[x] for x in original_survivors} == {Q(37, 45), Q(5, 6)},
         'finite preservation probabilities')
    need(preserved[1] == Q(37, 45), 'target-one preservation')
    need(all(preserved[x] == 0 for x in original_covered), 'no mass outside original survivors')
    need(1 in original_survivors and any(c == {3: 0, 9: 1, 27: 2} for _, c in states),
         'one legal fixed completion removes an original survivor')
    return {'period': 27, 'original_classes': original, 'selected_moduli': selected,
            'outcomes': len(states), 'weight_counts': weight_counts,
            'original_survivor_count': len(original_survivors),
            'minimum_preservation': min(preserved[x] for x in original_survivors),
            'target_one_preservation': preserved[1],
            'deterministic_completion_killing_target_one': {3: 0, 9: 1, 27: 2}}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seed', required=True, type=Path)
    ap.add_argument('--relative-ledger', required=True, type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    raw = args.seed.read_bytes()
    need(sha256(raw).hexdigest() == SEED_SHA, 'retained seven-core seed identity')
    seed = json.loads(raw)
    mass = Q(seed['seven_core_live_mass_lower'])
    upper = Q(seed['seven_core_unnormalized_density_cap'])
    R = Q(seed['seven_core_query_R_upper'])
    need((mass, upper, R) == (Q(1, 33750), Q(27, 2), Q(70874, 3375)), 'source seed constants')
    relative_raw = args.relative_ledger.read_bytes()
    need(sha256(relative_raw).hexdigest() == RELATIVE_LEDGER_SHA, 'relative terminal summary identity')
    relative = json.loads(relative_raw)
    need(relative['certificate_sha256'] == 'a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac',
         'same original terminal certificate')
    rho = Q(relative['maximum_aggregate_loss_reserve_ratio'])
    query_bound = Q(relative['query_bound_conditional_on_source_bridge'])
    need(rho == Q(16873, 16875) and query_bound == 11 + 10*rho == Q(70871, 3375),
         'stronger relative-ledger common-query bound')
    need(relative['row_count'] == 28001 and relative['minimum_integer_surplus'] == 4,
         'relative ledger retains complete original source and absolute gap')
    selected = set(MIXED)
    for p in PRIMES:
        n = p
        while n <= max(MIXED):
            selected.add(n)
            n *= p
    mixed_rows = []
    for m in MIXED:
        proper = sorted(d for d in selected if d < m and m % d == 0)
        charged = sum(m // d for d in proper)
        free = m - charged
        need(free >= 2, 'at least two free selected mixed residues')
        mixed_rows.append({'m': m, 'proper_selected_divisors': proper,
                           'free_lower': free, 'point_preservation_lower': Q(free-1, free)})
    need([row['free_lower'] for row in mixed_rows] == [7, 11, 23, 13, 23, 27, 19, 51], 'mixed free lower counts')
    pure_rows = []
    for p in PRIMES:
        # Finite controls of the stated all-e geometric identity.
        for e in range(1, 13):
            free = p**e - sum(p**(e-j) for j in range(1, e))
            need(free == ((p-2)*p**e+p)//(p-1), 'pure free-residue formula')
            need(Q(free) >= Q(p-2, p-1)*p**e, 'pure free-residue geometric lower')
        root = Q(p-1, p)
        tail_bad = Q(1, p*(p-2))
        pure_rows.append({'p': p, 'root_preservation_lower': root,
                          'sum_inverse_free_tail_upper': tail_bad,
                          'all_depth_preservation_lower': root*(1-tail_bad)})
    # Enumerate actual T-plus supersets for each possible |T| and active count.
    charged_rows = []
    for s in range(5):
        for t in ([0] if s == 0 else range(1, s+1)):
            active = set(range(t))
            target = 5
            supersets = [set(c) for c in combinations(range(6), s) if active <= set(c)]
            probability = Q(sum(target not in c for c in supersets), len(supersets))
            need(probability == Q(6-s, 6-t), 'charged point-preservation probability')
            need(probability >= Q(2, 5), 'uniform charged point-preservation lower')
            charged_rows.append({'s': s, 't': t, 'probability': probability})
    need(min(row['probability'] for row in charged_rows) == Q(2, 5), 'charged minimum is attained')
    pure = prod((row['all_depth_preservation_lower'] for row in pure_rows), start=Q(1))
    mixed = prod((row['point_preservation_lower'] for row in mixed_rows), start=Q(1))
    kappa = pure*mixed*Q(2, 5)
    live_lower = prod((Q(p-1, p-2) for p in PRIMES[2:]), start=Q(1))
    need(live_lower == Q(1536, 935) and prod(CAPS, start=Q(1)) == upper, 'live density factors')
    anchor_upper = Q(1, 2)*Q(3, 4)
    unnormalized_lower = live_lower*kappa
    normalized_lower = unnormalized_lower/anchor_upper
    normalized_upper = upper/mass
    need(kappa == Q(33886755094528, 713214217048905), 'total preservation constant')
    need(normalized_lower == Q(138800148867186688, 666855292940726175), 'normalized lower density constant')
    need(normalized_lower > Q(1, 5), 'rounded positive lower density')
    need(normalized_upper == 455625, 'unchanged normalized upper density')
    result = encode({
        'scope': 'Exact finite constants only. General preservation probability, source comparison uniformity and averaging are ordinary proofs; no source geometry rerun or Lean certification.',
        'seed_sha256': SEED_SHA, 'relative_ledger_sha256': RELATIVE_LEDGER_SHA,
        'reference_primes': PRIMES,
        'mixed_rows': mixed_rows, 'pure_rows': pure_rows, 'charged_rows': charged_rows,
        'finite_adaptive_completion_control': finite_completion_control(),
        'pure_preservation_lower': pure, 'mixed_preservation_lower': mixed,
        'charged_preservation_lower': Q(2, 5), 'whole_support_preservation_lower': kappa,
        'live_density_lower_on_enlarged_support': live_lower,
        'unnormalized_density_lower_on_original_survivors': unnormalized_lower,
        'total_mass_upper': anchor_upper, 'total_mass_lower': mass,
        'normalized_density_lower_on_original_survivors': normalized_lower,
        'rounded_lower_density': Q(1, 5), 'normalized_density_upper': normalized_upper,
        'previous_query_R_upper': R, 'query_R_upper': query_bound,
        'relative_terminal_loss_reserve_ratio': rho,
        'normalization_gap_above_rounded_lower': normalized_lower-Q(1, 5)
    })
    body = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(body)
        print('PASS: pinned common-law inputs, relative query bound, original-survivor density, and finite random-completion control.')
    else:
        print(body, end='')

if __name__ == '__main__':
    main()
