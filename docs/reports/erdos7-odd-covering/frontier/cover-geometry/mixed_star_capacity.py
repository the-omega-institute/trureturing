#!/usr/bin/env python3
"""Exact star-block and infinite-label frontier certificate for sixteen heads.

Consumes one retained tail. Does not enumerate original phases, truncate the
actual survivor, rerun the old label producer, or perform Lean verification.
"""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, prod
from pathlib import Path
import argparse
import hashlib
import heapq
import json


def subsets(items):
    for mask in range(1 << len(items)):
        yield tuple(p for i, p in enumerate(items) if mask & (1 << i))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path,
                        default=Path(__file__).with_name('phase_resampling_arithmetic.json'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    raw = args.input.read_bytes()
    pin = 'da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f'
    if hashlib.sha256(raw).hexdigest() != pin:
        raise ValueError('retained tail pin mismatch')
    data = json.loads(raw)
    primes = (3, 5, 7, 11, 13, 17, 19)
    star_primes = primes[1:]
    star_labels = {3*p for p in star_primes}
    max_heads = 16
    checks = {}

    def require(name, condition):
        checks[name] = bool(condition)
        if not condition:
            raise ValueError(name)

    def cap(d):
        return F(1, d)*prod(F(p-1, p-2) for p in primes if d % p == 0)

    require('cutoff', data['cutoff'] == 10**9)
    alpha = F(data['alpha'])
    require('original_alpha', alpha == F(7235955529, 6075000000000))
    density_cap = 1/alpha
    tail = F(data['tail'])
    require('retained_tail_positive', tail > 0)
    dmax = prod(F(p-1, p-2) for p in primes)
    euler = prod(F(p, p-1) for p in primes)
    budget_a = euler-1
    require('density_envelope', dmax == F(4096, 935))
    require('unused_cap_envelope', budget_a == F(212731, 110592))
    require('same_G_cap_above_800', density_cap > 800)
    require('all_prime_extension_factors_decrease',
            all(F(1, p) < 1 and F(p-1, p*(p-2)) < 1 for p in primes))

    # Every mixed label descends from a squarefree pq seed. Every edge d -> dp
    # strictly decreases cap. A best-first frontier therefore visits the full
    # infinite label set in nonincreasing cap order. Deduplication is by the
    # original integer label; it does not merge distinct numerical moduli.
    heap = []
    seen = set()

    def enqueue(d):
        if d not in seen:
            seen.add(d)
            heapq.heappush(heap, (-cap(d), d))

    seeds = [p*q for p, q in combinations(primes, 2)]
    for d in seeds:
        enqueue(d)
    popped = []
    nonstar = []
    while len(nonstar) < max_heads:
        negative_cap, d = heapq.heappop(heap)
        value = -negative_cap
        popped.append((d, value))
        if d not in star_labels:
            nonstar.append((d, value))
        for p in primes:
            enqueue(d*p)

    require('all_seed_pairs', len(seeds) == 21 and len(set(seeds)) == 21)
    require('six_star_labels_were_visited',
            star_labels.issubset({d for d, _ in popped}))
    require('sixteen_nonstar_labels', len(nonstar) == 16)
    require('popped_labels_are_unique', len(popped) == len({d for d, _ in popped}))
    require('priority_order', all(x[1] >= y[1] for x, y in zip(popped, popped[1:])))
    require('unvisited_frontier_below_last_rank',
            all(-value <= nonstar[-1][1] for value, _ in heap))
    require('all_generated_successors_accounted',
            all(d*p in seen for d, _ in popped for p in primes))
    expected_nonstar = (45, 35, 63, 75, 105, 55, 99, 65,
                        135, 117, 165, 77, 85, 147, 195, 95)
    require('nonstar_rank_labels', tuple(d for d, _ in nonstar) == expected_nonstar)
    require('reported_comparison_labels_are_shallow',
            all(d <= data['cutoff'] for d, _ in popped))

    cumulative = [F(0)]
    for _, value in nonstar:
        cumulative.append(cumulative[-1]+value)
    c = {p: F(p-1, p*(p-2)) for p in star_primes}

    def union_bound(block):
        return 1-prod(1-c[p] for p in block)

    deep = dmax*tail
    profiles = []
    partition_evaluations = 0
    for chosen in subsets(star_primes):
        best = F(-1)
        maximizing_block = None
        for block in subsets(chosen):
            complement = tuple(p for p in chosen if p not in block)
            value = F(2, 3)*union_bound(block)+F(1, 3)*union_bound(complement)
            partition_evaluations += 1
            if value > best:
                best, maximizing_block = value, block
        rest = max_heads-len(chosen)
        upper = best+cumulative[rest]+deep
        profiles.append({
            'star_primes': list(chosen),
            'two_thirds_block': list(maximizing_block),
            'star_union_upper': str(best),
            'nonstar_slots': rest,
            'nonstar_cap_sum': str(cumulative[rest]),
            'actual_loss_upper': str(upper),
        })
        require('sixteen_heads_profile_' + ('_'.join(map(str, chosen)) or 'empty'),
                upper < F(173, 250))

    require('all_star_subsets', len(profiles) == 64)
    require('all_bipartitions', partition_evaluations == 729)
    worst = max(profiles, key=lambda row: F(row['actual_loss_upper']))
    require('worst_relaxed_star_subset', worst['star_primes'] == list(star_primes))
    require('worst_relaxed_two_thirds_block',
            worst['two_thirds_block'] == [5, 7, 11, 13, 17])
    loss_upper = F(worst['actual_loss_upper'])
    threshold = F(173, 250)
    remaining = 1-threshold
    rho_density_upper = dmax/remaining
    unused_upper = (budget_a-threshold)/remaining
    query_upper = (dmax-1)/remaining
    require('universal_loss_upper', loss_upper < threshold)
    require('unused_budget_below_four', unused_upper < 4)
    require('density_below_fifteen', rho_density_upper < 15)
    require('original_density_cap_retained', rho_density_upper < density_cap)
    require('direct_query_bound', query_upper == F(158050, 14399))
    # Taylor bounds: S_5(1)<e; the remainder after degree six is bounded by
    # (1/7!)/(1-1/8). Both inequalities have the needed strict direction.
    lower_e = sum(F(1, factorial(k)) for k in range(6))
    upper_e = (sum(F(1, factorial(k)) for k in range(7))
               + F(1, factorial(7))/(1-F(1, 8)))
    require('e_above_19_over_7', lower_e > F(19, 7))
    require('e_below_68_over_25', upper_e < F(68, 25))
    require('relative_entropy_below_eight_thirds', F(19, 7)**8 > rho_density_upper**3)
    require('log_original_cap_above_twenty_thirds', F(68, 25)**20 < F(800)**3)
    require('entropy_unused_budget', unused_upper+F(8, 3) < F(20, 3))
    require('total_query_target', query_upper < F(565, 51))
    require('query_upper_below_display', query_upper < F(10977, 1000))

    # Fixed actual core separating the new sixteen-head hypothesis from v<=2/3.
    # Each row carries an explicit private point, not a searched phase optimum.
    mixed = (
        (15, 2, {3: 2, 5: 2}), (21, 2, {3: 2, 7: 2}),
        (33, 2, {3: 2, 11: 2}), (45, 38, {3: 2, 5: 3}),
        (39, 2, {3: 2, 13: 2}), (35, 3, {5: 3, 7: 3}),
        (51, 2, {3: 2, 17: 2}), (63, 38, {3: 2, 7: 3}),
        (57, 2, {3: 2, 19: 2}), (75, 29, {3: 2, 5: 4}),
        (105, 53, {3: 5, 5: 3, 7: 4}),
    )
    pure = tuple((p**e, p**(e-1), {p: p**(e-1)})
                 for p in primes for e in (1, 2, 3))
    core = pure+mixed
    period = prod(p**3 for p in primes)

    def crt(coordinates):
        return sum(coordinates.get(p, 0)*(period//p**3)
                   * pow(period//p**3, -1, p**3) for p in primes) % period

    require('fixture_distinct_odd_labels',
            len({d for d, _, _ in core}) == len(core)
            and all(d > 1 and d % 2 == 1 for d, _, _ in core))
    require('fixture_exactly_32_originals_and_11_mixed', len(core) == 32 and len(mixed) == 11)
    require('fixture_complete_period', all(period % d == 0 for d, _, _ in core))
    require('fixture_normalized_original_phases', all(0 <= a < d for d, a, _ in core))
    require('fixture_all_originals_shallow', all(d <= data['cutoff'] for d, _, _ in core))
    require('fixture_zero_survives', all(0 % d != a for d, a, _ in core))
    private_points = []
    for d, phase, coordinates in core:
        point = crt(coordinates)
        hits = [k for k, a, _ in core if point % k == a]
        require('fixture_private_point_' + str(d), hits == [d])
        private_points.append({'label': d, 'phase': phase, 'private_point': point,
                               'nonzero_crt_coordinates': {str(p): x for p, x in coordinates.items()},
                               'hit_labels': hits})
    pure_factors = {p: 1/(1-sum(F(1, p**e) for e in (1, 2, 3))) for p in primes}
    actual_v = sum(F(1, d)*prod(pure_factors[p] for p in primes if d % p == 0)
                   for d, _, _ in mixed)
    require('fixture_actual_capacity', actual_v == F(1881697945217311, 2771672360984296))
    require('fixture_outside_old_capacity_hypothesis', actual_v > F(2, 3))
    require('fixture_inside_new_head_hypothesis', len(mixed) <= max_heads)

    result = {
        'input_name': args.input.name, 'input_sha256': pin,
        'scope': 'six-star union relaxation and infinite numerical cap frontier; '
                 'all actual pure/deep originals and phases retained; no Lean verification',
        'primes': list(primes), 'cutoff': data['cutoff'], 'shallow_mixed_limit': max_heads,
        'alpha': str(alpha), 'Lambda': str(density_cap), 'A': str(budget_a),
        'Dmax': str(dmax), 'retained_tail': str(tail), 'deep_capacity_upper': str(deep),
        'seed_count': len(seeds), 'popped_count': len(popped),
        'frontier_count': len(heap), 'seen_count': len(seen),
        'frontier_max_cap': str(-heap[0][0]),
        'nonstar_rank': [{'label': d, 'cap': str(k)} for d, k in nonstar],
        'profiles': profiles, 'partition_evaluations': partition_evaluations,
        'worst_profile': worst, 'actual_loss_upper': str(loss_upper),
        'loss_threshold': str(threshold), 'strict_loss_margin': str(threshold-loss_upper),
        'density_upper': str(rho_density_upper), 'unused_upper': str(unused_upper),
        'entropy_upper': '8/3', 'entropy_unused_upper': str(unused_upper+F(8, 3)),
        'log_Lambda_lower': '20/3', 'total_query_upper': str(query_upper),
        'target': '565/51', 'target_margin': str(F(565, 51)-query_upper),
        'actual_separation_fixture': {
            'scope': 'complete fixed 32-class irredundant core; no other originals',
            'pure_rule': 'p^(e-1) modulo p^e, p in P and e=1,2,3',
            'complete_period': period, 'mixed_count': len(mixed),
            'private_point_certificates': private_points,
            'actual_pure_factors': {str(p): str(x) for p, x in pure_factors.items()},
            'actual_weighted_mixed_capacity': str(actual_v),
            'capacity_minus_two_thirds': str(actual_v-F(2, 3)),
            'conclusion': 'new hypothesis holds and old v<=2/3 hypothesis fails; '
                          'no lower bound on actual union loss is claimed',
        },
        'checks': checks, 'passed_count': len(checks),
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'passed_count': len(checks), 'profiles': len(profiles),
                      'popped_labels': len(popped), 'loss_upper': str(loss_upper),
                      'total_query_upper': str(query_upper),
                      'result': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
