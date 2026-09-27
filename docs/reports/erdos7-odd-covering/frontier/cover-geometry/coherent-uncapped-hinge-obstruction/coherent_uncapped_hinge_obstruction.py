#!/usr/bin/env python3
"""Exact finite certificate for an AH9-interface/coherent-load counterexample.

Ordinary proof obligations are stated in the companion note. This program checks
finite rational sums, actual label inventory and the claimed strict gaps. It does
not reconstruct Report467's source selector or prove a Lean theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import prod, isqrt, lcm
import argparse
import json

P = (3, 5, 7, 11, 13, 17, 19)
A = F(70871, 3375)
LAMBDA = F(6075000000000, 7235955529)
MIX = F(2, 5)
THRESHOLD = 32
CURRENT = 23

def require(test, message):
    if not test:
        raise ArithmeticError(message)

def rank_colored_check(profiles, event_mass, uncapped_hinge):
    """Verify one actual rank-coloured family, including literal private points."""
    labels = []
    for powers in profiles:
        rank = sum(powers)
        if rank == 0:
            continue
        d = prod(p ** e for p, e in zip(P, powers))
        modulus = CURRENT * d
        residue = d * ((rank * pow(d, -1, CURRENT)) % CURRENT)
        point, period = 0, 1
        for r, m in [(p ** e, p ** 3) for p, e in zip(P, powers)] + [(rank, CURRENT)]:
            point += period * (((r - point) * pow(period, -1, m)) % m)
            period *= m
        require(0 <= residue < modulus and residue % d == 0 and residue % CURRENT == rank, 'rank original CRT')
        require(all(point % (p ** 3) == p ** e for p, e in zip(P, powers)), 'private exact valuations')
        require(point % CURRENT == rank, 'private current colour')
        labels.append((rank, d, modulus, residue, point))
    require(len(labels) == len({row[2] for row in labels}) == 2186, 'rank distinct originals')
    require(period == CURRENT * prod(p ** 3 for p in P), 'private witness period')
    memberships = 0
    for i, (_, _, _, _, point) in enumerate(labels):
        hits = []
        for j, (_, _, modulus, residue, _) in enumerate(labels):
            memberships += 1
            if point % modulus == residue:
                hits.append(j)
        require(hits == [i], 'private witness has exactly its own membership')
    colour_counts, antichain_pairs = {}, 0
    for rank in range(1, 15):
        group = [d for r, d, _, _, _ in labels if r == rank]
        colour_counts[rank] = len(group)
        for i, d in enumerate(group):
            for other in group[i + 1:]:
                require(d % other != 0 and other % d != 0, 'same-colour divisor antichain')
                antichain_pairs += 1
    haar_actual = event_actual = haar_load = event_load = F(0)
    for powers in profiles:
        mass = prod(F(p - 1, p ** (e + 1)) if e < 2 else F(1, p ** 2)
                    for p, e in zip(P, powers))
        d2 = prod(e + 1 for e in powers)
        colours = {0}
        for exponent in powers:
            colours = {r + k for r in colours for k in range(exponent + 1)}
        colours.discard(0)
        require(colours == set(range(1, sum(powers) + 1)), 'all and only attainable ranks')
        alpha = F(len(colours), CURRENT)
        load = F(d2 - 1, CURRENT)
        actual = max(F(0), 2 * alpha - 1)
        additive = max(F(0), 2 * load - 1)
        require(alpha <= load and alpha <= F(14, 23) and actual <= F(5, 23), 'actual rank union bound')
        haar_actual += mass * actual
        haar_load += mass * additive
        if d2 >= THRESHOLD:
            event_actual += mass * actual
            event_load += mass * additive
    actual_hinge = (1 - MIX) * haar_actual + MIX * event_actual / event_mass
    repeated_hinge = (1 - MIX) * haar_load + MIX * event_load / event_mass
    require(repeated_hinge == uncapped_hinge, 'recolouring preserves additive hinge')
    require(haar_actual == event_actual, 'positive actual hinge lies in source event')
    require(actual_hinge == F(1219830493798061, 585086293700984182482375), 'rank actual hinge exact value')
    return {
        'family': 'a_d mod23d, a_d=0 mod d and a_d=sum_p v_p(d) mod23, 1<d|product_p p^2',
        'old_coherence': 'centre0', 'full_centre_coherence': False,
        'actual_originals': len(labels), 'colour_counts': colour_counts,
        'private_witness_period': period, 'private_witnesses': len(labels),
        'literal_membership_checks': memberships, 'same_colour_antichain_pairs': antichain_pairs,
        'actual_union_fraction': 'sum_p min(v_p(x),2)/23',
        'actual_union_hinge': str(actual_hinge),
        'actual_union_hinge_decimal': float(actual_hinge),
        'Haar_actual_union_hinge': str(haar_actual),
        'max_actual_union_fraction': '14/23', 'max_pointwise_union_hinge': '5/23',
        'uncapped_additive_hinge': str(repeated_hinge),
        'private_rule': 'CRT(p^e mod p^3 for every p; rank mod23)',
    }

def rank_continuation_check(r_infty, actual_hinge):
    """Apply existing killed-row/query accounting to the fixed rank head."""
    delta, next_prime = F(1, 2), 29
    for rank in range(15):
        alpha = F(rank, CURRENT)
        theta = min(alpha, delta)
        row_mass = (1 - alpha) / (1 - theta)
        require(row_mass == 1 - max(F(0), (alpha - delta) / (1 - delta)),
                'rank killed row mass identity')
        require(0 <= row_mass <= 1 and 1 / (1 - theta) <= 2,
                'rank killed marginal and prefix caps')
    live_mass = 1 - actual_hinge
    query_numerator = r_infty + (r_infty + 1) / ((1 - delta) * (CURRENT - 1))
    next_query_upper = query_numerator / live_mass
    query_gap = next_prime - 2 - next_query_upper
    deletion_upper = (next_query_upper + 1) / (next_prime - 1)
    normalized_reserve = 1 - deletion_upper
    unnormalized_reserve = live_mass * normalized_reserve
    ah9_numerator = A + (A + 1) / ((1 - delta) * (CURRENT - 1))
    hinge_threshold = 1 - ah9_numerator / (next_prime - 2)
    require(0 < live_mass <= 1 and query_gap > 0, 'rank continuation query budget')
    require(0 < normalized_reserve < 1, 'rank arbitrary29 continuation reserve')
    require(unnormalized_reserve ==
            ((next_prime - 2) * live_mass - query_numerator) / (next_prime - 1),
            'rank one-normalization reserve identity')
    require(hinge_threshold == F(49516, 334125) and actual_hinge < hinge_threshold,
            'AH9 sufficient actual-hinge threshold')
    exact = {
        'delta23': delta, 'actual_hinge23': actual_hinge, 'old_R_infty': r_infty,
        'killed_mass23': live_mass, 'query_numerator': query_numerator,
        'R_new_upper': next_query_upper, '27_minus_R_new_upper': query_gap,
        'arbitrary29_deletion_upper': deletion_upper,
        'normalized29_survivor_lower': normalized_reserve,
        'unnormalized_joint_survivor_lower': unnormalized_reserve,
        'AH9_actual_hinge_threshold': hinge_threshold,
        'AH9_threshold_minus_actual_hinge': hinge_threshold - actual_hinge,
    }
    return {
        'scope': 'all 2186 rank-coloured23 originals fixed; add only distinct29-bearing numerical originals d*29^k, k>=1, d supported on old P and23, arbitrary finite heights and fixed phases; no additional old-only or23-only blockers; not canonical467 source; no Lean claim',
        'source': 'the same original all-height old mixture and its actual23 killed kernel, normalized once',
        'measure': 'the joint survivor lower bound is under the unnormalized killed23 law tensor Haar29, not Haar on the full carrier',
        'next_prime': next_prime, 'rank_rows_checked': 15,
        'exact': {key: str(value) for key, value in exact.items()},
        'decimals': {key: float(exact[key]) for key in
                     ('R_new_upper', '27_minus_R_new_upper', 'normalized29_survivor_lower',
                      'unnormalized_joint_survivor_lower', 'AH9_actual_hinge_threshold')},
    }

def ternary_coloured_check(profiles, event_mass, r_infty):
    """Check one fixed colour formula and its all-threshold cylinder majorant."""
    exponents = profiles[1:]
    colour = tuple(sum(3 ** i * e for i, e in enumerate(v)) % CURRENT
                   for v in exponents)
    label_index = {v: i for i, v in enumerate(exponents)}
    profile_index = {v: i for i, v in enumerate(profiles)}
    ideals = tuple(tuple(label_index[e] for e in product(*(range(t + 1) for t in v))
                         if any(e)) for v in profiles)
    retained = tuple(i for i, v in enumerate(exponents)
                     if all(j == i or colour[j] != colour[i]
                            for j in ideals[profile_index[v]]))
    retained_set = set(retained)
    require(len(retained) == 536, 'ternary colour minimal labels')
    q2 = prod(p ** 2 for p in P)
    haar_counts, event_counts = [0] * 24, [0] * 24
    for v, ideal in zip(profiles, ideals):
        active = {colour[i] for i in ideal}
        reduced = {colour[i] for i in ideal if i in retained_set}
        require(active == reduced, 'ternary reduction preserves actual union')
        n = prod(p * (p - 1) if e == 0 else p - 1 if e == 1 else 1
                 for p, e in zip(P, v))
        haar_counts[len(active)] += n
        if prod(e + 1 for e in v) >= THRESHOLD:
            event_counts[len(active)] += n
    event_total = sum(event_counts)
    require(sum(haar_counts) == q2 and F(event_total, q2) == event_mass,
            'ternary same-source cell partition')
    masses = tuple((1 - MIX) * F(n, q2) + MIX * F(ne, event_total)
                   for n, ne in zip(haar_counts, event_counts))
    require(sum(masses) == 1 and masses[0] > 0, 'ternary probability and live fibre')
    h = sum((w * F(max(0, 2 * c - CURRENT), CURRENT)
             for c, w in enumerate(masses)), F(0))
    threshold = F(49516, 334125)
    require(h == F(898342963018123305464329, 2535373939370931457423625)
            and h > threshold, 'ternary actual hinge threshold obstruction')
    originals = []
    for i in retained:
        v, c = exponents[i], colour[i]
        d = prod(p ** e for p, e in zip(P, v))
        residue = d * ((c * pow(d, -1, CURRENT)) % CURRENT)
        point, period = 0, 1
        for r, m in [(p ** e, p ** 3) for p, e in zip(P, v)] + [(c, CURRENT)]:
            point += period * (((r - point) * pow(period, -1, m)) % m)
            period *= m
        require(d > 1 and all(point % (p ** 3) == p ** e for p, e in zip(P, v)),
                'ternary private exact old valuations and no pure23')
        originals.append((i, CURRENT * d, residue, point))
    require(len({m for _, m, _, _ in originals}) == len(retained),
            'ternary distinct numerical labels')
    membership_checks = 0
    for i, _, _, point in originals:
        hits = []
        for j, modulus, residue, _ in originals:
            membership_checks += 1
            if point % modulus == residue:
                hits.append(j)
        require(hits == [i], 'ternary literal private point')
    endpoints = []
    for j in range(CURRENT):
        delta = F(j, CURRENT)
        live = sum((w * (1 - F(c, CURRENT)) / (1 - min(F(c, CURRENT), delta))
                    for c, w in enumerate(masses)), F(0))
        numerator = r_infty + (r_infty + 1) / ((1 - delta) * (CURRENT - 1))
        require(live > 0, 'ternary threshold has positive live mass')
        endpoints.append((delta, live, numerator / live))
    best_delta, best_live, best_bound = min(endpoints, key=lambda row: row[2])
    require(best_delta == F(11, 23)
            and best_bound == F(35929581952530320495737057385,
                                1047991562150140478176100352)
            and best_bound > 27, 'ternary all-endpoint majorant obstruction')
    exact = {
        'actual_union_hinge': h, 'AH9_hinge_threshold': threshold,
        'hinge_minus_threshold': h - threshold,
        'half_threshold_cylinder_majorant': (r_infty + (r_infty + 1) / 11) / (1 - h),
        'best_delta': best_delta, 'best_live_mass': best_live,
        'minimum_cylinder_majorant': best_bound,
        'minimum_cylinder_majorant_minus27': best_bound - 27,
        'dead_fibre_mu_mass': masses[CURRENT],
    }
    return {
        'scope': 'fixed703 old law and old centre0; this uniform-cylinder query majorant fails for every delta in [0,1); not an actual query lower bound, not a covering counterexample; no Lean claim',
        'colour_formula': 'sum_i 3^i e_i mod23, i=0..6 in increasing old-prime order',
        'original_class': 'old residue0 mod product_p p^e; current residue colour(e) mod23',
        'reduction': 'retain exactly the coordinatewise minimal nonzero exponent vectors within each colour',
        'initial_labels': len(exponents), 'retained_labels': len(retained),
        'removed_labels': len(exponents) - len(retained),
        'retained_exponents_and_colours': [list(exponents[i]) + [colour[i]] for i in retained],
        'profile_union_equivalence_checks': len(profiles),
        'private_witness_period': period, 'private_witnesses': len(retained),
        'literal_membership_checks': membership_checks,
        'private_rule': 'CRT(p^e mod p^3 for every p; colour(e) mod23)',
        'actual_union_histogram': [
            {'active_colours': c, 'mu_mass': str(w)} for c, w in enumerate(masses)],
        'threshold_endpoints': [
            {'delta': str(d), 'live_mass': str(s), 'cylinder_majorant': str(b)}
            for d, s, b in endpoints],
        'all_threshold_scope': 'ordinary linear-fractional endpoint proof covers every delta in [0,1), including intervals between checked endpoints and delta>22/23; alpha=1 rows remain dead',
        'exact': {key: str(value) for key, value in exact.items()},
        'decimals': {key: float(exact[key]) for key in
                     ('actual_union_hinge', 'minimum_cylinder_majorant',
                      'minimum_cylinder_majorant_minus27', 'dead_fibre_mu_mass')},
    }

def ternary_actual_query_check(profiles, event_mass, ternary):
    """Exact joint cylinder maxima; the note proves the complete-height tails."""
    q2 = prod(p ** 2 for p in P)
    event_count = event_mass * q2
    require(event_count.denominator == 1, 'ternary integer event count')
    event_count = event_count.numerator
    common = lcm(*range(12, 24))
    denominator = 5 * q2 * event_count * common
    colour = {e: sum(3 ** i * r for i, r in enumerate(e)) % CURRENT
              for e in profiles if any(e)}
    cells = []
    for v in profiles:
        active = {colour[e] for e in product(*(range(r + 1) for r in v)) if any(e)}
        n = prod((p * (p - 1), p - 1, 1)[r] for p, r in zip(P, v))
        event = prod(r + 1 for r in v) >= THRESHOLD
        numerator = n * (3 * event_count + 2 * q2 * event)
        numerator *= common // (CURRENT - min(len(active), 11))
        cells.append([numerator if c not in active else 0 for c in range(CURRENT)])
    live_numerator = sum(map(sum, cells))
    live = F(live_numerator, denominator)
    require(live == F(ternary['exact']['best_live_mass']), 'same ternary live law')
    divisions = 0

    def transform(values):
        nonlocal divisions
        dimensions = [3] * len(P)
        for axis, p in enumerate(P):
            stride = prod(dimensions[axis + 1:])
            updated = [0] * (2 * len(values))
            for block in range(len(values) // (3 * stride)):
                for offset in range(stride):
                    at = block * 3 * stride + offset
                    a, b, c = values[at], values[at + stride], values[at + 2 * stride]
                    require(a % (p * (p - 1)) == 0 and b % (p - 1) == 0,
                            'exact Haar multiplicity division')
                    divisions += 1
                    rows = (a + b + c, a // (p - 1), b + c,
                            a // (p * (p - 1)), b // (p - 1), c)
                    for j, value in enumerate(rows):
                        updated[block * 6 * stride + j * stride + offset] = value
            values, dimensions[axis] = updated, 6
        return values

    def phase_maxima(values):
        dimensions = [6] * len(P)
        for axis in range(len(P)):
            stride = prod(dimensions[axis + 1:])
            updated = [0] * (len(values) // 2)
            for block in range(len(values) // (6 * stride)):
                for offset in range(stride):
                    at = block * 6 * stride + offset
                    rows = (values[at], max(values[at + stride], values[at + 2 * stride]),
                            max(values[at + 3 * stride], values[at + 4 * stride],
                                values[at + 5 * stride]))
                    for j, value in enumerate(rows):
                        updated[block * 3 * stride + j * stride + offset] = value
            values, dimensions[axis] = updated, 3
        return values

    old = phase_maxima(transform(list(map(sum, cells))))
    require(old[0] == live_numerator, 'old full-unit query mass')
    current = [0] * len(profiles)
    for c in range(CURRENT):
        maxima = phase_maxima(transform([row[c] for row in cells]))
        current = list(map(max, current, maxima))
    weights = [prod(p if e == 2 else p - 1 for p, e in zip(P, v)) for v in profiles]
    tail_denominator = prod(p - 1 for p in P)
    old_sum = sum(a * w for a, w in zip(old, weights))
    current_sum = sum(b * w for b, w in zip(current, weights))
    actual_query = F(22 * old_sum + 23 * current_sum,
                     22 * tail_denominator * live_numerator) - 1
    reserve = 1 - (1 + actual_query) / 28
    require(actual_query == F(48819613325418098388618839835627526373,
                              8863151607393243786151717247542886400),
            'ternary exact all-height query value')
    require(actual_query < 27 and reserve > 0, 'ternary arbitrary29 continuation')
    exact = {
        'delta': F(11, 23), 'live_mass': live,
        'old_nonunit_raw': F(old_sum, tail_denominator * denominator) - live,
        'all23_raw': F(23 * current_sum, 22 * tail_denominator * denominator),
        'R_new': actual_query, '27_minus_R_new': 27 - actual_query,
        'normalized29_survivor_lower': reserve,
        'unnormalized_joint_survivor_lower': live * reserve,
    }
    return {
        'scope': 'exact same-law joint-cylinder maxima; ordinary uniform-depth-tail proof supplies all heights; fixed ternary-coloured23 head plus arbitrary distinct29-bearing originals only, no extra old-only or23-only blockers; no Lean or unrestricted#7 claim',
        'prime_axis_cylinder_types': 6, 'joint_cylinder_types_per_transform': 6 ** len(P),
        'old_sum_transform_count': 1, 'current_root_transform_count': CURRENT,
        'exact_division_checks': divisions, 'common_integer_denominator': denominator,
        'exact': {key: str(value) for key, value in exact.items()},
        'decimals': {key: float(exact[key]) for key in
                     ('R_new', '27_minus_R_new', 'normalized29_survivor_lower')},
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args = parser.parse_args()
    require(all(p > 2 and all(p % k for k in range(2, isqrt(p) + 1)) for p in P + (CURRENT,)), 'primes')
    profiles = tuple(product(range(3), repeat=len(P)))
    old_moduli = tuple(prod(p ** e for p, e in zip(P, v)) for v in profiles)
    full = tuple(CURRENT * d for d in old_moduli if d > 1)
    short = tuple(CURRENT * p for p in P)
    require(len(profiles) == 2187, 'profile inventory')
    require(len(full) == len(set(full)) == 2186, 'full original inventory')
    require(len(short) == len(set(short)) == 7, 'short original inventory')
    require(all(m > 1 and m % 2 for m in full), 'distinct odd originals')
    require(set(short).issubset(full), 'short family included')
    require(all(any(m % k == 0 for k in short) for m in full), 'same union by cylinder containment')
    require(F(2 * len(short), CURRENT) < 1, 'short additive hinge zero')

    probability = first_inf = event_mass = event_first_inf = F(0)
    haar_hinge = event_hinge = F(0)
    actual_hinge = short_hinge = F(0)
    event_profiles = 0
    for v in profiles:
        # v_p=0,1,>=2 are exact Haar cells, independent across old primes.
        mass = prod(F(p - 1, p ** (e + 1)) if e < 2 else F(1, p ** 2)
                    for p, e in zip(P, v))
        d2 = prod(e + 1 for e in v)
        # Conditional tail expectation E(v_p+1 | v_p>=2)=2+p/(p-1).
        dinf = prod(F(e + 1) if e < 2 else F(2) + F(p, p - 1)
                    for p, e in zip(P, v))
        f_full = F(d2 - 1, CURRENT)
        f_short = F(sum(e > 0 for e in v), CURRENT)
        alpha = F(int(any(e > 0 for e in v)), CURRENT)
        h_full = max(F(0), 2 * f_full - 1)
        h_short = max(F(0), 2 * f_short - 1)
        h_actual = max(F(0), 2 * alpha - 1)
        require(h_short == h_actual == 0, 'pointwise zero short/actual hinge')
        probability += mass
        first_inf += mass * dinf
        haar_hinge += mass * h_full
        short_hinge += mass * h_short
        actual_hinge += mass * h_actual
        if d2 >= THRESHOLD:
            event_profiles += 1
            event_mass += mass
            event_first_inf += mass * dinf
            event_hinge += mass * h_full
    require(probability == 1, 'Haar profile partition')
    require(first_inf == prod(F(p, p - 1) for p in P), 'all-height Haar divisor moment')
    require(0 < event_mass < 1 and 0 < MIX < 1, 'full-support mixture')
    r_infty = (1 - MIX) * first_inf + MIX * event_first_inf / event_mass - 1
    density = 1 - MIX + MIX / event_mass
    hinge = (1 - MIX) * haar_hinge + MIX * event_hinge / event_mass
    require(r_infty < A, 'AH9 complete query cap')
    require(density < LAMBDA, 'AH9 density cap')
    require(hinge > 1, 'uncapped hinge exceeds one')
    require(short_hinge == actual_hinge == 0, 'short and actual hinges')
    rational = {
        'A': A, 'Lambda': LAMBDA, 'mixture': MIX,
        'Haar_event_mass': event_mass, 'Haar_infinite_divisor_moment': first_inf,
        'Haar_infinite_divisor_moment_on_event': event_first_inf,
        'Haar_uncapped_hinge': haar_hinge, 'Haar_uncapped_hinge_on_event': event_hinge,
        'R_infty': r_infty, 'A_minus_R_infty': A - r_infty,
        'density_max': density, 'Lambda_minus_density_max': LAMBDA - density,
        'uncapped_hinge': hinge, 'uncapped_hinge_minus_one': hinge - 1,
        'short_additive_hinge': short_hinge, 'actual_union_hinge': actual_hinge,
        'density_min': 1 - MIX,
    }
    result = {
        'scope': 'AH9 scalar/support interface, including an irredundant rank-coloured family; canonical467 source selection not reconstructed; no whole-cover premise; no Lean claim',
        'old_primes': P, 'current_prime': CURRENT, 'old_height': 2,
        'event_threshold': THRESHOLD, 'valuation_profiles': len(profiles),
        'event_profiles': event_profiles, 'actual_full_labels': len(full),
        'actual_short_labels': len(short), 'old_original_count': 0,
        'old_height_two_period': prod(p ** 2 for p in P),
        'same_union_certificate': 'short subset full; every full zero class is contained in one short zero class by literal modulus divisibility',
        'exact': {key: str(value) for key, value in rational.items()},
        'decimals': {key: float(rational[key]) for key in ('R_infty', 'density_max', 'uncapped_hinge')},
    }
    result['rank_colored'] = rank_colored_check(profiles, event_mass, hinge)
    result['rank_colored']['continuation23_29'] = rank_continuation_check(
        r_infty, F(result['rank_colored']['actual_union_hinge']))
    result['ternary_coloured'] = ternary_coloured_check(profiles, event_mass, r_infty)
    result['ternary_coloured']['actual_complete_query'] = ternary_actual_query_check(
        profiles, event_mass, result['ternary_coloured'])
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as handle:
            handle.write(rendered)
    print(rendered, end='')

if __name__ == '__main__':
    main()
