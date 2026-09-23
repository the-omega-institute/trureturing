#!/usr/bin/env python3
"""Exact certificate for anchored four-predecessor record accounting.

The ordinary proof supplies the original-label conditional comparison,
all-depth domination, normalized joint law and record-minimum invariant.
This program checks the fixed rational schedule and its finite potential
inequalities, using complete moments and an analytic remaining-prime bound.
"""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
import importlib.util
from itertools import combinations, permutations
import json
from math import comb, isqrt, prod
from pathlib import Path
import sys


HELPER_SHA256 = 'e8455f314b463dfc3d513289b2043b3143793bd2dca2ef4e480c37e034e646c6'
S = (11, 13, 17, 19, 23, 29, 31)
ROOT = (3, 5)
THREE = (3, 5, 7)
FOUR = (3, 5, 7, 11)
SCALE = 10**6


def delta(p):
    return {7: Q(1, 5), 11: Q(1, 3), 13: Q(29, 65)}.get(p, Q(5, 9))


def cap(p):
    if p in ROOT:
        return Q(p - 1, p - 2)
    return Q(p - 1, p - 2) / (1 - delta(p))


def ceil_scaled(value, scale):
    scaled = value * scale
    return -(-scaled.numerator // scaled.denominator)


def bounded_tuples(length, limit, prefix=(), value=1):
    if length == 0:
        yield prefix, value
        return
    for n in range(1, limit // value + 1):
        yield from bounded_tuples(length - 1, limit, prefix + (n,), value * n)


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper', type=Path, required=True)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    assert sha256(args.helper.read_bytes()).hexdigest() == HELPER_SHA256
    spec = importlib.util.spec_from_file_location('book_density', args.helper)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)

    def moments(p):
        c, z = cap(p), Q(1, p)
        first_three = helper.moments(p, c)
        s0 = z / (1 - z)
        s1 = z / (1 - z)**2
        s2 = z * (1 + z) / (1 - z)**3
        s3 = z * (1 + 4*z + z*z) / (1 - z)**4
        fourth = 1 + c * (4*s3 + 6*s2 + 4*s1 + s0)
        return (Q(1),) + first_three + (fourth,)

    @lru_cache(None)
    def fee(p, slots):
        threshold = 1 + delta(p) * (p - 2)
        denominator = (p - 2) * (1 - delta(p))
        limit = threshold.numerator // threshold.denominator
        mean = prod(moments(q)[1] for q in slots)
        correction = Q(0)
        terms = 0
        for indices, value in bounded_tuples(len(slots), limit):
            weight = prod(helper.mass(n, q, cap(q))
                          for n, q in zip(indices, slots))
            assert weight >= 0
            correction += (threshold - value) * weight
            terms += 1
        result = (mean - threshold + correction) / denominator
        assert result >= 0
        return result, terms

    def g(p, m):
        return fee(p, THREE + (m,))[0]

    assert tuple(cap(p) for p in (7, 11, 13, 17)) == (
        Q(3, 2), Q(5, 3), Q(65, 33), Q(12, 5))
    endpoints = (3, 5, 7, 11, 13, 17)
    first_tails = [cap(p)/p for p in endpoints]
    assert first_tails == [Q(2, 3), Q(4, 15), Q(3, 14),
                           Q(5, 33), Q(5, 33), Q(12, 85)]
    assert all(first_tails[i] >= first_tails[i+1]
               for i in range(len(first_tails)-1))
    # For every p>=17: C_p/p=(9/8)(1/p+1/(p-2)), decreasing.
    assert cap(17)/17 == Q(9, 8)*(Q(1, 17)+Q(1, 15))
    assert all(0 < x < 1 for x in first_tails)
    assert all(0 < delta(p) < 1 for p in endpoints[2:])

    base_rows = []
    for p in S[1:]:
        value, terms = fee(p, FOUR)
        ceiling = ceil_scaled(value, SCALE)
        base_rows.append(dict(prime=p, exact_fee=str(value),
                              ceiling_numerator=ceiling, ceiling_scale=SCALE,
                              finite_complement_terms=terms))
    assert [r['ceiling_numerator'] for r in base_rows] == [
        118226, 54761, 40053, 21957, 10490, 8544]
    base_ceiling = Q(sum(r['ceiling_numerator'] for r in base_rows), SCALE)
    assert base_ceiling == Q(254031, SCALE)

    potential = {}
    potential_rows = []
    transition_rows = []
    for m in S[1:] + (37,):
        terminal = g(11, m)
        candidates = [(11, terminal)]
        for p in S[1:]:
            if p < m:
                candidate = g(p, m) - g(p, 11) + potential[p]
                candidates.append((p, candidate))
        max_candidate = max(value for _, value in candidates)
        potential[m] = Q(ceil_scaled(max_candidate, SCALE), SCALE)
        potential_rows.append(dict(state=m, potential=str(potential[m]),
                                   terminal_fee=str(terminal),
                                   candidates=[dict(next_record=p, value=str(v))
                                               for p, v in candidates]))
        assert terminal <= potential[m]
        for p, candidate in candidates:
            assert candidate <= potential[m]
            if p != 11:
                slack = g(p, 11) + potential[m] - g(p, m) - potential[p]
                assert slack >= 0
                transition_rows.append(dict(before=m, next_record=p,
                                            exact_fee=str(g(p, m)),
                                            slack=str(slack)))
    assert [potential[m] for m in S[1:] + (37,)] == [
        Q(n, SCALE) for n in (186346, 180678, 175304, 169900,
                              165919, 164966, 162773)]
    small_ceiling = base_ceiling + potential[37]
    assert small_ceiling == Q(416804, SCALE) < Q(417, 1000)

    # A separate finite check of the telescoping accounting on every order
    # of the seven tracked primes. The unbounded theorem uses the invariant,
    # not an enumeration of actual families or original prime-power heights.
    maximum, maximizing_order = Q(-1), None
    order_count = 0
    for order in permutations(S):
        state, total = 37, Q(0)
        for p in order:
            total += g(p, state)
            state = min(state, p)
        assert state == 11 and total <= small_ceiling
        order_count += 1
        if total > maximum:
            maximum, maximizing_order = total, order
    assert order_count == 5040

    seven_fee, seven_terms = fee(7, ROOT)
    assert seven_fee == Q(41, 180)
    groups = ((37, 41, 43, 47, 53), (59, 61, 67, 71, 73),
              (79, 83, 89, 97), (101, 103, 107, 109, 113))
    group_rows, middle_rows = [], []
    for group in groups:
        group_numerator = 0
        for p in group:
            value, terms = fee(p, FOUR)
            ceiling = ceil_scaled(value, 10**7)
            group_numerator += ceiling
            middle_rows.append(dict(prime=p, exact_fee=str(value),
                                    ceiling_numerator=ceiling,
                                    ceiling_scale=10**7,
                                    finite_complement_terms=terms))
        group_rows.append(dict(primes=group, ceiling_numerator=group_numerator,
                               ceiling_scale=10**7))
    primes = tuple(p for p in range(37, 127)
                   if all(p%d for d in range(2, isqrt(p)+1)))
    assert tuple(p for group in groups for p in group) == primes
    assert [row['ceiling_numerator'] for row in group_rows] == [
        141314, 28921, 7468, 3622]
    middle_ceiling = Q(sum(r['ceiling_numerator'] for r in middle_rows), 10**7)
    assert middle_ceiling == Q(181325, 10**7) < Q(91, 5000)

    moment_rows = [moments(p) for p in FOUR]
    assert [row[1:] for row in moment_rows] == [
        (Q(2), Q(5), Q(31, 2), Q(59)),
        (Q(4, 3), Q(13, 6), Q(107, 24), Q(277, 24)),
        (Q(5, 4), Q(11, 6), Q(79, 24), Q(131, 18)),
        (Q(7, 6), Q(23, 15), Q(713, 300), Q(1664, 375))]
    fourth = sum(Q(comb(4, k) * (-1)**(4-k)) * prod(row[k] for row in moment_rows)
                 for k in range(5))
    assert fourth == Q(25915494211, 1296000)
    quartic_factor = Q(27, 256) / (delta(127)**3 * (1 - delta(127)))
    assert quartic_factor == Q(177147, 128000)
    odd_tail = Q(1, 125**4) + Q(1, 6*125**3)
    tail = quartic_factor * fourth * odd_tail
    assert tail == Q(2474903781656289, 10**18) < Q(1, 400)

    fee_ceiling = seven_fee + Q(417, 1000) + Q(91, 5000) + Q(1, 400)
    assert fee_ceiling == Q(59893, 90000)
    reserve = 1 - Q(1, 3) - fee_ceiling
    prefactor = reserve / Q(8, 3)
    assert reserve == Q(107, 90000)
    assert prefactor == Q(107, 240000)
    tighter_fee = seven_fee + small_ceiling + middle_ceiling + tail
    assert tighter_fee < fee_ceiling

    clique = (3, 5, 7, 11, 13)
    edges = set(combinations(clique, 2))
    edges.update(tuple(sorted((29, p))) for p in (3, 5, 7, 11, 17))
    graph_order = (3, 5, 7, 29, 11, 13, 17)
    earlier = set()
    counts = []
    for p in graph_order:
        counts.append(sum(tuple(sorted((p, q))) in edges for q in earlier))
        earlier.add(p)
    assert len(edges) == 15 and counts == [0, 1, 2, 3, 4, 4, 1]
    assert sum(29 in edge for edge in edges) == 5
    assert all(edge in edges for edge in combinations(clique, 2))
    pair_moduli = sorted(p*q for p,q in edges)
    assert len(set(pair_moduli)) == 15
    assert all(m > 1 and m%2 == 1 for m in pair_moduli)

    output = dict(
        schema='anchored-four-record-potential-v1',
        scope='Anchored order 3,5,7 followed by any order with at most four actual earlier graph neighbours; distinct odd nonunit original numerical moduli, arbitrary original heights and residues.',
        helper_sha256=HELPER_SHA256,
        threshold_schedule={'7':'1/5', '11':'1/3', '13':'29/65', 'p>=17':'5/9'},
        comparison_first_tails=[dict(prime=p, cap=str(cap(p)), first_tail=str(cap(p)/p))
                                for p in endpoints],
        seven_fee=dict(exact_fee=str(seven_fee), finite_complement_terms=seven_terms),
        tracked_primes=S, initial_state=37, base_fees=base_rows,
        potential_rows=potential_rows, record_inequalities=transition_rows,
        small_base_ceiling=str(base_ceiling), small_total_ceiling=str(small_ceiling),
        order_check=dict(count=order_count, maximum_exact_fee=str(maximum),
                         maximizing_order=maximizing_order),
        middle_fees=middle_rows, middle_groups=group_rows,
        middle_total_ceiling=str(middle_ceiling),
        complete_moments=[dict(prime=p, first_four=[str(v) for v in row[1:]])
                          for p,row in zip(FOUR,moment_rows)],
        fourth_moment_product_minus_one=str(fourth), quartic_factor=str(quartic_factor),
        odd_integer_tail_upper=str(odd_tail), analytic_prime_tail_upper=str(tail),
        strict_analytic_tail_ceiling='1/400', strict_total_fee_ceiling=str(fee_ceiling),
        tighter_fee_upper=str(tighter_fee), mixed_root_fee_upper='1/3',
        strict_weighted_survivor_lower=str(reserve), full_haar_prefactor=str(prefactor),
        uniform_private_prime_density_factor='5/12',
        graph_example=dict(vertices=sorted(graph_order), edges=sorted(edges),
                           anchored_order=graph_order, earlier_neighbour_counts=counts,
                           natural_order_predecessors_at_29=5,
                           clique_for_three_predecessor_obstruction=clique,
                           distinct_odd_pair_moduli=pair_moduli),
        verification='Exact rational schedule, complete geometric moments, finite record-potential inequalities and analytic infinite-prime tail. Ordinary comparison and actual-family proof obligations are not certified as new Lean results.')
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print('PASS: record potentials, 5040 tracked orders, 19 middle fees, complete fourth moment and analytic tail.')
    print('V37 =',potential[37],'; small-prime ceiling =',small_ceiling)
    print('fourth moment =',fourth,'; analytic tail =',tail)
    print('weighted reserve >',reserve,'; full Haar prefactor =',prefactor)


if __name__ == '__main__':
    main()
