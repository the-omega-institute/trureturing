#!/usr/bin/env python3
"""Exact original-AP control of two bounds on one conditional survivor law.

Python 3.10+ and its standard library suffice. All generated data describe
the fixed finite control; the uniform theorem requires its ordinary proof.
"""
import argparse
import json
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import gcd, prod
from pathlib import Path


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are certificate checks.')
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()

    pure = ((5, 0), (25, 1), (7, 0), (11, 0))
    child = ((25, 7), (35, 16), (55, 36), (77, 60), (1925, 1233))
    period = 25 * 7 * 11
    domains = (tuple(x for x in range(25) if x % 5 and x != 1),
               tuple(range(1, 7)), tuple(range(1, 11)))
    states = tuple(x for x in range(period)
                   if all(x % m != r for m, r in pure))
    assert len(states) == prod(map(len, domains)) == 1140
    # The whole 5-coordinate is uniform on 19 words. Its two base-5
    # digits are dependent: high digit 0 occurs elsewhere, but not at 1.
    assert 1 not in domains[0] and 6 in domains[0] and 2 in domains[0]
    first_digit_counts = [sum(x % 5 == r for x in domains[0]) for r in range(5)]
    assert first_digit_counts == [0, 4, 5, 5, 5]
    whole_coordinate_tuples = {(x % 25, x % 7, x % 11) for x in states}
    assert whole_coordinate_tuples == set(product(*domains))

    def mask(modulus, residue):
        return sum(1 << i for i, x in enumerate(states)
                   if x % modulus == residue)

    universe = (1 << len(states)) - 1
    events = tuple(mask(m, r) for m, r in child)
    probabilities = tuple(Fraction(e.bit_count(), len(states)) for e in events)
    vertex_set = (1 << len(events)) - 1
    conflicts = tuple(sum(1 << j for j, (n, s) in enumerate(child)
                          if j != i and (r-s) % gcd(m, n))
                      for i, (m, r) in enumerate(child))
    shared = tuple(sum(1 << j for j, (n, _) in enumerate(child)
                       if j != i and gcd(m, n) > 1)
                   for i, (m, _) in enumerate(child))

    def polynomial(neighbors):
        @lru_cache(None)
        def recurrence(subset):
            if not subset:
                return Fraction(1)
            bit = subset & -subset
            vertex = bit.bit_length()-1
            rest = subset ^ bit
            return (recurrence(rest) - probabilities[vertex]
                    * recurrence(rest & ~neighbors[vertex]))

        def direct(subset):
            vertices = [i for i in range(len(events)) if subset >> i & 1]
            result = Fraction(0)
            for count in range(len(vertices)+1):
                for selected in combinations(vertices, count):
                    if all(not (neighbors[i] >> j & 1)
                           for i, j in combinations(selected, 2)):
                        result += (-1)**count * prod(probabilities[i] for i in selected)
            return result

        values = [recurrence(s) for s in range(vertex_set+1)]
        assert values == [direct(s) for s in range(vertex_set+1)]
        assert min(values) > 0
        return recurrence, values

    conflict_poly, conflict_values = polynomial(conflicts)
    shared_poly, shared_values = polynomial(shared)
    survivor = universe
    for event in events:
        survivor &= ~event
    survivor_count = survivor.bit_count()
    assert survivor_count == 1001

    # Check every conditional nonneighbor inequality for the old vertices.
    lopsided_checks = 0
    for i, event in enumerate(events):
        allowed = vertex_set & ~(conflicts[i] | (1 << i))
        subset = allowed
        while True:
            avoidance = universe
            for j in range(len(events)):
                if subset >> j & 1:
                    avoidance &= ~events[j]
            assert ((avoidance & event).bit_count()*len(states)
                    <= event.bit_count()*avoidance.bit_count())
            lopsided_checks += 1
            if not subset:
                break
            subset = (subset-1) & allowed

    query_checks = 0
    selected_query = None
    for modulus in range(2, period+1):
        if period % modulus:
            continue
        for residue in range(modulus):
            query = mask(modulus, residue)
            p_query = Fraction(query.bit_count(), len(states))
            actual = Fraction((query & survivor).bit_count(), survivor_count)
            n_conflict = sum(1 << j for j, (m, r) in enumerate(child)
                             if (residue-r) % gcd(modulus, m))
            n_shared = sum(1 << j for j, (m, _) in enumerate(child)
                           if gcd(modulus, m) > 1)
            conflict_bound = (p_query * conflict_poly(vertex_set & ~n_conflict)
                              / conflict_poly(vertex_set))
            shared_bound = (p_query * shared_poly(vertex_set & ~n_shared)
                            / shared_poly(vertex_set))
            assert actual <= conflict_bound and actual <= shared_bound
            query_checks += 1
            if (modulus, residue) == (5, 1):
                assert actual == Fraction(176, 1001)
                assert conflict_bound < shared_bound
                selected_query = {
                    'modulus':modulus, 'residue':residue,
                    'source_probability':str(p_query),
                    'actual_conditional_probability':str(actual),
                    'conflict_bound':str(conflict_bound),
                    'shared_support_bound':str(shared_bound),
                    'strict_bound_improvement':str(shared_bound-conflict_bound),
                    'conflicting_event_indices':[i for i in range(len(child)) if n_conflict >> i & 1],
                    'shared_coordinate_event_indices':[i for i in range(len(child)) if n_shared >> i & 1],
                }
    assert query_checks == 2975 and selected_query is not None

    # Lift child cylinders back to distinct original crossing labels.
    crossing = []
    for cofactor, residue in child:
        original_residue = next(residue+j*cofactor for j in range(3)
                                if (residue+j*cofactor) % 3 == 0)
        crossing.append({'modulus':3*cofactor,'residue':original_residue,
                         'child_cofactor':cofactor,'child_residue':residue})
    original = [{'modulus':m,'residue':r} for m,r in pure]+crossing
    assert len({row['modulus'] for row in original}) == len(original)
    assert all(row['modulus'] > 1 and row['modulus'] % 2 for row in original)
    actual_parent_zero = tuple(x for x in range(3*period)
                              if x % 3 == 0 and all(x % m != r for m,r in pure))
    direct_survivors = tuple(x for x in actual_parent_zero
                            if all(x % row['modulus'] != row['residue'] for row in crossing))
    assert len(actual_parent_zero) == len(states) and len(direct_survivors) == survivor_count
    assert {x % period for x in direct_survivors} == {x for i,x in enumerate(states) if survivor >> i & 1}

    out = {
        'scope':'One actual conditional law, literal nested-prefix events, two strictly feasible graphs. Finite control only; no unrestricted positivity or noncoverage conclusion.',
        'original_labels':original, 'parent_prime':3, 'parent_residue':0,
        'child_period':period, 'original_period':3*period,
        'source_count':len(states), 'survivor_count':survivor_count,
        'whole_coordinate_domains':[list(d) for d in domains],
        'base5_first_digit_counts':first_digit_counts,
        'old_event_probabilities':list(map(str,probabilities)),
        'conflict_graph_neighbor_masks':list(conflicts),
        'shared_graph_neighbor_masks':list(shared),
        'conflict_induced_polynomials':list(map(str,conflict_values)),
        'shared_induced_polynomials':list(map(str,shared_values)),
        'lopsided_subset_checks':lopsided_checks, 'literal_queries_checked':query_checks,
        'selected_query':selected_query,
    }
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: 64 induced polynomials, 2975 actual conditional queries, original-label CRT control.')
    print(json.dumps(selected_query))


if __name__ == '__main__':
    main()
