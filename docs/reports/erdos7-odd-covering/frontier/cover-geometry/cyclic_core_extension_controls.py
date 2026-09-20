#!/usr/bin/env python3
"""Exact original-AP controls for tree elimination and unicyclic cores.

All labels and residues are constructed from the literal input models and
mathematical specifications below. No external data is read. Finite checks
validate these instances and the implementation, not the general theorem.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import gcd, isqrt, lcm, prod
from pathlib import Path
from random import Random
import json
import hashlib


@lru_cache(None)
def factor(n):
    result = []
    p = 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            result.append((p, exponent))
        p += 1
    if n > 1:
        result.append((n, 1))
    return tuple(result)


def divisors(n):
    result = [1]
    for p, height in factor(n):
        result = [d*p**a for d in result for a in range(height+1)]
    return sorted(result)


def crt(congruences):
    x, modulus = 0, 1
    for residue, m in congruences:
        assert gcd(modulus, m) == 1
        x += ((residue-x)*pow(modulus, -1, m) % m)*modulus
        modulus *= m
        x %= modulus
    return x


def intervals(values):
    values = sorted(values)
    result = []
    for x in values:
        if result and x == result[-1][1]+1:
            result[-1][1] = x
        else:
            result.append([x, x])
    return result


def mask_values(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask -= low


def prefix_mask(size, modulus, residue):
    return sum(1 << x for x in range(residue % modulus, size, modulus))


def original_rows(family):
    return [{'modulus': d, 'residue': family[d]} for d in sorted(family)]


def comparable_checks(family):
    closed = True
    disjoint = True
    checks = 0
    for d, a in family.items():
        for e in divisors(d):
            if e in (1, d):
                continue
            if e not in family:
                closed = False
            else:
                checks += 1
                if a % e == family[e]:
                    disjoint = False
    return {'divisor_closed': closed, 'comparable_disjoint': disjoint,
            'actual_comparable_pairs_checked': checks}


def forest_dp(family, verify_enumeration=False):
    """Exact existential domains AND numbers of original-coordinate extensions."""
    assert family and all(d > 1 and d % 2 and 0 <= a < d for d, a in family.items())
    supports = {d: dict(factor(d)) for d in family}
    assert all(len(s) <= 2 for s in supports.values())
    primes = sorted(set().union(*(s.keys() for s in supports.values())))
    heights = {p: max(s.get(p, 0) for s in supports.values()) for p in primes}
    sizes = {p: p**heights[p] for p in primes}
    neighbors = {p: set() for p in primes}
    pure = {p: [] for p in primes}
    edge_labels = defaultdict(list)
    for d, support in supports.items():
        if len(support) == 1:
            pure[next(iter(support))].append(d)
        else:
            p, q = sorted(support)
            neighbors[p].add(q)
            neighbors[q].add(p)
            edge_labels[p, q].append(d)
    parent, children, roots, order = {}, {p: [] for p in primes}, [], []
    for root in primes:
        if root in parent:
            continue
        roots.append(root)
        parent[root] = None
        stack = [root]
        while stack:
            p = stack.pop()
            order.append(p)
            for q in sorted(neighbors[p], reverse=True):
                if q == parent[p]:
                    continue
                assert q not in parent, 'Prime-support graph contains a cycle.'
                parent[q] = p
                children[p].append(q)
                stack.append(q)
    assert all(p >= 5 for p in primes if parent[p] is not None)
    counts, feasible, subtrees, messages = {}, {}, {}, {}
    node_rows = []
    for p in reversed(order):
        subtrees[p] = {p}.union(*(subtrees[q] for q in children[p]))
        weights = [int(all(x % d != family[d] for d in pure[p]))
                   for x in range(sizes[p])]
        for q in sorted(children[p]):
            labels = sorted(edge_labels[tuple(sorted((p, q)))])
            rectangles = [(p**supports[d][p], family[d] % p**supports[d][p],
                           prefix_mask(sizes[q], q**supports[d][q], family[d]))
                          for d in labels]
            allowed_by_parent = []
            extension_sums = {}
            blocking = []
            for x in range(sizes[p]):
                forbidden = 0
                for modulus, residue, qmask in rectangles:
                    if x % modulus == residue:
                        forbidden |= qmask
                allowed = feasible[q] & ~forbidden
                allowed_by_parent.append(allowed)
                if not allowed:
                    blocking.append(x)
                if allowed not in extension_sums:
                    extension_sums[allowed] = sum(counts[q][y] for y in mask_values(allowed))
                weights[x] *= extension_sums[allowed]
            delta = F(feasible[q].bit_count(), sizes[q])
            blocking_mass = F(len(blocking), sizes[p])
            cutoff_rows = []
            for cutoff in range(1, heights[p]+2):
                shallow = sum((F(1, q**supports[d][q]) for d in labels
                               if supports[d][p] < cutoff), F())
                tail = sum((F(1, d) for d in labels if supports[d][p] >= cutoff), F())
                bound = tail/(delta-shallow) if delta > shallow else None
                if bound is not None:
                    assert blocking_mass <= bound
                cutoff_rows.append({'cutoff': cutoff, 'L': shallow, 'T': tail,
                                    'delta_minus_L': delta-shallow, 'bound_when_applicable': bound})
            uniform_bound = F(1, (p-1)*p**((q-3)//2))
            assert delta >= F(1, 2) and blocking_mass <= uniform_bound
            leaf_bound = F(1, (p-1)*p**(q-3)) if not children[q] else None
            if leaf_bound is not None:
                assert delta >= 1-F(1, q-1) and blocking_mass <= leaf_bound
            messages[p, q] = allowed_by_parent
            node_rows.append({'kind': 'child_message', 'parent': p, 'child': q,
                              'original_edge_labels': labels,
                              'child_feasible_Haar': delta,
                              'blocked_parent_intervals': intervals(blocking),
                              'blocked_parent_Haar': blocking_mass,
                              'finite_cutoffs': cutoff_rows,
                              'uniform_half_domain_bound': uniform_bound,
                              'leaf_bound': leaf_bound})
        counts[p] = weights
        feasible[p] = sum(1 << x for x, weight in enumerate(weights) if weight)
        assert feasible[p] != 0
        if parent[p] is not None:
            assert F(feasible[p].bit_count(), sizes[p]) >= F(1, 2)
        exact_tree_lower = 1-F(1, p-1)-sum(
            (F(1, (p-1)*p**((q-3)//2)) for q in children[p]), F())
        assert F(feasible[p].bit_count(), sizes[p]) >= exact_tree_lower
        classes = defaultdict(list)
        for x, weight in enumerate(weights):
            classes[weight].append(x)
        node_rows.append({'kind': 'node', 'prime': p, 'parent': parent[p],
                          'full_original_coordinate_modulus': sizes[p],
                          'original_pure_labels': sorted(pure[p]),
                          'descendant_primes': sorted(subtrees[p]),
                          'feasible_intervals': intervals(mask_values(feasible[p])),
                          'feasible_Haar': F(feasible[p].bit_count(), sizes[p]),
                          'subtree_extension_count_classes': [
                              {'extension_count': weight, 'parent_word_intervals': intervals(xs)}
                              for weight, xs in sorted(classes.items())],
                          'tree_lower_bound': exact_tree_lower})
    period = prod(sizes.values())
    total_count = prod(sum(counts[p]) for p in roots)
    chosen = {}

    def choose(p, value):
        chosen[p] = value
        for q in children[p]:
            allowed = messages[p, q][value]
            assert allowed
            choose(q, next(mask_values(allowed)))

    for p in roots:
        choose(p, next(mask_values(feasible[p])))
    witness = crt((chosen[p], sizes[p]) for p in primes)
    assert all(witness % d != a for d, a in family.items())
    enumerations = []
    if verify_enumeration:
        cache = {}
        for p in primes:
            subtree = frozenset(subtrees[p])
            selected = {d: a for d, a in family.items() if supports[d].keys() <= subtree}
            # Use the ORIGINAL full coordinate sizes, including heights inherited
            # from the edge to the parent, not the smaller lcm of subtree labels.
            local_period = prod(sizes[q] for q in subtree)
            surviving = tuple(x for x in range(local_period)
                              if all(x % d != a for d, a in selected.items()))
            cache[subtree] = surviving
            actual_counts = [0]*sizes[p]
            for x in surviving:
                actual_counts[x % sizes[p]] += 1
            assert actual_counts == counts[p]
            enumerations.append({'root': p, 'original_subtree_period': local_period,
                                 'brute_survivor_count': len(surviving),
                                 'all_conditional_extension_counts_equal_DP': True})
        whole = frozenset(primes)
        surviving = cache.get(whole)
        if surviving is None:
            surviving = tuple(x for x in range(period)
                              if all(x % d != a for d, a in family.items()))
        assert len(surviving) == total_count
        assert witness in surviving
    return {'original_labels': original_rows(family), 'original_period': period,
            'prime_heights': heights,
            'prime_edges': sorted(edge_labels), 'roots': roots,
            'capacity_by_prime': {p: {'g': len(neighbors[p]), 'epsilon': int(heights[p] >= 2),
                                      'capacity': p-1} for p in primes},
            'original_Haar_avoidance_count': total_count,
            'original_Haar_avoidance_probability': F(total_count, period),
            'actual_uncovered_CRT_residue': witness,
            'exact_DP': node_rows,
            'exhaustive_subtree_checks': enumerations,
            'exhaustive_full_period_checked': verify_enumeration}, counts, feasible, messages


def sharp_control():
    family = {3: 0, 5: 0, 9: 2, 15: 11, 27: 8, 45: 17,
              81: 26, 135: 53, 405: 404}
    result, counts, feasible, messages = forest_dp(family, True)
    blocked = [x for x, allowed in enumerate(messages[3, 5]) if not allowed]
    assert blocked == [80] and list(mask_values(feasible[5])) == [1, 2, 3, 4]
    row = next(r for r in result['exact_DP'] if r['kind'] == 'child_message')
    cutoff = next(r for r in row['finite_cutoffs'] if r['cutoff'] == 4)
    assert cutoff['L'] == F(3, 5) and cutoff['T'] == F(1, 405)
    assert cutoff['bound_when_applicable'] == row['blocked_parent_Haar'] == F(1, 81)
    result['sharp_cutoff'] = cutoff
    result['comparable_checks'] = comparable_checks(family)
    return result


def peeling_control():
    family = {3: 0, 5: 0, 7: 0, 11: 0, 13: 0, 15: 1,
              25: 2, 35: 8, 55: 23, 65: 53, 75: 26}
    private = dict(zip(family, (3, 5, 7, 11, 13, 1, 2, 8, 23, 53, 101)))
    for d, x in private.items():
        assert x % d == family[d]
        assert all(x % e != a for e, a in family.items() if e != d)
    result, _, _, _ = forest_dp(family, True)
    assert result['original_period'] == 75075
    assert result['original_Haar_avoidance_count'] == 20790
    assert result['original_Haar_avoidance_probability'] == F(18, 65)
    checks = comparable_checks(family)
    assert checks['divisor_closed'] and checks['comparable_disjoint']
    capacity = result['capacity_by_prime']
    assert capacity[3] == {'g': 1, 'epsilon': 0, 'capacity': 2}
    assert capacity[5] == {'g': 4, 'epsilon': 1, 'capacity': 4}
    crowded = [p for p, row in capacity.items() if row['g']+row['epsilon'] > row['capacity']]
    assert min(crowded) == 5
    projections = {d: family[d] % 3 for d in family if d % 3 == 0}
    assert projections == {3: 0, 15: 1, 75: 2}
    fixed_survivors = [x for x in range(3) if all(x != a for a in projections.values())]
    assert fixed_survivors == []
    result.update({'private_points': private, 'comparable_checks': checks,
                   'incident_first_3_projections': projections,
                   'fixed_3_words_avoiding_every_incident_projection': fixed_survivors,
                   'least_crowded_prime': min(crowded)})
    return result


def prime_list(bound):
    return [p for p in range(2, bound+1) if all(p % k for k in range(2, isqrt(p)+1))]


def star_cost(family, p):
    grouped = defaultdict(list)
    for d, a in family.items():
        if d % p == 0 and factor(d//p) == ((d//p, 1),):
            q = d//p
            grouped[a % p].append(F(1, p if q == p else q-1))
    assert 0 not in grouped
    return sum((sum(ws, F())-1+prod(1-w for w in ws)
                for ws in grouped.values()), F()) / (p-1)


def large_control():
    primes = [p for p in prime_list(4001) if p >= 5]
    assert len(primes) == 549
    family = {3**a: 3**(a-1)-1 for a in range(1, 4)}
    for q in primes:
        family[q] = 0
        for a in range(1, 4):
            modulus = 3**a*q
            family[modulus] = crt(((2*3**(a-1)-1, 3**a), (1, q)))
    assert len(family) == 2199
    checks = comparable_checks(family)
    assert checks['divisor_closed'] and checks['comparable_disjoint']
    result, counts, feasible, _ = forest_dp(family, False)
    W = sum((F(1, q-1) for q in primes), F())
    product_nonchild = prod(1-F(1, q-1) for q in primes)
    S = sum((F(1, prod((p-1)*p**(a-1) for p, a in factor(d)))
             for d in family if sum(a for _, a in factor(d)) >= 2), F())
    assert S == F(2, 9)+F(13, 18)*W
    costs = {p: star_cost(family, p) for p in (3, *primes)}
    assert costs[3] == (W-1+product_nonchild)/2
    assert all(costs[q] == 0 for q in primes)
    reciprocal = sum((F(1, d) for d in family), F())
    gap = S-1-costs[3]
    assert reciprocal > F(2771, 1000) > 1
    assert gap > F(1, 10000) > 0
    assert all(S >= 1+value for value in costs.values())
    product_one = prod(1-F(1, q) for q in primes)
    product_two = prod(1-F(2, q) for q in primes)
    closed_U = product_one/27+F(13, 27)*product_two
    assert result['original_Haar_avoidance_probability'] == closed_U > 0
    assert counts[3][26] == prod(q-1 for q in primes)
    mixed_words = [x for x in range(27) if any(x % 3**a == 2*3**(a-1)-1 for a in range(1, 4))]
    assert len(mixed_words) == 13
    assert all(counts[3][x] == prod(q-2 for q in primes) for x in mixed_words)
    assert set(mask_values(feasible[3])) == {26, *mixed_words}
    assert result['capacity_by_prime'][3]['g'] == 549
    assert result['capacity_by_prime'][3]['epsilon'] == 1
    result.update({'support_leaf_primes': primes, 'comparable_checks': checks,
                   'reciprocal_sum': reciprocal, 'reciprocal_strict_lower_bound': F(2771, 1000),
                   'W': W, 'product_one_minus_one_over_q_minus_one': product_nonchild,
                   'no_prime_S': S, 'star_costs': costs, 'S_minus_one_minus_B3': gap,
                   'star_gap_strict_lower_bound': F(1, 10000),
                   'S_display': float(S), 'B3_display': float(costs[3]),
                   'gap_display': float(gap),
                   'original_Haar_closed_formula': '(1/27)*prod_q(1-1/q)+(13/27)*prod_q(1-2/q)',
                   'original_Haar_closed_value': closed_U,
                   'root_projection_Haar': F(feasible[3].bit_count(), 27),
                   'omega_lcm_over_3': len(result['prime_heights']),
                   'full_divisor_niceness_necessary_condition_fails': len(result['prime_heights']) >= 3,
                   'full_original_CRT_enumeration': 'Not performed: the exact tree DP and independent closed formula agree.'})
    return result


def random_controls():
    seed = 20260920
    rng = Random(seed)
    results = []
    for index in range(50):
        primes = sorted(rng.sample([3, 5, 7, 11], rng.randint(1, 4)))
        heights = {p: 1 for p in primes}
        for _ in range(5):
            p = rng.choice(primes)
            if heights[p] < 3 and prod(q**heights[q] for q in primes)*p <= 150000:
                heights[p] += 1
        shuffled = list(primes)
        rng.shuffle(shuffled)
        edges = []
        for j in range(1, len(shuffled)):
            if rng.randrange(4):
                edges.append(tuple(sorted((shuffled[j], rng.choice(shuffled[:j])))))
        moduli = {p**heights[p] for p in primes}
        for p in primes:
            moduli.update(p**a for a in range(1, heights[p]) if rng.randrange(2))
        for p, q in edges:
            candidates = [p**a*q**b for a in range(1, heights[p]+1)
                          for b in range(1, heights[q]+1)]
            selected = [d for d in candidates if rng.randrange(3)]
            moduli.update(selected or [rng.choice(candidates)])
        family = {d: rng.randrange(d) for d in sorted(moduli)}
        result, _, _, _ = forest_dp(family, True)
        result['sample_index'] = index
        results.append(result)
    assert any(len(r['roots']) > 1 for r in results)
    assert any(max(r['prime_heights'].values()) == 3 for r in results)
    return {'seed': seed, 'sample_count': len(results),
            'maximum_original_period': max(r['original_period'] for r in results),
            'total_full_period_residues_checked': sum(r['original_period'] for r in results),
            'scope': 'Arbitrary residues, distinct odd labels, forests; no CD or divisor-closure filter.',
            'samples': results}


def compact_large_control(result):
    """Keep the inputs/results; remove repeated, individually checked leaf data."""
    messages = [r for r in result['exact_DP'] if r['kind'] == 'child_message']
    nodes = [r for r in result['exact_DP'] if r['kind'] == 'node']
    root = next(r for r in nodes if r['prime'] == 3)
    for row in messages:
        q = row['child']
        assert row['parent'] == 3
        assert row['child_feasible_Haar'] == F(q-1, q)
        assert row['blocked_parent_Haar'] == 0
        assert row['blocked_parent_intervals'] == []
    for node in nodes:
        if node['prime'] == 3:
            continue
        q = node['prime']
        assert node['feasible_intervals'] == [[1, q-1]]
        assert node['subtree_extension_count_classes'] == [
            {'extension_count': 0, 'parent_word_intervals': [[0, 0]]},
            {'extension_count': 1, 'parent_word_intervals': [[1, q-1]]}]
    result['exact_DP_summary'] = {
        'verified_leaf_count': len(messages),
        'leaf_feasible_words': 'For each original q, exactly 1,...,q-1.',
        'leaf_extension_counts': 'Zero at 0; one at every other original q-word.',
        'actual_leaf_to_3_blockers': 'Every blocking set is empty.',
        'all_original_finite_cutoffs_checked': sum(len(r['finite_cutoffs']) for r in messages),
        'root': root,
    }
    del result['exact_DP']
    # This value was checked against the retained original-Haar probability.
    del result['original_Haar_closed_value']
    return result


def universal_weight(p):
    assert p >= 5
    return F(p-1, (p-1)**2-(p-1)-1)


def rational_constant_checks():
    small = (5, 7, 11, 13)
    tail = F(196, 181)**2*(F(1, 196)+F(1, 28))
    square = sum((universal_weight(p)**2 for p in small), F())+tail
    assert square == F(110535026441982184, 453169967387358001) < F(1, 4)
    w5, w7, w11 = (universal_weight(p) for p in (5, 7, 11))
    on_cycle = (
        F(18, 17)*(w5+w7+w5*w7),
        F(6, 5)*(w5+w11+w5*w11),
        2*(w7+w11+w7*w11),
    )
    assert on_cycle == (F(3708, 5423), F(276, 445), F(1768, 2581))
    assert max(on_cycle) < F(7, 10)
    triple = F(64, 1331)
    assert triple == w5**3
    off_cycle = F(24, 55)+F(3, 8)+triple
    absent = F(1, 4)+triple
    assert 2*w7 == F(12, 29) < F(24, 55) == F(6, 5)*w5
    assert off_cycle == F(45757, 53240) < F(19, 20)
    assert absent < F(19, 20)
    return {'small_prime_weights': {p: universal_weight(p) for p in small},
            'odd_tail_bound_from_integral': tail,
            'all_prime_square_budget_upper_bound': square,
            'all_prime_square_budget_strict_comparator': F(1, 4),
            'three_on_cycle_incident_and_potential_triangle_bounds': on_cycle,
            'three_on_cycle_incident_strict_comparator': F(7, 10),
            'triangle_away_from_three_bound': triple,
            'three_off_cycle_bound': off_cycle, 'three_absent_bound': absent,
            'unified_strict_bad_probability_comparator': F(19, 20),
            'retained_product_survival_strict_lower_bound': F(1, 20),
            'scope': 'Exact rational arithmetic for constants in the supplied ordinary proof; '
                     'the infinite-series comparison still uses that proof.'}


def exact_unicyclic_control(family, name):
    """Retain the cycle and 3-path, eliminate trees, then enumerate joint core."""
    assert all(d > 1 and d % 2 and 0 <= a < d for d, a in family.items())
    supports = {d: dict(factor(d)) for d in family}
    assert all(len(s) <= 3 for s in supports.values())
    primes = sorted(set().union(*(s.keys() for s in supports.values())))
    heights = {p: max(s.get(p, 0) for s in supports.values()) for p in primes}
    sizes = {p: p**heights[p] for p in primes}
    neighbors = {p: set() for p in primes}
    pure = {p: [] for p in primes}
    edges = defaultdict(list)
    for d, support in supports.items():
        if len(support) == 1:
            pure[next(iter(support))].append(d)
        for p, q in combinations(support, 2):
            neighbors[p].add(q)
            neighbors[q].add(p)
        if len(support) == 2:
            edges[tuple(sorted(support))].append(d)
    graph_edges = {tuple(sorted((p, q))) for p in primes for q in neighbors[p]}
    seen, stack = set(), [primes[0]]
    while stack:
        p = stack.pop()
        if p not in seen:
            seen.add(p)
            stack.extend(neighbors[p]-seen)
    assert len(seen) == len(primes) and len(graph_edges) == len(primes)

    def prune(keep):
        remaining = set(primes)
        while True:
            leaves = {p for p in remaining if p not in keep
                      and len(neighbors[p] & remaining) <= 1}
            if not leaves:
                return remaining
            remaining -= leaves

    cycle = prune(set())
    core = prune({3} if 3 in primes else set())
    assert cycle <= core and len(cycle) >= 3
    assert all(p >= 5 for p in set(primes)-core)
    assert 3 not in primes or 3 in core
    parent, children = {p: None for p in core}, {p: [] for p in primes}
    order = sorted(core)
    for p in order:
        for q in sorted(neighbors[p]):
            if q in core or q == parent[p]:
                continue
            assert q not in parent
            parent[q] = p
            children[p].append(q)
            order.append(q)
    assert set(order) == set(primes)
    counts, feasible, subtrees = {}, {}, {}
    message_rows, node_rows = [], []
    for p in reversed(order):
        subtrees[p] = {p}.union(*(subtrees[q] for q in children[p]))
        weights = [int(all(x % d != family[d] for d in pure[p])) for x in range(sizes[p])]
        for q in children[p]:
            labels = sorted(edges[tuple(sorted((p, q)))])
            assert labels
            rectangles = [(p**supports[d][p], family[d] % p**supports[d][p],
                           prefix_mask(sizes[q], q**supports[d][q], family[d])) for d in labels]
            extension_sums, blocked = {}, []
            for x in range(sizes[p]):
                forbidden = 0
                for modulus, residue, qmask in rectangles:
                    if x % modulus == residue:
                        forbidden |= qmask
                allowed = feasible[q] & ~forbidden
                if allowed not in extension_sums:
                    extension_sums[allowed] = sum(counts[q][y] for y in mask_values(allowed))
                if not allowed:
                    blocked.append(x)
                weights[x] *= extension_sums[allowed]
            delta_q = F(feasible[q].bit_count(), sizes[q])
            blocker_mass = F(len(blocked), sizes[p])
            bound = F(1, (p-1)*p**((q-3)//2))
            assert delta_q >= F(1, 2) and blocker_mass <= bound
            message_rows.append({'parent': p, 'child': q, 'original_edge_labels': labels,
                                 'actual_child_domain_Haar': delta_q,
                                 'blocked_parent_intervals': intervals(blocked),
                                 'blocked_parent_Haar': blocker_mass, 'half_domain_bound': bound})
        counts[p] = weights
        feasible[p] = sum(1 << x for x, weight in enumerate(weights) if weight)
        delta_p = F(feasible[p].bit_count(), sizes[p])
        lower = 1-F(1, p-1)-F(1, (p-1)**2)
        assert delta_p >= lower > 0
        groups = defaultdict(list)
        for x, weight in enumerate(weights):
            groups[weight].append(x)
        node_rows.append({'prime': p, 'retained': p in core, 'parent': parent[p],
                          'original_coordinate_modulus': sizes[p],
                          'feasible_intervals': intervals(mask_values(feasible[p])),
                          'feasible_Haar': delta_p, 'tree_domain_lower_bound': lower,
                          'extension_count_classes': [
                              {'extensions': weight, 'word_intervals': intervals(xs)}
                              for weight, xs in sorted(groups.items())]})

    core_order = sorted(core)
    core_labels = {d: a for d, a in family.items() if supports[d].keys() <= core and len(supports[d]) >= 2}
    represented = set(core_labels) | set(d for values in pure.values() for d in values)
    represented |= set(d for row in message_rows for d in row['original_edge_labels'])
    assert represented == set(family)
    core_period = prod(sizes[p] for p in core)
    original_period = prod(sizes.values())
    core_domains = {p: tuple(mask_values(feasible[p])) for p in core}
    joint_counts = {}
    for words in product(*(core_domains[p] for p in core_order)):
        x = crt((word, sizes[p]) for p, word in zip(core_order, words))
        if all(x % d != a for d, a in core_labels.items()):
            joint_counts[x] = prod(counts[p][word] for p, word in zip(core_order, words))
    restricted_source_size = prod(len(core_domains[p]) for p in core)
    restricted_survival = F(len(joint_counts), restricted_source_size)
    actual_count = sum(joint_counts.values())
    assert joint_counts and actual_count > 0

    # This direct check uses literal APs on the entire original CRT period.
    brute_projection = Counter()
    first_survivor = None
    for x in range(original_period):
        if all(x % d != a for d, a in family.items()):
            brute_projection[x % core_period] += 1
            if first_survivor is None:
                first_survivor = x
    assert dict(brute_projection) == joint_counts
    assert sum(brute_projection.values()) == actual_count

    conditional_event_probabilities = {
        d: prod(F(sum(x % p**a == family[d] % p**a for x in core_domains[p]),
                  len(core_domains[p])) for p, a in supports[d].items())
        for d in core_labels}
    finite_union_sum = sum(conditional_event_probabilities.values(), F())
    delta = {p: F(len(core_domains[p]), sizes[p]) for p in core}
    w = {p: 1/((p-1)*delta[p]) for p in core}
    retained_edges = sorted(edge for edge in graph_edges if set(edge) <= core)
    edge_budget = sum((w[p]*w[q] for p, q in retained_edges), F())
    triangle_budget = prod(w[p] for p in cycle) if len(cycle) == 3 else F()
    graph_budget = edge_budget + triangle_budget
    assert finite_union_sum <= graph_budget
    assert restricted_survival >= 1-finite_union_sum
    constants = rational_constant_checks()
    other_vertices = sorted(core-{3})
    assert all(w[p] <= universal_weight(p) for p in other_vertices)
    finite_square = sum((universal_weight(p)**2 for p in other_vertices), F())
    assert finite_square <= constants['all_prime_square_budget_upper_bound']
    three_density_lower = None
    if 3 in core:
        retained_three_neighbors = sorted(neighbors[3] & core)
        three_density_lower = F(1, 4)+sum(
            (F(1, 2*3**((q-3)//2)) for q in retained_three_neighbors), F())
        assert delta[3] >= three_density_lower
        if 3 in cycle:
            assert len(retained_three_neighbors) == 2
            q, r = retained_three_neighbors
            branch = 0 if (q, r) == (5, 7) else (1 if q == 5 else 2)
            incident_cap = constants['three_on_cycle_incident_and_potential_triangle_bounds'][branch]
            assert w[3]*(w[q]+w[r]+w[q]*w[r]) <= incident_cap
            degree_after_three = {p: len((neighbors[p] & core)-{3}) for p in other_vertices}
            assert max(degree_after_three.values()) <= 2
            budget_case = 'three_on_cycle'
            finite_structural_cap = incident_cap+finite_square
        else:
            assert len(retained_three_neighbors) == 1
            q = retained_three_neighbors[0]
            assert w[3]*w[q] <= F(24, 55)
            degree_after_three = {p: len((neighbors[p] & core)-{3}) for p in other_vertices}
            assert max(degree_after_three.values()) <= 3
            assert triangle_budget <= F(64, 1331)
            budget_case = 'three_off_cycle'
            finite_structural_cap = F(24, 55)+F(3, 2)*finite_square+F(64, 1331)
    else:
        assert all(len(neighbors[p] & core) == 2 for p in core)
        assert triangle_budget <= F(64, 1331)
        budget_case = 'three_absent'
        finite_structural_cap = finite_square+F(64, 1331)
    assert graph_budget <= finite_structural_cap < F(19, 20)
    assert restricted_survival >= 1-graph_budget > F(1, 20)
    original_Haar_lower = F(restricted_source_size, 20*original_period)
    assert F(actual_count, original_period) > original_Haar_lower
    histogram = Counter(joint_counts.values())
    assert sum(weight*number for weight, number in histogram.items()) == actual_count
    digest = hashlib.sha256(''.join(f'{x}\n' for x in sorted(joint_counts)).encode()).hexdigest()
    return {
        'name': name, 'original_labels': original_rows(family),
        'original_period': original_period, 'prime_heights': heights,
        'prime_edges': sorted(graph_edges), 'cycle_primes': sorted(cycle),
        'retained_core_primes': core_order, 'retained_path_primes_outside_cycle': sorted(core-cycle),
        'removed_tree_primes': sorted(set(primes)-core),
        'actual_tree_messages': message_rows, 'original_coordinate_domains': node_rows,
        'remaining_original_core_labels': sorted(core_labels),
        'remaining_three_prime_labels': sorted(d for d in core_labels if len(supports[d]) == 3),
        'core_original_period': core_period, 'restricted_independent_product_size': restricted_source_size,
        'legal_joint_core_tuple_count': len(joint_counts),
        'legal_core_residues_sha256': digest,
        'legal_core_extension_weight_histogram': [
            {'extensions': weight, 'joint_core_tuple_count': number} for weight, number in sorted(histogram.items())],
        'restricted_product_survival_probability': restricted_survival,
        'original_Haar_survivor_count': actual_count,
        'original_Haar_survival_probability': F(actual_count, original_period),
        'original_Haar_extension_formula': 'sum_(legal core tuple x) product_(p in core) '
                                           'subtree_extension_count_p(x_p) / original_period',
        'original_Haar_height_dependent_strict_lower_bound': original_Haar_lower,
        'retained_product_survival_strict_lower_bound': F(1, 20),
        'law_distinction': 'The 1/20 bound is for the uniform independent product of actual V_p; '
                           'full original Haar uses the recorded nonconstant extension weights.',
        'actual_original_uncovered_residue': first_survivor,
        'all_joint_core_extension_counts_equal_complete_CRT_enumeration': True,
        'actual_core_domain_densities': delta, 'actual_w': w,
        'actual_conditional_original_core_event_probabilities': conditional_event_probabilities,
        'finite_original_label_union_sum': finite_union_sum,
        'actual_domain_edge_product_budget': edge_budget,
        'actual_domain_triangle_product_budget': triangle_budget,
        'actual_domain_graph_budget': graph_budget,
        'actual_domain_graph_budget_below_one': graph_budget < 1,
        'uniform_bound_case': budget_case,
        'retained_neighbor_improved_three_density_lower_bound': three_density_lower,
        'finite_structural_cap': finite_structural_cap,
    }


def unicyclic_controls():
    fixed = [
        ('triangle_with_original_three_prime_labels', {
            3: 0, 9: 2, 5: 0, 25: 3, 7: 0, 11: 0, 15: 1, 45: 17,
            75: 26, 35: 8, 21: 5, 63: 11, 105: 44, 315: 98, 525: 209, 77: 31}),
        ('four_cycle_with_hanging_tree', {
            3: 0, 9: 1, 5: 2, 7: 4, 11: 3, 13: 0, 15: 7,
            45: 19, 35: 8, 77: 31, 33: 11, 99: 52, 65: 14}),
        ('three_on_retained_branch_to_triangle', {
            3: 0, 5: 1, 25: 4, 7: 2, 11: 3, 13: 0, 15: 2, 75: 31,
            35: 8, 175: 33, 77: 9, 55: 6, 275: 42, 91: 27, 385: 111, 1925: 822}),
    ]
    fixed_results = [exact_unicyclic_control(family, name) for name, family in fixed]
    assert fixed_results[0]['remaining_three_prime_labels'] == [105, 315, 525]
    assert len(fixed_results[1]['cycle_primes']) == 4
    assert fixed_results[2]['retained_path_primes_outside_cycle'] == [3]
    assert all(result['removed_tree_primes'] for result in fixed_results)
    seed = 20260921
    rng = Random(seed)
    random_results = []
    for index in range(30):
        shape = index % 3
        if shape == 0:
            cycle = rng.sample([3, 5, 7, 11], 3)
            extra = sorted(set([3, 5, 7, 11])-set(cycle))
            graph_edges = [tuple(sorted((cycle[j], cycle[(j+1) % 3]))) for j in range(3)]
            graph_edges.append(tuple(sorted((extra[0], rng.choice(cycle)))))
            primes = sorted(cycle+extra)
        elif shape == 1:
            cycle = rng.sample([3, 5, 7, 11, 13], 4)
            primes = sorted(cycle)
            graph_edges = [tuple(sorted((cycle[j], cycle[(j+1) % 4]))) for j in range(4)]
        else:
            cycle = rng.sample([5, 7, 11], 3)
            primes = [3, 5, 7, 11, 13]
            graph_edges = [tuple(sorted((cycle[j], cycle[(j+1) % 3]))) for j in range(3)]
            if index % 2:
                graph_edges += [(3, 13), tuple(sorted((13, rng.choice(cycle))))]
            else:
                graph_edges += [tuple(sorted((3, rng.choice(cycle)))),
                                tuple(sorted((13, rng.choice(cycle))))]
        heights = {p: 1 for p in primes}
        for _ in range(5):
            p = rng.choice(primes)
            if heights[p] < 3 and prod(q**heights[q] for q in primes)*p <= 150000:
                heights[p] += 1
        moduli = {p**a for p in primes for a in range(1, heights[p]+1) if rng.randrange(2)}
        for p, q in graph_edges:
            candidates = [p**a*q**b for a in range(1, heights[p]+1) for b in range(1, heights[q]+1)]
            selected = [d for d in candidates if rng.randrange(3)]
            moduli.update(selected or [rng.choice(candidates)])
        if len(cycle) == 3:
            candidates = [prod(p**a for p, a in zip(cycle, exponents))
                          for exponents in product(*(range(1, heights[p]+1) for p in cycle))]
            selected = [d for d in candidates if rng.randrange(2)]
            moduli.update(selected or [rng.choice(candidates)])
        family = {d: rng.randrange(d) for d in sorted(moduli)}
        result = exact_unicyclic_control(family, f'random_unicyclic_{index}')
        result['sample_index'] = index
        random_results.append(result)
    assert any(3 in r['retained_path_primes_outside_cycle'] for r in random_results)
    assert any(len(r['retained_path_primes_outside_cycle']) > 1 for r in random_results)
    assert {r['uniform_bound_case'] for r in random_results} == {
        'three_on_cycle', 'three_off_cycle', 'three_absent'}
    return {'fixed_original_controls': fixed_results, 'random_seed': seed,
            'random_sample_count': len(random_results),
            'random_full_CRT_residues_checked': sum(r['original_period'] for r in random_results),
            'fixed_full_CRT_residues_checked': sum(r['original_period'] for r in fixed_results),
            'random_samples': random_results}


def serializable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): serializable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serializable(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError('Exact checks require assertions; run without -O.')
    sharp = sharp_control()
    peeling = peeling_control()
    large = compact_large_control(large_control())
    random = random_controls()
    unicyclic = unicyclic_controls()
    payload = {
        'scope': 'Exact controls from literal original moduli/residues. '
                 'Finite exact controls do not prove forest or unicyclic noncoverage in general.',
        'probability_convention': 'Every DP count uses the full original prime-power coordinates '
                                  'and unconditioned original Haar; no-prime S and star costs are separately named.',
        'mathematical_specifications': {
            'blocker': 'H_p(B) <= T_pq(r)/(delta_q-L_pq(r)) when delta_q > L_pq(r)',
            'general_child': 'H_p(B) <= p^((3-q)/2)/(p-1)',
            'leaf': 'H_p(B) <= p^(3-q)/(p-1)',
            'large_S': '2/9+(13/18)*sum_q 1/(q-1)',
            'large_B3': '(1/2)*(sum_q 1/(q-1)-1+prod_q(1-1/(q-1)))',
            'large_U': '(1/27)*prod_q(1-1/q)+(13/27)*prod_q(1-2/q)',
            'peeling_U': '18/65'},
        'sharp_blocker': sharp, 'fixed_coordinate_peeling': peeling,
        'large_scalar_separation': large, 'random_forest_controls': random,
        'exact_unicyclic_constants': rational_constant_checks(),
        'tree_elimination_and_unicyclic_core': unicyclic,
    }
    output = Path(__file__).resolve().with_suffix('.json')
    output.write_text(json.dumps(serializable(payload), separators=(',', ':'))+'\n', encoding='utf-8')
    print(json.dumps({'sharp_blocker': '1/81', 'peeling_uncovered': '20790/75075 = 18/65',
                      'large_labels': len(large['original_labels']), 'large_S': large['S_display'],
                      'large_B3': large['B3_display'], 'large_gap': large['gap_display'],
                      'random_instances': random['sample_count'],
                      'random_CRT_residues_checked': random['total_full_period_residues_checked'],
                      'random_unicyclic_instances': unicyclic['random_sample_count'],
                      'random_unicyclic_CRT_residues_checked': unicyclic['random_full_CRT_residues_checked'],
                      'all_exact_checks_passed': True}, indent=2))


if __name__ == '__main__':
    main()
