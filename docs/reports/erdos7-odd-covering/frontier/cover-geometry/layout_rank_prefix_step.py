#!/usr/bin/env python3
"""Exact layout-rank increment counterexample and parent-prefix bound.

Report 424. Standard-library Python 3; no optimizer, repository imports,
working-directory assumption, file output, or floating-point arithmetic.
The public functions accept arbitrary finite rational layout mixtures.
"""
from fractions import Fraction as F
from itertools import combinations, product
import json

ROWS = (1, 2, 3, 4)
GROUPS = tuple((a, 3) for a in combinations(ROWS, 2)) + ((ROWS, 5),)
COUNTEREXAMPLE = (
    (2, (0, 2, 3, 17, 4, 53)),
    (3, (0, 2, 1, 22, 29, 29)),
    (1, (0, 2, 0, 7, 0, 98)),
    (9, (0, 1, 1, 18, 25, 123)),
    (10, (0, 1, 2, 18, 11, 158)),
    (4, (0, 2, 0, 28, 21, 168)),
    (5, (0, 2, 1, 29, 29, 29)),
    (4, (0, 2, 1, 29, 1, 99)),
    (3, (0, 1, 0, 14, 28, 224)),
    (8, (0, 1, 1, 8, 22, 218)),
    (8, (0, 2, 3, 18, 4, 53)),
    (1, (0, 2, 3, 18, 25, 123)),
    (10, (0, 2, 3, 18, 18, 18)),
    (10, (0, 1, 2, 18, 32, 228)),
    (4, (0, 1, 1, 1, 1, 99)),
    (8, (0, 1, 0, 28, 0, 168)),
    (10, (0, 2, 0, 14, 0, 224)),
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(height):
    need(type(height) is int and height >= 0, 'nonnegative integer height required')
    return tuple(d for j in range(height+1) for d in (7**j, 5*7**j))


def mixture(height, components):
    mods = divisors(height)
    need(type(components) in (tuple, list) and components, 'nonempty mixture required')
    result = []
    for item in components:
        need(type(item) in (tuple, list) and len(item) == 2, 'weight/layout pair required')
        weight, phases = item
        need(type(weight) in (int, F) and weight >= 0, 'nonnegative exact weight required')
        need(type(phases) in (tuple, list) and len(phases) == len(mods), 'all original phases required')
        need(all(type(a) is int and 0 <= a < d for a, d in zip(phases, mods)),
             'literal original residue required')
        result.append((F(weight), tuple(phases)))
    need(sum((w for w, _ in result), F()) == 1, 'mixture mass must equal one')
    return tuple(result)


def costs_crt(height, components):
    """Evaluate squares solely by integer CRT representatives and remainders."""
    components = mixture(height, components)
    mods, q = divisors(height), 7**height
    result = {}
    for r, y in product(ROWS, range(q)):
        x = y+q*((r-y)*pow(q, -1, 5) % 5)
        result[r, y] = sum((w*sum(int(x % d == a) for d, a in zip(mods, phases))**2
                            for w, phases in components), F())
    return result


def indicator_load(height, phases, row, y):
    return sum(int(y % 7**j == phases[2*j])
               + int(row == phases[2*j+1] % 5 and y % 7**j == phases[2*j+1] % 7**j)
               for j in range(height+1))


def costs_indicators(height, components):
    """Independent evaluation using row/prefix indicators, without CRT."""
    components = mixture(height, components)
    return {(r, y): sum((w*indicator_load(height, phases, r, y)**2
                         for w, phases in components), F())
            for r, y in product(ROWS, range(7**height))}


def tree_order(values, height, branching):
    """Bottom-up b-th-largest recursion for U_b."""
    divisors(height)
    need(type(branching) is int and 1 <= branching <= 7, 'branching must lie in 1..7')
    need(type(values) is dict and set(values) == set(range(7**height)), 'complete leaf values required')
    need(all(type(v) in (int, F) for v in values.values()), 'exact leaf values required')
    table = dict(values)
    for depth in range(height, 0, -1):
        width = 7**(depth-1)
        table = {u: sorted((table[u+c*width] for c in range(7)), reverse=True)[branching-1]
                 for u in range(width)}
    return table[0]


def tree_threshold(values, height, branching):
    """Independent Boolean superlevel contraction, with no order-statistic calls."""
    candidates = sorted(set(values.values()))
    answer = candidates[0]
    for threshold in candidates:
        good = {u for u, value in values.items() if value >= threshold}
        for depth in range(height, 0, -1):
            width = 7**(depth-1)
            counts = {}
            for u in good:
                parent = u % width
                counts[parent] = counts.get(parent, 0)+1
            good = {u for u, count in counts.items() if count >= branching}
        if 0 in good:
            answer = threshold
    return answer


def ranks(costs, height, method=tree_order):
    divisors(height)
    need(type(costs) is dict and set(costs) == set(product(ROWS, range(7**height))),
         'complete row/prefix table required')
    return tuple(method({u: max(costs[r, u] for r in rows) for u in range(7**height)},
                        height, b) for rows, b in GROUPS)


def parent_prefix_bound(height, components):
    """Compute the seven parent-prefix fields from whole-layout atoms.

    Summing atoms with the same old layout is exactly the unnormalized
    conditional Q/V/H formula in report 424. Coincidence tests use the
    complete new prefix, not merely its parent prefix.
    """
    need(type(height) is int and height >= 1, 'positive extension height required')
    components = mixture(height, components)
    old = costs_crt(height-1, [(w, phases[:-2]) for w, phases in components])
    new = costs_crt(height, components)
    width, branches = 7**(height-1), []
    for rows, b in GROUPS:
        field = {}
        for u in range(width):
            budget = F()
            for w, phases in components:
                loads = {r: indicator_load(height-1, phases[:-2], r, u) for r in rows}
                pure, mixed = phases[-2:]
                if pure % width == u:
                    budget += w*(2*max(loads.values())+1)
                r, v = mixed % 5, mixed % (7*width)
                if r in rows and v % width == u:
                    budget += w*(2*loads[r]+1)
                    if pure == v:
                        budget += 2*w
            a = max(old[r, u] for r in rows)
            gains = [max(new[r, u+c*width]-old[r, u] for r in rows) for c in range(7)]
            need(all(g >= 0 for g in gains) and sum(gains, F()) <= budget,
                 'parent increment budget does not dominate actual joint gains')
            children = [max(new[r, u+c*width] for r in rows) for c in range(7)]
            field[u] = a+budget/b
            need(sorted(children, reverse=True)[b-1] <= field[u], 'last-step rank bound')
        branches.append(tree_order(field, height-1, b))
    need(min(ranks(new, height)) <= min(branches), 'global parent-prefix rank bound')
    return tuple(branches)


def checked_ranks(height, components):
    crt = costs_crt(height, components)
    indicator = costs_indicators(height, components)
    need(crt == indicator, 'CRT and independent indicator costs differ')
    first = ranks(crt, height)
    second = ranks(indicator, height, tree_threshold)
    need(first == second, 'order-statistic and Boolean-threshold ranks differ')
    return first


def self_check():
    need(len(COUNTEREXAMPLE) == 17 and sum(w for w, _ in COUNTEREXAMPLE) == 100,
         'complete counterexample weights')
    theta = tuple((F(w, 100), phases) for w, phases in COUNTEREXAMPLE)
    old = checked_ranks(1, [(w, phases[:-2]) for w, phases in theta])
    new = checked_ranks(2, theta)
    need(old == tuple(F(n, 100) for n in (359, 356, 356, 359, 359, 243, 256)), 'old seven ranks')
    need(new == tuple(F(n, 100) for n in (363, 364, 356, 364, 363, 356, 356)), 'new seven ranks')
    violation = min(new)-min(old)-F(10, 9)
    need(violation == F(17, 900), 'strict fixed-increment violation')
    envelope = parent_prefix_bound(2, theta)
    need(min(envelope) == min(new), 'parent-prefix bound attains counterexample rank')
    concentrated = tuple((F(1, 4), (0, r, 0, 7*(3*r % 5))) for r in ROWS)
    small_old = checked_ranks(0, [(w, phases[:-2]) for w, phases in concentrated])
    small_new = checked_ranks(1, concentrated)
    small_envelope = parent_prefix_bound(1, concentrated)
    need(set(small_old) == set(small_new) == {F(7, 4)}, 'concentrated actual ranks')
    need(small_envelope == (F(17, 4),)*6+(F(83, 20),), 'concentrated envelope')
    need(min(small_envelope) > 4, 'envelope is not a universal target certificate')
    # Empty mixed phases and distinct new children sharing the same parent.
    boundary = ((F(1, 2), (0, 0, 0, 0)), (F(1, 2), (0, 1, 0, 1)))
    checked_ranks(1, boundary)
    parent_prefix_bound(1, boundary)
    rejected = 0
    for operation in (lambda: mixture(1, ((0.5, (0, 1, 0, 0)),)),
                      lambda: mixture(1, ((1, (0, 1, 0, 35)),)),
                      lambda: mixture(1, ((F(1, 2), (0, 1, 0, 0)),)),
                      lambda: parent_prefix_bound(0, ((1, (0, 1)),))):
        try:
            operation()
        except ValueError:
            rejected += 1
        else:
            raise ValueError('malformed control accepted')
    need(rejected == 4, 'malformed controls')
    return {'scope': 'literal-mixture rank increment refutation and general parent-prefix bound; no Lean claim',
            'counterexample': {'layouts': len(theta), 'weight_denominator': 100,
                              'old_ranks': old, 'new_ranks': new,
                              'rank_increment': min(new)-min(old), 'claimed_increment': F(10, 9),
                              'strict_violation': violation, 'parent_prefix_branches': envelope},
            'concentrated_child': {'actual_old_rank': min(small_old), 'actual_new_rank': min(small_new),
                                   'parent_prefix_branches': small_envelope, 'target': 4},
            'rejected_malformed_controls': rejected}


if __name__ == '__main__':
    print(json.dumps(self_check(), default=str, indent=2, sort_keys=True))
