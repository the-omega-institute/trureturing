#!/usr/bin/env python3
"""Exact controls for report 379, not witnesses of an extremal odd cover."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json
import random


def check(ok, message):
    if not ok:
        raise ValueError(message)


def prefixes(p, depth):
    return [x for a in range(depth + 1) for x in product(range(p), repeat=a)]


def complete_leaves(p, r, depth, shift):
    level = {()}
    for a in range(depth):
        next_level = set()
        for u in level:
            start = (shift + a + sum((i + 1) * d for i, d in enumerate(u))) % p
            next_level.update(u + ((start + j) % p,) for j in range(r))
        level = next_level
    return sorted(level)


def check_branching(leaves, r, depth):
    for a in range(depth):
        parents = {x[:a] for x in leaves}
        check(all(len({x[a] for x in leaves if x[:a] == u}) == r for u in parents),
              'complete subtree branching')
    check(len(leaves) == r ** depth, 'complete subtree leaf count')


frequency_checks = 0
for p, q in [(5, 3), (7, 3), (7, 5), (11, 7)]:
    r = p - q + 1
    for s in range(r, p + 1):
        ell = s - r + 1
        subsets = list(combinations(range(s), ell))
        for u in range(s):
            check(F(sum(u in T for T in subsets), len(subsets)) == F(ell, s),
                  'root subset inclusion frequency')
            frequency_checks += 1
        check(ell + p - s == q, 'missing roots complete a legal root selection')

# Independent recursive minimax evaluation of the weighted-tree selection.
rng = random.Random(379)
tree_checks = 0
for p, q, depth in [(5, 3, 3), (7, 5, 2), (11, 7, 2)]:
    r = p - q + 1
    nodes = prefixes(p, depth)
    sharp = set(complete_leaves(p, r, depth, 1))
    cases = [{u: F(int(u in sharp)) for u in nodes}]
    cases += [{u: F(rng.randrange(5), rng.randrange(1, 6)) for u in nodes}
              for _ in range(32)]
    for case_index, weights in enumerate(cases):
        def choose(u):
            if len(u) == depth:
                return weights[u], [u]
            children = sorted((choose(u + (d,)) for d in range(p)),
                              key=lambda item: (item[0], item[1]))[:q]
            return (weights[u] + max(v for v, _ in children),
                    [leaf for _, leaves in children for leaf in leaves])
        score, leaves = choose(())
        cost = sum((weights[u] * F(r) ** (-len(u)) for u in nodes), F(0))
        check_branching(leaves, q, depth)
        actual = max(sum((weights[x[:a]] for a in range(depth + 1)), F(0))
                     for x in leaves)
        check(actual == score and score <= cost, 'weighted-tree minimax bound')
        if case_index == 0:
            check(score == cost == 1, 'sharp complete complementary subtree')
        tree_checks += 1

# Six conditional forest laws. The first coordinate has a nonuniform
# depth-two tail. The last two full coordinates have depths two, with
# branching 3 and 5. A quantile coupling retains their marginal laws
# but deliberately does not make them independent.
roots = (1, 2, 3, 4)
subsets = list(combinations(roots, 2))
conditional = []
residual = set()
for j, T in enumerate(subsets):
    u = min(T)
    first = complete_leaves(5, 3, 2, j)
    second = complete_leaves(7, 3, 2, 0 if 1 in T else 2)
    third = complete_leaves(11, 5, 2, 0 if 1 in T else 4)
    for leaves, branching in [(first, 3), (second, 3), (third, 5)]:
        check_branching(leaves, branching, 2)
    residual.update(((u,) + a, b, c) for a, b, c in product(first, second, third))
    law = defaultdict(F)
    for a in first:
        for ticket in range(225):
            law[((u,) + a, second[ticket // 25], third[ticket // 9])] += F(1, 2025)
    check(sum(law.values(), F(0)) == 1, 'conditional normalization')
    check(all(x[0][0] in T for x in law), 'conditional root support')
    for coordinate, max_depth, base in [(0, 3, 3), (1, 2, 3), (2, 2, 5)]:
        for a in range(1, max_depth + 1):
            masses = defaultdict(F)
            for x, mass in law.items():
                masses[x[coordinate][:a]] += mass
            cap = F(base) ** (-(a - 1) if coordinate == 0 else -a)
            check(max(masses.values()) <= cap, 'conditional full-height prefix cap')
    conditional.append(law)

# The fourth root can be present with a narrow fibre; no positive or
# uniform mass at that root was assumed in the forest construction.
residual.add(((4, 0, 0), (0, 0), (0, 0)))
check({x[0][0] for x in residual} == set(roots), 'all four actual control roots')
mixture = defaultdict(F)
for law in conditional:
    for x, mass in law.items():
        mixture[x] += mass / len(conditional)
check(sum(mixture.values(), F(0)) == 1 and set(mixture) <= residual,
      'mixture normalization and common support')

query_checks = 0
unsaturated_product_excess = F(0)
for alpha, beta, gamma in product(range(4), range(3), range(3)):
    masses = defaultdict(F)
    for x, mass in mixture.items():
        masses[(x[0][:alpha], x[1][:beta], x[2][:gamma])] += mass
    c = min(F(3) ** (-beta), F(5) ** (-gamma))
    cap = c if alpha == 0 else F(1, 2) * min(F(3) ** (1 - alpha), c)
    for mass in masses.values():
        check(mass <= cap, 'averaged same-law composite price')
        query_checks += 1
    if (alpha, beta, gamma) == (0, 2, 2):
        unsaturated_product_excess = max(masses.values()) - F(1, 225)
check(unsaturated_product_excess > 0, 'the unsaturated pair is not independent')
root_masses = {u: sum((mass for x, mass in mixture.items() if x[0][0] == u), F(0))
               for u in roots}
check(root_masses[1] == F(1, 2) > F(1, 3), 'the old first-prime cap need not remain')

# Finite cost fields test the order of integration and root selection.
# They are not claimed to be an original AP palette.
tails = [(rho, t) for rho in (1, 2) for t in product(range(3), repeat=2)
         if not ((rho == 1 and t[0] == 0) or (rho == 2 and t == (0, 0)))]
check(F(len(tails), 9) == F(14, 9), 'non-pure tail measure at H=3')
integrated = {u: F(0) for u in roots}
dynamic = F(0)
for rho, t in tails:
    zero_root = roots[(rho + t[0] + 2 * t[1]) % 4]
    costs = {u: F(u != zero_root) for u in roots}
    choices = [sum((costs[u] for u in T), F(0)) for T in subsets]
    check(min(choices) == 1, 'whole-menu root selection')
    dynamic += min(choices) / 9
    for u in roots:
        integrated[u] += costs[u] / 9
static = min(sum((integrated[u] for u in T), F(0)) for T in subsets)
averaged = sum(integrated.values(), F(0)) / 2
check(dynamic < static <= averaged, 'integral of minimum precedes minimum of integrals')

price_rows = []
for modulus, alpha, beta in [(5, 1, 0), (25, 2, 0), (35, 1, 1),
                              (175, 2, 1), (245, 1, 2)]:
    old = min(F(3) ** (-alpha), F(3) ** (-beta))
    new = F(1, 2) * min(F(3) ** (1 - alpha), F(3) ** (-beta))
    price_rows.append(dict(modulus=modulus, old=str(old), forest=str(new)))

print(json.dumps(dict(root_frequency_checks=frequency_checks, weighted_tree_checks=tree_checks,
                      conditional_laws=len(conditional), control_residual_points=len(residual),
                      mixture_support_points=len(mixture), composite_query_checks=query_checks,
                      first_root_masses={str(u): str(v) for u, v in root_masses.items()},
                      unsaturated_product_excess=str(unsaturated_product_excess),
                      tail_costs=dict(dynamic=str(dynamic), static=str(static),
                                      averaged=str(averaged)), price_rows=price_rows,
                      scope='Exact finite construction controls; no extremal odd-cover witness'),
                 indent=2))
