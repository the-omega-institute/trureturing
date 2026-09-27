#!/usr/bin/env python3
"""Exact abstract-source countermodel for report 388.

Standard library only. The output is deterministic JSON. All checks remain
enabled under Python -O. No actual odd-cover residual is asserted.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, prod
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


PRIMES = (5, 7, 11)
BASES = (3, 3, 5)
SHIFTS = (0, 1, 3)
CAPS = tuple(F(1, r) for r in BASES)
AMBIENT = tuple(product(*(range(p) for p in PRIMES)))
R = tuple(sorted({(u + 1, i + 1, i + SHIFTS[u] + d + 1)
                  for u in range(3) for i in range(6) for d in (0, 1)}))
check(len(R) == 36, "the constructed source has exactly 36 points")
check(all(all(0 < x[i] < PRIMES[i] for i in range(3)) for x in R),
      "every source coordinate is a nonzero original first root")
R_membership = tuple(x for x in AMBIENT
                     if 1 <= x[0] <= 3 and 1 <= x[1] <= 6
                     and x[2] - x[1] - SHIFTS[x[0] - 1] in (0, 1))
check(R == R_membership, "independent ambient-membership construction")


# Test every increasing nonempty subchain above q=3. The next tree
# branching number is the preceding selected prime, not the preceding
# ambient prime. Intersections are checked on this same 36-point source.
chain_results = []
for length in range(1, 4):
    for axes in combinations(range(3), length):
        branchings = (3,) + tuple(PRIMES[i] for i in axes[:-1])
        tree_options = [tuple(combinations(range(PRIMES[i]), width))
                        for i, width in zip(axes, branchings)]
        checked = 0
        for trees in product(*tree_options):
            check(any(all(x[i] in roots for i, roots in zip(axes, trees))
                      for x in R), "a complete chain-tree product misses R")
            checked += 1
        expected = prod(comb(PRIMES[i], width)
                        for i, width in zip(axes, branchings))
        check(checked == expected, "complete chain enumeration count")
        chain_results.append(dict(primes=[PRIMES[i] for i in axes],
                                  branchings=list(branchings), tests=checked))
check(sum(row["tests"] for row in chain_results) == 85890,
      "all seven subchains were checked completely")


projection_sizes = [len({x[i] for x in R}) for i in range(3)]
check(projection_sizes == [3, 6, 10], "source projection sizes")
marginal_counts = [Counter(x[i] for x in R) for i in range(3)]
marginal_max = [F(max(counts.values()), len(R)) for counts in marginal_counts]
check(marginal_max == [F(1, 3), F(1, 6), F(1, 6)],
      "uniform source marginal maxima")
check(all(value <= cap for value, cap in zip(marginal_max, CAPS)),
      "one common law satisfies the complete-chain marginal caps")


# All squarefree queries obey the k=1 saturated-prefix bound of report
# 378 for the COMPLETE chain 3<5<7<11. No stronger subchain caps are pooled.
query_results = []
for length in range(4):
    for axes in combinations(range(3), length):
        counts = Counter(tuple(x[i] for i in axes) for x in R)
        actual = F(max(counts.values()), len(R))
        other_cap = min([CAPS[i] for i in axes if i != 0] + [F(1)])
        cap = CAPS[0] * other_cap if 0 in axes else other_cap
        check(actual <= cap, "saturated-prefix common-law query cap")
        query_results.append(dict(primes=[PRIMES[i] for i in axes],
                                  maximum=str(actual), cap=str(cap)))
pair_max = []
for axes in combinations(range(3), 2):
    maximum = F(max(Counter(tuple(x[i] for i in axes) for x in R).values()),
                len(R))
    check(maximum <= prod(CAPS[i] for i in axes),
          "even all three pair-product bounds hold")
    pair_max.append(dict(primes=[PRIMES[i] for i in axes], maximum=str(maximum)))


# At the final step of ANY full-coordinate read-once policy, fixing the
# two already sampled roots leaves at most two allowed roots. This
# pointwise check supplies the obstruction for every adaptive schedule.
max_terminal_fibres = []
for axis in range(3):
    groups = {}
    for x in R:
        key = tuple(x[i] for i in range(3) if i != axis)
        groups.setdefault(key, set()).add(x[axis])
    maximum = max(map(len, groups.values()))
    check(maximum == 2, "largest final-coordinate root fibre")
    check(maximum * CAPS[axis] < 1, "terminal row has insufficient total capacity")
    max_terminal_fibres.append(maximum)
atom_cap = prod(CAPS)
check(atom_cap == F(1, 45) and len(R) * atom_cap == F(4, 5),
      "joint root-cell capacity deficit")


def crt(roots):
    value, modulus = 0, 1
    for root, prime in zip(roots, PRIMES):
        value += ((root - value) * pow(modulus, -1, prime) % prime) * modulus
        modulus *= prime
        value %= modulus
    check(modulus == 385, "complete squarefree carrier")
    return value


DIVISORS = tuple(sorted(prod(PRIMES[i] for i in range(3) if mask & (1 << i))
                        for mask in range(8)))
check(DIVISORS == (1, 5, 7, 11, 35, 55, 77, 385), "complete divisor layout")
ambient_crt = {x: crt(x) for x in AMBIENT}
check(set(ambient_crt.values()) == set(range(385)), "CRT bijection")
tau = F(49)
layout_checks = 0
hinges = {}
for center in R:
    c = ambient_crt[center]
    for x in AMBIENT:
        load = sum((ambient_crt[x] - c) % d == 0 for d in DIVISORS)
        check(load == prod(1 + int(a == b) for a, b in zip(x, center)),
              "fixed integer-residue layout equals product load")
        hinge = max(F(load * load) - tau, F(0))
        check(hinge == (F(15) if x == center else F(0)),
              "squared-load stop-loss is one fixed root-cell indicator")
        if x in R:
            hinges[center, x] = hinge
        layout_checks += 1

# This pointwise equality is the dual certificate for ALL supported laws:
# after integrating, the sum of the 36 fixed-layout hinge costs is 15.
for x in R:
    check(sum(hinges[center, x] for center in R) == 15,
          "pointwise uniform-layout dual certificate")
minimax_cost = F(15, len(R))
check(all(sum(hinges[center, x] for x in R) / len(R) == minimax_cost
          for center in R), "uniform R attains the restricted-layout minimax")
auxiliary_cost = F(0)
auxiliary_mass = F(0)
for bits in product((0, 1), repeat=3):
    probability = prod(cap if bit else 1 - cap for bit, cap in zip(bits, CAPS))
    load = prod(1 + bit for bit in bits)
    auxiliary_mass += probability
    auxiliary_cost += probability * max(F(load * load) - tau, F(0))
check(auxiliary_mass == 1, "independent finite-depth comparison normalization")
check(minimax_cost == F(5, 12) and auxiliary_cost == F(1, 3),
      "exact strict stop-loss separation")
check(minimax_cost - auxiliary_cost == F(1, 12), "positive dual separation")


print(json.dumps(dict(
    scope="Abstract source; no actual odd-cover residual or E7 conclusion",
    primes=list(PRIMES), shifts=list(SHIFTS), source_points=[list(x) for x in R],
    source_size=len(R), subchain_tests=chain_results,
    total_subchain_tests=sum(row["tests"] for row in chain_results),
    projection_sizes=projection_sizes, complete_chain_bases=list(BASES),
    uniform_marginal_maxima=[str(x) for x in marginal_max],
    saturated_queries=query_results, pair_product_controls=pair_max,
    maximum_terminal_root_fibres=max_terminal_fibres,
    root_cell_cap=str(atom_cap), total_root_cell_capacity=str(len(R) * atom_cap),
    stoploss=dict(tau=str(tau), complete_layout_checks=layout_checks,
                  supported_law_minimax=str(minimax_cost),
                  independent_bernoulli_value=str(auxiliary_cost),
                  strict_gap=str(minimax_cost - auxiliary_cost)),
    all_height_scope="Uniform-tail lift and its conditional-law obstruction are proved in report 388; no infinite-height stop-loss comparison is claimed"
), indent=2, sort_keys=True))
