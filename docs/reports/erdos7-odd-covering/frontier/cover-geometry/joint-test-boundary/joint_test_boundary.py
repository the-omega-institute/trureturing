#!/usr/bin/env python3
"""Exact original-label counterexample to a composable scalar Gamma summary.

The carrier is Z/35 and the coarse projection is reduction modulo five.
All 1,5,7,35 test phases are independent. No covering conjecture is settled.
"""
from fractions import Fraction as F
from itertools import product
import json


LABELS = (1, 5, 7, 35)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def cost(x, phases):
    return sum(x % d == a for d, a in zip(LABELS, phases)) ** 2


def gamma(law):
    require(all(type(x) is int and 0 <= x < 35 for x in law), "actual carrier")
    require(all(w >= 0 for w in law.values()) and sum(law.values()) == 1,
            "one probability before all tests")
    best, witness, count = F(-1), None, 0
    for a5, a7, a35 in product(range(5), range(7), range(35)):
        phases = (0, a5, a7, a35)
        value = sum((w * cost(x, phases) for x, w in law.items()), F())
        count += 1
        if value > best:
            best, witness = value, phases
    require(count == 1225, "complete independent numerical-label inventory")
    return {"value": str(best), "attaining_phases": witness, "layouts": count}


def project(law):
    marginal = {}
    for x, w in law.items():
        marginal[x % 5] = marginal.get(x % 5, F()) + w
    return marginal


def mix_with_zero(law):
    result = {x: w / 2 for x, w in law.items()}
    result[0] = result.get(0, F()) + F(1, 2)
    return result


def main():
    zero, five = {0: F(1)}, {5: F(1)}
    require(project(zero) == project(five) == {0: F(1)}, "same coarse marginal")
    before = [gamma(zero), gamma(five)]
    after = [gamma(mix_with_zero(zero)), gamma(mix_with_zero(five))]
    require([r["value"] for r in before] == ["16", "16"], "same scalar readout")
    require([r["value"] for r in after] == ["16", "10"],
            "the same continuation separates the scalar summary")
    require(project(mix_with_zero(zero)) == project(mix_with_zero(five)),
            "continuation still has the same coarse marginal")

    # One shared mixture of two literal coherent layouts, on the same two points.
    centers = tuple(tuple(x % d for d in LABELS) for x in (0, 5))
    columns = tuple(tuple(cost(x, layout) for x in (0, 5)) for layout in centers)
    require(columns == ((16, 4), (4, 16)), "literal centered costs")
    common_prices = tuple(F(columns[0][j] + columns[1][j], 2) for j in range(2))
    common_minimum = min(common_prices)
    separate_minima = sum((F(min(c), 2) for c in columns), F())
    require(common_minimum == 10 and separate_minima == 4,
            "minimization cannot be distributed over the common layout mixture")
    # This dual supplies ten against every supported law, and the balanced
    # probability above has full-layout maximum ten, so the minimax is exact.
    require(set(common_prices) == {F(10)} and after[1]["value"] == "10",
            "exact two-point common-law minimax")

    print(json.dumps({
        "carrier": 35, "coarse_modulus": 5, "labels": LABELS,
        "same_source": "The full residue carrier with no original exclusions.",
        "before": before, "after_fixed_half_mixture_with_delta_zero": after,
        "coherent_layouts": centers, "cost_vectors_by_layout": columns,
        "minimum_after_common_layout_mixture": str(common_minimum),
        "mixture_of_separately_minimized_costs": str(separate_minima),
        "two_point_support_minimax": "10",
        "scope": "Scalar-state insufficiency under one fixed operation; no minimum odd-cover realization or Lean certification claimed."
    }, indent=2))


if __name__ == "__main__":
    main()
