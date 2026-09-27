#!/usr/bin/env python3
"""Exact CRT phase maxima for a load-20 layer; Python standard library only."""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import json
import argparse
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    primes = (3, 5, 7, 11, 13, 17, 19)
    heights = (4, 1, 1, 1, 1, 1, 1)
    period = prod(p ** h for p, h in zip(primes, heights))
    patterns = [w for w in product(*(range(h + 1) for h in heights))
                if prod(v + 1 for v in w) == 20]
    require(len(patterns) == 15, "Unexpected valuation patterns")
    require(all(w[0] == 4 and sum(w[1:]) == 2 for w in patterns),
            "Layer characterization")

    def count(p, h, w):
        return 1 if w == h else (p - 1) * p ** (h - w - 1)

    size = sum(prod(count(p, h, w) for p, h, w in zip(primes, heights, ws))
               for ws in patterns)
    maxima = []
    by_other_support = {}
    for exponents in product(*(range(h + 1) for h in heights)):
        phase_types = {}
        for ws in patterns:
            phase_type = tuple(min(w, a) for w, a in zip(ws, exponents))
            n = prod(count(p, h, w) if w >= a else p ** (h - a)
                     for p, h, w, a in zip(primes, heights, ws, exponents))
            phase_types[phase_type] = phase_types.get(phase_type, 0) + n
        maxima.append(max(phase_types.values()))
        other_support = tuple(p for p, a in zip(primes[1:], exponents[1:]) if a)
        this_maximum = max(phase_types.values())
        require(other_support not in by_other_support or
                by_other_support[other_support] == this_maximum,
                "Three-adic depth changed the phase maximum")
        by_other_support[other_support] = this_maximum
    maximum_mean = F(sum(maxima), size)

    # Independent closed form. The q's count nonzero root values.
    q = tuple(p - 1 for p in primes[1:])
    elementary = [sum(prod(t) for t in combinations(q, j)) for j in range(7)]
    require(size == elementary[4] == 166464, "Layer count")
    closed_form = 5 * (4 + F(sum(elementary[:4]), elementary[4]))
    require(len(maxima) == 320, "Divisor count")
    require(maximum_mean == closed_form == F(3454915, 166464),
            "All-phase maximum")
    haar_mass = F(size, period)
    density = 1 / haar_mass
    density_cap = F(6075000000000, 7235955529)
    r_bound = F(70871, 3375)
    require(haar_mass == F(1088, 855855), "Haar mass")
    require(F(1, 5) <= density < density_cap, "Density bounds")
    require(maximum_mean - 1 < r_bound, "All-query bound")

    # E cannot be the entire original survivor set with moduli dividing K.
    # At 3-depth zero, projections to at most two other primes are full.
    # All remaining labels together have insufficient reciprocal inventory.
    other = primes[1:]
    reciprocal_product = prod(1 + F(1, p) for p in other)
    triple_tail = sum((F(1, prod(t)) for j in range(3, 7)
                       for t in combinations(other, j)), F())
    cover_budget = sum((F(1, 3 ** j) for j in range(1, 5)), F()) \
        * reciprocal_product + triple_tail
    cover_gap = 1 - haar_mass - cover_budget
    require(cover_budget == F(133338, 146965), "Available cover budget")
    require(cover_gap == F(1330577, 14549535) > 0, "Original survivor obstruction")

    # Any law on a higher lift, not only the uniform lift, must pay for
    # partitioning each phase into 3^j finer three-adic cylinders.
    # Three-prime labels give an additional bound for arbitrary pair weights.
    complement_reciprocals = {
        pair: sum((F(1, r - 1) for r in other if r not in pair), F())
        for pair in combinations(other, 2)
    }
    least_complement = min(complement_reciprocals.values())
    require(least_complement == F(217, 720), "Triple-label complement minimum")
    require([pair for pair, value in complement_reciprocals.items()
             if value == least_complement] == [(5, 7)], "Minimum pair")
    one_depth_lower = 4 + least_complement / 3
    require(one_depth_lower == F(8857, 2160), "One-depth phase lower bound")
    depth_bounds = []
    for extra_depth in range(3):
        depth_factor = 5 + sum((F(1, 3 ** j)
                               for j in range(1, extra_depth + 1)), F())
        closed_factor = F(11, 2) - F(1, 2 * 3 ** extra_depth)
        require(depth_factor == closed_factor, "Higher-prefix factor")
        lower = depth_factor * one_depth_lower
        depth_bounds.append({"extra_three_depth": extra_depth,
                             "total_three_height": 4 + extra_depth,
                             "three_depth_factor": str(depth_factor),
                             "maximum_complete_mean_lower": str(lower),
                             "R_lower": str(lower - 1),
                             "R_lower_minus_source_bound": str(lower - 1 - r_bound)})
    require(F(depth_bounds[1]["R_lower_minus_source_bound"]) < 0,
            "One-extra-depth comparison")
    require(F(depth_bounds[2]["R_lower_minus_source_bound"]) == F(158401, 486000) > 0,
            "Two-extra-depth exclusion")
    supported_r_lower = F(depth_bounds[2]["R_lower"])
    escape_mass = 1 - r_bound / supported_r_lower
    escape_haar = escape_mass / density_cap
    require(escape_mass == F(158401, 10363825), "Partial-support escape mass")
    require(escape_haar == F(1146182591749129, 62960236875000000000),
            "Partial-support Haar floor")

    result = {
        "result": "PASS", "period": period, "primes": primes, "heights": heights,
        "set": "0 mod 81; exactly two of 5,7,11,13,17,19 divide x",
        "query": "phase zero for every divisor, including one",
        "query_load_on_E": 20, "E_count": size, "haar_mass": str(haar_mass),
        "uniform_density": str(density), "source_density_cap": str(density_cap),
        "complete_divisors_checked": len(maxima),
        "sum_of_phase_maximum_counts": sum(maxima),
        "phase_maxima_by_other_prime_support": [
            {"other_primes": t, "maxcount": n, "number_of_three_depths": 5}
            for t, n in sorted(by_other_support.items(), key=lambda row: (len(row[0]), row[0]))
        ],
        "phase_maxima_aggregated_by_support_size": [
            {"size": j, "supports": sum(len(t) == j for t in by_other_support),
             "sum_maxcounts_at_one_three_depth": sum(n for t, n in by_other_support.items()
                                                      if len(t) == j)}
            for j in range(7)
        ],
        "maximum_complete_query_mean": str(maximum_mean),
        "R_nonunit": str(maximum_mean - 1), "R_bound": str(r_bound),
        "R_margin": str(r_bound - (maximum_mean - 1)),
        "original_survivor_obstruction": {
            "scope": "Original distinct nonunit moduli dividing this exact K only",
            "available_reciprocal_budget": str(cover_budget),
            "required_complement_mass": str(1 - haar_mass),
            "positive_gap": str(cover_gap),
        },
        "higher_prefix_obstruction": {
            "quantifier": "Every probability nu on Z/(3^(4+h)*5*7*11*13*17*19) "
                          "whose projection is supported on E; arbitrary projected weights "
                          "and arbitrary dependent higher digits",
            "one_other_prime_layout_lower": str(one_depth_lower),
            "minimum_complement_reciprocal_sum": str(least_complement),
            "minimum_pair": [5, 7],
            "maximum_complete_mean_lower": "(5+sum_(j=1..h)3^(-j))*8857/2160",
            "R_lower": "(5+sum_(j=1..h)3^(-j))*8857/2160-1",
            "mechanism": "For arbitrary zero-pair weights w_C, labels with at most two "
                         "other primes contribute at least four. For each three-prime T, "
                         "its maximum phase mass is at least (1/3) sum_(C subset T,|C|=2) "
                         "w_C/(r-1), where {r}=T\\C. Summing T gives at least 217/2160 "
                         "in addition. Each selected phase is partitioned into 3^j "
                         "higher three-adic cylinders; their maximum mass is at least "
                         "3^(-j) times its original mass. Labels choose phases independently.",
            "first_excluded_extra_depth_for_this_lower_bound": 2,
            "first_excluded_total_three_height": 6,
            "positive_gap_at_extra_depth_two": "158401/486000",
            "finite_depth_checks": depth_bounds,
            "no_uniform_lift_or_independence_assumption": True,
        },
        "source_measure_escape": {
            "prime_scope": "Original family supported on a subset of 3,5,7,11,13,17,19",
            "period_scope": "A common finite period resolving the original family and "
                          "all divisors of 3^6*5*7*11*13*17*19",
            "premises": "One actual source probability mu supported on original U, "
                       "R(mu)<=70871/3375, and mu<=Lambda7*H from report467",
            "submeasure_inequality": "R(mu)>=R(mu restricted to E)>=mu(E)*414553/19440",
            "mu_U_minus_E_lower": str(escape_mass),
            "haar_U_minus_E_lower": str(escape_haar),
            "scope": "Mass must escape this low-R base layer. Escaped points are not "
                    "asserted to have positive two-prime capacity; no new noncoverage range.",
        },
        "scope": "Actual complete queries and one actual probability meet all phase maxima, "
                 "prefix consistency, density and R bounds at the displayed base period. "
                 "E is provably not the complete original survivor set at this K. Every probability "
                 "supported over E violates the source R bound after two additional "
                 "three-adic query depths, so no compatible all-depth source law can have "
                 "this projected support. The exact-K cover budget does not classify "
                 "larger-period original-family realizations.",
        "phase_maximum_method": "For each divisor exponent vector, enumerate the actual "
                 "truncated valuation type of every possible phase. Count all E patterns "
                 "in each type. Nonzero phases of one type have equal counts by multiplication "
                 "by units in the separate CRT coordinates. Take the largest exact count. "
                 "This uses all 320 labels without enumerating the full period.",
    }
    encoded = json.dumps(result, indent=2) + "\n"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON result path")
    args = parser.parse_args()
    if args.output:
        args.output.write_text(encoded)
        print(json.dumps({"result": "PASS", "output": str(args.output),
                          "labels": len(maxima), "maximum_complete_query_mean": str(maximum_mean)}))
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
