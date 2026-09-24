#!/usr/bin/env python3
"""Check the finite constants and local facts of the all-height comb family."""
import argparse
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pair(value):
    return [value.numerator, value.denominator]


def calculate():
    qs = (5, 7, 11, 13, 17, 19)
    cutoff = 3
    height = 405
    a = {q: sum((F(1, q ** e) for e in range(1, cutoff + 1)), F(0)) for q in qs}
    u = {q: a[q] / (1 - a[q]) for q in qs}
    g = prod(1 - u[q] for q in qs)
    h1 = sum(u[q] * prod(1 - u[r] for r in qs if r != q) for q in qs)
    bad_fibre = 3 * g + 2 * h1 - 2
    residual_fibre = 2 + sum(u.values()) - prod(1 + value for value in u.values())
    v = {q: u[q] / (1 - u[q]) for q in qs}
    require(all(0 < value < 1 for value in v.values()), "invalid Bernoulli parameter")
    overlap_w = g * (3 - 2 * sum(v.values()) - 2 * prod(1 - value for value in v.values()))
    overlap_z = 2 - sum(u.values()) - g
    mask = {q: 1 - 2 * r * a[q] for r, q in enumerate(qs, 1)}
    require(all(value > 0 for value in mask.values()), "empty product mask")
    query_unrounded = 2 * prod(1 + 1 / ((q - 1) * mask[q]) for q in qs) - 1
    query_upper = 2 * prod(1 + F(1, q - 1 - 2 * r)
                                for r, q in enumerate(qs, 1)) - 1
    density_unrounded = 2 / prod(mask.values())
    density_upper = 2 * prod(F(q - 1, q - 1 - 2 * r) for r, q in enumerate(qs, 1))
    reserve = 1 - F(51, 616) * (1 + query_upper)

    def side(p, e, digit):
        return ((digit + 1) * p ** (e - 1) - 1, p ** e)

    # Finite controls of the local disjointness used by the symbolic proof.
    cylinder_pairs = 0
    for p in (3,) + qs:
        cylinders = [side(p, e, digit) for e in range(1, cutoff + 1)
                     for digit in range(p - 1)]
        for (r, m), (s, n) in combinations(cylinders, 2):
            require((r - s) % min(m, n) != 0, "side cylinders intersect")
            cylinder_pairs += 1

    def gamma(q, size, epsilon):
        return min(2 * size - 2 + epsilon, q - 2)

    supports = [set(d) for size in range(2, 7) for d in combinations(qs, size)]
    proper_checks = 0
    equal_checks = 0
    mask_checks = 0
    for support in supports:
        size = len(support)
        q = max(support)
        rank = qs.index(q) + 1
        require(q - 2 >= 2 * rank, "rank separation failed")
        require(gamma(q, size, 0) < gamma(q, size, 1), "equal-support phases collide")
        equal_checks += 1
        for epsilon in (0, 1):
            require(gamma(q, size, epsilon) == 2 * size - 2 + epsilon
                    <= 2 * rank - 1, "largest-coordinate mask fails")
            mask_checks += 1
        for smaller in supports:
            if smaller < support:
                prime = max(smaller)
                for epsilon, other in product((0, 1), repeat=2):
                    require(gamma(prime, len(smaller), other) < gamma(prime, size, epsilon),
                            "proper-support private-point separation failed")
                    proper_checks += 1
    require(all(gamma(q, len(d), epsilon) >= 2 for d in supports
                for q in d for epsilon in (0, 1)), "mixed side overlaps an earlier blocker")

    require(bad_fibre < F(-19, 1000), "negative fibre bound failed")
    require(residual_fibre < F(27, 40), "residual fibre bound failed")
    concentration = F(19, 694)
    uniform_z4 = F(2, 3 ** 4 + 1)
    uniform_bound4 = (1 - uniform_z4) * F(-19, 1000) + uniform_z4 * F(27, 40)
    require(uniform_bound4 == F(-17, 8200) < 0, "uniform source obstruction failed")
    height_surplus = height * concentration - F(565, 51)
    require(height_surplus == F(335, 35394) > 0, "height threshold failed")
    require(overlap_w > F(1, 10) and overlap_z > F(3, 4), "overlap repair failed")
    require(query_unrounded < query_upper == F(1097, 128) < F(565, 51), "query target failed")
    require(density_unrounded < density_upper == 720, "source density bound failed")
    require(reserve == F(2339, 11264) > 0, "later continuation failed")
    require(reserve / density_upper > F(1, 3500), "Haar floor failed")
    return {
        "scope": "Finite local facts and rational constants; arbitrary-height deductions are ordinary proofs.",
        "q_primes": list(qs),
        "nonternary_height": cutoff,
        "method_obstruction_from_height": height,
        "original_count_at_threshold": (height + 1) * (cutoff + 1) ** len(qs) - 1,
        "side_cylinder_pair_checks_through_depth_three": cylinder_pairs,
        "proper_support_phase_checks": proper_checks,
        "equal_support_phase_checks": equal_checks,
        "largest_coordinate_mask_checks": mask_checks,
        "u_parameters": [pair(u[q]) for q in qs],
        "K": pair(bad_fibre),
        "T": pair(residual_fibre),
        "coarse_concentration_floor": pair(concentration),
        "uniform_source_upper_at_height_four": pair(uniform_bound4),
        "query_obstruction_surplus_at_threshold": pair(height_surplus),
        "overlap_corrected_w_mass": pair(overlap_w),
        "overlap_corrected_z_mass": pair(overlap_z),
        "alternative_query_unrounded_uniform_upper": pair(query_unrounded),
        "alternative_query_upper": pair(query_upper),
        "alternative_query_target_surplus": pair(F(565, 51) - query_upper),
        "alternative_density_unrounded_uniform_upper": pair(density_unrounded),
        "alternative_density_upper": pair(density_upper),
        "later_remaining_probability": pair(reserve),
        "later_haar_floor": pair(reserve / density_upper),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = calculate()
    if args.output is None:
        expected = json.loads(Path(__file__).with_suffix(".json").read_text())
        require(result == expected, "retained result mismatch")
    else:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"method_obstruction_from_height": result["method_obstruction_from_height"],
                      "alternative_query_upper": result["alternative_query_upper"],
                      "later_haar_floor": result["later_haar_floor"]}))


if __name__ == "__main__":
    main()
