#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
"""
from fractions import Fraction as F
from math import isqrt, prod
from pathlib import Path
import argparse
import json

HEAD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
               37, 41, 43, 47, 53, 59, 61, 67, 71, 73)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def primes_to(limit):
    prime = [True] * (limit + 1)
    prime[0] = prime[1] = False
    for divisor in range(2, isqrt(limit) + 1):
        if prime[divisor]:
            for value in range(divisor * divisor, limit + 1, divisor):
                prime[value] = False
    result = [value for value in range(2, limit + 1) if prime[value]]
    trial = [value for value in range(2, limit + 1)
             if all(value % divisor for divisor in range(2, isqrt(value) + 1))]
    require(result == trial, "sieve and trial-division prime lists agree")
    return result


def ternary_profile(height):
    require(height >= 1, "positive ternary height")
    r = F(1, 3 ** height)
    density = (1 - r) / 2
    first_sum = sum((F(1, 3 ** e) for e in range(1, height + 1)), F(0))
    chi_sum = sum((F(2 * e + 1, 3 ** e) for e in range(1, height + 1)), F(0))
    require(first_sum == density, "ternary first-moment sum")
    require(chi_sum == 2 - (height + 2) * r, "finite ternary chi sum")
    chi_factor = 1 + chi_sum / density
    require(chi_factor == 5 - 2 * height * r / (1 - r) < 5,
            "finite ternary Gamma factor")
    require(1 + first_sum / density == 2, "finite ternary cylinder factor")
    return {"height": height, "density": str(density), "chi_sum": str(chi_sum),
            "chi_factor": str(chi_factor), "cylinder_factor": "2"}


def certificate():
    all_primes = primes_to(4000)
    require(tuple(p for p in all_primes if 3 <= p <= 73) == HEAD_PRIMES,
            "all 20 odd head primes")
    external_chi_factor = prod(F(p * p - p + 2, (p - 3) * (p - 1))
                               for p in HEAD_PRIMES[1:])
    external_cylinder_factor = prod(F(p - 2, p - 3) for p in HEAD_PRIMES[1:])
    k_zero = 5 * external_chi_factor
    c_zero = 2 * external_cylinder_factor
    require(F(176921, 1000) < k_zero < F(176922, 1000) < 177,
            "all-positive-height star Gamma bound")
    require(c_zero < F(73, 10), "all-positive-height star cylinder sum")
    # For S_H=2-(H+2)3^-H, S_0=0. Multiplying S_H-S_(H-1) by 3^H
    # gives -(H+2)+3(H+1)=2H+1. These are coefficients of 1 and H.
    recurrence_coefficients = [-2 + 3, -1 + 3]
    require(2 - (0 + 2) == 0 and recurrence_coefficients == [1, 2],
            "finite chi-sum base case and recurrence polynomial")
    profiles = [ternary_profile(height) for height in (1, 2, 3, 8, 31, 64)]
    selected = [prime for prime in all_primes if prime > 73]
    scale = 10 ** 9
    ceiling_sum = sum((scale + (q - 1) ** 2 - 1) // ((q - 1) ** 2)
                      for q in selected)
    exact_partial = sum((F(1, (q - 1) ** 2) for q in selected), F(0))
    require(len(selected) == 529 and ceiling_sum == 2363054,
            "fixed finite prime-square calculation")
    require(exact_partial <= F(ceiling_sum, scale), "rounded prime upper sum")
    # For q>4000 prime, q=2j+1 with j>=2000. The decreasing-function bound
    # sum_(j>=n) j^-2 <= n^-2 + integral_n^infty x^-2 dx controls the tail.
    tail_index = 2000
    odd_tail = F(1, 4 * tail_index ** 2) + F(1, 4 * tail_index)
    prime_square_upper = F(ceiling_sum, scale) + odd_tail
    require(prime_square_upper == F(4976233, 2000000000) < F(1, 400),
            "infinite prime-square upper bound")
    pair_factor = 2 * F(157, 156) ** 2
    matching_loss = F(177, 400) * pair_factor
    retained = 1 - matching_loss
    require(matching_loss == F(1454291, 1622400) < F(9, 10), "matching loss")
    require(retained == F(168109, 1622400) > F(1, 10), "matching retained fibres")
    delta = F(3, 4)
    singleton_loss = F(177, 400) / delta ** 2
    residual_threshold = 1 - singleton_loss
    pair_raw_threshold = residual_threshold * (1 - delta) ** 2
    edge_threshold = pair_raw_threshold / F(73, 10)
    require(singleton_loss == F(59, 75), "singleton loss")
    require(residual_threshold == F(16, 75), "residual crossing budget")
    require(pair_raw_threshold == F(1, 75), "two-prime raw crossing budget")
    require(edge_threshold == F(2, 1095), "weighted graph-edge threshold")
    dense_primes = [q for q in all_primes if 79 <= q <= 181]
    dense_sum = sum((F(1, q * r) for j, q in enumerate(dense_primes)
                     for r in dense_primes[j + 1:]), F(0))
    require(len(dense_primes) == 21, "dense comparison prime count")
    require(dense_sum > F(14, 1000) > F(1, 75), "simplified budget is not universal")
    # The comparison has only 0 mod qr classes and no singleton-tail classes.
    # Thus E=0 and J=16*dense_sum. It violates the simplified uniform budget
    # I<=1/75 but DOES satisfy the full E+J<1 criterion.
    dense_actual_budget = 16 * dense_sum
    require(dense_actual_budget < 1, "dense comparison satisfies full block criterion")
    # General {3,5,7} actual head: the same uniform law supplies both
    # constants. The block identities and graph reductions are proved in
    # the accompanying problem dossier; this section checks their numbers.
    general_gamma = F(1889, 48)
    general_cylinder = F(2009, 360)
    finite_31 = sum((F(1, (q - 1) ** 2) for q in HEAD_PRIMES if q >= 31), F(0))
    finite_37 = sum((F(1, (q - 1) ** 2) for q in HEAD_PRIMES if q >= 37), F(0))
    square_31_upper = prime_square_upper + finite_31
    square_37_upper = prime_square_upper + finite_37
    component_factor = 3 * F(2791, 2700) ** 2
    component_loss = general_gamma * component_factor * square_31_upper
    degree_delta = F(2, 3)
    degree_coefficient = (general_gamma / degree_delta ** 2
                          + general_cylinder * (1 / (1 - degree_delta) ** 2
                                                + F(1, 108) / (1 - degree_delta) ** 3))
    require(degree_coefficient == F(403681, 2880), "maximum-degree-two coefficient")
    degree_loss = degree_coefficient * square_37_upper
    require(component_loss == F(8083223933051729599312138630673,
                                8423301546359219520000000000000) < 1,
            "prime-31 components of size at most three")
    require(degree_loss == F(189362442782277858843265057,
                             207982754231091840000000000) < 1,
            "prime-37 maximum degree two")
    # Every rounded term exceeds its true scaled value by less than one.
    # The resulting finite prime lower bound already makes the best common
    # delta scalar expression exceed one, even before its triangle term.
    square_31_lower = F(ceiling_sum - len(selected), scale) + finite_31
    require(exact_partial > F(ceiling_sum - len(selected), scale),
            "strict rounded prime lower bound")
    gamma_cube_margin = general_gamma * square_31_lower - F(33, 50) ** 3
    cylinder_cube_margin = general_cylinder * square_31_lower - F(17, 50) ** 3
    require(gamma_cube_margin > 0 and cylinder_cube_margin > 0,
            "prime-31 common-delta scalar obstruction")
    general_head = {
        "primes": [3, 5, 7], "same_uniform_law_Gamma_bound": str(general_gamma),
        "same_uniform_law_complete_cylinder_sum_bound": str(general_cylinder),
        "tail_prime_square_31_upper": str(square_31_upper),
        "tail_prime_square_37_upper": str(square_37_upper),
        "component_at_most_three_prime_31_factor": str(component_factor),
        "component_at_most_three_prime_31_loss_upper": str(component_loss),
        "component_at_most_three_prime_31_retained_lower": str(1 - component_loss),
        "maximum_degree_two_prime_37_delta": str(degree_delta),
        "maximum_degree_two_prime_37_coefficient": str(degree_coefficient),
        "maximum_degree_two_prime_37_loss_upper": str(degree_loss),
        "maximum_degree_two_prime_37_retained_lower": str(1 - degree_loss),
        "prime_31_common_delta_scalar_boundary": {
            "finite_prime_square_lower": str(square_31_lower),
            "Gamma_times_lower_exceeds_33_over_50_cubed": True,
            "cylinder_times_lower_exceeds_17_over_50_cubed": True,
            "Gamma_cube_margin": str(gamma_cube_margin),
            "cylinder_cube_margin": str(cylinder_cube_margin),
            "scope": "Only the common-delta scalar sufficient expression; not a covering counterexample."}}
    return {
        "general_357_head": general_head,
        "head_primes": list(HEAD_PRIMES), "minimum_each_head_height": 1,
        "K0": str(k_zero), "C0": str(c_zero),
        "ternary_finite_height": {
            "r": "3^(-H)", "density": "(1-r)/2", "chi_sum": "2-(H+2)*r",
            "chi_factor": "5-2*H*r/(1-r)", "cylinder_factor": "2",
            "base_H0_sum": "0", "recurrence_increment_coefficients": recurrence_coefficients,
            "exact_examples": profiles},
        "prime_cutoff": 4000, "rounding_scale": scale,
        "tail_primes_to_cutoff": selected, "prime_count": len(selected),
        "ceiling_sum": ceiling_sum, "odd_integer_tail_bound": str(odd_tail),
        "prime_square_upper": str(prime_square_upper),
        "matching_pair_factor": str(pair_factor), "matching_loss_upper": str(matching_loss),
        "matching_retained_lower": str(retained), "singleton_delta": str(delta),
        "singleton_loss_upper": str(singleton_loss),
        "residual_crossing_threshold": str(residual_threshold),
        "two_prime_raw_crossing_threshold": str(pair_raw_threshold),
        "weighted_edge_threshold": str(edge_threshold),
        "dense_comparison_primes": dense_primes, "dense_comparison_edges": 210,
        "dense_pair_reciprocal_sum": str(dense_sum),
        "dense_comparison_actual_E": "0", "dense_comparison_actual_J": str(dense_actual_budget),
        "dense_comparison_violates_simplified_uniform_budget": True,
        "dense_comparison_satisfies_full_block_criterion": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("star_block_obstruction_certificate.json"))
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    data = certificate()
    if args.write_certificate:
        args.certificate.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    else:
        require(json.loads(args.certificate.read_text(encoding="utf-8")) == data,
                "fixed certificate matches recomputed exact values")
    print(json.dumps({"result": "PASS", "minimum_each_head_height": 1,
                      "K0_decimal": float(F(data["K0"])), "C0_decimal": float(F(data["C0"])),
                      "prime_square_upper": data["prime_square_upper"],
                      "matching_retained_lower": data["matching_retained_lower"],
                      "residual_crossing_threshold": data["residual_crossing_threshold"],
                      "weighted_edge_threshold": data["weighted_edge_threshold"],
                      "dense_comparison_satisfies_full_block_criterion": True,
                      "general_357_component3_prime31_loss": data["general_357_head"]["component_at_most_three_prime_31_loss_upper"],
                      "general_357_degree2_prime37_loss": data["general_357_head"]["maximum_degree_two_prime_37_loss_upper"],
                      "prime31_scalar_Gamma_cube_obstruction": data["general_357_head"]["prime_31_common_delta_scalar_boundary"]["Gamma_times_lower_exceeds_33_over_50_cubed"],
                      "prime31_scalar_cylinder_cube_obstruction": data["general_357_head"]["prime_31_common_delta_scalar_boundary"]["cylinder_times_lower_exceeds_17_over_50_cubed"],
                      "scope": "Exact constants; arbitrary-height lifting is an ordinary proof."}))


if __name__ == "__main__":
    main()
