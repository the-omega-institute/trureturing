#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product as cartesian_product
from math import gcd, isqrt, prod
from pathlib import Path
import argparse
import json

HEAD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
               37, 41, 43, 47, 53, 59, 61, 67, 71, 73)



# The entrypoint source pin transitively binds every split arithmetic module.
_SPLIT_SOURCE_SHA256 = {'star_block/base.py': '4c297e9df73860240770c96fd66b64ad32c2f7baac83e610367d24574848c0c0',
 'star_block/density.py': '0bb2f9bb7f4eedea9e53efac665492e2a2605d3d033f6a226dff1412f0e9d389',
 'star_block/ranks.py': 'a97e457b48e080b5fd52082cf1821aa401a4988527a41f0f96ad6fa73909a53f',
 'star_block/stoploss.py': 'ceda5556d5bcdff861254dd57523a9b3a4486c26618c8a4ec6be8ac7ffd9043a'}
for _relative, _pin in _SPLIT_SOURCE_SHA256.items():
    if _certificate_sha256((_certificate_root / _relative).read_bytes()).hexdigest() != _pin:
        raise ValueError("split arithmetic source SHA-256 mismatch: " + _relative)

from star_block.base import *
from star_block.ranks import *
from star_block.stoploss import *
from star_block.density import *

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
    # A sharper, separately retained prime bound supports the new graph
    # criteria. The earlier 4000 certificate and its constants stay intact.
    extended_primes = primes_to(40000)
    extended_tail = [p for p in extended_primes if p > 73]
    extended_scale = 10 ** 12
    extended_ceiling = sum((extended_scale + (p - 1) ** 2 - 1) // ((p - 1) ** 2)
                           for p in extended_tail)
    extended_odd_tail = F(1, 1600000000) + F(1, 80000)
    extended_square = F(extended_ceiling, extended_scale) + extended_odd_tail
    require(len(extended_tail) == 4182 and extended_ceiling == 2387697612,
            "extended finite prime-square sum")
    require(extended_square == F(2400198237, 10 ** 12),
            "extended infinite prime-square bound")

    def square_upper(cutoff):
        return extended_square + sum((F(1, (p - 1) ** 2)
                                      for p in HEAD_PRIMES if cutoff <= p <= 73), F(0))

    def graph_bounds(cutoff, gamma, cylinder, hub_count, matching_hubs):
        a0 = F(1, cutoff - 1)
        square = square_upper(cutoff)
        hub_primes = [p for p in extended_primes if p >= cutoff][:hub_count]
        weights = [F(1, p - 1) for p in hub_primes]
        product = prod(1 + a for a in weights)
        moment_factor = prod(1 + 3 * a + 2 * a * a for a in weights)
        cube_margin = square - hub_count * a0 * a0
        derivative_margin = (cylinder - 2 * gamma * a0 * (1 + a0)
                             * (1 + 2 * a0) ** hub_count)
        require(cube_margin >= 0 and derivative_margin > 0,
                "hub comparison is monotone on the entire padded cube")
        loss = (cylinder * (product - 1)
                + gamma * moment_factor * (square - sum(a * a for a in weights)))
        require(loss < 1, "vertex-cover exclusion")
        matching_weights = weights[:matching_hubs]
        pair_factor = 2 * (1 + a0 / 2) ** 2
        matching = (cylinder * (prod(1 + a for a in matching_weights) - 1)
                    + gamma * prod(1 + 3 * a + 2 * a * a for a in matching_weights)
                    * pair_factor * square)
        require(matching < 1, "hub deletion leaving a matching")
        return {"tail_prime_minimum": cutoff, "Gamma_bound": str(gamma),
                "cylinder_sum_bound": str(cylinder), "prime_square_upper": str(square),
                "vertex_cover_cardinality": hub_count, "worst_hub_primes": hub_primes,
                "cube_nonnegative_remainder_margin": str(cube_margin),
                "partial_derivative_lower_margin": str(derivative_margin),
                "hub_cylinder_product": str(product), "hub_moment_factor": str(moment_factor),
                "vertex_cover_loss_upper": str(loss),
                "vertex_cover_retained_lower": str(1 - loss),
                "matching_deletion_cardinality": matching_hubs,
                "matching_pair_factor": str(pair_factor), "matching_loss_upper": str(matching),
                "matching_retained_lower": str(1 - matching)}

    star_hubs = graph_bounds(79, F(177), F(73, 10), 8, 1)
    general_hubs = graph_bounds(37, general_gamma, general_cylinder, 6, 2)
    forest_rows = []
    for name, cutoff, gamma, target in [
            ("star_head", 79, F(177), F(58842, 100000)),
            ("arbitrary_357_head", 19, general_gamma, F(858311, 1000000))]:
        a0 = F(1, cutoff - 1)
        factor = 1 + 3 * a0 + 2 * a0 * a0
        loss = F(4, 3) * gamma * factor * square_upper(cutoff)
        require(loss < target < 1, "star-forest exclusion")
        forest_rows.append({"head": name, "tail_prime_minimum": cutoff,
                            "Gamma_bound": str(gamma), "maximum_center_factor": str(factor),
                            "prime_square_upper": str(square_upper(cutoff)),
                            "loss_upper": str(loss), "retained_lower": str(1 - loss)})
    # For a saturated star, alpha+sum beta>=1. The identity
    # alpha^2+1-alpha = (alpha-1/2)^2+3/4 supplies the 4/3 factor.
    require([F(1, 4) + F(3, 4), F(-1), F(1)] == [F(1), F(-1), F(1)],
            "saturation quadratic identity coefficients")
    # Exact polynomial arithmetic for the potential identity, with variables
    # b,c and Phi(t)=t-t^3/3. This checks the identity for all real b,c;
    # its sign conditions and the finite-tree cancellation are ordinary proofs.
    def polynomial_sum(*terms):
        result = {}
        for term in terms:
            for exponent, coefficient in term.items():
                result[exponent] = result.get(exponent, F(0)) + coefficient
        return {exponent: coefficient for exponent, coefficient in result.items()
                if coefficient}

    def polynomial_scale(coefficient, term):
        return {exponent: coefficient * value for exponent, value in term.items()
                if coefficient * value}

    def polynomial_product(*terms):
        result = {(0, 0): F(1)}
        for term in terms:
            products = [
                {(left[0] + right[0], left[1] + right[1]): x * y}
                for left, x in result.items() for right, y in term.items()]
            result = polynomial_sum(*products)
        return result

    one, b, c = ({(0, 0): F(1)}, {(1, 0): F(1)}, {(0, 1): F(1)})
    b_square = polynomial_product(b, b)
    c_square = polynomial_product(c, c)
    b_cube = polynomial_product(b_square, b)
    c_cube = polynomial_product(c_square, c)
    one_minus_c = polynomial_sum(one, polynomial_scale(-1, c))
    one_minus_b = polynomial_sum(one, polynomial_scale(-1, b))
    b_minus_c = polynomial_sum(b, polynomial_scale(-1, c))
    phi_b = polynomial_sum(b, polynomial_scale(F(-1, 3), b_cube))
    phi_c = polynomial_sum(c, polynomial_scale(F(-1, 3), c_cube))
    potential_left = polynomial_sum(polynomial_product(b, one_minus_c, one_minus_c),
                                    phi_c, polynomial_scale(-1, phi_b))
    potential_right = polynomial_sum(
        polynomial_product(c, one_minus_b, one_minus_b),
        polynomial_scale(F(1, 3), polynomial_product(b_minus_c, b_minus_c, b_minus_c)))
    require(potential_left == potential_right,
            "forest potential identity holds coefficient by coefficient")
    arbitrary_forest_rows = []
    for name, cutoff, gamma, target, expected_loss in [
            ("arbitrary_357_head", 19, general_gamma, F(965600, 1000000),
             F(6024840902671133365942778501, 6239482626932755200000000000)),
            ("star_head", 79, F(177), F(661972, 1000000),
             F(11187323982657, 16900000000000))]:
        a0 = F(1, cutoff - 1)
        factor = 1 + 3 * a0 + 2 * a0 * a0
        loss = F(3, 2) * gamma * factor * square_upper(cutoff)
        require(loss == expected_loss < target < 1, "arbitrary-forest exclusion")
        finite_profiles = []
        for height in (1, 2, 8):
            exponent_pairs = sum((F(1, cutoff ** max(e, f))
                                  for e in range(height + 1)
                                  for f in range(height + 1)), F(0))
            counted_pairs = 1 + sum((F(2 * e + 1, cutoff ** e)
                                      for e in range(1, height + 1)), F(0))
            require(exponent_pairs == counted_pairs < factor,
                    "finite parent coefficient retains pure and edge labels")
            finite_profiles.append({"height": height, "coefficient": str(counted_pairs)})
        arbitrary_forest_rows.append({
            "head": name, "tail_prime_minimum": cutoff, "Gamma_bound": str(gamma),
            "maximum_parent_factor": str(factor), "saturation_energy_factor": "3/2",
            "prime_square_upper": str(square_upper(cutoff)),
            "loss_upper": str(loss), "retained_lower": str(1 - loss),
            "finite_parent_coefficients": finite_profiles})
    feedback_rows = []
    for name, cutoff, gamma, depth, target, expected_loss in [
            ("arbitrary_357_head", 23, general_gamma, 1, F(956460, 1000000),
             F(1175604260732733206684398339119, 1229120627265994463000000000000)),
            ("star_head", 79, F(177), 2, F(966288, 1000000),
             F(16950596065609491264623331474432, 17541985668975977644799361621325))]:
        a0 = F(1, cutoff - 1)
        parent_factor = 1 + 3 * a0 + 2 * a0 * a0
        coefficient = F(3, 2) * parent_factor
        levels = [{"feedback_vertices": 0, "coefficient": str(coefficient)}]
        for level in range(1, depth + 1):
            previous = coefficient
            z = previous * parent_factor
            require(z >= F(3, 2) and 4 * z - 1 > 0, "feedback recurrence denominator")
            linear = 4 * z / (4 * z - 1)
            coefficient = 4 * z * z / (4 * z - 1)
            require(linear > 1 and coefficient == linear * z
                    and linear - linear * linear / (4 * coefficient) == 1,
                    "feedback root quadratic has exact minimum one")
            require(coefficient >= z >= previous,
                    "feedback recurrence dominates all smaller feedback sets")
            levels.append({"feedback_vertices": level, "coefficient": str(coefficient),
                           "linear_coefficient": str(linear), "z": str(z)})
        loss = gamma * coefficient * square_upper(cutoff)
        require(loss == expected_loss < target < 1, "bounded feedback-vertex exclusion")
        feedback_rows.append({
            "head": name, "tail_prime_minimum": cutoff, "Gamma_bound": str(gamma),
            "maximum_parent_factor": str(parent_factor),
            "feedback_vertices_per_component": depth, "levels": levels,
            "prime_square_upper": str(square_upper(cutoff)),
            "loss_upper": str(loss), "retained_lower": str(1 - loss)})
    finite_heads = finite_head_supported_laws()
    finite_gamma = {row["period_bound"]: F(row["Gamma_bound"]) for row in finite_heads}
    degeneracy_rows = []
    for name, cutoff, gamma, degree, threshold, target in [
            ("arbitrary_357_forest", 17, general_gamma, 1, F(11, 25), F(955226, 1000000)),
            ("arbitrary_357_degree2", 19, general_gamma, 2, F(41, 100), F(885762, 1000000)),
            ("arbitrary_357_planar", 23, general_gamma, 5, F(37, 100), F(945592, 1000000)),
            ("star_head_degree20", 79, F(177), 20, F(9, 25), F(990060, 1000000)),
            ("finite_315_head_planar", 17, finite_gamma[315], 5, F(7, 20), F(808363, 1000000)),
            ("finite_945_head_planar", 19, finite_gamma[945], 5, F(9, 25), F(732710, 1000000))]:
        require(0 < threshold <= F(1, 2), "capped-kernel threshold range")
        primes = [p for p in extended_primes if p >= cutoff][:degree + 1]
        require(len(primes) == degree + 1, "complete distinct-parent prefix")
        weights = [F(1, p - 1) for p in primes]
        factors = [1 + (3 * a + 2 * a * a) / (1 - threshold) for a in weights]
        require(all(factors[i] > factors[i + 1] > 1 for i in range(degree)),
                "parent factors strictly decrease along allowed primes")
        parent_product = prod(factors[:-1])
        square = square_upper(cutoff)
        first_squares = sum((a * a for a in weights[:-1]), F(0))
        correction = sum((a * a * (factors[-1] / factor - 1)
                          for a, factor in zip(weights[:-1], factors[:-1])), F(0))
        adjusted_square = square + correction
        positive_decomposition = (square - first_squares
                                  + sum((a * a * factors[-1] / factor
                                         for a, factor in zip(weights[:-1], factors[:-1])), F(0)))
        require(square > first_squares and correction < 0
                and adjusted_square == positive_decomposition > 0,
                "self-parent exclusion retains a positive completed vertex sum")
        denominator = 4 * threshold * (1 - threshold)
        loss = gamma * parent_product * adjusted_square / denominator
        uniform_loss = gamma * square * factors[0] ** degree / denominator
        require(loss < uniform_loss and loss < target < 1,
                "local-parent capped-kernel noncoverage criterion")
        degeneracy_rows.append({
            "head_and_graph": name, "tail_prime_minimum": cutoff,
            "Gamma_bound": str(gamma), "degeneracy": degree,
            "delta": str(threshold), "kernel_density_cap": str(1 / (1 - threshold)),
            "violation_denominator": str(denominator), "comparison_primes": primes,
            "parent_factors": [str(factor) for factor in factors],
            "distinct_parent_product": str(parent_product),
            "prime_square_upper": str(square), "self_parent_correction": str(correction),
            "adjusted_square_sum": str(adjusted_square),
            "uniform_parent_loss_upper": str(uniform_loss),
            "loss_upper": str(loss), "retained_lower": str(1 - loss)})
    leaf_moment_coefficient = general_gamma * (1 + 3 * (F(3, 36) + F(2, 36 ** 2)))
    require(leaf_moment_coefficient == F(511919, 10368) < degree_coefficient,
            "pendant-leaf coefficient is dominated by the degree-two core coefficient")
    pendant_loss = degree_coefficient * square_upper(37)
    require(pendant_loss < F(898149, 1000000) < 1, "pendant degree-two core exclusion")
    pendant_core = {"tail_prime_minimum": 37, "core_threshold": "2/3",
                    "core_coefficient": str(degree_coefficient),
                    "leaf_coefficient": str(leaf_moment_coefficient),
                    "prime_square_upper": str(square_upper(37)),
                    "loss_upper": str(pendant_loss), "retained_lower": str(1 - pendant_loss)}
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
    head_mass = head_mixed_mass_improvement()
    finite_945_tail17 = pure_head_unrestricted_stoploss(
        [(head, 17, 8192) for head in finite_heads if head["period_bound"] == 945])
    require(len(finite_945_tail17) == 1, "unique finite 945 head specialization")
    finite_adaptive_runs = {
        315: (
            (17, 4), (23, 6), (31, 8), (47, 12), (67, 16), (71, 18),
            (97, 24), (101, 27), (137, 32), (139, 36), (199, 48),
            (277, 64), (293, 72), (307, 80), (443, 96), (449, 108),
            (613, 128), (673, 144), (1021, 192),
        ),
        945: (
            (17, 4), (19, 6), (31, 8), (37, 12), (59, 16), (61, 18),
            (73, 24), (109, 32), (113, 36), (149, 48), (211, 64),
            (227, 72), (283, 96), (419, 128), (443, 144), (571, 192),
            (823, 256), (881, 288), (883, 320), (1129, 384), (1657, 512),
            (1789, 576), (2357, 768), (2371, 864), (3467, 1024),
            (3793, 1152), (3797, 1296), (5059, 1536), (5101, 1728),
            (7591, 2048), (8423, 2304), (8431, 2560), (11551, 3072),
            (11657, 3456), (11677, 3840), (17827, 4096), (20071, 4608),
            (20101, 5120), (20113, 5184), (28517, 6144), (28817, 6912),
            (28837, 7680), (32141, 8192),
        ),
    }
    finite_adaptive = {
        head['period_bound']: adaptive_head_stoploss(
            finite_head=head, threshold_runs=finite_adaptive_runs[head['period_bound']], first=13)
        for head in finite_heads
    }
    actual_sharpness = cm1_actual_head_sharpness()
    return {
        "general_357_head": general_head,
        "extended_prime_square": {"cutoff": 40000, "scale": extended_scale,
                                  "prime_count": len(extended_tail), "ceiling_sum": extended_ceiling,
                                  "odd_integer_tail": str(extended_odd_tail),
                                  "upper_bound": str(extended_square)},
        "star_forest": forest_rows, "pendant_degree_two_core": pendant_core,
        "arbitrary_forest": arbitrary_forest_rows,
        "feedback_vertex": feedback_rows,
        "finite_head_supported_laws": finite_heads,
        "local_parent_capped_kernel": degeneracy_rows,
        "rank_two_tail": rank_two_tail_bounds(),
        "rank_three_tail": rank_three_tail_bounds(),
        "finite_support_switch": finite_support_switch_bounds(),
        "unrestricted_star_stoploss": unrestricted_star_stoploss(),
        "pure_head_unrestricted_stoploss": pure_head_unrestricted_stoploss(),
        "finite_945_tail17_stoploss": finite_945_tail17[0],
        "finite_315_tail13_adaptive": finite_adaptive[315],
        "finite_945_tail13_adaptive": finite_adaptive[945],
        "head_mixed_mass_improvement": head_mass,
        "cm1_actual_head_sharpness": actual_sharpness,
        "finite_head_sharp_density": finite_head_sharp_density(actual_sharpness),
        "sharp_head_unmarked_comparison": sharp_head_unmarked_comparison(actual_sharpness),
        "adaptive_head_stoploss": adaptive_head_stoploss(head_mass),
        "homogeneous_comb_capacity": homogeneous_comb_capacity(),
        "comb_stoploss_dual_transport": comb_stoploss_dual_transport(),
        "local_kernel_crt_regression": local_kernel_crt_regression(),
        "binary_path_regression": binary_path_regression(),
        "unrestricted_energy_boundary": unrestricted_energy_boundary(),
        "forest_potential_identity": [
            {"b_exponent": exponent[0], "c_exponent": exponent[1],
             "coefficient": str(coefficient)}
            for exponent, coefficient in sorted(potential_left.items())],
        "star_head_hubs": star_hubs,
        "general_357_head_hubs": general_hubs,
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
                        default=(Path(__file__).resolve().parent / 'certificates/star_block_obstruction_certificate.json'))
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    data = certificate()
    if args.write_certificate:
        write_certificate_text(args.certificate, json.dumps(data, indent=2) + "\n", encoding="utf-8")
    else:
        require(json.loads(read_artifact_text(args.certificate, encoding="utf-8")) == data,
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
                      "star_forest_loss_bounds": {row["head"]: row["loss_upper"] for row in data["star_forest"]},
                      "arbitrary_forest_loss_bounds": {row["head"]: row["loss_upper"] for row in data["arbitrary_forest"]},
                      "feedback_vertex_loss_bounds": {row["head"]: row["loss_upper"] for row in data["feedback_vertex"]},
                      "local_parent_capped_kernel_loss_bounds": {row["head_and_graph"]: row["loss_upper"] for row in data["local_parent_capped_kernel"]},
                      "rank_two_tail_loss_bounds": {row["head"]: row["loss_upper"] for row in data["rank_two_tail"]["rows"]},
                      "coupled_mixed_head_mass_upper": data["head_mixed_mass_improvement"]["mixed_head_mass_upper"],
                      "adaptive_tail19_supported_Gamma_upper": data["adaptive_head_stoploss"]["supported_Gamma_upper"],
                      "adaptive_tail19_stopping_lower": data["adaptive_head_stoploss"]["stopping_lower"],
                      "finite_945_tail17_supported_Gamma_upper": data["finite_945_tail17_stoploss"]["supported_Gamma_upper"],
                      "finite_945_tail17_stopping_lower": data["finite_945_tail17_stoploss"]["stopping_lower"],
                      "finite_tail13_adaptive_Gamma_bounds": {
                          q: data[f"finite_{q}_tail13_adaptive"]["supported_Gamma_upper"]
                          for q in (315, 945)},
                      "finite_tail13_adaptive_stopping_lower": {
                          q: data[f"finite_{q}_tail13_adaptive"]["stopping_lower"]
                          for q in (315, 945)},
                      "comb_flow_comparisons": data["homogeneous_comb_capacity"]["flow_comparisons"],
                      "pure_head_unrestricted_Gamma_bounds": {row["head"]: row["supported_Gamma_upper"] for row in data["pure_head_unrestricted_stoploss"]},
                      "unrestricted_star_supported_Gamma_upper": data["unrestricted_star_stoploss"]["supported_Gamma_upper"],
                      "unrestricted_star_stopping_lower": data["unrestricted_star_stoploss"]["stopping_lower"],
                      "finite_support_switch_seed_bounds": {row["head"]: row["strict_seed_ceiling"] for row in data["finite_support_switch"]["rows"]},
                      "rank_three_tail_loss_bounds": {row["head"]: row["loss_upper"] for row in data["rank_three_tail"]["rows"]},
                      "finite_head_supported_Gamma_bounds": {row["period_bound"]: row["Gamma_bound"] for row in data["finite_head_supported_laws"]},
                      "local_kernel_crt_regression_cases": data["local_kernel_crt_regression"]["cases"],
                      "binary_path_regression_cases": data["binary_path_regression"]["cases"],
                      "pendant_degree_two_core_loss": data["pendant_degree_two_core"]["loss_upper"],
                      "star_vertex_cover_8_loss": data["star_head_hubs"]["vertex_cover_loss_upper"],
                      "general_vertex_cover_6_loss": data["general_357_head_hubs"]["vertex_cover_loss_upper"],
                      "scope": "Exact constants; arbitrary-height lifting is an ordinary proof."}))


if __name__ == "__main__":
    main()
