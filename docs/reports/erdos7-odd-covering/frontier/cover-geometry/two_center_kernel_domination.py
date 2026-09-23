#!/usr/bin/env python3
"""Exact all-depth comparison masses for the two-center 23/29 theorem.

GOOD has a finite valuation description; BAD is its exact complement.
The conditional-kernel domination and original-family bridge are ordinary
proof inputs in report476, not conclusions of this arithmetic program.
"""

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path


SOURCE_SHA = "3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4"
PRIMES = (5, 7, 11, 13, 17, 19)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def profiles(bound, dimension):
    """Every nonnegative tuple with product(v_i+1)<=bound, exactly once."""
    if dimension == 0:
        yield ()
        return
    for value in range(bound):
        for tail in profiles(bound // (value + 1), dimension - 1):
            yield (value,) + tail


def probability(p, cap, valuation):
    # P(J>=e)=cap/p^e for every e>=1; cap=1 is the Haar law.
    return 1 - cap / p if valuation == 0 else cap * (p - 1) / p**(valuation + 1)


def numerator(qa, qb):
    return max(22 - qa, 0) * max(28 - qb, 0) - qa


def ternary_states(product_value):
    # Root labels 0 and 1 mean the two centers, not absolute integer phases.
    # Each center-root depth v>=1 has unnormalized Haar mass 2/3^(v+1).
    for depth in range(1, 27):
        yield 0, depth, (depth + 1) * product_value, product_value, Q(2, 3**(depth + 1))
        yield 1, depth, product_value, (depth + 1) * product_value, Q(2, 3**(depth + 1))
    yield 2, 0, product_value, product_value, Q(1, 3)


def product_distribution(primes, caps):
    """Independent convolution by scalar product, without valuation tuples."""
    distribution = {1: Q(1)}
    for p, cap in zip(primes, caps):
        next_distribution = {}
        for current, weight in distribution.items():
            for factor in range(1, 19 // current + 1):
                value = current * factor
                next_distribution[value] = next_distribution.get(value, Q()) + weight * probability(p, cap, factor - 1)
        distribution = next_distribution
    return distribution


def convolution_good(distribution):
    masses = [Q(), Q(), Q()]
    floor = None
    for value, weight in distribution.items():
        for root, _, qa, qb, root_mass in ternary_states(value):
            n = numerator(qa, qb)
            if n > 0:
                masses[root] += weight * root_mass
                floor = n if floor is None else min(floor, n)
    return masses, floor


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).with_name("common_law_mass_tail.json"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.source.read_bytes()
    need(sha256(raw).hexdigest() == SOURCE_SHA, "retained source data identity")
    source = json.loads(raw)["common_seven_core_law"]
    mass_lower = Q(source["unnormalized_mass_lower"])
    density_cap = Q(source["unnormalized_joint_density_cap"])
    caps = (Q(1),) + tuple(Q(value) for value in source["conditional_caps"])
    need(len(caps) == len(PRIMES) and all(1 <= cap < p for p, cap in zip(PRIMES, caps)), "comparison laws are probabilities")
    need(prod(caps) == density_cap == Q(27, 2), "same-process density cap")
    need(mass_lower == Q(7235955529, 450000000000), "same-process lower mass")

    # Completeness: C>=20 implies F<=2*8-20<0. On root0,
    # v3>=21 implies Qa>=22; on root1, v3>=27 implies Qb>=28.
    need(numerator(20, 20) < 0, "large product is bad")
    need(all(numerator(22 * value, value) <= 0 and numerator(value, 28 * value) <= 0
             for value in range(1, 20)), "large ternary depth is bad")
    good = [Q(), Q(), Q()]
    good_v5_zero = [Q(), Q(), Q()]
    counts = [0, 0, 0]
    zero_counts = [0, 0, 0]
    floors = [None, None, None]
    floor_pairs = [set(), set(), set()]
    max_depth = [0, 0, 0]
    for rest in profiles(19, len(PRIMES)):
        value = prod(v + 1 for v in rest)
        weight = prod(probability(p, cap, v) for p, cap, v in zip(PRIMES, caps, rest))
        for root, depth, qa, qb, root_mass in ternary_states(value):
            n = numerator(qa, qb)
            if n <= 0:
                continue
            good[root] += root_mass * weight
            counts[root] += 1
            max_depth[root] = max(max_depth[root], depth)
            if rest[0] == 0:
                # Condition only at5; root3 retains its absolute mass1/3.
                good_v5_zero[root] += root_mass * weight / Q(4, 5)
                zero_counts[root] += 1
            if floors[root] is None or n < floors[root]:
                floors[root] = n
                floor_pairs[root] = set()
            if n == floors[root]:
                floor_pairs[root].add((qa, qb))

    independent, independent_floor = convolution_good(product_distribution(PRIMES, caps))
    independent_zero, _ = convolution_good(product_distribution(PRIMES[1:], caps[1:]))
    need(independent == good and independent_zero == good_v5_zero, "tuple sum and scalar convolution agree exactly")
    need(counts == [403, 723, 669] and sum(zero_counts[:2]) == 816, "complete GOOD profile counts")
    need(floors == [4, 4, 8] and independent_floor == 4, "all-root positive fibre floor")

    bad = [Q(1, 3) - value for value in good]
    bad_zero = [Q(1, 3) - value for value in good_v5_zero]
    need(all(Q() <= b <= Q(1, 3) and Q() <= z <= b for b, z in zip(bad, bad_zero)), "bad comparison masses")
    cases = []
    for excluded in range(3):
        remaining = [root for root in range(3) if root != excluded]
        rho_bad = sum((bad[root] for root in remaining), Q())
        beta_zero = sum((bad_zero[root] for root in remaining), Q())
        upper = rho_bad - beta_zero / 5
        cases.append({"excluded_root": excluded, "rho_bad": rho_bad,
                      "beta_v5_zero": beta_zero, "removed_bad_lower": beta_zero / 5,
                      "bad_upper": upper, "bad_upper_decimal": float(upper)})
    need(cases[2]["bad_upper"] >= max(case["bad_upper"] for case in cases), "third forbidden root is worst")
    upper = cases[2]["bad_upper"]
    delta = mass_lower - upper
    need(delta > Q(1, 5000), "strict positive mass margin")
    fibre_floor = Q(independent_floor, 22 * 28)
    haar_lower = delta * fibre_floor / density_cap
    need(fibre_floor == Q(1, 154) and haar_lower == delta / 2079, "original-fibre Haar conversion")
    need(haar_lower > Q(1, 10395000), "strict full-family Haar floor")

    # Chapter33 SH11--SH13: explicitly switch to Haar restricted to the
    # actual nine-prime survivors, with density1 and this positive mass.
    head_primes = (3,) + PRIMES + (23, 29)
    second_moment = prod(Q(p * (p + 1), (p - 1)**2) for p in head_primes)
    need(second_moment == Q(14003665, 540672), "nine-prime Haar second moment")
    cutoff, ell = 500000000, 18
    need(cutoff >= 286 and ell >= 4 and 3**ell <= cutoff, "analytic-tail applicability")
    c = Q(2 * ell**2 + 1, 2 * ell**2 - 1)
    series = sum((Q(factorial(7), factorial(7 - j) * ell**j) for j in range(8)), Q())
    tau = c**7 / cutoff * Q(cutoff, cutoff - 3)**2 * series
    tail_loss = second_moment * tau
    tail_margin = Q(1, 10395000) - tail_loss
    need(tail_margin > Q(1, 75000000), "strict unrestricted-large-prime-tail margin")

    result = {
        "scope": "Exact comparison arithmetic for report476. Conditional reverse integration, completion, source mass and original-fibre transfer are ordinary mathematical inputs; no Lean certification or unrestricted Erdos7 settlement.",
        "inputs": {"common_law_mass_tail.json": SOURCE_SHA},
        "source_producer_rerun": False,
        "reference_primes": [3] + list(PRIMES),
        "later_conditional_caps": caps[1:],
        "source_mass_lower": mass_lower,
        "source_joint_density_cap": density_cap,
        "finite_complement": {
            "maximum_good_other_product": 19,
            "maximum_good_ternary_depth_by_root": max_depth,
            "good_profile_counts_by_root": counts,
            "good_profile_counts_with_v5_zero_by_root": zero_counts,
            "minimum_positive_fibre_numerators_by_root": floors,
            "minimum_pairs_by_root": [sorted(pairs) for pairs in floor_pairs],
            "good_mass_by_root": good,
            "good_mass_conditioned_only_on_v5_zero_by_root": good_v5_zero,
            "independent_scalar_convolution_agrees": True,
            "scope": "No tail truncation: every omitted profile is BAD; root2 is one full ternary root with Qa=Qb=C."},
        "forbidden_ternary_root_cases": cases,
        "worst_bad_upper": upper,
        "worst_bad_upper_decimal": float(upper),
        "positive_mass_margin": delta,
        "positive_mass_margin_decimal": float(delta),
        "simple_strict_mass_margin": Q(1, 5000),
        "good_fibre_haar_floor": fibre_floor,
        "full_survivor_haar_lower": haar_lower,
        "full_survivor_haar_lower_decimal": float(haar_lower),
        "simple_strict_full_survivor_haar_lower": Q(1, 10395000),
        "large_prime_tail": {
            "head_primes": head_primes,
            "seed": "Haar restricted to the actual original head survivors; joint density at most1",
            "seed_mass_strict_lower": Q(1, 10395000),
            "second_moment": second_moment,
            "cutoff": cutoff, "ell": ell, "three_power_ell": 3**ell,
            "prime_product_constant": c, "series": series, "tau7": tau,
            "tail_loss_upper": tail_loss, "tail_loss_upper_decimal": float(tail_loss),
            "remaining_mass_strict_lower": tail_margin,
            "remaining_mass_strict_lower_decimal": float(tail_margin),
            "simple_strict_remaining_mass_lower": Q(1, 75000000),
            "scope": "Chapter33 SH11--SH13 and its analytic prime-product premise are ordinary inputs. Final mass is a distorted-law mass, not a Haar reserve. Tail classes have arbitrary original phases, heights and shared outside primes."},
        "noncoverage_scope": {
            "old_support": [3, 5, 7, 11, 13, 17, 19],
            "new_support": [23, 29],
            "distinct_odd_numerical_moduli_greater_than_one": True,
            "old_only_phases": "arbitrary",
            "old_centers": "a and b differ modulo3 and share all required nonternary old prefixes",
            "later_old_phases": "23-only and cross at a; 29-only at b",
            "finite_heights_and_new_coordinate_phases": "arbitrary",
            "unrestricted_erdos7_resolved": False}}
    output = json.dumps(encode(result), indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
        print("PASS: complete GOOD complement, independent convolution, all forbidden-root choices, two-center Haar reserve, and large-prime tail margin.")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
