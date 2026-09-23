#!/usr/bin/env python3
"""Consume retained bounds for one seven-core law and its large-prime tail.

The common charged-process mass proof and the analytic tail estimate are
ordinary mathematical inputs. This program checks their finite constants,
not those proofs. It imports no producer, reruns no geometry or old query
rows, and invokes no Lean checker. All checks remain active with -O.
"""

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path


PREFIX_SHA = "44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d"
RANDOMIZED_SHA = "35bb2ad24786cc125f188c59a073e6df23e42433eb8195f01fd3b21b16c28938"


def need(ok, why):
    if not ok:
        raise ValueError(why)


def read_pinned(path, expected, label):
    raw = path.read_bytes()
    need(sha256(raw).hexdigest() == expected, label + " data SHA256")
    return json.loads(raw)


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--randomized", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    prefix = read_pinned(args.prefix, PREFIX_SHA, "ordinary prefix")
    randomized = read_pinned(args.randomized, RANDOMIZED_SHA, "randomized completion")

    rows = [row for row in prefix["summaries"] if row["core_count"] == 7]
    need(len(rows) == 1, "unique retained seven-core summary")
    row = rows[0]
    m7 = Q(row["submeasure_live_mass_lower"])
    need(m7 == Q(7235955529, 450000000000) and m7 > Q(2, 125),
         "retained ordinary seven-core mass")
    need(prefix["basic_vertices"] == 32, "retained basic-domain size")
    need(prefix["retained_deletion_thresholds"] == [2, 4, 4, 8, 8, 12],
         "retained ordinary threshold schedule")
    caps = (Q(3, 2), Q(5, 3), Q(3, 2), Q(2), Q(9, 5))
    unnormalized_cap = prod(caps)
    need(unnormalized_cap == Q(27, 2), "joint cap through prime19")
    cap = unnormalized_cap / m7
    need(cap == Q(row["normalized_Haar_density_cap"])
         == Q(6075000000000, 7235955529), "mass-normalized common-law cap")
    rounded_cap = Q(840)
    need(cap < rounded_cap, "strict cap simplification")

    A = Q(randomized["query_R_upper"])
    lower = Q(randomized["rounded_lower_density"])
    mass_upper = Q(randomized["total_mass_upper"])
    support_lower = Q(randomized["unnormalized_density_lower_on_original_survivors"])
    need(A == Q(70871, 3375) < 21, "retained simultaneous query bound")
    need(lower == Q(1, 5) and mass_upper == Q(3, 8),
         "retained full-support lower density and mass upper")
    need(support_lower / mass_upper
         == Q(randomized["normalized_density_lower_on_original_survivors"])
         > lower, "same averaging lower-density calculation")
    need(m7 > Q(randomized["total_mass_lower"]), "stronger mass on the same process")
    need(cap < Q(randomized["normalized_density_upper"]), "strict cap improvement")

    # Report463's actual two-prime product/deletion inequality, using the
    # conservative query bound. The d=1 mixed cofactor contributes +1.
    coarse_A = Q(21)
    q, r = 43, 47
    N = (q - coarse_A - 2) * (r - coarse_A - 2) - (coarse_A**2 + coarse_A + 1)
    extension_mass = 1 - coarse_A / (q - 2) - coarse_A / (r - 2) \
        - (coarse_A + 1) / ((q - 2) * (r - 2))
    need(N == 17 and extension_mass == N / ((q - 2) * (r - 2))
         == Q(17, 1845), "two-prime common-product live mass")
    pure_density = Q(q - 1, q - 2) * Q(r - 1, r - 2)
    exact_head = extension_mass / (cap * pure_density)
    rounded_head = extension_mass / (rounded_cap * pure_density)
    simple_head = Q(1, 100000)
    need(exact_head == N / (cap * (q - 1) * (r - 1)), "exact Haar conversion")
    need(rounded_head == Q(17, 1622880), "rounded-cap Haar reserve")
    need(exact_head > rounded_head > simple_head, "strict head reserve simplification")

    head_primes = (3, 5, 7, 11, 13, 17, 19, 43, 47)
    M2 = prod(Q(p * (p + 1), (p - 1)**2) for p in head_primes)
    need(M2 == Q(1026827659, 43877376), "reference-head second-moment product")
    B, ell = 5000000, 14
    need(B >= 286 and ell >= 4 and 3**ell <= B,
         "Chapter33 analytic-tail numerical applicability")
    c = Q(2 * ell**2 + 1, 2 * ell**2 - 1)
    need(c == Q(393, 391), "prime-product constant")
    terms = [Q(factorial(7), factorial(7 - j) * ell**j) for j in range(8)]
    series = sum(terms, Q(0))
    tau = c**7 / B * Q(B, B - 3)**2 * series
    loss = M2 * tau
    margins = {"exact_cap": exact_head - loss,
               "rounded_cap": rounded_head - loss,
               "simple_head": simple_head - loss}
    simple_margin = Q(1, 1000000)
    need(margins["exact_cap"] > margins["rounded_cap"]
         > margins["simple_head"] > simple_margin,
         "strict positive distorted-tail mass above one millionth")

    result = {
        "scope": "Exact constants from retained data. The same charged-law mass transfer, shared query law, full-support averaging, prime transport and Chapter33 analytic tail are ordinary proof inputs, not conclusions of this arithmetic consumer. No new Lean certification or unrestricted Erdos7 conclusion.",
        "inputs": {"query_stoploss_completion.json": PREFIX_SHA,
                   "randomized_completion_support.json": RANDOMIZED_SHA},
        "ordinary_proof_inputs": {
            "mass": "Chapter31 SV16-SV24 and report461's retained 32-vertex prefix bound",
            "same_charged_process": "Chapter30's retained charged7 ordinary domination and report467's mass-transfer proof",
            "query_and_full_support": "Report466's common-law query estimate and randomized completion averaging",
            "two_prime_extension": "Report463 PE8-PE10, including the old unit cofactor",
            "tail": "Chapter33 SH11-SH13, including its inherited analytic prime-product premise"},
        "source_producer_rerun": False,
        "geometry_enumeration_rerun": False,
        "old_query_rows_recomputed": False,
        "common_seven_core_law": {
            "unnormalized_mass_lower": m7,
            "unnormalized_mass_upper": mass_upper,
            "conditional_caps": caps,
            "unnormalized_joint_density_cap": unnormalized_cap,
            "normalized_joint_density_cap": cap,
            "rounded_strict_density_cap": rounded_cap,
            "cap_gap": rounded_cap - cap,
            "query_R_upper": A,
            "coarse_query_R_upper": coarse_A,
            "density_lower_on_full_original_survivor_set": lower,
            "scope": "One law, one fixed finite original family and resolved core period; the separate compactness argument gives a compatible all-depth law."},
        "nine_core_head": {
            "reference_new_primes": [q, r],
            "coarse_extension_numerator": N,
            "unnormalized_product_live_mass_lower": extension_mass,
            "pure_product_density_cap": pure_density,
            "haar_lower_with_exact_cap": exact_head,
            "haar_lower_with_rounded_cap": rounded_head,
            "simple_strict_haar_lower": simple_head},
        "tail": {
            "reference_head_primes": head_primes,
            "M2": M2, "B": B, "ell": ell, "3_power_ell": 3**ell, "c": c,
            "tau7_series_terms": terms, "tau7_series": series, "tau7": tau,
            "tail_loss_upper": loss,
            "remaining_live_mass_lower": margins,
            "simple_strict_remaining_live_mass_lower": simple_margin,
            "scope": "Remaining unnormalized distorted-law mass, not a Haar-density lower bound."},
        "noncoverage_scope": {
            "distinct_odd_numerical_moduli_greater_than_one": True,
            "maximum_support_primes_below43": 7,
            "maximum_support_primes_at_most5000000": 9,
            "larger_prime_count": "unrestricted finite",
            "original_phases_and_finite_heights": "unrestricted",
            "shared_large_primes_per_modulus": "unrestricted",
            "unrestricted_erdos7_resolved": False}}
    output = json.dumps(encode(result), indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
        print("PASS: two pinned data summaries, common-law constants, nine-core reserve, and exact five-million tail margin.")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
