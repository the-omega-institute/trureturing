#!/usr/bin/env python3
"""Exact finite prefix potential and coherent two-prime consumer constants."""
import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    primes = (3, 5, 7, 11, 13, 17, 19)
    heights = (4, 1, 1, 1, 1, 1, 1)
    fine_heights = tuple(h + 1 for h in heights)
    period = prod(p ** h for p, h in zip(primes, heights))
    profiles = list(product(*(range(h + 1) for h in heights)))
    fine_labels = list(product(*(range(h + 1) for h in fine_heights)))
    require(len(profiles) == 320, "Coarse profile count")
    require(len(fine_labels) == 4374, "Fine label count")

    grouped_weights = {g: F() for g in profiles}
    for exponents in fine_labels:
        coarse = tuple(min(e, h) for e, h in zip(exponents, heights))
        weight = prod(F(1, p ** (e - g))
                      for p, e, g in zip(primes, exponents, coarse))
        grouped_weights[coarse] += weight
    for g, weight in grouped_weights.items():
        expected = prod(1 + F(1, p) if a == h else F(1)
                        for p, a, h in zip(primes, g, heights))
        require(weight == expected, "Grouped fine-label weight")

    values = []
    for v in profiles:
        load = prod(a + 1 for a in v)
        potential = prod(F(a + 1) + (F(1, p) if a == h else F())
                         for p, a, h in zip(primes, v, heights))
        expanded = sum((weight for g, weight in grouped_weights.items()
                        if all(a <= b for a, b in zip(g, v))), F())
        require(potential == expanded, "Prefix potential expansion")
        values.append((v, load, potential))

    high = [(v, q, psi) for v, q, psi in values if q >= 20]
    low = [(v, q, psi) for v, q, psi in values if q < 20]
    lower = min(psi for _, _, psi in high)
    minimizers = [v for v, _, psi in high if psi == lower]
    spectrum = sorted({q for _, q, _ in values})
    largest_low_load = max(q for _, q, _ in low)
    require(len(high) == 170, "High profile count")
    require(lower == F(7280, 323), "High potential minimum")
    require(minimizers == [(4, 0, 0, 0, 0, 1, 1)], "Minimum profile")
    require(largest_low_load == 16, "Low load spectrum")
    require(not any(q in spectrum for q in (17, 18, 19)), "Missing spectrum values")

    cases = []
    for three_depth in range(5):
        for other_zero_count in range(7):
            rows = [(v, q, psi) for v, q, psi in values
                    if v[0] == three_depth and sum(v[1:]) == other_zero_count]
            require(rows, "Missing depth/count case")
            case_minimum = min(psi for _, _, psi in rows)
            loads = {q for _, q, _ in rows}
            require(len(loads) == 1, "Case load is not constant")
            load = next(iter(loads))
            cases.append({
                "three_depth": three_depth,
                "other_zero_count": other_zero_count,
                "profiles": len(rows), "coherent_load": load,
                "high_load": load >= 20,
                "minimum_potential": str(case_minimum),
                "minimum_profiles": [v for v, _, psi in rows if psi == case_minimum],
            })

    r_bound = F(70871, 3375)
    density_cap = F(6075000000000, 7235955529)
    nonunit_lower = lower - 1
    escape_mass = 1 - r_bound / nonunit_lower
    require(nonunit_lower == F(6957, 323), "High nonunit lower bound")
    require(escape_mass == F(588542, 23479875) > 0, "Escape probability")

    q, r = 23, 29
    active_cofactor_bound = largest_low_load
    q_good = 1 - F(active_cofactor_bound, q - 1)
    r_good = 1 - F(active_cofactor_bound, r - 1)
    mixed_bad = F(active_cofactor_bound, (q - 1) * (r - 1))
    fibre_survival = q_good * r_good - mixed_bad
    haar_survival = escape_mass * fibre_survival / density_cap
    require(q_good == F(3, 11) and r_good == F(3, 7), "Single-axis reserve")
    require(mixed_bad == F(2, 77), "Mixed-label inventory")
    require(fibre_survival == F(1, 11), "Two-prime fibre reserve")
    require(haar_survival == F(193575624497669, 71320120312500000000),
            "Full Haar survival bound")

    result = {
        "result": "PASS", "primes": primes, "coarse_heights": heights,
        "fine_heights": fine_heights, "coarse_period": period,
        "fine_period": prod(p ** h for p, h in zip(primes, fine_heights)),
        "coarse_profiles_checked": len(profiles),
        "fine_divisor_labels_grouped": len(fine_labels),
        "grouped_weight_checks": len(grouped_weights),
        "potential_expansion_checks": len(values),
        "coherent_load_formula": "Q(v)=product_p(v_p+1)",
        "potential_formula": "Psi(v)=product_p(v_p+1+1/p if v_p=H_p else v_p+1)",
        "load_spectrum": spectrum,
        "high_load_threshold": 20, "high_load_profiles": len(high),
        "minimum_high_potential": str(lower), "minimum_profiles": minimizers,
        "largest_load_below_threshold": largest_low_load,
        "cases_by_three_depth_and_other_zero_count": cases,
        "source_measure_escape": {
            "prime_scope": "Original old-only family supported on a subset of "
                           "3,5,7,11,13,17,19, with arbitrary finite heights and phases",
            "period_scope": "One common finite period resolving every old-only original "
                            "class and the displayed fine query heights",
            "R_upper": str(r_bound), "density_upper": str(density_cap),
            "high_support_R_lower": str(nonunit_lower),
            "same_law_inequality": "R(mu)>=integral(Psi-1)dmu>=(c-1)*mu(Q>=20)",
            "mu_Q_at_most_16_lower": str(escape_mass),
        },
        "coherent_two_prime_consumer": {
            "new_primes": [q, r],
            "hypotheses": "All original numerical moduli are distinct and greater than "
                          "one, supported on the nine displayed primes. Every class "
                          "touching 23 or 29 has old cofactor d dividing coarse K and "
                          "old phase a mod d for one common a. New-coordinate heights "
                          "and phases are arbitrary finite. Old-only heights and phases "
                          "are unrestricted. The source mu avoids the old-only family.",
            "active_old_cofactors_including_unit_upper": active_cofactor_bound,
            "q_only_good_Haar_lower": str(q_good),
            "r_only_good_Haar_lower": str(r_good),
            "cross_bad_Haar_upper": str(mixed_bad),
            "same_old_point_fibre_survival_lower": str(fibre_survival),
            "mu_times_new_Haar_survival_lower": str(escape_mass * fibre_survival),
            "full_Haar_survival_lower": str(haar_survival),
            "scope": "The common old phase and bounded old cofactors are required; "
                     "this does not prove unrestricted nine-prime noncoverage.",
        },
        "verification_scope": "Finite exact profile and label counts, potential "
                            "expansions, spectrum and rational consumer constants. "
                            "The general prefix-partition and same-law source "
                            "arguments are mathematical premises supplied by report472; "
                            "this program does not enumerate original families or "
                            "reverify the source theorem. No Lean certification.",
    }
    encoded = json.dumps(result, indent=2) + "\n"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON result path")
    args = parser.parse_args()
    if args.output:
        args.output.write_text(encoded)
        print(json.dumps({"result": "PASS", "output": str(args.output),
                          "profiles": len(profiles), "fine_labels": len(fine_labels),
                          "minimum_high_potential": str(lower),
                          "fibre_survival_lower": str(fibre_survival)}))
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
