#!/usr/bin/env python3
"""Exact FC6 comparisons for common finite-height profiles and infinite inventories.

Standard library only.  Prints the complete JSON result to stdout by default;
--output PATH writes it instead.  These are comparison lower bounds, not actual
survivor masses.  A negative value does not exhibit a covering system.
"""

import argparse
from fractions import Fraction
import json
from math import prod
from pathlib import Path


ODD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)


def compare(primes, heights=None):
    """Minimize FC6 over every complementary partition pair of Q=primes-{3}."""
    qs = primes[1:]
    if not primes or primes[0] != 3 or not qs or len(set(primes)) != len(primes):
        raise ValueError("Distinct support primes beginning with 3 required")
    if heights is None:
        inventory_numerators = (1,) * len(qs)
        inventory_denominators = tuple(q - 2 for q in qs)
        caps = tuple(Fraction(q - 1, q - 2) for q in qs)
    else:
        if len(heights) != len(qs) or any(h < 1 for h in heights):
            raise ValueError("One positive common height cap per nonternary prime required")
        inventory_numerators = tuple(q ** h - 1 for q, h in zip(qs, heights))
        inventory_denominators = tuple((q - 2) * q ** h + 1
                                       for q, h in zip(qs, heights))
        caps = tuple(Fraction((q - 1) * q ** h, denominator)
                     for q, h, denominator in zip(qs, heights, inventory_denominators))
    budgets = tuple(Fraction(a, d) for a, d in
                    zip(inventory_numerators, inventory_denominators))
    if not all(0 < b < 1 for b in budgets):
        raise ValueError("Coordinate budgets must lie in (0,1)")
    n = len(qs)
    full = (1 << n) - 1
    bitindex = {1 << i: i for i in range(n)}
    steps = [(subset, subset & (subset - 1), bitindex[subset & -subset])
             for subset in range(1, full + 1)]
    inventories = [1] * (full + 1)
    for subset, previous, index in steps:
        inventories[subset] = inventories[previous] * inventory_numerators[index]
    denominator = 2 * prod(inventory_denominators)
    rows = []
    for mask in range(1, full + 1, 2):
        left = [1] * (full + 1)
        right = [1] * (full + 1)
        for subset, previous, index in steps:
            in_left = bool(mask & (1 << index))
            a, d = inventory_numerators[index], inventory_denominators[index]
            left[subset] = left[previous] * (d - a if in_left else d)
            right[subset] = right[previous] * (d if in_left else d - a)
        value = left[full] + right[full]
        for removed in range(1, full + 1):
            if removed.bit_count() < 2:
                continue
            retained = full ^ removed
            value -= inventories[removed] * (
                left[retained] + right[retained] + max(left[retained], right[retained]))
        rows.append({"mask": mask, "numerator": value})
    minimum = min(row["numerator"] for row in rows)
    minimizers = [row["mask"] for row in rows if row["numerator"] == minimum]
    return {
        "support_primes": primes,
        "height_caps_nonternary": heights,
        "source_caps": list(map(str, caps)),
        "coordinate_budgets": list(map(str, budgets)),
        "inventory_numerators": inventory_numerators,
        "inventory_denominators": inventory_denominators,
        "partition_count": len(rows),
        "all_partition_count_including_complements": 2 * len(rows),
        "common_denominator": denominator,
        "minimum_numerator": minimum,
        "minimum_comparison": str(Fraction(minimum, denominator)),
        "minimum_comparison_decimal": float(Fraction(minimum, denominator)),
        "minimizing_masks": minimizers,
        "minimizing_partitions_containing_5": [
            [qs[i] for i in range(n) if mask & (1 << i)] for mask in minimizers],
        "partition_numerators": rows,
    }


def reweighting_certificate(profile):
    """Certify the global real-weight maximum at the first two-prime breakpoint.

    At A={5}, the indicated tie support is D={5,7}.  Concavity and the
    two exact one-sided derivatives certify the entire interval [0,1];
    no floating-point optimizer or grid argument is used.
    """
    qs = profile["support_primes"][1:]
    bs = tuple(Fraction(b) for b in profile["coordinate_budgets"])
    if qs[:2] != (5, 7):
        raise ValueError("Expected first nonternary primes 5,7")

    def fibres(removed):
        left = Fraction(1) if removed & 1 else 1 - bs[0]
        right = prod((1 - bs[i] for i in range(1, len(qs))
                      if not removed & (1 << i)), start=Fraction(1))
        return left, right

    tie_mask = 3
    a, b = fibres(tie_mask)
    weight = b / (a + b)
    a0, b0 = fibres(0)
    value = weight * a0 + (1 - weight) * b0
    left_derivative = right_derivative = a0 - b0
    ties = []
    term_count = 0
    for removed in range(1 << len(qs)):
        if removed.bit_count() < 2:
            continue
        term_count += 1
        bD = prod((bs[i] for i in range(len(qs)) if removed & (1 << i)),
                  start=Fraction(1))
        a, b = fibres(removed)
        first, second = weight * a, (1 - weight) * b
        value -= bD * (first + second + max(first, second))
        if first > second:
            slope_left = slope_right = a
        elif first < second:
            slope_left = slope_right = -b
        else:
            slope_left, slope_right = -b, a
            ties.append([qs[i] for i in range(len(qs)) if removed & (1 << i)])
        left_derivative -= bD * (a - b + slope_left)
        right_derivative -= bD * (a - b + slope_right)
    if not 0 < weight < 1 or not left_derivative > 0 or not right_derivative < 0:
        raise ValueError("Strict global concave-maximum slope certificate failed")
    if not value < -Fraction(7, 1000):
        raise ValueError("Claimed negative reweighting margin failed")
    return {
        "partition": [5],
        "weight_on_first_retained_root": str(weight),
        "weight_decimal": float(weight),
        "maximum_comparison": str(value),
        "maximum_comparison_decimal": float(value),
        "left_derivative": str(left_derivative),
        "right_derivative": str(right_derivative),
        "tied_deletion_supports": ties,
        "deletion_support_count": term_count,
        "strict_upper_bound": "-7/1000",
        "margin_below_strict_upper_bound": str(-Fraction(7, 1000) - value),
        "certificate": "Concavity on [0,1], positive left derivative and negative right derivative at the stated interior weight.",
        "limitation": "One relaxed partition point only; no attainability by an actual original family is claimed.",
    }


def result():
    calibration = compare(ODD_PRIMES[:8])
    if calibration["minimum_comparison"] != "2142533/15904350":
        raise ValueError("Existing FC16 calibration failed")
    cases = []
    for size in (11, 12):
        primes = ODD_PRIMES[:size]
        heights = tuple(min(5 if q <= 7 else 4, 2 + (5 * size - 9) // (q - 2))
                        for q in primes[1:])
        cases.append({"support_size": size, "arbitrary_height": compare(primes),
                      "bounded_height": compare(primes, heights)})
    return {
        "scope": "Exact FC6 comparison under one shared exponent profile; ordinary arithmetic, not Lean verification.",
        "limitation": "Negative comparison values do not imply an actual cover or an upper bound on survivor mass.",
        "finite_source_cap": "c(q,H)=(q-1)*q^H/((q-2)*q^H+1)",
        "finite_inventory": "b(q,H)=(q^H-1)/((q-2)*q^H+1)",
        "partition_mask_order": "Nonternary primes in ascending order; only masks containing 5, by complement symmetry.",
        "calibration": calibration,
        "cases": cases,
        "eleven_prime_reweighting": reweighting_certificate(cases[0]["bounded_height"]),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write JSON here instead of stdout")
    args = parser.parse_args()
    payload = json.dumps(result(), indent=2) + "\n"
    if args.output is None:
        print(payload, end="")
    else:
        args.output.write_text(payload)


if __name__ == "__main__":
    main()
