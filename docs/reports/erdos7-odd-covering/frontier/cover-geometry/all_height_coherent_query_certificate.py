#!/usr/bin/env python3
"""Verify a finite rational query certificate for arbitrary coherent heights.

Only the final rational weights are inputs. No optimization package, original
source producer, or complete CRT-period enumeration is used.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import lcm, prod
from pathlib import Path


PRIMES = (3, 5, 7, 11, 13, 17, 19)
COARSE_HEIGHT = 19
EXTRA_DIGITS = 2
TARGET = Fraction(221, 10)
SOURCE_R_CAP = Fraction(70871, 3375)
SOURCE_DENSITY_CAP = Fraction(6075000000000, 7235955529)
DEFAULT_CERTIFICATE = Path(__file__).with_name("all_height_coherent_query_weights.json")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def decode(value):
    """The least significant base-20 digit belongs to prime 3."""
    require(type(value) is int and value >= 0, "Invalid encoded exponent tuple")
    digits = []
    for _ in PRIMES:
        value, digit = divmod(value, 20)
        digits.append(digit)
    require(value == 0, "Exponent encoding has more than seven digits")
    return tuple(digits)


def minimal_profiles():
    """Enumerate independently, without a hardcoded list of factor shapes.

    A coordinatewise minimal product >=20 is at most 38: if some factor is
    2, minimality makes the product an even integer <40. If all nonunit
    factors are at least 3, reducing one makes its product <30.
    """
    answer = []

    def visit(prefix, factor_product):
        if len(prefix) == len(PRIMES):
            if factor_product >= 20 and all(
                a == 0 or factor_product // (a + 1) * a < 20 for a in prefix
            ):
                answer.append(tuple(prefix))
            return
        for factor in range(1, min(20, 38 // factor_product) + 1):
            visit(prefix + [factor - 1], factor_product * factor)

    visit([], 1)
    require(len(answer) == len(set(answer)) == 644, "Minimal-profile inventory")
    return sorted(answer)


def verify(certificate_path):
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    require(certificate["primes"] == list(PRIMES), "Prime inventory")
    require(certificate["max_coarse_exponent"] == COARSE_HEIGHT, "Coarse height")
    require(certificate["top_extra_digits"] == EXTRA_DIGITS, "Extra heights")
    require(Fraction(certificate["target_payoff"]) == TARGET, "Target payoff")

    masses = defaultdict(Fraction)
    coefficients = defaultdict(Fraction)
    seen_rows = set()
    row_count = 0
    for row in certificate["rows"]:
        require(isinstance(row, list) and len(row) == 3, "Invalid weight row")
        e, t = decode(row[0]), decode(row[1])
        require(all(0 <= b <= a <= COARSE_HEIGHT for a, b in zip(e, t)),
                "Invalid prefix relation")
        require((e, t) not in seen_rows, "Duplicate label-prefix weight")
        seen_rows.add((e, t))
        require(isinstance(row[2], str), "Weight must be an exact rational string")
        weight = Fraction(row[2])
        require(weight >= 0, "Negative weight")
        masses[e] += weight
        denominator = prod(p ** (a - b) for p, a, b in zip(PRIMES, e, t))
        coefficients[t] += weight / denominator
        row_count += 1

    # Fine exponent f has the unique coarse label min(f,19) coordinatewise.
    # This makes the resources below actual distinct numerical divisors.
    fine_resources = set()
    saturated_labels = 0
    for e, mass in sorted(masses.items()):
        beta = prod(
            sum((Fraction(1, p ** j) for j in range(EXTRA_DIGITS + 1)), Fraction())
            if a == COARSE_HEIGHT else Fraction(1)
            for p, a in zip(PRIMES, e)
        )
        require(mass <= beta, "Per-label rational resource budget exceeded")
        saturated_labels += mass == beta
        choices = [range(COARSE_HEIGHT, COARSE_HEIGHT + EXTRA_DIGITS + 1)
                   if a == COARSE_HEIGHT else (a,) for a in e]
        resource_sum = Fraction()
        for fine in product(*choices):
            require(fine not in fine_resources, "Repeated fine numerical divisor")
            require(tuple(min(a, COARSE_HEIGHT) for a in fine) == e,
                    "Fine divisor has the wrong coarse label")
            fine_resources.add(fine)
            resource_sum += Fraction(
                1, prod(p ** (b - a) for p, a, b in zip(PRIMES, e, fine))
            )
        require(resource_sum == beta, "Fine resource grouping disagrees with beta")

    zero = (0,) * len(PRIMES)
    require(masses[zero] == 1 and (zero, zero) in seen_rows, "Unit query resource")
    require(coefficients[zero] >= 1, "Payoff must be at least one everywhere")
    require(row_count == 9190 and len(masses) == 8857 and len(fine_resources) == 8987,
            "Final certificate inventory")

    # Each summand is nonnegative and coordinatewise nondecreasing. Every
    # coherent heavy profile dominates a minimal profile after clipping at 19.
    profiles = minimal_profiles()
    denominator = lcm(*(weight.denominator for weight in coefficients.values()))
    terms = [(t, weight.numerator * (denominator // weight.denominator))
             for t, weight in sorted(coefficients.items())]
    numerators = [sum(weight for t, weight in terms
                      if all(vp >= tp for vp, tp in zip(v, t))) for v in profiles]
    minimum_numerator = min(numerators)
    minimum = Fraction(minimum_numerator, denominator)
    require(minimum >= TARGET, "Rational monotone payoff does not reach target")

    escape = 1 - SOURCE_R_CAP / (TARGET - 1)
    require(escape == Fraction(683, 142425) and escape > 0, "Source escape mass")
    q, r = 23, 29
    fibre_values = [Fraction((q - 1 - n) * (r - 1 - n) - n,
                            (q - 1) * (r - 1)) for n in range(1, 20)]
    require(min(fibre_values) == Fraction(1, 77), "Actual two-prime fibre margin")
    haar_floor = escape * min(fibre_values) / SOURCE_DENSITY_CAP
    require(haar_floor == Fraction(449287056937, 6056623125000000000),
            "Full survivor Haar floor")

    return {
        "result": "PASS",
        "input": {"path": certificate_path.name, "sha256": sha256(raw).hexdigest(),
                  "bytes": len(raw)},
        "primes": PRIMES,
        "coarse_height": COARSE_HEIGHT,
        "maximum_query_height": max(max(e) for e in fine_resources),
        "rational_weight_rows": row_count,
        "base_label_count": len(masses),
        "fine_numerical_label_count": len(fine_resources),
        "saturated_label_budgets": saturated_labels,
        "combined_monotone_terms": len(terms),
        "minimal_heavy_profile_count": len(profiles),
        "minimum_payoff": str(minimum),
        "retained_payoff_lower_bound": str(TARGET),
        "attaining_minimal_profiles": [v for v, n in zip(profiles, numerators)
                                      if n == minimum_numerator],
        "unit_resource": "1",
        "payoff_at_least_one_everywhere": True,
        "source_nonunit_query_cap": str(SOURCE_R_CAP),
        "source_density_cap": str(SOURCE_DENSITY_CAP),
        "source_mass_outside_coherent_heavy_region": str(escape),
        "max_active_old_cofactors_outside_heavy_region": 19,
        "new_primes": [q, r],
        "minimum_new_coordinate_survivor_Haar_mass": str(min(fibre_values)),
        "full_original_survivor_Haar_lower_bound": str(haar_floor),
        "verification": "Exact rational prefix budgets and all minimal heavy profiles; no CRT-period enumeration or optimization runtime.",
        "scope": "The original family is finite, its numerical moduli are pairwise distinct and greater than one, and all their prime supports lie in the first nine odd primes. Every class touching 23 or 29 has one common old-coordinate centre; old cofactor heights and all other original phases and heights are arbitrary. No independent-old-phase conclusion.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(verify(args.certificate), indent=2) + "\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.write_text(output)


if __name__ == "__main__":
    main()
