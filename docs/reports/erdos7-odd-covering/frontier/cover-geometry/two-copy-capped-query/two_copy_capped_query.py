#!/usr/bin/env python3
"""Exact all-depth budgets for the two-copy six-prime capped law.

The positive-part expectation uses every geometric tail through its full
mean. Only probabilities below the requested threshold are enumerated.
This computes the numerical premises of report348's ordinary proof; it
does not certify arbitrary original phases or perform Lean verification.
"""
import argparse
from fractions import Fraction as F
import json
from math import prod
from pathlib import Path


REFERENCE_PRIMES = (5, 7, 11, 13, 17, 19)
DEFAULT_STAGES = (2, 2, 4, 4)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pair(number):
    return [number.numerator, number.denominator]


def multiplier_hinge(coordinates, threshold, removed=()):
    """Return E[(product N-threshold)+], its full mean, and low masses.

    With removed mass u, mass(N=1)=1-u-C/p and
    mass(N=n)=C*(p-1)/p**n for n>=2; the total mass is 1-u.
    Default u=0 gives a probability measure.
    The coordinates are independent comparison variables, not a claim
    of independence for the actual survivor law.
    """
    require(type(threshold) is int and 1 <= threshold <= 64,
            "query threshold must be an integer between 1 and 64")
    require(len(removed) <= len(coordinates), "removed masses exceed coordinate count")
    low = {1: F(1)} if threshold > 1 else {}
    mean = F(1)
    total_mass = F(1)
    for index, (prime, cap) in enumerate(coordinates):
        require(type(prime) is int and prime >= 2, "invalid coordinate size")
        require(0 <= cap <= prime, "comparison cap outside [0,p]")
        missing = removed[index] if index < len(removed) else F(0)
        require(0 <= missing <= 1 and cap / prime <= 1 - missing,
                "removed mass leaves an invalid comparison measure")
        total_mass *= 1 - missing
        mean *= 1 - missing + cap / (prime - 1)
        probabilities = {1: 1 - missing - cap / prime}
        probabilities.update({n: cap * F(prime - 1, prime ** n)
                              for n in range(2, threshold)})
        following = {}
        for value, mass in low.items():
            for number, probability in probabilities.items():
                target = value * number
                if target < threshold:
                    following[target] = following.get(target, F(0)) + mass * probability
        low = following
    positive_part = mean - threshold * total_mass + sum(
        (threshold - value) * mass for value, mass in low.items())
    require(positive_part >= 0, "negative positive-part expectation")
    return positive_part, mean, low


def budgets(stage_thresholds=DEFAULT_STAGES, query_threshold=6, pure_removed=None):
    require(len(stage_thresholds) == 4, "exactly four stage thresholds are required")
    coordinates = [(5, F(1)), (7, F(1))]
    removed = () if pure_removed is None else tuple(pure_removed)
    if pure_removed is None:
        pure_mass = (1 - F(2, 4)) * (1 - F(2, 6))
    else:
        require(len(removed) == 2 and 0 <= removed[0] <= F(1, 2)
                and 0 <= removed[1] <= F(1, 3), "pure masses outside their rectangle")
        pure_mass = prod(1 - value for value in removed)
    mixed_mass = F(2, 4 * 6)
    anchor_mass = pure_mass - mixed_mass
    mass = anchor_mass
    rows = []
    for prime, threshold in zip(REFERENCE_PRIMES[2:], stage_thresholds):
        require(type(threshold) is int and 0 < 2 * threshold < prime - 1,
                "stage thresholds must satisfy 0 < 2t < p-1")
        positive_part, _, _ = multiplier_hinge(coordinates, threshold, removed)
        cap = F(prime - 1, prime - 1 - 2 * threshold)
        loss = F(2, prime - 1 - 2 * threshold) * positive_part
        mass -= loss
        coordinates.append((prime, cap))
        rows.append({"prime": prime, "threshold": threshold, "cap": pair(cap),
                     "hinge": pair(positive_part), "loss": pair(loss),
                     "mass_lower": pair(mass)})
    require(mass > 0, "schedule does not certify positive final mass")
    positive_part, mean, low = multiplier_hinge(coordinates, query_threshold, removed)
    query_bound = query_threshold - 1 + positive_part / mass
    density_cap = prod(cap for _, cap in coordinates) / mass
    continuation = 1 - F(51, 616) * (1 + query_bound)
    result = {
        "reference_primes": list(REFERENCE_PRIMES),
        "multiplicity_per_nonunit_numerical_modulus": 2,
        "pure_anchor_mass_lower": pair(pure_mass),
        "mixed_anchor_loss_upper": pair(mixed_mass),
        "anchor_mass_lower": pair(anchor_mass),
        "stages": rows,
        "mass_lower": pair(mass),
        "unnormalized_density_cap": pair(prod(cap for _, cap in coordinates)),
        "query_threshold": query_threshold,
        "multiplier_full_mean": pair(mean),
        "multiplier_masses_below_threshold": [
            {"value": value, "probability": pair(probability)}
            for value, probability in sorted(low.items())],
        "query_hinge": pair(positive_part),
        "query_upper": pair(query_bound),
        "density_upper": pair(density_cap),
        "later_23_29_probability_lower": pair(continuation),
        "later_23_29_haar_lower": pair(max(F(0), continuation) / density_cap),
    }
    if pure_removed is not None:
        result["pure_removed_masses"] = [pair(value) for value in removed]
        result["multiplier_total_mass"] = pair(pure_mass)
    if pure_removed is None and tuple(stage_thresholds) == DEFAULT_STAGES and query_threshold == 6:
        require(mass > F(3, 64), "default mass does not exceed 3/64")
        require(query_bound < 10, "default query bound is not below 10")
        require(density_cap < 192, "default density cap is not below 192")
        require(continuation > F(3, 20), "default continuation reserve is not above 3/20")
    return result


def joint_anchor_budgets(stage_thresholds=DEFAULT_STAGES, query_threshold=3):
    corners = [budgets(stage_thresholds, query_threshold, (u, v))
               for u in (F(0), F(1, 2)) for v in (F(0), F(1, 3))]
    mass = min(F(*corner["mass_lower"]) for corner in corners)
    query = max(F(*corner["query_upper"]) for corner in corners)
    density = max(F(*corner["density_upper"]) for corner in corners)
    reserve = 1 - F(51, 616) * (1 + query)
    target = F(565, 51)
    transfer_parameter = 1 + 2 * query
    crossing = (target * transfer_parameter / (transfer_parameter - target)
                if transfer_parameter > target else None)
    result = {
        "reference_primes": list(REFERENCE_PRIMES),
        "stage_thresholds": list(stage_thresholds),
        "query_threshold": query_threshold,
        "corners": corners,
        "mass_lower": pair(mass),
        "query_upper": pair(query),
        "density_upper": pair(density),
        "gap_above_lower_certificate_threshold": pair(query - F(257, 51)),
        "tc6_strict_height_threshold": None if crossing is None else pair(crossing),
        "tc6_least_possible_integer_height": (None if crossing is None else
                                              crossing.numerator // crossing.denominator + 1),
        "later_23_29_probability_lower": pair(reserve),
        "later_23_29_haar_lower": pair(max(F(0), reserve) / density),
    }
    if tuple(stage_thresholds) == DEFAULT_STAGES and query_threshold == 3:
        require(query < F(103, 20), "joint-anchor query bound is not below 103/20")
        require(density < 88, "joint-anchor density cap is not below 88")
        require(reserve > F(49, 100), "joint-anchor continuation reserve is not above 49/100")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stages", nargs=4, type=int, default=DEFAULT_STAGES,
                        metavar=("T11", "T13", "T17", "T19"))
    parser.add_argument("--query-threshold", type=int,
                        help="default: 6, or 3 with --joint-anchor")
    parser.add_argument("--joint-anchor", action="store_true",
                        help="retain both actual pure-anchor masses and bound all four corners")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        threshold = args.query_threshold
        if threshold is None:
            threshold = 3 if args.joint_anchor else 6
        calculator = joint_anchor_budgets if args.joint_anchor else budgets
        result = calculator(args.stages, threshold)
    except ValueError as error:
        parser.error(str(error))
    content = json.dumps(result, indent=2) + "\n"
    if args.output is None:
        print(content, end="")
    else:
        args.output.write_text(content, encoding="utf-8")


if __name__ == "__main__":
    main()
