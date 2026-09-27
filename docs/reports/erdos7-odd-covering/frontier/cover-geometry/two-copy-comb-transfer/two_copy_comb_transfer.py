#!/usr/bin/env python3
"""Check partial ternary-comb lifts and the six-prime two-copy constants.

An input JSON has A and B lists of [modulus, residue] pairs. Within each
list moduli are distinct, nonunit and coprime to 6. At most six primes
may occur. --max-period bounds literal enumeration, not the theorem.
Default execution rechecks the finite controls in the sibling JSON.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import json
from math import gcd, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pair(value):
    return [value.numerator, value.denominator]


def primes(number):
    result = []
    divisor = 2
    while divisor * divisor <= number:
        if number % divisor == 0:
            result.append(divisor)
            while number % divisor == 0:
                number //= divisor
        divisor += 1
    if number > 1:
        result.append(number)
    return result


def validate(spec, height, max_period):
    require(type(height) is int and height > 0, "height must be positive")
    require(type(max_period) is int and max_period > 0, "period cap must be positive")
    require(isinstance(spec, dict) and set(spec) == {"A", "B"}, "expected A and B lists")
    period = 1
    for name in ("A", "B"):
        require(isinstance(spec[name], list), "input family must be a list")
        seen = set()
        for row in spec[name]:
            require(isinstance(row, list) and len(row) == 2, "expected [modulus, residue]")
            modulus, residue = row
            require(type(modulus) is int and modulus > 1 and gcd(modulus, 6) == 1,
                    "modulus must be nonunit and coprime to 6")
            require(type(residue) is int and 0 <= residue < modulus, "noncanonical residue")
            require(modulus not in seen, "duplicate modulus within one input family")
            seen.add(modulus)
            period = lcm(period, modulus)
            require(period <= max_period, "cofactor period exceeds enumeration cap")
    require(len(primes(period)) <= 6, "more than six cofactor primes")
    ternary = 1
    for _ in range(height):
        require(ternary <= max_period // (3 * period), "full period exceeds enumeration cap")
        ternary *= 3
    return period, ternary


def construct(spec, height, max_period):
    period, ternary = validate(spec, height, max_period)
    rows = [list(row) for row in spec["A"]]
    power = 1
    for _ in range(height):
        old_power = power
        power *= 3
        rows.append([power, old_power - 1])
        side = 2 * old_power - 1
        for modulus, residue in spec["B"]:
            joined = side + power * (((residue - side) * pow(power, -1, modulus)) % modulus)
            rows.append([power * modulus, joined])
    require(len({m for m, _ in rows}) == len(rows), "lifted numerical labels collide")
    require(len(rows) == len(spec["A"]) + height * (1 + len(spec["B"])),
            "incorrect lifted label count")
    return period, ternary, rows


def avoids(value, rows):
    return all(value % modulus != residue for modulus, residue in rows)


def check_input(spec, height, max_period):
    period, ternary, rows = construct(spec, height, max_period)
    va = {x for x in range(period) if avoids(x, spec["A"])}
    vab = {x for x in va if avoids(x, spec["B"])}
    w = {t for t in range(ternary)
         if any(t % (3 ** i) == 2 * 3 ** (i - 1) - 1 for i in range(1, height + 1))}
    require(len(w) == (ternary - 1) // 2, "incorrect side-union cardinality")
    survivors = []
    for x in range(period * ternary):
        direct = avoids(x, rows)
        formula = ((x % ternary in w and x % period in vab)
                   or (x % ternary == ternary - 1 and x % period in va))
        require(direct == formula, "actual survivor disagrees with the two-fibre formula")
        if direct:
            survivors.append(x)
    require(len(survivors) == len(w) * len(vab) + len(va), "survivor count mismatch")

    # A correlated law on the actual survivors checks the finite factor-two
    # inequality. No marginal product or normalization of eta is substituted.
    query_control = None
    if survivors:
        weights = {x: 1 + (7 * x + x // ternary) % 11 for x in survivors}
        total = sum(weights.values())
        eta = Counter()
        for x, weight in weights.items():
            if x % ternary in w:
                eta[x % period] += weight
        full_sum = 0
        old_sum = 0
        for divisor in range(1, period + 1):
            if period % divisor:
                continue
            coarse = Counter()
            for y, weight in eta.items():
                coarse[y % divisor] += weight
            old_sum += max(coarse.values(), default=0)
            for i in range(height + 1):
                cylinder = Counter()
                for x, weight in weights.items():
                    cylinder[x % (divisor * 3 ** i)] += weight
                full_sum += max(cylinder.values(), default=0)
        require(full_sum >= 2 * old_sum, "same-law factor-two query inequality failed")
        query_control = {
            "law_total_weight": total,
            "restricted_mass": pair(F(sum(eta.values()), total)),
            "finite_full_query_sum": pair(F(full_sum, total)),
            "twice_restricted_query_sum": pair(F(2 * old_sum, total)),
        }
    return {
        "input": spec,
        "height": height,
        "cofactor_period": period,
        "full_period": period * ternary,
        "lifted_label_count": len(rows),
        "A_survivors": len(va),
        "AB_survivors": len(vab),
        "lifted_survivors": len(survivors),
        "same_law_query_control": query_control,
    }


def constants():
    common_query = F(70871, 3375)
    common_density = F(6075000000000, 7235955529)
    two_query = (common_query - 1) / 2
    two_density = common_density / 2
    reserve = 1 - F(51, 616) * (1 + two_query)
    height = 16
    tail_cap = common_density / 3 ** height
    finite_query = (1 + common_query) / (2 * (1 - tail_cap)) - 1
    finite_density = common_density * (1 - F(1, 3 ** height)) / (2 * (1 - tail_cap))
    lower_input = F(6)
    lower_height = 75
    lower_output = (1 + 2 * lower_input) * lower_height / (lower_height + 1 + 2 * lower_input)
    require(two_query == F(33748, 3375) < 10, "query target failed")
    require(two_density == F(3037500000000, 7235955529) < 420, "density target failed")
    require(1 / two_density > F(1, 420), "two-copy Haar bound failed")
    require(reserve == F(61909, 693000) > F(5, 56), "23/29 reserve failed")
    require(reserve / two_density > F(1, 4704), "23/29 Haar bound failed")
    require(0 <= tail_cap < 1 and finite_query < 10 and finite_density < 420,
            "height-sixteen finite transfer failed")
    require(lower_output == F(975, 88) and lower_output - F(565, 51) == F(5, 4488),
            "conditional lower-certificate transfer failed")
    return {
        "source_query_bound": pair(common_query),
        "source_density_cap": pair(common_density),
        "two_copy_query_bound": pair(two_query),
        "two_copy_density_cap": pair(two_density),
        "two_copy_haar_floor": pair(1 / two_density),
        "later_23_29_reserve": pair(reserve),
        "later_23_29_haar_floor": pair(reserve / two_density),
        "finite_transfer_height": height,
        "finite_tail_cap": pair(tail_cap),
        "finite_query_bound": pair(finite_query),
        "finite_density_cap": pair(finite_density),
        "conditional_cofactor_lower_bound": pair(lower_input),
        "conditional_lower_transfer_height": lower_height,
        "conditional_seven_prime_lower_bound": pair(lower_output),
        "conditional_query_target_surplus": pair(lower_output - F(565, 51)),
    }


def controls(max_period):
    fixtures = [
        {"A": [], "B": []},
        {"A": [[5, 0]], "B": [[5, 1]]},
        {"A": [[5, 2], [35, 9]], "B": [[7, 3], [35, 19]]},
        {"A": [[5, 0], [7, 1], [25, 7], [175, 23]],
         "B": [[5, 1], [25, 18], [35, 4], [175, 114]]},
    ]
    checked = [check_input(spec, h, max_period) for spec in fixtures for h in (1, 2, 4)]
    rejected = 0
    invalid = [
        ({"A": [[5, 0], [5, 1]], "B": []}, 1, 200000),
        ({"A": [[1, 0]], "B": []}, 1, 200000),
        ({"A": [[3, 1]], "B": []}, 1, 200000),
        ({"A": [[10, 1]], "B": []}, 1, 200000),
        ({"A": [[5, 5]], "B": []}, 1, 200000),
        ({"A": [[5, 0]], "B": []}, 0, 200000),
        ({"A": [[5, 0]], "B": []}, 4, 100),
    ]
    for spec, height, cap in invalid:
        try:
            validate(spec, height, cap)
        except ValueError:
            rejected += 1
        else:
            raise ValueError("invalid input was accepted")
    return {
        "scope": "Finite CRT masks, correlated-law query controls and rational constants; ordinary proof supplies all-height claims.",
        "constants": constants(),
        "controls": checked,
        "period_points_checked": sum(row["full_period"] for row in checked),
        "rejections_checked": rejected,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path)
    parser.add_argument("--height", type=int)
    parser.add_argument("--max-period", type=int, default=200000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require((args.input is None) == (args.height is None), "input and height must be supplied together")
    if args.input is None:
        result = controls(args.max_period)
        if args.output is None:
            expected = json.loads(Path(__file__).with_suffix(".json").read_text())
            require(result == expected, "retained result mismatch")
    else:
        result = check_input(json.loads(args.input.read_text()), args.height, args.max_period)
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result if args.input else {
        "period_points_checked": result["period_points_checked"],
        "rejections_checked": result["rejections_checked"],
        "two_copy_query_bound": result["constants"]["two_copy_query_bound"],
    }))


if __name__ == "__main__":
    main()
