#!/usr/bin/env python3
"""Necessary pure-label conditions for an actual two-copy R lower witness.

Consume the retained four-corner PA ledger, without rerunning its producer.
The target is R_*(V)>257/51 for a complete actual survivor V on the six
reference primes. Numerical output uses the ordinary PA comparison proof;
it is not an original-family search or Lean verification.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

PA_SHA256 = "45939ae4a727d63d0e91d836b8519eea84482f8c06cfe46eb96cb082a2f78a53"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fraction(value):
    require(isinstance(value, list) and len(value) == 2
            and all(type(v) is int for v in value) and value[1] > 0,
            "expected an exact rational pair with positive denominator")
    return F(*value)


def pair(value):
    return [value.numerator, value.denominator]


def replace_last_prime(corner):
    """Replace the last auxiliary 19-coordinate by 23 using stored moments."""
    stages = corner.get("stages")
    require(isinstance(stages, list) and len(stages) == 4
            and all(isinstance(stage, dict) for stage in stages)
            and stages[2].get("prime") == 17 and stages[3].get("prime") == 19,
            "missing PA prefix at 17 and last-stage hinge")
    prefix_mass = fraction(stages[2].get("mass_lower"))
    old_prefix_hinge = fraction(stages[3].get("hinge"))
    mass = prefix_mass - old_prefix_hinge / 7
    low_rows = corner.get("multiplier_masses_below_threshold")
    require(isinstance(low_rows, list) and len(low_rows) == 2,
            "expected two low product masses")
    low = {}
    for row in low_rows:
        require(isinstance(row, dict) and type(row.get("value")) is int
                and row["value"] in (1, 2) and row["value"] not in low,
                "invalid or repeated low product value")
        low[row["value"]] = fraction(row.get("probability"))
    old_n1, old_n2 = F(86, 95), F(162, 1805)
    prefix_p1 = low[1] / old_n1
    prefix_p2 = (low[2] - prefix_p1 * old_n2) / old_n1
    require(min(prefix_p1, prefix_p2) >= 0, "negative recovered prefix mass")
    prefix_mean = fraction(corner.get("multiplier_full_mean")) / F(11, 10)
    total_mass = fraction(corner.get("multiplier_total_mass"))
    new_n1, new_n2 = F(150, 161), F(242, 3703)
    hinge = (prefix_mean * F(15, 14) - 3 * total_mass
             + 2 * prefix_p1 * new_n1 + prefix_p2 * new_n1 + prefix_p1 * new_n2)
    require(mass > 0 and hinge >= 0, "replacement does not give a positive mass and hinge")
    return {"pure_removed_masses": corner["pure_removed_masses"],
            "mass_lower": pair(mass), "query_hinge": pair(hinge),
            "query_upper": pair(2 + hinge / mass),
            "density_upper": pair(F(55, 7) / mass)}


def boundary(data):
    require(data.get("reference_primes") == [5, 7, 11, 13, 17, 19],
            "unexpected reference primes")
    require(data.get("stage_thresholds") == [2, 2, 4, 4]
            and data.get("query_threshold") == 3, "unexpected PA schedule")
    corners = data.get("corners")
    require(isinstance(corners, list) and len(corners) == 4,
            "exactly four PA corners are required")
    target = F(257, 51)
    values = {}
    for corner in corners:
        require(isinstance(corner, dict), "invalid corner record")
        removed = corner.get("pure_removed_masses")
        require(isinstance(removed, list) and len(removed) == 2,
                "each corner must give two removed masses")
        u, v = map(fraction, removed)
        require(u in (0, F(1, 2)) and v in (0, F(1, 3))
                and (u, v) not in values, "invalid or repeated PA corner")
        require(corner.get("query_threshold") == 3, "corner uses another query threshold")
        mass = fraction(corner.get("mass_lower"))
        hinge = fraction(corner.get("query_hinge"))
        require(mass > 0 and hinge >= 0, "invalid corner mass or hinge")
        values[u, v] = (target - 2) * mass - hinge
    constant = values[F(1, 2), F(1, 3)]
    coefficient5 = (values[0, F(1, 3)] - constant) / F(1, 2)
    coefficient7 = (values[F(1, 2), 0] - constant) / F(1, 3)
    joint = (values[0, 0] - constant - coefficient5 / 2
             - coefficient7 / 3) / F(1, 6)
    require(constant < 0 and min(coefficient5, coefficient7, joint) > 0,
            "the retained corners do not give the stated increasing deficit boundary")
    cutoff5, cutoff7 = -constant / coefficient5, -constant / coefficient7
    forced = {}
    for prime, cutoff in ((5, cutoff5), (7, cutoff7)):
        power = prime
        labels = []
        while F(1, power) >= cutoff:
            labels.append(power)
            power *= prime
        forced[str(prime)] = labels
    require(forced == {"5": [5, 25, 125], "7": [7, 49]},
            "the input yields a different forced-label inventory")
    deficit5, deficit7 = F(1, 250), F(1, 147)
    height_gap = (constant + coefficient5 * deficit5 + coefficient7 * deficit7
                  + joint * deficit5 * deficit7)
    require(height_gap > 0, "joint pure-height restriction is not excluded")
    replaced = [replace_last_prime(corner) for corner in corners]
    replaced_query = max(fraction(corner["query_upper"]) for corner in replaced)
    replaced_density = max(fraction(corner["density_upper"]) for corner in replaced)
    require(replaced_query < target, "prime-23 reference does not exclude the lower target")
    return {
        "target": pair(target),
        "deficit_coordinates": ["1/2 - actual pure-5 union mass",
                                "1/3 - actual pure-7 union mass"],
        "gap_constant": pair(constant),
        "gap_coefficient5": pair(coefficient5),
        "gap_coefficient7": pair(coefficient7),
        "gap_joint_coefficient": pair(joint),
        "necessary_strict_deficit5_upper": pair(cutoff5),
        "necessary_strict_deficit7_upper": pair(cutoff7),
        "forced_two_copy_pure_moduli": forced,
        "minimum_positive_overlap_mass_among_forced_pure5_cylinders": pair(F(1, forced["5"][-1])),
        "minimum_positive_overlap_mass_among_forced_pure7_cylinders": pair(F(1, forced["7"][-1])),
        "excluded_joint_pure_height_upper": [3, 2],
        "joint_height_minimum_deficits": [pair(deficit5), pair(deficit7)],
        "joint_height_positive_gap": pair(height_gap),
        "prime_23_reference": {
            "primes": [5, 7, 11, 13, 17, 23],
            "last_cap": pair(F(11, 7)),
            "raw_density_cap": pair(F(55, 7)),
            "corners": replaced,
            "query_upper": pair(replaced_query),
            "density_upper": pair(replaced_density),
            "gap_below_target": pair(target - replaced_query),
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path,
                        default=Path(__file__).with_name("two_copy_pure_anchor.json"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        raw = args.input.read_bytes()
        require(sha256(raw).hexdigest() == PA_SHA256,
                "input must be the retained PA ledger with SHA-256 " + PA_SHA256)
        data = json.loads(raw.decode("utf-8"))
        require(isinstance(data, dict), "PA input must be an object")
        result = {"source_sha256": PA_SHA256, **boundary(data)}
    except (OSError, ValueError, TypeError, KeyError) as error:
        parser.error(str(error))
    content = json.dumps(result, indent=2) + "\n"
    if args.output is None:
        print(content, end="")
    else:
        args.output.write_text(content, encoding="utf-8")


if __name__ == "__main__":
    main()
