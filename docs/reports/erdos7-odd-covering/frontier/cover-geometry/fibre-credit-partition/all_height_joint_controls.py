#!/usr/bin/env python3
"""Two exact finite controls for the arbitrary-height joint-profile bridge.

This is a finite arithmetic check, not a Lean verification or an E7 proof.
Run with Python standard library only; --output is the sole output path.
"""

import argparse
from fractions import Fraction as F
import json


def frac(q):
    return str(q)


def run():
    checks = 0

    def check(condition):
        nonlocal checks
        assert condition
        checks += 1

    # Actual labels 3, 99=9*11, 351=27*13.  Work inside the retained
    # first ternary root t=1 (mod 3); t resolves every actual prefix.
    ternary = tuple(range(1, 27, 3))
    rows = [(t, x, y) for t in ternary for x in range(11) for y in range(13)]
    survivors = [
        (t, x, y) for t, x, y in rows
        if not (t % 9 == 1 and x == 0)
        and not (t == 4 and y == 0)
    ]
    check(55 % 9 == 1 and 55 % 11 == 0)
    check(247 % 27 == 4 and 247 % 13 == 0)
    check(len(rows) == 1287)
    check(len(survivors) == 1237)
    mean11 = sum((F(10, 11) if t % 9 == 1 else F(1)) for t in ternary) / 9
    mean13 = sum((F(12, 13) if t == 4 else F(1)) for t in ternary) / 9
    joint_survival = F(len(survivors), len(rows))
    check(mean11 == F(32, 33))
    check(mean13 == F(116, 117))
    check(mean11 * mean13 - joint_survival == F(1, 3861))
    # The conditional nonternary coordinates become dependent after the
    # common ternary leaf is erased and star survival is conditioned on.
    n11 = sum(x == 0 for t, x, y in survivors)
    n13 = sum(y == 0 for t, x, y in survivors)
    nboth = sum(x == 0 and y == 0 for t, x, y in survivors)
    check((n11, n13, nboth) == (77, 85, 5))
    dependence = F(nboth, len(survivors)) - F(n11 * n13, len(survivors) ** 2)
    check(dependence == F(-360, 1237**2))
    for t in ternary:
        fibre = [(x, y) for tt, x, y in survivors if tt == t]
        expected = (10 if t % 9 == 1 else 11) * (12 if t == 4 else 13)
        check(len(fibre) == expected)

    # Actual distinct odd labels 3,5,7,105,315 with fixed phases.
    # Pure-source coordinates avoid 0 mod 3,5,7.  The two remaining
    # originals share d=35 but have different k and different first roots.
    actual_classes = ((0, 3), (0, 5), (0, 7), (1, 105), (281, 315))
    source = [n for n in range(315) if n % 3 and n % 5 and n % 7]
    selected1 = [n for n in source if n % 105 == 1]
    selected2 = [n for n in source if n % 315 == 281]
    check(len({m for a, m in actual_classes}) == len(actual_classes))
    check(all(m > 1 and m % 2 for a, m in actual_classes))
    check((281 % 9, 281 % 35) == (2, 1))
    check(len(source) == 144)
    check(len(selected1) == 3 and len(selected2) == 1)
    check(not set(selected1).intersection(selected2))
    first_fee = F(len(selected1), len(source))
    second_fee = F(len(selected2), len(source))
    actual_union = F(len(set(selected1 + selected2)), len(source))
    head5 = min(F(4, 15), F(1, 4))
    head7 = min(F(6, 35), F(1, 6))
    mincap = head5 * head7
    once_selected = F(1, 2) * mincap
    correct_sum = (F(1, 2) + F(1, 6)) * mincap
    check(mincap == F(1, 24))
    check(first_fee == F(1, 48))
    check(second_fee == F(1, 144))
    check(actual_union == F(1, 36))
    check(once_selected == first_fee)
    check(correct_sum == actual_union)
    check(actual_union - once_selected == F(1, 144))
    # Even the looser universal-depth cap fails if only one selected fee
    # is retained for d; the min-cap example above is exact.
    loose_once = F(1, 2) * F(4, 15) * F(6, 35)
    check(actual_union - loose_once == F(31, 6300))

    return {
        "contract": {
            "evidence": "exact finite arithmetic, not Lean verification",
            "scope": "two actual finite globally phased odd-modulus families",
            "positivity_claim": "none for unrestricted Erdős #7",
        },
        "shared_ternary_mixture": {
            "actual_classes": [[0, 3], [55, 99], [247, 351]],
            "condition": "pure3-conditioned Haar, then first root t=1 mod3",
            "grid_size": len(rows),
            "survivors": len(survivors),
            "mean11": frac(mean11),
            "mean13": frac(mean13),
            "joint_survival": frac(joint_survival),
            "product_of_means_minus_joint": frac(mean11 * mean13 - joint_survival),
            "surviving_coordinate_zero_counts": [n11, n13, nboth],
            "conditioned_joint_minus_product": frac(dependence),
        },
        "distinct_height_labels": {
            "actual_classes": [list(a) for a in actual_classes],
            "source_size": len(source),
            "label105_mass": frac(first_fee),
            "label315_mass": frac(second_fee),
            "actual_union": frac(actual_union),
            "incorrect_once_per_d_mincap_fee": frac(once_selected),
            "correct_per_height_fee": frac(correct_sum),
            "undercharge": frac(actual_union - once_selected),
            "universal_cap_once_per_d_undercharge": frac(actual_union - loose_once),
        },
        "exact_checks": checks,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = run()
    with open(args.output, "w", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"exact_checks": result["exact_checks"], "output": args.output}))


if __name__ == "__main__":
    main()
