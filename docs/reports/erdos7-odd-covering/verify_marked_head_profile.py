#!/usr/bin/env python3
"""Verify the complete 315 marked-head convex profile using exact arithmetic.

The adjacent fixed certificate contains finite results, not executable input.
Every old-head layout histogram, ordered histogram pair, integer survivor
count and integer threshold is checked.  Only the Python standard library is
used.  The universal pruning and convex-rearrangement argument is stated in
Problems/erdos-7-marked-head-profile.md; this program verifies its finite calculation.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


MODULI = (3, 5, 9, 15, 45)
CATEGORIES = ("same_other_column", "other_same_column", "other_other_column")
THRESHOLDS = range(13)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def crt(a, m, b, n):
    return next(x for x in range(m * n) if x % m == a and x % n == b)


def old_head(root, category):
    other = 3 - root
    row, column = {
        "same_other_column": (root, 2),
        "other_same_column": (other, 1),
        "other_other_column": (other, 2),
    }[category]
    classes = ((3, 0), (9, 4), (5, 0),
               (15, crt(root, 3, 1, 5)), (45, crt(row, 9, column, 5)))
    points = [x for x in range(45) if all(x % d != a for d, a in classes)]
    support = sum(1 << x for x in points)
    masks = [sorted({sum(1 << x for x in range(a, 45, d)) & support
                     for a in range(d)} - {0}) for d in MODULI]
    histograms = set()
    layouts = 0
    for choices in product(*masks):
        histogram = [0] * 6
        for x in points:
            # The unit-divisor term is one: index zero means load one.
            histogram[sum(bool(mask & (1 << x)) for mask in choices)] += 1
        histograms.add(tuple(histogram))
        layouts += 1
    maxima = [max(mask.bit_count() for mask in group) for group in masks]
    return points, sorted(histograms), layouts, maxima


def hinges(histogram):
    """All integer hinge sums for a histogram indexed by load value."""
    result = [0] * len(histogram)
    count = 0
    for t in range(len(histogram) - 2, -1, -1):
        count += histogram[t + 1]
        result[t] = result[t + 1] + count
    return result


def complete_profile(n, histograms, minimum):
    """Maximize MP1 over all ordered histogram pairs and every admissible D."""
    counts = range(minimum, 6 * n + 1)
    best = [(0, 1)] * 13
    data = [(h, [v for v, count in enumerate(h, 1) for _ in range(count)])
            for h in histograms]
    pairs_and_counts = 0
    for h, a in data:
        # Five extra slots at each old point.  Hinge values are increasing in
        # its load, so the same descending order gives Top for every t.
        extras = [v for v in reversed(a) for _ in range(5)]
        top = []
        for t in THRESHOLDS:
            prefix = [0]
            for v in extras:
                prefix.append(prefix[-1] + max(v - t, 0))
            top.append(prefix)
        for _, b in data:
            summed = [0] * 13
            for x, y in zip(a, b):
                summed[x + y] += 1
            cross = hinges(summed)
            for d in counts:
                pairs_and_counts += 1
                extra_count = d - n
                for t in THRESHOLDS:
                    numerator = cross[t] + top[t][extra_count]
                    p, q = best[t]
                    if numerator * q > p * d:
                        best[t] = (numerator, d)
    return [Fraction(p, q) for p, q in best], pairs_and_counts


def sharp_example(theta):
    classes = ((3, 0), (9, 4), (5, 0), (15, 11), (45, 1), (7, 0),
               (21, 8), (63, 16), (35, 17), (105, 32), (315, 47))
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    require({d for d, _ in classes} == set(divisors) - {1},
            "sharp family has exactly every nonunit original modulus")
    old = [x for x in range(45) if all(x % d != a for d, a in classes[:5])]
    survivors = [x for x in range(315) if all(x % d != a for d, a in classes)]
    centre = 272
    old_hist = Counter(sum(x % d == centre % d for d in (1,) + MODULI) for x in old)
    full_hist = Counter(sum(x % d == centre % d for d in divisors) for x in survivors)
    mixed_masses = [sum(x % (d // 7) == a % (d // 7) for x in old)
                    for d, a in classes[6:]]
    require([a % 7 for _, a in classes[6:]] == [1, 2, 3, 4, 5],
            "mixed classes have distinct septenary residues")
    require(all(x % 7 != 6 or x % 45 in old for x in survivors),
            "clean septenary fibre projects into old survivors")
    require(sum(x % 7 == 6 for x in survivors) == len(old),
            "septenary residue six contains the full old survivor set")
    values = []
    for t in range(6, 13):
        actual = Fraction(sum(n * max(k - t, 0) for k, n in full_hist.items()),
                          len(survivors))
        formula = Fraction(max(12 - t, 0) + 2 * max(8 - t, 0), 74)
        require(actual == formula == theta[t], "high-threshold sharpness")
        values.append(str(actual))
    return {
        "original_classes": [list(pair) for pair in classes],
        "test_centre": centre,
        "old_survivors": len(old),
        "complete_survivors": len(survivors),
        "mixed_old_cylinder_masses": mixed_masses,
        "old_test_load_histogram": {str(k): n for k, n in sorted(old_hist.items())},
        "complete_test_load_histogram": {str(k): n for k, n in sorted(full_hist.items())},
        "profile_at_thresholds_6_through_12": values,
        "profile_for_real_t_at_least_6": "((12-t)_+ + 2*(8-t)_+)/74",
    }


def verify(expected):
    cases = []
    for root, category in product((1, 2), CATEGORIES):
        points, histograms, layouts, maxima = old_head(root, category)
        n = len(points)
        minimum = 6 * n - sum(maxima)
        profile, checked = complete_profile(n, histograms, minimum)
        require(checked == len(histograms) ** 2 * (6 * n - minimum + 1),
                "all ordered histogram pairs and integer survivor counts checked")
        cases.append({
            "shape": f"root{root}_{category}",
            "old_survivors": n,
            "test_layouts": layouts,
            "distinct_histograms": len(histograms),
            "old_cylinder_maxima_in_modulus_order": maxima,
            "survivor_count_range_inclusive": [minimum, 6 * n],
            "ordered_histogram_pair_count_cases": checked,
            "integer_hinge_cases": 13 * checked,
            "profile": list(map(str, profile)),
        })
    theta = [max(Fraction(row["profile"][t]) for row in cases) for t in THRESHOLDS]
    atoms = {k: theta[k - 1] - 2 * theta[k] + (theta[k + 1] if k < 12 else 0)
             for k in range(1, 13)}
    require(all(p >= 0 for p in atoms.values()) and sum(atoms.values()) == 1,
            "auxiliary atoms form a probability law")
    for t in THRESHOLDS:
        require(sum(p * max(k - t, 0) for k, p in atoms.items()) == theta[t],
                "auxiliary law has the entire universal hinge profile")
    result = {
        "schema": "marked-head-profile-v1",
        "head_modulus": 315,
        "old_moduli_order": list(MODULI),
        "thresholds": list(THRESHOLDS),
        "cases": cases,
        "universal_profile": list(map(str, theta)),
        "auxiliary_atoms": {str(k): str(p) for k, p in atoms.items() if p},
        "mean": str(sum(k * p for k, p in atoms.items())),
        "second_moment": str(sum(k * k * p for k, p in atoms.items())),
        "sharp_example": sharp_example(theta),
    }
    require(result == expected, "computed exact result differs from the fixed certificate")
    print(json.dumps({"verified": True, "old_test_layouts": sum(r["test_layouts"] for r in cases),
                      "integer_hinge_cases": sum(r["integer_hinge_cases"] for r in cases),
                      "mean": result["mean"], "second_moment": result["second_moment"]}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("marked_head_profile_certificate.json"))
    args = parser.parse_args()
    verify(json.loads(args.certificate.read_text()))


if __name__ == "__main__":
    main()
