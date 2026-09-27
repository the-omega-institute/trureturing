#!/usr/bin/env python3
"""Verify the complete 315 marked-head convex profile using exact arithmetic.

The adjacent fixed certificate contains finite results, not executable input.
Every old-head layout histogram, ordered histogram pair, integer survivor
count and integer threshold is checked.  Only the Python standard library is
used.  The universal pruning and convex-rearrangement argument is stated in
marked_head_profile.md; this program verifies its finite calculation.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

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
    return (points,) + layout_histograms(points)


def layout_histograms(points):
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
    return sorted(histograms), layouts, maxima


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


def elementary_comparison(old_cases, integer_theta):
    """Check the elementary old bounds, their transfer, and rational law."""
    bounds = {16: {1: 22, 2: 10, 3: 5, 4: 2, 6: 0},
              17: {1: 25, 2: 11, 3: 5, 4: 2, 6: 0}}
    old_checks = []
    for shape, points, histograms, layouts in old_cases:
        n = len(points)
        maxima = {t: max(sum(count * max(k - t, 0)
                             for k, count in enumerate(h, 1)) for h in histograms)
                  for t in bounds[n]}
        require(all(maxima[t] <= bounds[n][t] for t in maxima),
                "elementary old-profile bounds hold for every layout")
        old_checks.append({"shape": shape, "test_layouts": layouts,
                           "exact_old_profile_at_1_2_3_4_6": list(maxima.values())})

    def phi(n, t):
        if t >= 6:
            return Fraction(0)
        knots = sorted(bounds[n])
        require(t >= 1, "old interpolation domain")
        for a, b in zip(knots, knots[1:]):
            if a <= t <= b:
                return Fraction(bounds[n][a]) + (t - a) * Fraction(
                    bounds[n][b] - bounds[n][a], b - a)
        raise RuntimeError("old interpolation interval")

    def transfer(n, t):
        return (5 * phi(n, t) + 2 * phi(n, t / 2)) / (74 if n == 16 else 77)

    knots = list(map(Fraction, (2, 3, 4, 6, 8, 12)))
    crossings = []
    for a, b in zip(knots, knots[1:]):
        da = transfer(17, a) - transfer(16, a)
        db = transfer(17, b) - transfer(16, b)
        if da * db < 0:
            crossings.append(a - da * (b - a) / (db - da))
    require(crossings == [Fraction(117, 22)], "unique interior transfer crossing")
    atoms = {Fraction(2): Fraction(3, 7), Fraction(3): Fraction(15, 77),
             Fraction(4): Fraction(18, 77), Fraction(117, 22): Fraction(2, 259),
             Fraction(6): Fraction(7, 74), Fraction(8): Fraction(1, 37),
             Fraction(12): Fraction(1, 74)}
    require(sum(atoms.values()) == 1 and min(atoms.values()) > 0,
            "fractional comparison probability law")

    def profile(t):
        return sum(p * max(w - t, 0) for w, p in atoms.items())

    # Both sides are affine between this complete set of knots and crossings.
    for t in knots + crossings:
        require(profile(t) == max(transfer(n, t) for n in (16, 17)),
                "fractional profile equals the elementary transfer envelope")
    for t in map(Fraction, (0, 1, 2)):
        require(profile(t) == Fraction(37, 11) - t,
                "low-threshold continuation")
    require([profile(Fraction(t)) for t in THRESHOLDS] == integer_theta,
            "fractional and integer comparators agree at integer thresholds")
    crossing = crossings[0]
    integer_at_crossing = ((6 - crossing) * integer_theta[5]
                          + (crossing - 5) * integer_theta[6])
    require(integer_at_crossing > profile(crossing), "strict fractional improvement")
    full_histograms, full_layouts, _ = layout_histograms(list(range(45)))
    full_high = [max(sum(count * max(k - t, 0) for k, count in enumerate(h, 1))
                     for h in full_histograms) for t in (4, 5, 6)]
    require(full_high == [2, 1, 0], "full-period old upper-tail bound")
    moment = sum(w * w * p for w, p in atoms.items())
    require(moment == Fraction(909287, 62678), "exact fractional second moment")
    return {
        "old_profile_thresholds": [1, 2, 3, 4, 6],
        "old_profile_bounds": {str(n): list(row.values()) for n, row in bounds.items()},
        "old_case_checks": old_checks,
        "transfer_formula": "(5*phi_n(t)+2*phi_n(t/2))/D_n, D_16=74, D_17=77",
        "transfer_knots": list(map(str, knots)),
        "transfer_values": {str(n): [str(transfer(n, t)) for t in knots] for n in (16, 17)},
        "crossing": str(crossing),
        "auxiliary_atoms": {str(w): str(p) for w, p in atoms.items()},
        "mean": str(sum(w * p for w, p in atoms.items())),
        "second_moment": str(moment),
        "second_moment_reduction_from_integer_law": str(Fraction(41336, 2849) - moment),
        "profile_at_crossing": str(profile(crossing)),
        "integer_profile_at_crossing": str(integer_at_crossing),
        "full_period_old_layouts": full_layouts,
        "full_period_old_profile_at_4_5_6": full_high,
        "all_measure_upper_tail_identity": "Theta_mu(t)=(12-t)*max_x(mu(x)), 8<=t<=12",
        "universal_supported_law_minimax": "(12-t)/74, 8<=t<=12",
    }


def fixed_marginal_obstruction():
    classes = ((3, 0), (9, 4), (5, 0), (15, 11), (45, 37), (7, 0),
               (21, 8), (63, 2), (35, 3), (105, 53), (315, 173))
    old = [x for x in range(45) if all(x % d != a for d, a in classes[:5])]
    survivors = [x for x in range(315) if all(x % d != a for d, a in classes)]
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    require({d for d, _ in classes} == set(divisors) - {1}, "obstruction labels")
    centre = 83
    fibres = Counter(x % 45 for x in survivors)
    old_load = {x: sum(x % d == centre % d for d in (1,) + MODULI) for x in old}
    require(len(old) == 16 and len(survivors) == 75, "obstruction survivor counts")
    require(all(fibres[x] == 7 - old_load[x] for x in old), "obstruction exact fibres")
    mu = {x: Fraction(1, len(old) * fibres[x % 45]) for x in survivors}
    require(sum(mu.values()) == 1, "fixed uniform old marginal normalization")
    load = {x: sum(x % d == centre % d for d in divisors) for x in survivors}
    for x in old:
        y = old_load[x]
        actual = Counter(load[v] for v in survivors if v % 45 == x)
        desired = Counter({2 * y: 1})
        if y < 6:
            desired[y] += 6 - y
        require(actual == desired, "obstruction conditional load law")
    mass = max(mu.values())
    require(mass == Fraction(1, 16) and mu[centre] == mass, "obstruction maximum atom")
    second = sum(mu[x] * load[x] ** 2 for x in survivors)
    require(second == Fraction(1427, 80), "obstruction second moment")
    require(all(sum(mu[x] * max(load[x] - t, 0) for x in survivors)
                == Fraction(12 - t, 16) for t in range(8, 13)), "obstruction upper tail")
    return {
        "original_classes": [list(pair) for pair in classes], "test_centre": centre,
        "old_survivors": len(old), "complete_survivors": len(survivors),
        "old_load_histogram": {str(k): n for k, n in sorted(Counter(old_load.values()).items())},
        "load_probabilities": {str(k): str(sum(mu[x] for x in survivors if load[x] == k))
                               for k in sorted(set(load.values()))},
        "mean": str(sum(mu[x] * load[x] for x in survivors)), "second_moment": str(second),
        "maximum_atom": str(mass), "upper_tail": "(12-t)/16, 8<=t<=12",
    }
