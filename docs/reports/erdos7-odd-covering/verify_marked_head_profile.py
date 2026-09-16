#!/usr/bin/env python3
"""Verify the complete 315 marked-head convex profile using exact arithmetic.

The adjacent fixed certificate contains finite results, not executable input.
Every old-head layout histogram, ordered histogram pair, integer survivor
count and integer threshold is checked.  Only the Python standard library is
used.  The universal pruning and convex-rearrangement argument is stated in
marked_head_profile.md; this program verifies its finite calculation.
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


def deletion_weighted_comparison(old_cases, integer_theta):
    """Keep each original mixed7 cylinder in the numerator/denominator bound."""
    hinge_bounds = (
        ('271/86', '185/86', '100/81', '61/81', '16/39', '7/26'),
        ('263/85', '178/85', '101/84', '30/41', '32/79', '21/79'),
        ('263/85', '178/85', '101/84', '30/41', '32/79', '21/79'),
        ('3', '2', '89/75', '11/15', '2/5', '4/15'),
        ('234/77', '157/77', '91/76', '14/19', '2/5', '4/15'),
        ('234/77', '157/77', '91/76', '14/19', '2/5', '4/15'),
    )
    square_bounds = ('1091/82', '1103/85', '1103/85',
                     '965/76', '993/77', '993/77')
    require(len(old_cases) == 6, 'all six deletion-coupled canonical shapes')
    results = []
    for case_index, (shape, points, _, expected_layouts) in enumerate(old_cases):
        n = len(points)
        cylinders = [[tuple(i for i, x in enumerate(points) if x % d == a)
                      for a in sorted({x % d for x in points})] for d in MODULI]
        loads = []
        for chosen in product(*cylinders):
            load = [1] * n
            for cylinder in chosen:
                for i in cylinder:
                    load[i] += 1
            loads.append(tuple(load))
        require(len(loads) == expected_layouts, 'all effective old test layouts')
        hinge_sums = [tuple(sum(max(v - t, 0) for v in a) for t in range(6))
                      for a in loads]
        maxima = [max(h[t] for h in hinge_sums) for t in range(6)]
        square_maximum = max(sum(v*v for v in a) for a in loads)
        constants = [Fraction(c) for c in hinge_bounds[case_index]]
        square_constant = Fraction(square_bounds[case_index])
        minimum_slacks = [None] * 7

        def scaled_slack(values, cost_upper, c):
            positive = [max(c.numerator - c.denominator * v, 0) for v in values]
            deletion_cap = sum(max(sum(positive[i] for i in cylinder)
                                   for cylinder in group) for group in cylinders)
            return 6*n*c.numerator - c.denominator*cost_upper - deletion_cap

        for a, hinges_a in zip(loads, hinge_sums):
            slacks = []
            for t, c in enumerate(constants):
                values = [max(v-t, 0) for v in a]
                # (u+v-t)+ <= (u-k)+ + (v-(t-k))+ for every k.
                joint_upper = min(hinges_a[k] + maxima[t-k] for k in range(t+1))
                slacks.append(scaled_slack(values, 5*hinges_a[t] + joint_upper, c))
            squares = [v*v for v in a]
            # max_B sum A*B = sum A + sum_d max_C sum_C A.
            cross_upper = sum(a) + sum(max(sum(a[i] for i in cylinder)
                                          for cylinder in group) for group in cylinders)
            square_cost = 6*sum(squares) + 2*cross_upper + square_maximum
            slacks.append(scaled_slack(squares, square_cost, square_constant))
            require(min(slacks) >= 0, 'every deletion-weighted hinge and square inequality')
            minimum_slacks = [v if old is None else min(old, v)
                              for old, v in zip(minimum_slacks, slacks)]
        require(minimum_slacks == [0]*7, 'all seven stated cap bounds attain equality')
        results.append({
            'shape': shape, 'old_survivors': n, 'test_layouts': len(loads),
            'maximum_old_hinge_sums_at_0_through_5': maxima,
            'maximum_old_square_sum': square_maximum,
            'hinge_bounds_at_0_through_5': list(hinge_bounds[case_index]),
            'second_moment_bound': str(square_constant),
            'minimum_scaled_slacks': minimum_slacks,
        })

    low = [max(Fraction(row[t]) for row in hinge_bounds) for t in range(6)]
    knots = list(zip(map(Fraction, range(6)), low)) + [
        (Fraction(t), integer_theta[t]) for t in (6, 8, 12)]
    slopes = [(b[1]-a[1])/(b[0]-a[0]) for a, b in zip(knots, knots[1:])] + [Fraction(0)]
    require(slopes[0] == -1 and all(a <= b for a, b in zip(slopes, slopes[1:])),
            'hinge chord upper profile is a convex probability profile')
    atoms = {knots[i][0]: slopes[i]-slopes[i-1] for i in range(1, len(knots))
             if slopes[i] != slopes[i-1]}
    require(sum(atoms.values()) == 1 and min(atoms.values()) > 0,
            'deletion-coupled comparison atoms form a probability law')
    for t, value in knots:
        require(sum(p*max(w-t, 0) for w, p in atoms.items()) == value,
                'comparison law has each certified hinge knot')
    for t in range(6, 13):
        require(sum(p*max(w-t, 0) for w, p in atoms.items()) == integer_theta[t],
                'new law retains the certified sharp upper profile')
    mean = sum(w*p for w, p in atoms.items())
    second = sum(w*w*p for w, p in atoms.items())
    actual_second = max(map(Fraction, square_bounds))
    require((mean, second, actual_second) == (
        Fraction(271, 86), Fraction(45292361, 3350646), Fraction(1091, 82)),
        'exact simultaneous uniform-law moment constants')
    return {
        'law': 'uniform on the actual complete survivors after canonical old-head pruning',
        'cases': results,
        'old_test_layouts': sum(r['test_layouts'] for r in results),
        'integer_cap_inequalities': 7*sum(r['test_layouts'] for r in results),
        'hinge_knots': {str(t): str(v) for t, v in knots},
        'auxiliary_atoms': {str(w): str(p) for w, p in atoms.items()},
        'mean': str(mean), 'comparison_second_moment': str(second),
        'actual_second_moment_upper': str(actual_second),
        'sharpness': 'Zero cap slack alone does not establish actual-family sharpness; the mean and first hinge are separately witnessed.',
    }


def prime11_residual_geometry():
    original = ((3, 0), (9, 4), (5, 0), (15, 11), (45, 1), (7, 0),
                (21, 8), (63, 16), (35, 17), (105, 32), (315, 47))
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    points = [x for x in range(315) if all(x % d != a for d, a in original)]
    require(len(points) == 74, 'actual old survivor count')
    cylinders = {d: [[x for x in points if x % d == a]
                     for a in sorted({x % d for x in points})] for d in divisors[1:]}
    scalar_caps = [max(map(len, cylinders[d])) for d in divisors[1:]]
    pair = []
    for centre in (33, 301):
        load = {x: sum(x % d == centre % d for d in divisors) for x in points}
        histogram = dict(sorted(Counter(load.values()).items()))
        require(histogram == {1: 38, 2: 31, 4: 5}, 'identical complete-load histogram')
        # For h(v)=v^2 and c=2, (c-h(load))_+ is exactly 1_{load=1}.
        weights = {x: max(2-load[x]**2, 0) for x in points}
        require(all(weights[x] == int(load[x] == 1) for x in points), 'exact residual weight')
        caps = [max(sum(weights[x] for x in cylinder) for cylinder in cylinders[d])
                for d in divisors[1:]]
        pair.append({'test_centre': centre, 'load_histogram': {str(k):v for k,v in histogram.items()},
                     'residual_cylinder_caps': caps, 'residual_capacity': sum(caps)})
    require([r['residual_capacity'] for r in pair] == [98, 114],
            'same scalar profile, distinct residual cylinder capacities')
    require(sum(scalar_caps) == 142 and 114 < 142, 'strict improvement over scalar cap')

    new_mixed = ((33, 23), (55, 2), (77, 69), (99, 92), (165, 137),
                 (231, 83), (385, 62), (495, 272), (693, 20),
                 (1155, 692), (3465, 3422))
    centre = 272
    require(centre in points, 'emptied old point was an old survivor')
    for i, ((modulus, residue), d) in enumerate(zip(new_mixed, divisors[1:])):
        require(modulus == 11*d and residue % d == centre % d
                and residue % 11 == 1+i % 10, 'actual mixed cofactor and digit assignment')
    full_original = original + ((11, 0),) + new_mixed
    require(len(full_original) == 23 and {d for d,a in full_original}
            == {d for d in range(2, 3466) if 3465 % d == 0},
            'exactly one original class for every nonunit divisor of3465')
    full = [x for x in range(3465) if all(x % d != a for d,a in full_original)]
    counts = Counter(x % 315 for x in full)
    empty = [x for x in points if counts[x] == 0]
    require(empty == [272] and len(full) == 627, 'exact empty fibre and full survivor count')
    fibre_histogram = dict(sorted(Counter(counts[x] for x in points).items()))
    require(sum(r*n for r,n in fibre_histogram.items()) == len(full), 'fibre accounting')
    return {
        'schema': 'prime11-residual-geometry-v1',
        'original315_classes': [list(pair) for pair in original],
        'old_survivor_count': len(points), 'nonunit_old_divisors': divisors[1:],
        'unweighted_cylinder_caps': scalar_caps, 'unweighted_capacity': sum(scalar_caps),
        'same_histogram_pair': pair,
        'empty_fibre_extension': {
            'pure11_class': [11,0], 'mixed11_classes': [list(pair) for pair in new_mixed],
            'old_coherent_centre': centre, 'empty_old_fibres': empty,
            'full_survivor_count': len(full),
            'fibre_size_histogram': {str(k):v for k,v in fibre_histogram.items()},
        },
    }


def residual_mass_next_label_obstruction():
    classes = ((3, 0), (9, 4), (5, 0), (15, 11), (45, 1), (7, 0),
               (21, 8), (63, 16), (35, 17), (105, 32), (315, 47))
    old = [x for x in range(315) if all(x % d != a for d, a in classes)]
    require(len(old) == 74 and sum(x % 3 == 1 for x in old) == 36,
            'actual sharp head and ternary root sizes')
    profiles = []
    cases = []
    for mixed in (1, 13):
        extended = classes + ((11, 0), (33, mixed))
        survivors = [x for x in range(3465) if all(x % d != a for d, a in extended)]
        counts = Counter(x % 315 for x in survivors)
        profile = [Fraction(counts[x], 11) for x in old]
        profiles.append(profile)
        require(len(survivors) == 704 and all(counts[x] == (9 if x % 3 == 1 else 10)
                                            for x in old),
                'identical residual masses at every individual old point')
        base_classes = extended + ((13, 0),)
        base = [x for x in range(45045) if all(x % d != a for d, a in base_classes)]
        hits = sum(x % 143 == 1 for x in base)
        cases.append({
            'mixed33_residue': mixed, 'mixed33_11_digit': mixed % 11,
            'survivors_mod3465': len(survivors),
            'raw_11_survival': str(Fraction(len(survivors), 74*11)),
            'surviving11_digit1_probability': str(Fraction(sum(x % 11 == 1 for x in survivors),
                                                         len(survivors))),
            'base_survivors_mod45045': len(base), 'fixed143_query_hits': hits,
            'fixed143_query_probability': str(Fraction(hits, len(base))),
        })
    require(profiles[0] == profiles[1], 'same complete old-point residual vector')
    require([row['fixed143_query_probability'] for row in cases] == ['19/4224', '37/4224'],
            'same residual vector has different next original cofactor charge')
    return {
        'head_classes': [list(pair) for pair in classes], 'head_survivors': len(old),
        'root1_head_points': 36,
        'same_old_point_residual_masses': {'root1': '9/11', 'other_root': '10/11'},
        'same_normalized_head_marginal': True,
        'next_original_query': {'modulus': 143, 'residue': 1}, 'cases': cases,
        'conclusion': 'Head-indexed residual masses do not determine the next labelled cofactor probability.',
    }


def conditioned_3465_comparison(old_deletion_result, signed_deletion_result):
    """Exact upper-quantile transfer of the already checked uniform315 law."""
    old = {Fraction(x): Fraction(p)
           for x, p in old_deletion_result['auxiliary_atoms'].items()}
    require(min(old) >= 1 and min(old.values()) > 0 and sum(old.values()) == 1,
            'old deletion comparison is a probability law supported above one')
    mean = sum(x*p for x, p in old.items())
    actual_second = Fraction(signed_deletion_result['actual_second_moment_upper'])
    require(mean == Fraction(old_deletion_result['mean']) == Fraction(271, 86),
            'same uniform315 mean bound supplies the mixed11 deletion capacity')
    require(actual_second == Fraction(1131, 86)
            and actual_second < Fraction(old_deletion_result['actual_second_moment_upper']),
            'same uniform315 law has the improved signed-deletion square bound')
    capacity = mean - 1
    survival = 1 - capacity/10
    product_law = {}
    for x, p in old.items():
        for y, weight in ((1, Fraction(9, 10)), (2, Fraction(1, 10))):
            product_law[x*y] = product_law.get(x*y, Fraction(0)) + p*weight
    require(sum(product_law.values()) == 1,
            'unconditioned colour concentration comparator has total mass one')
    remainder = 1-survival
    atoms = {}
    removed = {}
    for x, p in sorted(product_law.items()):
        cut = min(p, remainder)
        remainder -= cut
        if cut:
            removed[x] = cut
        if p > cut:
            atoms[x] = (p-cut)/survival
    require(remainder == 0 and min(atoms.values()) > 0 and sum(atoms.values()) == 1,
            'exact upper survival-quantile is a positive probability law')
    require(set(removed) == {Fraction(1), Fraction(2)} and min(atoms) == 2,
            'conditioning trims all atom one and part of atom two')

    def call(law, t):
        return sum(p*max(x-t, 0) for x, p in law.items())

    # Independently obtain the same law by repairing the signed unit-loss law.
    signed = {x: p/survival for x, p in product_law.items()}
    signed[Fraction(1)] -= (1-survival)/survival
    require(signed[Fraction(1)] < 0,
            'signed unit-loss comparator has a deficit at one')
    signed[Fraction(2)] += signed.pop(Fraction(1))
    require(signed == atoms,
            'unit-loss deficit transfer equals exact upper-quantile conditioning')

    hinges = [call(atoms, Fraction(t)) for t in range(25)]
    for t in range(2, 25):
        require(hinges[t] == (9*call(old, Fraction(t))
                              + 2*call(old, Fraction(t, 2)))/(10-capacity),
                'new call profile equals the scaled product call for t at least two')
    require(hinges[:3] == [hinges[2]+2, hinges[2]+1, hinges[2]],
            'new call profile has slope minus one below two')
    require(all(a >= b >= 0 for a, b in zip(hinges, hinges[1:]))
            and all(a-2*b+c >= 0 for a, b, c in zip(hinges, hinges[1:], hinges[2:]))
            and hinges[-1] == 0,
            'integer hinge profile is decreasing convex and ends at zero')
    new_mean = sum(x*p for x, p in atoms.items())
    comparator_second = sum(x*x*p for x, p in atoms.items())
    separate_second = 1+(Fraction(13, 10)*actual_second-1)/survival
    chosen_second = min(comparator_second, separate_second)
    require((survival, new_mean, separate_second, comparator_second, chosen_second) == (
        Fraction(135, 172), Fraction(4816, 1215), Fraction(14518, 675),
        Fraction(1746200, 80919), Fraction(14518, 675)),
        'exact conditioned3465 survival and simultaneous moment bounds')
    return {
        'law': 'uniform315 times ten pure11 survivors, conditioned on the actual mixed11 survivor event',
        'head_modulus': 3465,
        'prime_heights': [[3, 2], [5, 1], [7, 1], [11, 1]],
        'first_tail_prime': 13,
        'input315_actual_second_moment_upper': str(actual_second),
        'mixed11_deleted_mass_upper': str(1-survival),
        'survival_lower': str(survival),
        'removed_product_mass': {str(x): str(p) for x, p in removed.items()},
        'auxiliary_atoms': {str(x): str(p) for x, p in atoms.items()},
        'hinges_at_0_through_24': list(map(str, hinges)),
        'mean': str(new_mean),
        'separate_actual_second_moment_upper': str(separate_second),
        'comparison_second_moment': str(comparator_second),
        'actual_second_moment_upper': str(chosen_second),
    }


def uniform315_mean_sharpness():
    """Literal actual-family witness for the sharp uniform315 mean and first hinge."""
    original = ((3, 0), (9, 4), (5, 0), (15, 1), (45, 37), (7, 0),
                (21, 1), (35, 9), (63, 52), (105, 4), (315, 187))
    test = ((1, 0), (3, 2), (5, 3), (9, 2), (15, 2), (45, 2),
            (7, 6), (21, 20), (35, 13), (63, 20), (105, 62), (315, 272))
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    require(sorted(d for d, _ in original) == divisors[1:],
            'mean witness has every nonunit original divisor exactly once')
    require(sorted(d for d, _ in test) == divisors,
            'mean witness has a complete test layout including the unit divisor')
    require(all(0 <= a < d for d, a in original+test),
            'mean witness residues are canonical')
    old = [x for x in range(45) if all(x % d != a for d, a in original[:5])]
    require(len(old) == 17, 'mean witness uses the first canonical old shape')
    survivors = [x for x in range(315) if all(x % d != a for d, a in original)]
    loads = [sum(x % d == a for d, a in test) for x in survivors]
    histogram = dict(sorted(Counter(loads).items()))
    require(len(survivors) == 86 and sum(loads) == 271,
            'literal mean witness has86 survivors and total load271')
    require(histogram == {1: 5, 2: 28, 3: 29, 4: 11, 5: 5, 6: 6, 8: 1, 10: 1},
            'exact mean-witness test-load histogram')
    mean = Fraction(sum(loads), len(survivors))
    first_hinge = Fraction(sum(max(load-1, 0) for load in loads), len(survivors))
    require(mean == Fraction(271, 86) and first_hinge == Fraction(185, 86),
            'actual uniform survivor law attains both certified low hinge bounds')
    return {
        'original_classes': [list(pair) for pair in original],
        'test_classes': [list(pair) for pair in test],
        'survivor_count': len(survivors),
        'test_load_histogram': {str(k): v for k, v in histogram.items()},
        'test_load_sum': sum(loads),
        'mean': str(mean),
        'hinge_at1': str(first_hinge),
        'scope': 'sharp for the uniform law on complete canonical-pruned315 survivors; no minimax claim',
    }


def residual_prefix_depletion_obstruction():
    from math import gcd, lcm
    from collections import Counter
    from fractions import Fraction

    def require(condition, message):
        if not condition:
            raise ValueError(message)

    def crt_pair(a, d, b, p):
        return a % d + d * ((b - a) * pow(d, -1, p) % p)

    def kernel(base, forbidden, delta):
        alpha = Fraction(len(forbidden), len(base))
        theta = min(alpha, delta)
        row = {y: ((alpha-delta)/(len(base)*alpha*(1-delta)) if alpha > delta else Fraction(0))
               if y in forbidden else Fraction(1, len(base))/(1-theta) for y in base}
        require(sum(row.values()) == 1 and min(row.values()) >= 0,
                'normalized distortion kernel reconstructed from actual union')
        return row

    div315 = [d for d in range(1, 316) if 315 % d == 0]
    div3465 = [d for d in range(1, 3466) if 3465 % d == 0]
    head = [(d, 0) for d in div315 if d > 1]
    old = [x for x in range(315) if all(x % d != a for d, a in head)]
    require(old == [x for x in range(315) if gcd(x, 315) == 1] and len(old) == 144,
            'actual head survivors are exactly the144 units')
    cofactors11 = (3, 5, 7, 15, 21, 35, 105, 9, 45)
    mixed11 = [(11*d, crt_pair(1, d, colour, 11)) for colour, d in enumerate(cofactors11, 1)]
    centre = crt_pair(1, 315, 10, 11)
    mixed31 = [(31*d, crt_pair(centre % d, d, colour, 31))
               for colour, d in enumerate(div3465[1:], 1)]
    original = head + [(11, 0)] + mixed11 + [(31, 0)] + mixed31
    require(len(original) == len({d for d, _ in original}) == 45,
            'exactly45 distinct original moduli')
    require(all(d > 1 and d % 2 and 0 <= a < d for d, a in original),
            'every original class has a valid distinct nontrivial odd modulus')
    require(lcm(*(d for d, _ in original)) == 107415, 'actual full least common multiple')
    delta = Fraction(2, 5)
    total = loss11 = loss31 = overlap = retained31 = Fraction(0)
    head_high = []
    n_counts = Counter()
    positive_charge_head = set()
    positive11_head = set()
    rows11 = {}
    for x in old:
        lifts = {y: crt_pair(x, 315, y, 11) for y in range(1, 11)}
        bad11 = {y for y, v in lifts.items() if any(v % d == a for d, a in mixed11)}
        n = len(bad11)
        require(n == sum(x % d == 1 for d in cofactors11), 'actual11 colours equal original cofactor hits')
        A, B, C, D = (int(x % d == 1) for d in (3, 9, 5, 7))
        require(n == (1+C)*((1+A)*(1+D)+B)-1, 'symbolic nine-label head count')
        n_counts[n] += 1
        k11 = kernel(tuple(range(1, 11)), bad11, delta)
        rows11[x] = (bad11, k11)
        charge11 = sum(k11[y] for y in bad11)
        require(charge11 == Fraction(max(n-4, 0), 6), 'exact conditional11 charge')
        if charge11 > 0:
            positive11_head.add(x)
        ell = sum(x % d == 1 % d for d in div315)
        if ell > 6:
            head_high.append({'head': x, 'coherent_load': ell, 'active11_labels': n,
                              'surviving_row_mass': str(1-charge11),
                              'free11_digit10_mass': str(k11[10])})
        for y, old_v in lifts.items():
            bad31 = {z for z in range(1, 31)
                     if any(crt_pair(old_v, 3465, z, 31) % d == a for d, a in mixed31)}
            literal_load = sum(old_v % d == centre % d for d in div3465)
            require(literal_load == ell*(1+int(y == 10)) and len(bad31) == literal_load-1,
                    'literal original31 labels have exactly one missing unit')
            k31 = kernel(tuple(range(1, 31)), bad31, delta)
            charge31 = sum(k31[z] for z in bad31)
            require(charge31 == Fraction(max(literal_load-13, 0), 18), 'exact conditional31 charge')
            if charge31 > 0:
                positive_charge_head.add(x)
            for z, conditional in k31.items():
                mass = Fraction(1, 144)*k11[y]*conditional
                total += mass
                if y in bad11:
                    loss11 += mass
                if z in bad31:
                    loss31 += mass
                    if y in bad11:
                        overlap += mass
                    else:
                        retained31 += mass
    require(total == 1, 'entire normalized physical chain has massone')
    require((loss11, loss31, overlap, retained31) == (
        Fraction(1, 54), Fraction(17, 15552), Fraction(0), Fraction(17, 15552)),
        'exact first charge, later charge, intersection, and survivor-weighted later charge')
    require(positive_charge_head == {1, 106, 211} and positive_charge_head <= positive11_head,
            'every head carrying later charge was positively depleted')
    require({n: count for n, count in n_counts.items() if n > 4} == {5: 5, 7: 2, 9: 1},
            'complete head multiplicities above the first charge threshold')
    conditioned = retained31/(1-loss11)
    require(conditioned == Fraction(17, 15264) > loss31, 'normalization increases the later charge')

    # The all-height proof is in the accompanying note. These checks independently
    # reconstruct every prefix mass and every hinge segment for heights1..3.
    height_checks = []
    bad11, k11 = rows11[1]
    for height in range(1, 4):
        row = {y: k11[y % 11]/11**(height-1) for y in range(11**height) if y % 11 != 0}
        good = {y: v for y, v in row.items() if y % 11 not in bad11}
        prefix_caps = []
        for e in range(1, height+1):
            before = [sum((v for y, v in row.items() if y % (11**e) == a), Fraction(0))
                      for a in range(11**e)]
            after = [sum((v for y, v in good.items() if y % (11**e) == a), Fraction(0))
                     for a in range(11**e)]
            require(max(before) == max(after) == Fraction(1, 6*11**(e-1)),
                    'all positive-depth actual unnormalized prefix maxima survive unchanged')
            prefix_caps.append(str(max(after)))
        for threshold in range(12, 12*(height+1)+1, 12):
            def excess(y):
                value = 12*(1+sum(y % (11**e) == 10 for e in range(1, height+1)))
                return max(value-threshold, 0)
            require(sum((v*excess(y) for y, v in row.items()), Fraction(0)) ==
                    sum((v*excess(y) for y, v in good.items()), Fraction(0)),
                    'all hinge knot values at threshold>=12 are unchanged by actual killing')
        height_checks.append({'height': height, 'row_mass_before': str(sum(row.values())),
                              'row_mass_after': str(sum(good.values())),
                              'equal_positive_depth_prefix_caps': prefix_caps})
    return {
        'head_modulus': 315, 'head_survivors': 144, 'lcm': 107415,
        'original_classes': [list(pair) for pair in original], 'original_modulus_count': len(original),
        'cofactor11_order': list(cofactors11), 'coherent_old_centre_mod3465': centre,
        'thresholds': {'11': str(delta), '31': str(delta)},
        'active11_label_histogram': {str(n): count for n, count in sorted(n_counts.items())},
        'later_charge_head_rows': head_high,
        'first_charge': str(loss11), 'later_charge_before_killing': str(loss31),
        'charge_event_intersection': str(overlap), 'later_charge_after_killing_raw': str(retained31),
        'remaining_mass_after11': str(1-loss11),
        'later_charge_after_conditioning11': str(conditioned),
        'all_later_charge_head_points_previously_depleted': True,
        'height_prefix_checks': height_checks,
    }


def signed_deletion_square_comparison(old_cases, old_deletion_result):
    """Exact signed union caps give the sharp prescribed uniform315 square bound."""
    bound = Fraction(1131, 86)
    require(len(old_cases) == 6 and len(old_deletion_result['cases']) == 6,
            'all canonical old shapes are covered')
    shape, points, _, expected_layouts = old_cases[0]
    require(shape == 'root1_same_other_column' and len(points) == 17
            and expected_layouts == 4760, 'signed square check selects the first canonical shape')
    moduli = (3, 5, 9, 15, 45)
    cylinders = [[sum(1 << i for i, x in enumerate(points) if x % d == a)
                  for a in sorted({x % d for x in points})] for d in moduli]
    unions = [{0}]
    for subset in range(1, 32):
        bit = subset & -subset
        label = bit.bit_length()-1
        unions.append({old | cylinder for old in unions[subset ^ bit]
                       for cylinder in [0]+cylinders[label]})

    def mask_sum(mask, values):
        total = 0
        while mask:
            bit = mask & -mask
            total += values[bit.bit_length()-1]
            mask ^= bit
        return total

    layouts = []
    for choices in product(*cylinders):
        load = tuple(1+sum(bool(mask & (1 << i)) for mask in choices)
                     for i in range(len(points)))
        layouts.append(load)
    require(len(layouts) == expected_layouts, 'all effective old test layouts enumerated')
    Q = max(sum(a*a for a in load) for load in layouts)
    require(Q == 130, 'old square maximum for the first canonical shape')
    screened = exact = 0
    signed_slacks = []
    for load in layouts:
        squares = [a*a for a in load]
        cross = sum(load)+sum(max(mask_sum(mask, load) for mask in group)
                             for group in cylinders)
        numerator = 6*sum(squares)+2*cross+Q
        weights = [bound.numerator-bound.denominator*a for a in squares]
        positive = [max(w, 0) for w in weights]
        clipped = sum(max(mask_sum(mask, positive) for mask in group)
                      for group in cylinders)
        allowance = 6*len(points)*bound.numerator-bound.denominator*numerator
        if clipped <= allowance:
            screened += 1
            continue
        exact += 1
        values = {mask: mask_sum(mask, weights) for mask in unions[31]}
        block = [max(values[mask] for mask in group) for group in unions]
        dp = [0]*32
        for subset in range(1, 32):
            anchor = subset & -subset
            first = subset
            best = 0
            while first:
                if first & anchor:
                    best = max(best, block[first]+dp[subset ^ first])
                first = (first-1) & subset
            dp[subset] = best
        require(dp[31] <= clipped, 'signed union cap refines the positive independent cap')
        slack = allowance-dp[31]
        require(slack >= 0, 'exact signed partition cap proves the proposed square bound')
        signed_slacks.append(slack)
    require(screened+exact == expected_layouts and signed_slacks
            and min(signed_slacks) == 0, 'all layouts bounded and signed bound attained algebraically')
    other_bounds = [Fraction(row['second_moment_bound'])
                    for row in old_deletion_result['cases'][1:]]
    require(all(c < bound for c in other_bounds),
            'existing bounds for the other five shapes are strictly smaller')

    original = ((3, 0), (9, 4), (5, 0), (15, 1), (45, 37), (7, 0),
                (21, 1), (35, 9), (63, 52), (105, 4), (315, 142))
    test = ((1, 0), (3, 2), (5, 3), (9, 2), (15, 8), (45, 38),
            (7, 6), (21, 20), (35, 13), (63, 20), (105, 83), (315, 83))
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    require(sorted(d for d, _ in original) == divisors[1:]
            and sorted(d for d, _ in test) == divisors,
            'sharp square witness has all original and test labels exactly once')
    require(all(0 <= a < d for d, a in original+test), 'square witness residues are canonical')
    require([x for x in range(45) if all(x % d != a for d, a in original[:5])] == points,
            'literal witness uses the canonical old survivor set checked above')
    survivors = [x for x in range(315) if all(x % d != a for d, a in original)]
    loads = [sum(x % d == a for d, a in test) for x in survivors]
    histogram = dict(sorted(Counter(loads).items()))
    require(len(survivors) == 86 and sum(loads) == 271
            and sum(a*a for a in loads) == 1131,
            'literal actual-family witness attains the mean and square bounds simultaneously')
    require(histogram == {1: 5, 2: 38, 3: 14, 4: 18, 6: 8, 8: 2, 12: 1},
            'literal sharp square witness histogram')
    return {
        'law': 'uniform on actual complete survivors after canonical old-head pruning',
        'actual_second_moment_upper': str(bound),
        'shape': shape, 'old_test_layouts': expected_layouts,
        'clipped_screened_layouts': screened, 'signed_union_dp_layouts': exact,
        'union_counts_by_label_subset': [len(group) for group in unions],
        'minimum_scaled_signed_slack': min(signed_slacks),
        'other_shape_square_bounds': list(map(str, other_bounds)),
        'sharp_witness': {
            'original_classes': [list(pair) for pair in original],
            'test_classes': [list(pair) for pair in test],
            'survivor_count': len(survivors),
            'test_load_histogram': {str(k): v for k, v in histogram.items()},
            'test_load_sum': sum(loads), 'test_load_square_sum': sum(a*a for a in loads),
            'mean': str(Fraction(sum(loads), len(survivors))),
            'hinge_at1': str(Fraction(sum(a-1 for a in loads), len(survivors))),
            'second_moment': str(Fraction(sum(a*a for a in loads), len(survivors))),
        },
        'sharpness': 'Sharp for the prescribed uniform law; no minimax claim over other supported laws.',
    }


def verify(expected):
    cases = []
    old_cases = []
    for root, category in product((1, 2), CATEGORIES):
        points, histograms, layouts, maxima = old_head(root, category)
        old_cases.append((f"root{root}_{category}", points, histograms, layouts))
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
    deletion_result = deletion_weighted_comparison(old_cases, theta)
    signed_result = signed_deletion_square_comparison(old_cases, deletion_result)
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
        "elementary_comparison": elementary_comparison(old_cases, theta),
        "fixed_marginal_obstruction": fixed_marginal_obstruction(),
        "deletion_weighted_comparison": deletion_result,
        "conditioned_3465_comparison": conditioned_3465_comparison(deletion_result, signed_result),
        "signed_deletion_square_comparison": signed_result,
        "uniform315_mean_sharpness": uniform315_mean_sharpness(),
        "residual_prefix_depletion_obstruction": residual_prefix_depletion_obstruction(),
        "prime11_residual_geometry": prime11_residual_geometry(),
        "residual_mass_next_label_obstruction": residual_mass_next_label_obstruction(),
    }
    require(result == expected, "computed exact result differs from the fixed certificate")
    print(json.dumps({"verified": True, "old_test_layouts": sum(r["test_layouts"] for r in cases),
                      "integer_hinge_cases": sum(r["integer_hinge_cases"] for r in cases),
                      "mean": result["mean"], "second_moment": result["second_moment"],
                      "deletion_weighted_inequalities": result["deletion_weighted_comparison"]["integer_cap_inequalities"],
                      "deletion_weighted_mean": result["deletion_weighted_comparison"]["mean"],
                      "deletion_weighted_actual_second": result["deletion_weighted_comparison"]["actual_second_moment_upper"],
                      "sharp_actual_second": signed_result["actual_second_moment_upper"],
                      "conditioned_3465_actual_second": result["conditioned_3465_comparison"]["actual_second_moment_upper"]}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("marked_head_profile_certificate.json"))
    args = parser.parse_args()
    verify(json.loads(args.certificate.read_text()))


if __name__ == "__main__":
    main()
