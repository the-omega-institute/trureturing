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


def uniform315_energy_rebate_obstruction(signed_square_result):
    from collections import Counter
    from fractions import Fraction as F
    from math import lcm

    def require(condition, message):
        if not condition:
            raise RuntimeError(message)

    def crt(a, d, b, p):
        require(d % p != 0, 'coprime CRT factors')
        return a % d + d*((b-a)*pow(d, -1, p)%p)

    def kernel(forbidden, p, delta):
        base=tuple(range(1,p))
        alpha=F(len(forbidden),len(base))
        theta=min(alpha,delta)
        row={y: (F(1,len(base))/(1-theta) if y not in forbidden else
                 ((alpha-delta)/(len(base)*alpha*(1-delta)) if alpha>delta else F(0)))
             for y in base}
        require(sum(row.values())==1 and min(row.values())>=0,'actual normalized clipped row')
        return row

    head=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),(21,1),(35,9),(63,52),(105,4),(315,142)]
    test=[(1,0),(3,2),(5,3),(9,2),(15,8),(45,38),(7,6),(21,20),(35,13),(63,20),(105,83),(315,83)]
    require(signed_square_result['actual_second_moment_upper']=='1131/86', 'same verified universal upper bound')
    require(signed_square_result['sharp_witness']['original_classes']==[list(v) for v in head], 'same sharp actual head family')
    require(signed_square_result['sharp_witness']['test_classes']==[list(v) for v in test], 'same verified energy-maximizing test layout')
    survivors=[x for x in range(315) if all(x%d!=a for d,a in head)]
    load={x:sum(x%d==a for d,a in test) for x in survivors}
    require(len(survivors)==86 and sum(a*a for a in load.values())==1131,'published sharp head witness')
    centres=[x for x in survivors if load[x]==1]
    require(len(centres)==5,'five minimal-load points of the energy maximizer')
    centre=centres[0]
    cofactors=[35,45,63,105,315]
    mixed11=[(11*d,crt(centre,d,i,11)) for i,d in enumerate(cofactors,1)]
    full_test=test+[(11*d,crt(a,d,10,11)) for d,a in test]
    require(len(full_test)==24 and len({d for d,a in full_test})==24,'complete3465test layout')
    mixed31=[(31*d,crt(a,d,i,31)) for i,(d,a) in enumerate(full_test[1:],1)]
    # full_test[1:] omits only the original unit; it retains the pure11 test label.
    family=head+[(11,0)]+mixed11+[(31,0)]+mixed31
    require(len(family)==len({d for d,a in family})==41,'41distinct original moduli')
    require(all(d>1 and d%2 and 0<=a<d for d,a in family),'ordinary odd congruence family')
    require(lcm(*(d for d,a in family))==107415,'actual lcm')
    delta=F(2,5)
    charge11=charge31=intersection=retained31=F(0)
    base_energy=residual_energy=F(0)
    cap_before={};cap_after={};row_mass={};charge_support=[]
    charge31_head=Counter(); hit_hist=Counter(); joint_mass=F(0)
    for x in survivors:
        lifts={y:crt(x,315,y,11) for y in range(1,11)}
        bad={y for y,v in lifts.items() if any(v%d==a for d,a in mixed11)}
        n=len(bad)
        require(n==sum(x%d==centre%d for d in cofactors),'different colours count original cofactor hits')
        require((n==5)==(x==centre),'firstcharge only at chosen minimal-loadpoint')
        hit_hist[n]+=1
        k=kernel(bad,11,delta)
        r=sum(v for y,v in k.items() if y not in bad)
        b=1-r
        require(b==(F(1,6) if x==centre else 0),'rowcharge')
        row_mass[x]=r
        cap_before[x]=max(k.values())
        cap_after[x]=max(k[y] if y not in bad else 0 for y in k)
        require(cap_before[x]==cap_after[x], 'positive-depth actual prefix cap unchanged')
        charge11+=b/86
        base_energy+=F(load[x]**2,86)
        residual_energy+=r*F(load[x]**2,86)
        if b: charge_support.append(x)
        for y,v in lifts.items():
            extended_load=sum(v%d==a for d,a in full_test)
            require(extended_load==load[x]*(1+(y==10)),'same old energy-maximizing layout in both layers')
            forbidden31={z for z in range(1,31) if any(crt(v,3465,z,31)%d==a for d,a in mixed31)}
            require(len(forbidden31)==extended_load-1,'actual original31labels miss exactly one unit')
            k31=kernel(forbidden31,31,delta)
            b31=sum(k31[z] for z in forbidden31)
            require(b31==F(max(extended_load-13,0),18),'actual latercharge from complete headload')
            if b31: charge31_head[x]+=1
            mass=F(1,86)*k[y]
            joint_mass+=mass*sum(k31.values())
            charge31+=mass*b31
            if y in bad: intersection+=mass*b31
            else: retained31+=mass*b31
    require(joint_mass==1,'same actual full normalized physicalchain')
    require(charge11==F(1,516),'firstcharge')
    require(base_energy==F(1131,86),'old sharp energy')
    require(residual_energy==base_energy-charge11,'only unavoidable unit-mass energyloss')
    require(intersection==0 and retained31==charge31 and charge31>0,'zero latercharge intersection despite positivecharge')
    require(centre not in charge31_head,'latercharge entirely outside firstcharge head support')
    require(cap_before==cap_after,'all depthone cap weights identical')
    conditioned=retained31/(1-charge11)
    require(conditioned>charge31,'normalizing afterdeletion increases futurecharge')
    normalized_old_gamma=residual_energy/(1-charge11)
    require(normalized_old_gamma==F(1357,103)>base_energy,
            'conditioning the old marginal increases its exact complete-layout energy')
    height_checks=[]
    for height in range(1,4):
        lifted_family=family+([(11**height,0)] if height>1 else [])
        require(len(lifted_family)==len({d for d,a in lifted_family}), 'higher pure class preserves distinctness')
        require(lcm(*(d for d,a in lifted_family))==315*31*11**height,'actual higher-height lcm')
        for x in survivors:
            forbidden_roots={i for i,d in enumerate(cofactors,1) if x%d==centre%d}
            k=kernel(forbidden_roots,11,delta)
            for depth in range(1,height+1):
                before={a:k[a%11]/11**(depth-1) for a in range(11**depth) if a%11}
                after={a:(v if a%11 not in forbidden_roots else F(0)) for a,v in before.items()}
                require(max(before.values())==max(after.values()), 'all actual lifted prefix maxima unchanged')
        height_checks.append({'height':height,'class_count':len(lifted_family),
                              'actual_lcm':315*31*11**height,'all_positive_depth_caps_equal':True})
    result={
     'scope':'actual ordinary proof plus exact arithmetic, no new Lean theorem',
     'old_gamma_upper_source':'5506e7f580; marked_head_profile.md sharp uniform315 square1131/86',
     'head_original_classes':[list(v) for v in head],'complete_head_test_layout':[list(v) for v in test],
     'head_survivors':survivors,'head_size':len(survivors),'head_load_histogram':{str(k):v for k,v in sorted(Counter(load.values()).items())},
     'minimal_load_centres':centres,'chosen_centre':centre,'mixed11_cofactors':cofactors,
     'all_original_classes':[list(v) for v in family],'class_count':len(family),'actual_lcm':107415,
     'delta11':str(delta),'delta31':str(delta),'first_hit_histogram':{str(k):v for k,v in sorted(hit_hist.items())},
     'first_charge_support':charge_support,'first_charge':str(charge11),
     'old_gamma':str(base_energy),'weighted_old_gamma':str(residual_energy),
     'normalized_old_gamma':str(normalized_old_gamma),
     'weighted_old_gamma_proof':'Lower bound by the displayed maximizing layout; upper bound Gamma(rmu)<=Gamma(mu)-b since every complete layout has load>=1.',
     'prefix_caps_by_hit_count':{str(n):str(F(1,10-min(n,4))) for n in sorted(hit_hist)},
     'all_actual_positive_depth_prefix_caps_equal':True,
     'height_checks':height_checks,
     'same_positive_depth_weighted_gamma':True,
     'later_charge':str(charge31),'charge_intersection':str(intersection),'later_raw_charge_after_deletion':str(retained31),
     'later_charge_after_conditioning':str(conditioned),'later_charge_head_support':sorted(charge31_head),
    }
    return result


def two_prime_block_grid_comparison():
    """Check joint grid gain for prescribed old test blocks, without a universal Gamma claim."""
    def crt(items):
        answer, modulus = 0, 1
        for residue, next_modulus in items:
            answer += modulus*((residue-answer)*pow(modulus, -1, next_modulus) % next_modulus)
            modulus *= next_modulus
        return answer


    old_original = ((3, 0), (9, 4), (5, 0), (15, 1), (45, 37), (7, 0),
                    (21, 1), (35, 9), (63, 52), (105, 4), (315, 142))
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    S = [x for x in range(315) if all(x % d != a for d, a in old_original)]
    require(len(S) == 86 and 2 in S, 'fixed old supported survivor set')
    q, r = 11, 13
    Q, R = q-1, r-1
    holes = ((1, 1), (2, 2), (2, 3), (3, 2), (3, 3))
    labels = []
    original = list(old_original)
    for axis, prime, number in (('q', q, 7), ('r', r, 9)):
        for index, d in enumerate(divisors):
            digit = index+3 if 1 <= index <= number else 0
            old_residue = 2 % d
            original.append((d*prime, crt(((old_residue, d), (digit, prime)))))
            labels.append({'axis': axis, 'd': d, 'old_residue': old_residue, 'digit': digit})
    for index, d in enumerate(divisors):
        row, column = holes[index] if index < len(holes) else (0, 0)
        old_residue = 2 % d
        original.append((d*q*r, crt(((old_residue, d), (row, q), (column, r)))))
        labels.append({'axis': 'qr', 'd': d, 'old_residue': old_residue,
                       'row': row, 'column': column})
    all_divisors = [d for d in range(1, 45046) if 45045 % d == 0]
    require(sorted(d for d, _ in original) == all_divisors[1:], 'one class for all47 nonunit divisors')


    def survivor_grid(x):
        rows = {item['digit'] for item in labels if item['axis'] == 'q'
                and x % item['d'] == item['old_residue']}
        cols = {item['digit'] for item in labels if item['axis'] == 'r'
                and x % item['d'] == item['old_residue']}
        cells = {(item['row'], item['column']) for item in labels if item['axis'] == 'qr'
                 and x % item['d'] == item['old_residue']}
        return {(i, j) for i in range(1, q) for j in range(1, r)
                if i not in rows and j not in cols and (i, j) not in cells}


    def block_score(T):
        if not T:
            return (0, 0, 0, 0)
        row_count = Counter(i for i, _ in T)
        col_count = Counter(j for _, j in T)
        n = len(T)
        # A=B=C=D=1. The D cell contributes9 together with its two crosses
        # if the selected row/column intersect in T, otherwise at most5.
        joint = n+max(3*row_count[i]+3*col_count[j]+(9 if (i, j) in T else 5)
                      for i in row_count for j in col_count)
        separate = n+3*max(row_count.values())+3*max(col_count.values())+9
        sequential_qr = n+3*len(row_count)+3*max(row_count.values())+9
        sequential_rq = n+3*len(col_count)+3*max(col_count.values())+9
        require(joint <= separate <= min(sequential_qr, sequential_rq),
                'joint compatibility refines independent intersection caps and both sequential scalar orders')
        return (joint, separate, sequential_qr, sequential_rq)


    grids = {x: survivor_grid(x) for x in S}
    star = {(1, 2), (1, 3), (2, 1), (3, 1)}
    require(grids[2] == star, 'literal oldpoint2 has incompatible maximal row and column')
    require(block_score(star) == (22, 25, 28, 28), 'strict local moment gain')
    direct_star = max(sum((1+(u == i)+(v == j)+((u, v) == z))**2 for u, v in star)
                      for i in range(1, q) for j in range(1, r) for z in star)
    require(direct_star == 22, 'direct independent local maximization')
    counts = Counter(pair for T in grids.values() for pair in T)
    N = sum(map(len, grids.values()))
    direct_survivors = [x for x in range(45045) if all(x % d != a for d, a in original)]
    require(len(direct_survivors) == N, 'CRT grid counts equal direct full survivor count')
    totals = [sum(block_score(T)[k] for T in grids.values()) for k in range(4)]
    require(totals[0] < totals[1] <= min(totals[2:]), 'strict aggregate improvement for the same actual old law')

    # Complete old test blocks are identically1 on S if every nonunit old
    # test cofactor uses its original forbidden residue. Only the three unit
    # cofactors can then contribute new-prime indicators. Optimize those here.
    row_total = {i: sum(value for (u, v), value in counts.items() if u == i) for i in range(1, q)}
    col_total = {j: sum(value for (u, v), value in counts.items() if v == j) for j in range(1, r)}
    global_best = max((N+3*row_total[i]+3*col_total[j]+2*counts[i,j]
                       +(3+2*(z[0] == i)+2*(z[1] == j))*counts[z], i, j, z)
                      for i in range(1, q) for j in range(1, r) for z in counts)
    require(global_best[0] <= totals[0], 'pointwise block maximum bounds every fixed global layout')
    old_residues = dict(old_original)
    complete_test = []
    for d in divisors:
        for e, f in ((0, 0), (1, 0), (0, 1), (1, 1)):
            conditions = [(old_residues.get(d, 0), d)]
            if e:
                conditions.append(((global_best[1] if not f else global_best[3][0])
                                   if d == 1 else 0, q))
            if f:
                conditions.append(((global_best[2] if not e else global_best[3][1])
                                   if d == 1 else 0, r))
            complete_test.append((d*q**e*r**f, crt(conditions)))
    require(sorted(d for d, _ in complete_test) == all_divisors,
            'constant old blocks are realized by one complete48-label test layout')
    require(sum(sum(x % d == a for d, a in complete_test)**2 for x in direct_survivors)
            == global_best[0], 'literal full test layout attains the reported restricted maximum')
    result = {
        'scope': 'single height at 11 and 13; prescribed constant old test blocks only; no universal Gamma or prime-cutoff claim',
        'prescribed_old_blocks': {'A': '1', 'B': '1', 'C': '1', 'D': '1',
                                  'realization': 'every nonunit old test cofactor uses its original forbidden residue'},
        'old_original_classes': [list(pair) for pair in old_original],
        'old_survivor_count': len(S),
        'new_prime_heights': [[q, 1], [r, 1]],
        'complete_original_classes': [list(pair) for pair in original],
        'full_survivor_count': N,
        'local_old_point': 2, 'local_survivor_grid': [list(pair) for pair in sorted(star)],
        'local_square_numerators': {'joint':22, 'independent_intersection_caps':25,
                                   'sequential_qr':28, 'sequential_rq':28},
        'aggregate_square_numerators': {'joint':totals[0], 'independent_intersection_caps':totals[1],
                                       'sequential_qr':totals[2], 'sequential_rq':totals[3]},
        'aggregate_normalized_bounds': [str(Fraction(t, N)) for t in totals],
        'strict_compatibility_gain': str(Fraction(totals[1]-totals[0], N)),
        'constant_old_block_actual_maximum': {'square_numerator':global_best[0],
                                             'second_moment':str(Fraction(global_best[0], N)),
                                             'row':global_best[1], 'column':global_best[2],
                                             'cell':list(global_best[3])},
    }
    return result


def two_prime_block_gap_regression():
    """Check the general rebate identity against selected literal allocations."""
    grids = (
        ('singleton', 1, 1, ((0, 0),)),
        ('rectangle', 2, 3, tuple(product(range(2), range(3)))),
        ('incompatible_maxima', 3, 3, ((0, 1), (0, 2), (1, 0), (2, 0))),
        ('empty_ambient_rows_columns', 4, 5, ((1, 2), (1, 3), (2, 1), (3, 1))),
        ('missing_corner', 3, 3, tuple(p for p in product(range(3), repeat=2) if p != (0, 0))),
        ('matching', 3, 3, ((0, 0), (1, 1), (2, 2))),
        ('single_row', 1, 3, ((0, 0), (0, 1), (0, 2))),
    )
    coefficients = tuple(tuple(map(Fraction, values)) for values in (
        (0, 0, 0, 0), (1, 1, 1, 1), (0, 1, 1, 0), (1, 1, 1, 0),
        (1, 2, 2, 0), (0, 3, 2, 1), (1, 0, 3, 2), (1, 3, 0, 2),
        (2, 3, 1, 0), ('1/2', '3/2', '2/3', '4/5'), (10, 1, 1, 1),
    ))
    branches = Counter()
    examples = {}
    cases = 0
    for name, height, width, grid in grids:
        rows = [sum(y == i for y, _ in grid) for i in range(height)]
        columns = [sum(z == j for _, z in grid) for j in range(width)]
        row_max, column_max = max(rows), max(columns)
        incompatible = not any(rows[i] == row_max and columns[j] == column_max for i, j in grid)
        for A, B, C, D in coefficients:
            direct = max(sum((A + B*(y == i) + C*(z == j) + D*((y, z) == cell))**2
                             for y, z in grid)
                         for i, j, cell in product(range(height), range(width), grid))
            a, b = B*(2*A+B), C*(2*A+C)
            e = 2*B*C + 2*D*min(B, C)
            P = a*row_max + b*column_max
            E = max(a*rows[i] + b*columns[j] for i, j in grid)
            independent = len(grid)*A*A + P + 2*B*C + 2*A*D + D*D + 2*B*D + 2*C*D
            rebate = min(e, P-E)
            require(independent-direct == rebate, 'literal allocations satisfy exact block rebate')
            require((rebate > 0) == (B > 0 and C > 0 and incompatible),
                    'strict rebate criterion includes zero coefficients and empty ambient rows')
            if min(A, B, C, D) >= 1:
                require(rebate >= 3*incompatible, 'complete-layout block rebate is at least three')
            branch = ('zero' if rebate == 0 else
                      'cross_coefficient_limited' if e < P-E else
                      'degree_deficit_limited' if e > P-E else 'positive_branch_equality')
            branches[branch] += 1
            if branch not in examples:
                examples[branch] = {
                    'grid_name': name, 'ambient_dimensions': [height, width],
                    'grid': [list(pair) for pair in grid],
                    'coefficients': list(map(str, (A, B, C, D))),
                    'direct_F': str(direct), 'independent_G': str(independent),
                    'cross_limit': str(e), 'degree_limit': str(P-E), 'rebate': str(rebate),
                }
            if name == 'incompatible_maxima' and (A, B, C, D) == (1, 1, 1, 1):
                require((direct, independent, rebate) == (22, 25, 3), 'actual four-cell witness')
            cases += 1
    require(cases == 77, 'declared targeted regression scope')
    require(set(branches) == {'zero', 'cross_coefficient_limited', 'degree_deficit_limited',
                              'positive_branch_equality'}, 'both minimum branches and their boundaries')
    return {
        'scope': 'targeted exact regressions of the ordinary nonnegative-real rebate identity',
        'grid_names': [name for name, _, _, _ in grids],
        'coefficient_tuples': [list(map(str, values)) for values in coefficients],
        'grid_coefficient_cases': cases, 'branch_counts': dict(branches),
        'representative_cases': examples, 'complete_layout_uniform_rebate': '3',
    }


def ldlt_psd(matrix):
    n=len(matrix)
    lower=[[Fraction(i==j) for j in range(n)] for i in range(n)]
    diagonal=[]
    for j in range(n):
        pivot=matrix[j][j]-sum(lower[j][k]**2*diagonal[k] for k in range(j))
        require(pivot>=0,'nonnegative exact LDL pivot')
        diagonal.append(pivot)
        for i in range(j+1,n):
            remaining=matrix[i][j]-sum(lower[i][k]*lower[j][k]*diagonal[k] for k in range(j))
            if pivot:
                lower[i][j]=remaining/pivot
            else:
                require(remaining==0,'zero pivot has zero remaining column')
    require(all(sum(lower[i][k]*diagonal[k]*lower[j][k] for k in range(n))==matrix[i][j]
                for i in range(n) for j in range(n)), 'exact PSD factorization reconstruction')
    return diagonal


def punctured_grid_nonuniform_transfer(signed_square_result):
    from math import lcm
    m,n=10,12
    grid=[(i,j) for i in range(m) for j in range(n) if (i,j)!=(0,0)]
    epsilon=Fraction(1,2000)
    adjacent=Fraction(1,119)+epsilon
    interior=Fraction(1,119)-Fraction(20,99)*epsilon
    weight={(i,j):(adjacent if i==0 or j==0 else interior) for i,j in grid}
    require(sum(weight.values())==1 and min(weight.values())>0,'supported rational law normalized')
    rows=[sum(weight.get((i,j),Fraction(0)) for j in range(n)) for i in range(m)]
    cols=[sum(weight.get((i,j),Fraction(0)) for i in range(m)) for j in range(n)]
    ri,ci=rows[1],cols[1]
    diagonal=[1+ri+ci+interior,2*ri+2*interior,2*ci+2*interior,4*interior]
    constant=sum(diagonal)
    require(constant==Fraction(6386411,3927000),'universal transfer constant')
    matrices={}
    all_forms=[]
    count=0
    for i,j,z in product(range(m),range(n),grid):
        wz=weight[z];wij=weight.get((i,j),Fraction(0))
        wzr=wz if z[0]==i else Fraction(0);wzc=wz if z[1]==j else Fraction(0)
        matrix=((Fraction(1),rows[i],cols[j],wz),(rows[i],rows[i],wij,wzr),
                (cols[j],wij,cols[j],wzc),(wz,wzr,wzc,wz))
        matrices.setdefault(matrix,[i,j,list(z)])
        count+=1
        all_forms.append(sum(sum(row) for row in matrix))
    pivots=[]
    for matrix,witness in sorted(matrices.items()):
        difference=[[diagonal[i]*int(i==j)-matrix[i][j] for j in range(4)] for i in range(4)]
        ds=ldlt_psd(difference)
        pivots.append({'representative':witness,'pivots':list(map(str,ds))})
    require(count==14280 and len(matrices)==20,'all actual row-column-cell choices and Gram types')
    require(max(all_forms)==constant,'aligned interior unitlayout attains the transfer constant')
    old=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),(21,1),(35,9),(63,52),(105,4),(315,142)]
    require(signed_square_result['actual_second_moment_upper'] == '1131/86',
            'current sharp uniform315 square bound')
    require(signed_square_result['sharp_witness']['original_classes'] == [list(pair) for pair in old],
            'current sharp actual head family')
    original=old+[(11,0),(13,0),(143,1)]
    require(len(original)==len({d for d,a in original})==14,'fourteen distinct original moduli')
    require(all(d>1 and d%2 and 0<=a<d for d,a in original),'ordinary odd congruence family')
    require(lcm(*(d for d,a in original))==45045,'actual lcm')
    old_survivors=[x for x in range(315) if all(x%d!=a for d,a in old)]
    survivors=[x for x in range(45045) if all(x%d!=a for d,a in original)]
    require(len(old_survivors)==86 and len(survivors)==86*119,'complete actual support is oldsupport times puncturedgrid')
    require(all((x%11-1,x%13-1) in weight and x%315 in old_survivors for x in survivors),
            'CRT support matches the constructed law')
    uniform_constant=Fraction(194,119)
    require(uniform_constant-constant==Fraction(131,33000),'strict universal multiplier improvement')
    return {'scope':'ordinary universal Gamma tensorization with exact rational PSD certificate; not Lean verification',
        'rows':m,'columns':n,'missing_cell':[0,0],'grid_cells':len(grid),
        'epsilon':str(epsilon),'adjacent_cell_weight':str(adjacent),'interior_cell_weight':str(interior),
        'row_masses':list(map(str,rows)),'column_masses':list(map(str,cols)),
        'diagonal_majorant':list(map(str,diagonal)),'Gram_choices':count,'distinct_Gram_matrices':len(matrices),
        'LDL_certificates':pivots,'Gamma_and_tensorization_constant':str(constant),
        'uniform_Gamma_and_tensorization_constant':str(uniform_constant),'strict_multiplier_gain':str(uniform_constant-constant),
        'uniform_unweighted_grid_gap':0,
        'actual_original_classes':[list(t) for t in original],'actual_lcm':45045,
        'actual_survivor_count':len(survivors),'sharp_old_Gamma':'1131/86',
        'resulting_Gamma':str(constant*Fraction(1131,86)),
        'uniform_resulting_Gamma':str(uniform_constant*Fraction(1131,86))}


def matching_hole_common_lambda():
    """Check symbolic identities and PSD proof patterns, without grid instances."""
    class Polynomial(dict):
        # Sparse integer polynomials in m,n,k,epsilon,j, used only below.
        def __init__(self, value=0):
            super().__init__(value if isinstance(value, dict) else
                             ({(0,)*5: value} if value else {}))

        def __add__(self, other):
            out = dict(self)
            for powers, value in Polynomial(other).items():
                out[powers] = out.get(powers, 0)+value
            return Polynomial({powers: value for powers, value in out.items() if value})

        __radd__ = __add__

        def __mul__(self, other):
            out = {}
            for a, x in self.items():
                for b, y in Polynomial(other).items():
                    powers = tuple(i+j for i, j in zip(a, b))
                    out[powers] = out.get(powers, 0)+x*y
            return Polynomial({powers: value for powers, value in out.items() if value})

        __rmul__ = __mul__

        def __sub__(self, other):
            return self + Polynomial(other)*(-1)

        def __rsub__(self, other):
            return Polynomial(other) + self*(-1)

    m,n,k,e,j = [Polynomial({tuple(int(i==q) for i in range(5)): 1}) for q in range(5)]
    identities = []

    def identity(name, left, right):
        require(not Polynomial(left)-Polynomial(right), name)
        identities.append(name)

    S,V,H = m+n,m*n-k,k*(m+n-k-1)
    A = 3*(S+3)
    B = m*m+n*n+(2-k)*S-k-3
    identity('probability normalization', H*(1+e)+(m-k)*(n-k), V+H*e)
    identity('coefficient sum numerator',
             S+1+2*k*e+2*(n+1+k*e)+2*(m+1+k*e)+4, A+6*k*e)
    identity('strict multiplier gain numerator', A*H-6*k*V, 3*k*B)
    mx,ny = k+1+m,k+1+n
    identity('positive gain polynomial after translation',
             mx*mx+ny*ny+(2-k)*(mx+ny)-k-3,
             5*k+3+(k+4)*(m+n)+m*m+n*n)
    identity('row perturbation bound first slack', 2*n-(2*k+2), 2*(n-k-1))
    identity('row perturbation bound second slack', 2*n-(2*n-2*k), 2*k)
    D = lambda index: m*n-index+e*index*(S-index-1)
    N = lambda index: A+6*e*index
    delta = lambda index: 1-e*(S-2*index-2)
    T = lambda index: 6*e*D(index)+N(index)*delta(index)
    identity('varying-count denominator difference', D(j)-D(j+1), delta(j))
    identity('varying-count factor difference numerator', N(j+1)*D(j)-N(j)*D(j+1), T(j))
    identity('increasing difference numerator', T(j+1)-T(j), 2*e*N(j+1))
    identity('mean-count saving numerator', N(1)*D(0)-N(0)*D(1),
             6*e*m*n+A*(1-e*(S-2)))

    patterns = 0
    for hi,hj,u,v,t in product((0,1), repeat=5):
        r,q = n-hi,m-hj
        matrix = [[V,r,q,1],[r,r,u,v],[q,u,q,t],[1,v,t,1]]
        diagonal = [V+S+1,2*(n+1),2*(m+1),4]
        slacks = [hi+hj,2+2*hi-u-v,2+2*hj-u-t,2-v-t]
        require(all(not diagonal[a]-sum(matrix[a])-Polynomial(slacks[a]) for a in range(4)),
                'symbolic uniform Gram row-sum slack formula')
        require(min(slacks)>=0, 'all abstract row-sum slacks nonnegative')
        require((max(slacks)==0)==(hi==hj==0 and u==v==t==1),
                'only untouched aligned configurations have zero slack')
        patterns += 1

    norms = []
    for ell in range(4):
        transform = []
        for i in range(4):
            row = [1,0,0,0]
            if ell:
                row[ell] += 1
            if i:
                row[i] -= 1
            transform.append(row)
        recover = [[int(i==ell) for i in range(4)], [1,-1,0,0], [1,0,-1,0], [1,0,0,-1]]
        require(all(sum(transform[a][q]*recover[q][b] for q in range(4))==int(a==b)
                    for a in range(4) for b in range(4)), 'exact anchored-star coordinate inverse')
        norms.append(sum(value*value for row in transform for value in row))
    require(norms==[7,9,9,9], 'anchored-star squared Frobenius norms')
    return {
        'scope': 'symbolic identities and abstract PSD proof patterns; ordinary proof, not Lean verification',
        'parameter_domain': 'm,n>=3; 0<=k<min(m,n)',
        'epsilon_interval': '0<=epsilon<=1/(9*max(m+n+2*k-1,2*m,2*n))',
        'symbolic_identities': identities,
        'abstract_incidence_slack_patterns': patterns,
        'anchor_squared_Frobenius_norms': norms,
        'concrete_grid_instances': 0,
    }


def matching_height_lift():
    """Exact constants and regressions for the ordinary all-height theorem."""
    def tail(p, height):
        u = sum((Fraction(1, p**t) for t in range(1, height)), Fraction(0))
        v = sum((Fraction(2*t-1, p**t) for t in range(1, height)), Fraction(0))
        return u, 4*u+v


    def bound(m, n, k, epsilon, uq, ur, wq, wr, G, M):
        V, H = m*n-k, k*(m+n-k-1)
        D = V+H*epsilon
        c = 1/D
        atom = c*(1+epsilon) if k else c
        row, col = c*(n+k*epsilon), c*(m+k*epsilon)
        F = 1+c*(3*(m+n+3)+6*k*epsilon)
        E = (row+3*atom)*wq+(col+3*atom)*wr+atom*wq*wr
        lam = M*((row+atom)*uq+(col+atom)*ur+atom*uq*ur)
        require(lam < 1, "positive supported mass")
        return {"F": F, "E": E, "lambda": lam,
                "square": (F+E)*G, "conditioned": ((F+E)*G-lam)/(1-lam)}


    q, r, m, n, k = 11, 13, 10, 12, 1
    epsilon = Fraction(1, 216)
    G, M = Fraction(1131, 86), Fraction(271, 86)
    uq, ur = Fraction(1, 10), Fraction(1, 12)
    wq, wr = Fraction(13, 25), Fraction(31, 72)
    require(wq == 4*uq+Fraction(12, 100), "q infinite pair sum")
    require(wr == 4*ur+Fraction(14, 144), "r infinite pair sum")
    uniform = bound(m,n,k,Fraction(0),uq,ur,wq,wr,G,M)
    perturbed = bound(m,n,k,epsilon,uq,ur,wq,wr,G,M)
    require(perturbed["conditioned"] < uniform["conditioned"], "infinite-tail gain")

    V, H = Fraction(119), Fraction(20)
    Lmax = 13*uq+11*ur+uq*ur
    Nmax = V+75+15*wq+13*wr+wq*wr
    drop_min = 786-176*wq-216*wr-99*wq*wr
    charge_slope_max = Fraction(3,2)
    corners = [-22*x+18*y+99*x*y for x in (Fraction(0), uq) for y in (Fraction(0),ur)]
    require(max(corners) == charge_slope_max, "bilinear maximum")
    require(Lmax == Fraction(89,40), "largest unscaled high charge")
    margin40 = drop_min*(V-40*Lmax)-Nmax*40*charge_slope_max
    require(margin40 > 0, "uniform derivative margin for all M <= 40")
    denominator40 = V+H*epsilon-40*(Lmax+epsilon*(2*(uq+ur)+uq*ur))
    require(denominator40 > 0, "all-height positive denominator for M <= 40")

    checked = 0
    for hq in range(1, 9):
        for hr in range(1, 9):
            au, aw = tail(q,hq)
            bu, bw = tail(r,hr)
            require(0 <= au <= uq and 0 <= bu <= ur, "tail mass range")
            require(0 <= aw <= wq and 0 <= bw <= wr, "pair sum range")
            pair_q = sum((Fraction(1, q**(max(i,j)-1))
                          for i in range(hq+1) for j in range(hq+1)
                          if max(i,j) >= 1), Fraction(0))
            require(pair_q == 3+aw, "ordered exponent-pair count")
            a = bound(m,n,k,Fraction(0),au,bu,aw,bw,G,M)
            b = bound(m,n,k,epsilon,au,bu,aw,bw,G,M)
            require(b["conditioned"] < a["conditioned"], "finite-height gain")
            N0=V+75+15*aw+13*bw+aw*bw
            N1=H+6+4*(aw+bw)+aw*bw
            L0=13*au+11*bu+au*bu
            L1=2*(au+bu)+au*bu
            delta=(G*N0-M*L0)*(H-M*L1)-(G*N1-M*L1)*(V-M*L0)
            exact_gain=epsilon*delta/((V-M*L0)*(V+epsilon*H-M*(L0+epsilon*L1)))
            require(exact_gain == a["conditioned"]-b["conditioned"], "gain identity")
            require(delta > 0, "derivative certificate")
            checked += 1

    certificate = {
        "scope": "ordinary symbolic transfer with exact rational regressions; not Lean",
        "parameters": {"q":q,"r":r,"m":m,"n":n,"k":k,"epsilon":str(epsilon),"G":str(G),"M":str(M)},
        "infinite_tail_uniform": {x:str(y) for x,y in uniform.items()},
        "infinite_tail_perturbed": {x:str(y) for x,y in perturbed.items()},
        "strict_gain": str(uniform["conditioned"]-perturbed["conditioned"]),
        "all_height_proof_constants": {"Lmax":str(Lmax),"Nmax":str(Nmax),"drop_min":str(drop_min),"charge_slope_max":str(charge_slope_max),"derivative_margin_at_M40":str(margin40),"denominator_at_M40":str(denominator40)},
        "finite_height_pairs_checked": checked,
    }
    return certificate


def matching_height_tail17(old_result, lift_result):
    """Fixed tail17 schedule, using the verified comparator and actual square."""
    import hashlib
    from runpy import run_path
    arithmetic=run_path(str(Path(__file__).with_name('verify_star_block_obstruction.py')))
    continuation=run_path(str(Path(__file__).with_name('verify_finite_continuation.py')))
    SCALE=10**18
    runs=((17,4),(23,6),(31,8),(47,12),(61,16),(67,18),(89,24),(127,32),
          (131,36),(137,40),(191,48),(251,64),(271,72),(397,96),(523,128),
          (577,144),(587,160),(857,192),(859,216),(863,240),(1129,256),
          (1289,288),(1297,320),(1693,384))
    ps=list(continuation['segmented_primes'](0,runs[-1][0]))
    choices=[]
    previous=16
    for end,t in runs:
        require(end in ps and previous<end,'schedule endpoints are increasing primes')
        choices.extend((q,t) for q in ps if previous<q<=end)
        previous=end
    def up_fraction(x):
        return arithmetic['stoploss_ceiling'](SCALE*x.numerator,x.denominator)
    ceil_ratio=arithmetic['stoploss_ceiling']
    require([q for q,t in choices]==[q for q in ps if q>=17], 'consecutive full tail primes')
    require(all(isinstance(t,int) and 1<t<=q-2 for q,t in choices), 'normalized kernel domains')
    cap=max(t for q,t in choices)
    atoms={1:Fraction(581,6966),2:Fraction(3031,6966),3:Fraction(146,1053),4:Fraction(425,2106),5:Fraction(10,1443),6:Fraction(45,481),8:Fraction(1,37),12:Fraction(1,74)}
    require(atoms=={int(k):Fraction(v) for k,v in old_result['auxiliary_atoms'].items()},
            'directly reuse the verified old315 comparator')
    require(sum(atoms.values())==1,'old315 comparator probability')
    mean=sum(d*v for d,v in atoms.items())
    require(mean==Fraction(271,86),'old315 comparator mean')
    exact=[Fraction(0)]*(cap+1)
    for d,v in atoms.items():exact[d]=v
    for p,c in ((11,Fraction(11,10)),(13,Fraction(13,12))):
        law=[Fraction(0),1-c/p]+[c*(p-1)/p**f for f in range(2,cap+1)]
        new=[Fraction(0)]*(cap+1)
        for f in range(1,cap+1):
            for d in range(1,cap//f+1):
                new[f*d]+=law[f]*exact[d]
        exact=new
        mean*=1+c/(p-1)
    bad=Fraction(lift_result['infinite_tail_perturbed']['lambda'])
    head_second=Fraction(lift_result['infinite_tail_perturbed']['conditioned'])
    amax=(1+Fraction(1,216))/(119+20*Fraction(1,216))
    require((bad,amax,head_second)==(Fraction(5213769,88490560),Fraction(217,25724),Fraction(6074954672,249830373)),
            'same actual law supplies reference density and separate square bound')
    ell=(1-bad)/(120*amax)
    require(ell==Fraction(83276791,89577600), 'reference density fraction')
    require(1-exact[1]-exact[2]<=ell<=1-exact[1], 'upper quantile threshold two')
    mass2=(ell-1+exact[1]+exact[2])/ell
    mean=2+(mean-2+exact[1])/ell
    w=[up_fraction(v/ell if d>2 else mass2 if d==2 else Fraction(0)) for d,v in enumerate(exact)]
    mean_scaled=up_fraction(mean);second=up_fraction(head_second)
    charge=0;rows=[]
    for q,t in choices:
        s=q-1-t;c=Fraction(q-1,s)
        require(0<c<=q,'conditional geometric law probability')
        numerator=mean_scaled-t*SCALE+sum((t-d)*w[d] for d in range(1,t))
        require(numerator>=0,'nonnegative hinge upper')
        step=ceil_ratio(numerator,s);charge+=step
        require(charge<SCALE,'survival at every prefix')
        w=arithmetic['stoploss_product_update'](w,arithmetic['stoploss_atom_bounds'](q,c,cap,SCALE),SCALE)
        a=1+c/(q-1);b=1+c*Fraction(3*q-1,(q-1)**2)
        mean_scaled=ceil_ratio(mean_scaled*a.numerator,a.denominator)
        second=ceil_ratio(second*b.numerator,b.denominator)
        rows.append({'prime':q,'threshold':t,'s':s,'delta':str(Fraction(t-1,q-2)),
                     'charge_scaled_upper':step,'cumulative_scaled_upper':charge})
    gamma=1+Fraction(second-SCALE,SCALE-charge)
    stop=continuation['stopping_threshold'](len(ps))
    require(gamma<4856<4868<stop,'strict rational stopping chain')
    result={'scope':'Exact directed arithmetic; comparator proof and BBMST continuation are separate ordinary mathematical inputs.',
            'scale':SCALE,'retained_product_states':cap,'first_tail_prime':17,
            'last_prime':choices[-1][0],'global_prime_index':len(ps),'head_density_fraction':str(ell),
            'reference_mass_at_one':str(exact[1]),'reference_mass_at_two':str(exact[2]),
            'reference_mean':str(Fraction(271,86)*Fraction(111,100)*Fraction(157,144)),
            'head_quantile_mass_at_two':str(mass2),'head_comparator_mean':str(mean),
            'head_actual_second_upper':str(head_second),
            'mean_upper':str(Fraction(mean_scaled,SCALE)), 'second_moment_upper':str(Fraction(second,SCALE)),
            'total_charge_upper':str(Fraction(charge,SCALE)), 'survival_lower':str(Fraction(SCALE-charge,SCALE)),
            'Gamma_upper':str(gamma),'stopping_lower':str(stop),'stopping_margin':str(stop-gamma),
            'steps':rows,'final_low_state_digest':hashlib.sha256(json.dumps(w,separators=(',',':')).encode()).hexdigest()}
    result['threshold_runs']=[{'last_prime':q,'threshold':t} for q,t in runs]
    return result


def arbitrary_hole_degree_symbolic():
    """Symbolic algebra for the ordinary arbitrary-hole Gram proof."""
    class P(dict):
        def __init__(self,x=0):
            super().__init__(x if isinstance(x,dict) else ({():x} if x else {}))
        def __add__(self,other):
            answer=P(self)
            for term,value in P(other).items():
                answer[term]=answer.get(term,0)+value
                if not answer[term]: del answer[term]
            return answer
        __radd__=__add__
        def __neg__(self): return P({term:-value for term,value in self.items()})
        def __sub__(self,other): return self+-P(other)
        def __rsub__(self,other): return P(other)+-self
        def __mul__(self,other):
            answer=P()
            for term,value in self.items():
                for term2,value2 in P(other).items():
                    product=tuple(sorted(term+term2))
                    answer[product]=answer.get(product,0)+value*value2
            return P({term:value for term,value in answer.items() if value})
        __rmul__=__mul__
        def __pow__(self,n):
            answer=P(1)
            for _ in range(n): answer=answer*self
            return answer


    def variable(name): return P({(name,):1})


    m,n,k,e,t,d,u,x,y,a,b,s=[variable(v) for v in 'm n k epsilon t d u x y a b s'.split()]
    identities=[]
    certificates=[]
    def identity(name,left,right):
        if left-right: raise RuntimeError(name)
        identities.append(name)
    def nonnegative(name,poly):
        if not poly or any(value<0 for value in poly.values()):
            raise RuntimeError(name)
        certificates.append({'name':name,'terms':[
            {'monomial':'*'.join(term) or '1','coefficient':value}
            for term,value in sorted(poly.items())]})

    S=m+n
    V=m*n-k
    D=V+e*k*(S-k-1)
    H=k*S-(k*k+k-2*t)
    identity('degree-square disjoint-pair normalization',H,k*(S-k-1)+2*t)
    identity('common diagonal sum numerator',
             S+1+2*k*e+2*(n+1+k*e)+2*(m+1+k*e)+4,
             3*(S+3+2*k*e))
    B=m*m+n*n+(2-k)*S-k-3
    identity('strict gain numerator',
             3*(S+3)*D-3*(S+3+2*k*e)*V,
             3*k*e*B)
    Dnext=m*n-(k+1)+e*(k+1)*(S-(k+1)-1)
    identity('hole-count denominator difference',D-Dnext,1-e*(S-2*k-2))
    identity('perturbation row zero bound',
             2*k+k*(n-1)+k*(m-1)+k,k*(S+1))
    identity('row derivative with excess neighboring degree',
             d*(n-d)+k-(d+u),k+d*(n-d-1)-u)
    identity('row-cap residual',
             n+k*e-(n-d+e*(k+d*(n-d-1)-u)),
             d*(1-e*(n-d-1))+e*u)
    identity('filled-row and filled-column center remainder',
             (3+x)*a+(3+y)*b-2*(a+b),
             (1+x)*a+(1+y)*b)
    identity('large-row-derivative norm remainder',
             2*k*(n-1)-2*(k*(n-1)-s),2*s)
    nonnegative('small-row-derivative norm remainder, n=3+x',
                2*k*((3+x)-1)-4*k)
    nonnegative('restored-edge anchor surplus',x*a+y*b)
    nonnegative('large-row-derivative norm remainder',2*s)
    identity('10x12 gain polynomial',
             10*10+12*12+(2-k)*(10+12)-k-3,285-23*k)
    identity('10x12 gain at k=12-x',285-23*(12-x),9+23*x)
    nonnegative('10x12 gain for k<=12',9+23*x)
    result={'status':'PASS','scope':'symbolic algebra; semantic proof remains in note',
            'identities':identities,'nonnegative_coefficient_certificates':certificates}
    return result


def varying_hole_head(old_result, square_result):
    """Correlated hole-count input bounds for the same actual law."""
    X={1:Fraction(581,6966),2:Fraction(3031,6966),3:Fraction(146,1053),4:Fraction(425,2106),
       5:Fraction(10,1443),6:Fraction(45,481),8:Fraction(1,37),12:Fraction(1,74)}
    M,G=Fraction(271,86),Fraction(1131,86)
    require(X=={int(k):Fraction(v) for k,v in old_result['auxiliary_atoms'].items()},'verified old315 comparator')
    require(G==Fraction(square_result['actual_second_moment_upper']),'same old law square bound')
    require(sum(X.values())==1,'X normalization')
    require(sum(x*p for x,p in X.items())==M,'X mean')
    uq,ur,wq,wr=Fraction(1,10),Fraction(1,12),Fraction(13,25),Fraction(31,72)
    Nmean=Fraction(111,100)*Fraction(157,144)


    def top(alpha):
        out={x:Fraction(0) for x in X}
        rest=alpha
        for x in sorted(X,reverse=True):
            out[x]=min(rest,X[x])
            rest-=out[x]
        require(rest==0,'upper quantile mass')
        return out


    def parameters(j,eps):
        D=120-j+eps*j*(21-j)
        R=(12+j*eps)/D
        C=(10+j*eps)/D
        a=(1+j*eps)/D
        F=1+(75+6*j*eps)/D
        T=(R+a)*uq+(C+a)*ur+a*uq*ur
        E=(R+3*a)*wq+(C+3*a)*wr+a*wq*wr
        return {'D':D,'R':R,'C':C,'a':a,'F':F,'T':T,'chi':F+E,'d':120*a,
                'lambda0':1+(23+2*j*eps)/D,
                'lambda1':2*(13+j*eps)/D,
                'lambda2':2*(11+j*eps)/D,'lambda3':4/D}


    def reference_low(raw_old,cap=24):
        weights=[Fraction(0)]*(cap+1)
        for x,v in raw_old.items():
            weights[x]=v
        for p in (11,13):
            new=[v*Fraction(p-2,p-1) for v in weights]
            for f in range(2,cap+1):
                prob=Fraction(1,p**(f-1))
                for x in range(1,cap//f+1):
                    new[f*x]+=weights[x]*prob
            weights=new
        return weights


    def quantify(raw_old,survival):
        mass=sum(raw_old.values())
        mean=Nmean*sum(x*v for x,v in raw_old.items())
        low=reference_low(raw_old)
        remove=mass-survival
        below=Fraction(0)
        cut=None
        for j in range(1,len(low)):
            if below+low[j]>=remove:
                cut=j
                break
            below+=low[j]
        require(cut is not None,'quantile located in retained range')
        correction=sum((cut-j)*low[j] for j in range(1,cut))
        final_mean=cut+(mean-cut*mass+correction)/survival
        cut_mass=(survival-mass+sum(low[:cut+1]))/survival
        def hinge(t):
            if t<cut:
                return final_mean-t
            return (mean-t*mass+sum((t-j)*low[j] for j in range(1,t+1)))/survival
        return {'mass':mass,'ell':survival/mass,'raw_mean':mean,'cut':cut,
                'cut_mass':cut_mass,'mean':final_mean,'raw_mass1':low[1],
                'raw_mass2':low[2]},[hinge(t) for t in range(25)]


    rows=[]
    for K in range(1,13):
        eps=Fraction(1,207*K)
        vals=[parameters(j,eps) for j in range(K+1)]
        zero,last=vals[0],vals[-1]
        for field in ('R','C','a','F','T','chi','d','lambda0','lambda1','lambda2','lambda3'):
            seq=[v[field] for v in vals]
            require(all(seq[j]<=seq[j+1] for j in range(K)),field+' monotonic')
            require(all(seq[j+2]-seq[j+1]>=seq[j+1]-seq[j] for j in range(K-1)),field+' convex')
            require(all(seq[j]<=seq[0]+Fraction(j,K)*(seq[K]-seq[0]) for j in range(K+1)),field+' chord')
        alpha=min(Fraction(1),M/K)
        upper=top(alpha)
        Talpha=sum(x*v for x,v in upper.items())
        lam=zero['T']*M+(last['T']-zero['T'])*Talpha
        square=last['chi']*G-(last['chi']-zero['chi'])*(1-alpha)
        final=(square-lam)/(1-lam)
        old_lam=last['T']*M
        old_square=last['chi']*G
        old_final=(old_square-old_lam)/(1-old_lam)
        raw={x:X[x]+(last['d']-1)*upper[x] for x in X}
        profile,hinges=quantify(raw,1-lam)
        old_profile,old_hinges=quantify({x:last['d']*X[x] for x in X},1-old_lam)
        require(lam<1 and final>=1,'positive conditioned law')
        if alpha<1:
            require(lam<old_lam and square<old_square and final<old_final,'strict square and mass improvement')
            require(all(a<b for a,b in zip(hinges,old_hinges)),'strict profile improvement')
        else:
            require(lam==old_lam and square==old_square and profile==old_profile,'unchanged vacuous mean bound')
        rows.append({'K':K,'epsilon':str(eps),'alpha':str(alpha),
           'old_upper_quantile_cut':min(x for x,v in upper.items() if v),
           'old_upper_quantile_raw_mean':str(Talpha),
           'lambda':str(lam),'square_before_conditioning':str(square),'J':str(final),
           'worstK_lambda':str(old_lam),'worstK_J':str(old_final),
           'density_max':str(last['d']),
           'survival_lower':str(1-lam),
           'raw_old_mixture_atoms':{str(x):str(v) for x,v in raw.items()},
           'upper_old_subprobability_atoms':{str(x):str(v) for x,v in upper.items()},
           'profile':{k:str(v) if isinstance(v,Fraction) else v for k,v in profile.items()},
           'worstK_profile_mean':str(old_profile['mean'])})

    result={'scope':'Exact rational head inputs only; no tail schedule; symbolic proof separate',
            'old_mean':str(M),'old_square':str(G),'rows':rows,'hinge_regressions':12*25}
    return result


def arbitrary_holes12_tail17(head):
    """Fixed 414-step schedule for the verified K12 finite comparison measure."""
    import hashlib
    from runpy import run_path
    arithmetic=run_path(str(Path(__file__).with_name('verify_star_block_obstruction.py')))
    continuation=run_path(str(Path(__file__).with_name('verify_finite_continuation.py')))
    SCALE=10**18
    runs=((17, 4), (23, 6), (31, 8), (43, 12), (61, 16), (89, 24), (113, 32), (127, 36), (179, 48), (233, 64), (251, 72), (257, 80), (359, 96), (367, 108), (467, 128), (523, 144), (761, 192), (769, 216), (997, 256), (1117, 288), (1129, 320), (1669, 384), (1697, 432), (1699, 480), (2239, 512), (2551, 576), (2579, 640), (2903, 768))
    ps=list(continuation['segmented_primes'](0,runs[-1][0]))
    choices=[]
    previous=16
    for end,t in runs:
        require(end in ps and previous<end,'schedule endpoints are increasing primes')
        choices.extend((q,t) for q in ps if previous<q<=end)
        previous=end
    def up_fraction(x):
        return arithmetic['stoploss_ceiling'](SCALE*x.numerator,x.denominator)
    ceil_ratio=arithmetic['stoploss_ceiling']
    require([q for q,t in choices]==[q for q in ps if q>=17], 'consecutive full tail primes')
    require(all(isinstance(t,int) and 1<t<=q-2 for q,t in choices), 'normalized kernel domains')
    cap=max(t for q,t in choices)
    require(head['K']==12,'all twelve old cross-cofactor labels')
    atoms={int(a):Fraction(v) for a,v in head['raw_old_mixture_atoms'].items()}
    rawmass=sum(atoms.values())
    require(rawmass==Fraction(head['profile']['mass']),'raw old measure total mass')
    mean=sum(d*v for d,v in atoms.items())
    exact=[Fraction(0)]*(cap+1)
    for d,v in atoms.items():exact[d]=v
    for p,c in ((11,Fraction(11,10)),(13,Fraction(13,12))):
        law=[Fraction(0),1-c/p]+[c*(p-1)/p**f for f in range(2,cap+1)]
        new=[Fraction(0)]*(cap+1)
        for f in range(1,cap+1):
            for d in range(1,cap//f+1):
                new[f*d]+=law[f]*exact[d]
        exact=new
        mean*=1+c/(p-1)
    ell=Fraction(head['survival_lower'])
    head_second=Fraction(head['J'])
    require(rawmass-exact[1]-exact[2]<=ell<=rawmass-exact[1], 'upper surviving-mass quantile threshold two')
    mass2=(ell-rawmass+exact[1]+exact[2])/ell
    refmean=mean
    mean=2+(mean-2*rawmass+exact[1])/ell
    require(mean==Fraction(head['profile']['mean']),'verified full comparator mean')
    w=[up_fraction(v/ell if d>2 else mass2 if d==2 else Fraction(0)) for d,v in enumerate(exact)]
    mean_scaled=up_fraction(mean);second=up_fraction(head_second)
    charge=0;rows=[]
    for q,t in choices:
        s=q-1-t;c=Fraction(q-1,s)
        require(0<c<=q,'conditional geometric law probability')
        numerator=mean_scaled-t*SCALE+sum((t-d)*w[d] for d in range(1,t))
        require(numerator>=0,'nonnegative hinge upper')
        step=ceil_ratio(numerator,s);charge+=step
        require(charge<SCALE,'survival at every prefix')
        w=arithmetic['stoploss_product_update'](w,arithmetic['stoploss_atom_bounds'](q,c,cap,SCALE),SCALE)
        a=1+c/(q-1);b=1+c*Fraction(3*q-1,(q-1)**2)
        mean_scaled=ceil_ratio(mean_scaled*a.numerator,a.denominator)
        second=ceil_ratio(second*b.numerator,b.denominator)
        rows.append({'prime':q,'threshold':t,'s':s,'delta':str(Fraction(t-1,q-2)),
                     'charge_scaled_upper':step,'cumulative_scaled_upper':charge})
    gamma=1+Fraction(second-SCALE,SCALE-charge)
    stop=continuation['stopping_threshold'](len(ps))
    require(gamma<9826<9833<stop,'strict rational stopping chain')
    result={'scope':'Exact directed arithmetic; comparator proof and BBMST continuation are separate ordinary mathematical inputs.',
            'scale':SCALE,'retained_product_states':cap,'first_tail_prime':17,
            'last_prime':choices[-1][0],'global_prime_index':len(ps),'head_survival_lower':str(ell),'head_raw_comparator_mass':str(rawmass),
            'reference_mass_at_one':str(exact[1]),'reference_mass_at_two':str(exact[2]),
            'reference_mean':str(refmean),
            'head_quantile_mass_at_two':str(mass2),'head_comparator_mean':str(mean),
            'head_actual_second_upper':str(head_second),
            'mean_upper':str(Fraction(mean_scaled,SCALE)), 'second_moment_upper':str(Fraction(second,SCALE)),
            'total_charge_upper':str(Fraction(charge,SCALE)), 'survival_lower':str(Fraction(SCALE-charge,SCALE)),
            'Gamma_upper':str(gamma),'stopping_lower':str(stop),'stopping_margin':str(stop-gamma),
            'steps':rows,'final_low_state_digest':hashlib.sha256(json.dumps(w,separators=(',',':')).encode()).hexdigest()}
    result['threshold_runs']=[{'last_prime':q,'threshold':t} for q,t in runs]
    return result



def variable_axis_clipped_head(witnesses, old, signed):
    """Check exact area duals and the global scalar-clipping LP certificate."""
    F = Fraction
    M, G = F(old['mean']), F(signed['actual_second_moment_upper'])
    atoms = {int(x): F(p) for x, p in old['auxiliary_atoms'].items()}
    knots = (0, 1, 2, 3, 4, 5, 6, 8)
    bounds = {t: sum(p * max(x-t, 0) for x, p in atoms.items()) for t in knots}
    require(M == F(271,86) and G == F(1131,86), 'same canonical old law')
    lam = M * (F(13,1200) + F(11,1440) + F(1,14400))
    chi = (1+(3+F(13,25))/10)*(1+(3+F(31,72))/12)
    require(lam == F(24119,412800) and chi == F(187759,108000), 'full-height reference constants')
    # Match the exact LP's interleaved per-coordinate feature ordering.
    meta = [(axis, kind, t) for axis in range(3)
            for kind, t in [('hinge', t) for t in knots]+[('square',0)]]
    bs = [bounds[t] if kind == 'hinge' else G for axis, kind, t in meta]
    points = list(product(range(1,13), repeat=3))
    def feature(a, term):
        axis, kind, t = term
        require(axis in range(3) and kind in ('hinge','square'), 'valid marginal feature')
        return max(a[axis]-t,0) if kind == 'hinge' else a[axis]**2
    def area(a):
        return max(max(11-a[0],0)*(13-a[1])-a[2],0)
    fixed = []
    for cert in witnesses['fixed_area']:
        clip = F(cert.get('clip','1'))
        terms = [(int(v['axis']),v['kind'],int(v['knot'])) for v in cert['dual_terms']]
        coeffs = [F(v['coefficient']) for v in cert['dual_terms']]
        const = F(cert['dual_constant'])
        primal_atoms = [(tuple(v['loads']),F(v['mass'])) for v in cert['primal_atoms']]
        require(clip >= 1 and all(v <= 0 for v in coeffs), 'fixed area dual signs')
        require(all(a in points and p >= 0 for a,p in primal_atoms)
                and sum(p for a,p in primal_atoms)==1, 'fixed area primal probability')
        for term,b in zip(meta,bs):
            require(sum(p*feature(a,term) for a,p in primal_atoms)<=b, 'fixed area marginal feasibility')
        for a in points:
            require(const+sum(v*feature(a,term) for v,term in zip(coeffs,terms))
                    <=min(F(120)/clip,area(a)), 'pointwise clipped area dual')
        dual = const+sum(v*(bounds[t] if kind=='hinge' else G)
                         for v,(axis,kind,t) in zip(coeffs,terms))
        primal = sum(p*min(F(120)/clip,area(a)) for a,p in primal_atoms)
        require(dual==primal==F(cert['low_survivor_cells_mean_lower']), 'fixed area exact primal-dual equality')
        z=clip*dual/120; survival=z-clip*lam
        require(survival>0, 'fixed area positive full survival')
        j1=1+(G-1+clip*F(5,8)*G)/z
        j=1+(G-1+clip*(chi-1)*G)/survival
        require(j1==F(cert['height1_J']) and j==F(cert['allheight_J']), 'fixed area square bounds')
        fixed.append({'clip':str(clip),'low_mass_lower':str(z),'full_mass_lower':str(survival),
                      'height1_J':str(j1),'allheight_J':str(j),'primal_atoms':len(primal_atoms)})
    cert=witnesses['global_optimum']
    matrix=[]; rhs=[]
    for a in points:
        fs=[F(feature(a,term)) for term in meta]
        matrix.append([F(-1),F(0),F(1)]+fs);rhs.append(F(0))
        matrix.append([F(0),-F(area(a),120),F(1)]+fs);rhs.append(F(0))
    matrix.append([F(0),lam,F(-1)]+[-b for b in bs]);rhs.append(F(-1))
    matrix.append([F(1),F(-1),F(0)]+[F(0)]*len(meta));rhs.append(F(0))
    cost=[G-1,(chi-1)*G,F(0)]+[F(0)]*len(meta)
    x=list(map(F,cert['primal_variables']))
    require(len(x)==30 and len(matrix)==3458, 'global LP dimensions')
    require(x[0]>0 and x[1]>=x[0] and all(v<=0 for v in x[3:]), 'global LP primal signs')
    for row,b in zip(matrix,rhs):
        require(sum(a*v for a,v in zip(row,x))<=b, 'global LP primal feasibility')
    y={v['index']:F(v['value']) for v in cert['dual_variables']}
    require(len(y)==len(cert['dual_variables']) and all(0<=i<len(matrix) and v<=0 for i,v in y.items()), 'global LP dual signs and indices')
    residual=[cost[i]-sum(v*matrix[j][i] for j,v in y.items()) for i in range(len(cost))]
    require(residual[0]>=0 and residual[1]>=0 and residual[2]==0
            and all(v<=0 for v in residual[3:]), 'global LP dual stationarity signs')
    primal=sum(a*v for a,v in zip(cost,x));dual=sum(rhs[j]*v for j,v in y.items())
    require(primal==dual==F(cert['objective_minus_one']), 'global clipping exact optimality')
    clip=x[1]/x[0];z=(x[2]+sum(a*b for a,b in zip(x[3:],bs)))/x[0]
    survival=z-clip*lam
    j=1+(G-1+clip*(chi-1)*G)/survival
    require(clip==F(40,31) and z==F(74101,97929) and survival==1/x[0]>0,
            'optimal clip and normalization')
    # Verify the short direct lower certificate as well as the robust LP.
    for a in points:
        short=1-F(3,31)*max(a[0]-2,0)-F(2,93)*max(a[0]-4,0)-F(7,93)*max(a[1]-2,0)-F(2,93)*max(a[1]-4,0)-F(1,93)*max(a[2]-2,0)
        require(short<=min(F(1),F(area(a),93)), 'five-term pointwise area certificate')
    require(1-F(17,93)*bounds[2]-F(4,93)*bounds[4]==z,
            'five-term area mean')
    # Low reference atoms and its full mean include all higher digits.
    raw=[F(0)]*4
    for a,p in atoms.items():
        if a<len(raw):raw[a]=p
    auxmean=F(1)
    for p in (11,13):
        law=[F(0),F(p-2,p-1),F(1,p),F(1,p*p)]
        nxt=[F(0)]*4
        for a in range(1,4):
            for b in range(1,3//a+1):nxt[a*b]+=raw[a]*law[b]
        raw=nxt;auxmean*=1+F(p,(p-1)**2)
    ell=survival/clip
    require(1-sum(raw[1:4])<ell<1-sum(raw[1:3]), 'reference quantile cut three')
    mean=3+(M*auxmean-3+2*raw[1]+raw[2])/ell
    first=1+(M-1+clip*(auxmean-1)*M)/survival
    require(first<=mean and j==F(42723250051,1147550665), 'same-law moment comparison')
    return {'scope':'all low axis and point patterns; full original 357 part divides 315; arbitrary finite 11/13 heights; no tail conclusion',
            'witnesses':witnesses,'fixed_area_bounds':fixed,'clip':str(clip),
            'low_mass_lower':str(z),'high_reference_mass_upper':str(lam),'square_reference_factor':str(chi),
            'full_mass_lower':str(survival),'Gamma_upper':str(j),
            'same_law_first_upper':str(first),'reference_auxiliary_mean':str(auxmean),
            'reference_mean':str(M*auxmean),'reference_quantile_mass':str(ell),
            'reference_quantile_cut':3,'reference_comparison_mean':str(mean),
            'same_clip_height1_Gamma_upper':str(1+(G-1+clip*F(5,8)*G)/z),
            'primal_constraints_verified':len(matrix),'dual_coordinates_verified':len(cost),
            'nonzero_dual_terms':len(y),'pointwise_area_triples_verified':len(points)}


def shared_count_clipped_head(old_cases, old, signed):
    """Recompute common-shape/count moments, then reuse the fixed VC6 dual."""
    F = Fraction
    clip = F(40, 31)
    chi = F(187759, 108000)
    height_mean = F(5809, 4800)
    thresholds = (0, 2, 4)
    # The local grid count is distinct from the old survivor count below.
    caps = (F(55, 240), 26*clip/120, 22*clip/120, 4*clip/120)
    max_center = F(0)
    max_extra = F(0)
    grid_cases = 0
    maximizers = []
    for m, n in product(range(1, 11), range(1, 13)):
        for k in range(min(12, m*n-1)+1):
            grid_cases += 1
            cells = m*n-k
            density = min(clip, F(120, cells))
            center = density*(m+n+1)
            q = (center/120, 2*density*(n+1)/120,
                 2*density*(m+1)/120, 4*density/120)
            require(all(a <= b for a, b in zip(q, caps)), 'actual rectangle diagonal caps')
            require(sum(q) == density*(m+n+3)/40 <= F(3, 4),
                    'actual rectangle unit-load saving')
            if center > max_center:
                max_center, maximizers = center, []
            if center == max_center:
                maximizers.append([m, n, k])
            max_extra = max(max_extra, sum(q))
    saving = clip*F(5, 8)-sum(caps)
    unit_rebate = sum(caps)-max_extra
    require(grid_cases == 1372 and max_center == F(55, 2)
            and saving == F(9, 496) and unit_rebate == F(19, 496),
            'complete actual-grid domain and exact two savings')
    require(len(old_cases) == len(old['cases']) == 6, 'six common old shapes')
    squares = [F(signed['actual_second_moment_upper'])] + [
        F(case['second_moment_bound']) for case in old['cases'][1:]]
    cases = []
    branches = []
    layout_total = 0
    for index, (shape, points, histograms, expected_layouts) in enumerate(old_cases):
        n = len(points)
        groups = [[tuple(i for i, x in enumerate(points) if x % d == a)
                   for a in sorted({x % d for x in points})] for d in MODULI]
        minimum = 6*n - sum(max(map(len, group)) for group in groups)
        counts = list(range(minimum, 6*n + 1))
        loads = []
        for cylinders in product(*groups):
            a = [1]*n
            for cylinder in cylinders:
                for i in cylinder:
                    a[i] += 1
            loads.append(tuple(a))
        require(len(loads) == expected_layouts, 'all effective old layouts for common count')
        layout_total += len(loads)
        hs = [tuple(sum(max(v-t, 0) for v in a) for t in range(5)) for a in loads]
        maxima = [max(h[t] for h in hs) for t in range(5)]
        q = max(sum(v*v for v in a) for a in loads)
        require(maxima[3] <= 5 and all(max(a) <= 6 for a in loads),
                'common-count high-hinge numerator at most ten')
        old_bounds = list(map(F, old['cases'][index]['hinge_bounds_at_0_through_5']))
        require(old['cases'][index]['shape'] == shape, 'same canonical shape indexing')
        tops = [[0]*4 for _ in counts]
        for a, h in zip(loads, hs):
            cross = sum(a) + sum(max(sum(a[i] for i in c) for c in group) for group in groups)
            costs = [5*h[t] + min(h[k] + maxima[t-k] for k in range(t+1))
                     for t in thresholds]
            costs.append(6*sum(v*v for v in a) + 2*cross + q)
            for cost_index, cost in enumerate(costs):
                values = ([max(v-thresholds[cost_index], 0) for v in a]
                          if cost_index < 3 else [v*v for v in a])
                least = [0]
                for v in sorted(values):
                    for _ in range(5):
                        least.append(least[-1] + v)
                label_bounds = []
                for eta in sorted({0, *values}):
                    positive = [max(eta-v, 0) for v in values]
                    cap = sum(max(sum(positive[i] for i in c) for c in group) for group in groups)
                    label_bounds.append((eta, cap))
                for j, count in enumerate(counts):
                    deleted = 6*n-count
                    # b<=5 gives the least-entry bound; b<=sum_d 1_Cd
                    # gives every eta*deleted-cap lower bound on sum b*h.
                    loss = max([least[deleted]] + [eta*deleted-cap for eta, cap in label_bounds])
                    tops[j][cost_index] = max(tops[j][cost_index], cost-loss)
        rows = []
        for count, top in zip(counts, tops):
            bounds = {t: min(F(top[j], count), old_bounds[t]) for j, t in enumerate(thresholds)}
            m, g = bounds[0], min(F(top[3], count), squares[index])
            high6 = F(10, count)
            z = 1-F(17, 93)*bounds[2]-F(4, 93)*bounds[4]
            lam = F(89, 4800)*m
            survival = z-clip*lam
            require(m >= 1 and g >= 1 and 0 < survival <= z <= 1,
                    'same-branch moments and positive clipped survival')
            gamma = 1+(g-1+clip*(chi-1)*g)/survival
            mean = 1+(m-1+clip*(height_mean-1)*m)/survival
            row = {'survivors':count, 'mean_upper':str(m), 'square_upper':str(g),
                   'hinge2_upper':str(bounds[2]), 'hinge4_upper':str(bounds[4]),
                   'hinge6_upper':str(high6), 'low_mass_lower':str(z),
                   'full_mass_lower':str(survival), 'Gamma_upper':str(gamma),
                   'same_law_first_upper':str(mean)}
            rows.append(row)
            branches.append((index, row))
        cases.append({'shape':shape, 'old_survivors':n, 'test_layouts':len(loads),
                      'survivor_count_range_inclusive':[minimum, 6*n], 'rows':rows})
    checked = 0
    for a, b, d in product(range(1, 13), repeat=3):
        area = max(max(11-a, 0)*(13-b)-d, 0)
        dual = 93-9*max(a-2, 0)-2*max(a-4, 0)-7*max(b-2, 0)-2*max(b-4, 0)-max(d-2, 0)
        require(dual <= min(93, area), 'common-count fixed VC6 pointwise area bound')
        checked += 1
    require(len(branches) == 144 and layout_total == 27720, 'complete common shape/count domain')
    worst_shape, worst = max(branches, key=lambda pair: F(pair[1]['Gamma_upper']))
    mean_shape, mean_worst = max(branches, key=lambda pair: F(pair[1]['same_law_first_upper']))
    survival = min(F(row['full_mass_lower']) for _, row in branches)
    ell = survival/clip
    joint = max(F(row['square_upper'])+50*F(row['hinge6_upper']) for _, row in branches)
    refined = []
    for index, row in branches:
        g = F(row['square_upper'])
        numerator = g-1+clip*(chi-1)*g-saving*g-unit_rebate
        require(numerator > 0, 'positive refined numerator before denominator replacement')
        refined.append((1+numerator/F(row['full_mass_lower']), index, row['survivors']))
    refined_gamma, refined_shape, refined_count = max(refined)
    # The existing global old comparator remains valid on every branch.
    atoms = {int(x):F(p) for x, p in old['auxiliary_atoms'].items()}
    raw = [F(0)]*4
    for a, p in atoms.items():
        if a < 4:
            raw[a] = p
    for p in (11, 13):
        law = [F(0), F(p-2, p-1), F(1, p), F(1, p*p)]
        nxt = [F(0)]*4
        for a in range(1, 4):
            for b in range(1, 3//a+1):
                nxt[a*b] += raw[a]*law[b]
        raw = nxt
    require(1-sum(raw[1:4]) < ell < 1-sum(raw[1:3]), 'shared-count reference quantile cut three')
    comparison_mean = 3+(F(old['mean'])*height_mean-3+2*raw[1]+raw[2])/ell
    require(F(worst['Gamma_upper']) < F(42723250051, 1147550665),
            'common geometry strictly improves the global-marginal square bound')
    return {'scope':'all low axis and point patterns; full original 357 part divides 315; arbitrary finite 11/13 heights; common old shape and survivor count; no tail or Lean conclusion',
            'clip':str(clip), 'cases':cases, 'old_layouts_verified':layout_total,
            'shared_branches_verified':len(branches), 'pointwise_area_triples_verified':checked,
            'square_reference_factor':str(chi), 'reference_auxiliary_mean':str(height_mean),
            'high_reference_mass_per_old_mean':'89/4800',
            'Gamma_upper':worst['Gamma_upper'], 'worst_shape':worst_shape,
            'worst_survivors':worst['survivors'],
            'same_law_first_upper':mean_worst['same_law_first_upper'],
            'worst_first_shape':mean_shape, 'worst_first_survivors':mean_worst['survivors'],
            'full_mass_lower':str(survival), 'reference_quantile_mass':str(ell),
            'reference_quantile_cut':3, 'reference_comparison_mean':str(comparison_mean),
            'joint_square_plus_50_hinge6_upper':str(joint),
            'actual_rectangle_refinement':{
                'grid_count_triples_verified':grid_cases,
                'max_density_times_axes_plus_one':str(max_center),
                'maximizing_grid_counts':maximizers,
                'low_extra_diagonal_caps':list(map(str, caps)),
                'max_low_extra_diagonal_sum':str(max_extra),
                'square_saving_coefficient':str(saving), 'unit_load_rebate':str(unit_rebate),
                'high_square_coefficient':str(clip*(chi-F(13, 8))),
                'Gamma_upper':str(refined_gamma), 'worst_shape':refined_shape,
                'worst_survivors':refined_count}}


def signed_conditioning_obstruction():
    """Reconstruct the actual 47-class family and signed-criterion barrier."""
    F = Fraction
    OLD=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
         (21,16),(35,24),(63,25),(105,19),(315,109)]
    TABLE=[
     (1,None,None,(0,9,8)),
     (3,(2,6),(1,11),(2,10,11)),
     (5,(2,2),(4,2),(2,10,5)),
     (7,(5,5),(6,3),(6,10,6)),
     (9,(2,3),(5,4),(2,9,6)),
     (15,(2,7),(11,2),(2,9,10)),
     (21,(2,4),(20,12),(2,10,6)),
     (35,(17,5),(34,9),(34,2,7)),
     (45,(2,8),(41,5),(11,2,9)),
     (63,(47,4),(34,12),(23,8,3)),
     (105,(17,4),(34,10),(26,8,7)),
     (315,(52,7),(244,4),(97,10,7)),
    ]


    def divisors(n): return [d for d in range(1,n+1) if n%d==0]


    def crt(a,m,b,n):
        return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
    ds=divisors(315)
    omega=[x for x in range(315) if all(x%d!=a for d,a in OLD)]
    A={x:sum((x-8)%d==0 for d in ds) for x in omega}
    require((len(omega),sum(A.values()),sum(a*a for a in A.values()))==(86,271,1131),
            'old survivor moments')
    histogram=Counter(A.values())
    require(histogram=={1:5,2:38,3:14,4:18,6:8,8:2,12:1},'old histogram')
    require([crt(a,d,y,7) for d,a,y in
             [(3,1,2),(5,4,3),(9,7,4),(15,4,5),(45,19,4)]]
            ==[16,24,25,19,109],'old mixed CRT')

    cylinders=[]
    max_linear_load=0
    max_cross_load=0
    for d in ds:
        mass=[sum(x%d==a for x in omega) for a in range(d)]
        cross=[sum(A[x] for x in omega if x%d==a) for a in range(d)]
        max_linear_load+=max(mass)
        max_cross_load+=max(cross)
        if d==1: continue
        low=[(sum(x%d==a and A[x]<=5 for x in omega),
              sum(A[x]**2 for x in omega if x%d==a and A[x]<=5)) for a in range(d)]
        max25=max(25*count-square for count,square in low)
        max35=max(35*count-square for count,square in low)
        shared=[a for a,(count,square) in enumerate(low)
                if 25*count-square==max25 and 35*count-square==max35]
        require(shared,'one affine cylinder maximizes throughout [25,35]')
        a=shared[0]
        count,square=low[a]
        cylinders.append({'d':d,'residue':a,'count_low':count,'square_low':square})
    require(max_linear_load==271,'maximum independent-layout first moment')
    require(max_cross_load==1131,'maximum cross moment with A')
    N=sum(v['count_low'] for v in cylinders)
    S=sum(v['square_low'] for v in cylinders)
    require((N,S)==(164,1197),'weighted-cylinder affine sum')
    low_count=sum(a<=5 for a in A.values())
    low_square=sum(a*a for a in A.values() if a<=5)
    require((low_count,low_square)==(75,571),'global positive-part affine sum')
    G=F(1131,86)
    intercept=F(13,8)*G-F(23*S+low_square,120*86)
    slope=F(23*N+low_count,120*86)
    require(intercept==F(192443,10320) and slope==F(3847,10320),
            'criterion affine expression')
    zstar=intercept/(1-slope)
    require(zstar==F(192443,6473) and 25<zstar<35,'criterion threshold')
    lipschitz=F(23,120)*(F(max_linear_load,86)-1)+F(1,120)
    require(lipschitz==F(1447,3440)<1,'global strict contraction bound')
    require(intercept+30*slope==30-F(1747,10320),'criterion at 30')

    classes=OLD+[(11,0),(13,0)]
    for d,row,col,point in TABLE:
        if row:
            a,i=row
            classes.append((11*d,crt(a,d,i,11)))
        if col:
            a,j=col
            classes.append((13*d,crt(a,d,j,13)))
        a,i,j=point
        b=crt(a,d,i,11)
        classes.append((143*d,crt(b,11*d,j,13)))
    fine_ds=divisors(45045)
    require(len(classes)==47,'47 original congruences')
    require(sorted(d for d,a in classes)==fine_ds[1:],'every nonunit divisor once')
    require(all(d>1 and d%2==1 and 0<=a<d for d,a in classes),'odd canonical moduli')
    center=17018
    require((center%315,center%11,center%13)==(8,1,1),'coherent test center')
    direct_survivors=[x for x in range(45045) if all(x%d!=a for d,a in classes)]
    direct_loads=[sum((x-center)%d==0 for d in fine_ds) for x in direct_survivors]
    require(len(direct_survivors)==6872,'direct survivor count')
    direct_square=sum(a*a for a in direct_loads)
    require(direct_square==177110,'direct squared load sum')

    crt_survivors=[]
    crt_square=0
    cells=Counter()
    for x in omega:
        for i in range(1,11):
            for j in range(1,13):
                forbidden=False
                for d,row,col,point in TABLE:
                    if row and x%d==row[0] and i==row[1]: forbidden=True
                    if col and x%d==col[0] and j==col[1]: forbidden=True
                    if x%d==point[0] and i==point[1] and j==point[2]: forbidden=True
                if forbidden: continue
                fine=crt(crt(x,315,i,11),3465,j,13)
                crt_survivors.append(fine)
                factor=(1+(i==1))*(1+(j==1))
                crt_square+=(A[x]*factor)**2
                cells[A[x],factor]+=1
    require(sorted(crt_survivors)==direct_survivors,'direct and CRT support equality')
    require(crt_square==direct_square,'direct and CRT squared-load agreement')
    actual=F(direct_square,len(direct_survivors))
    require(actual==F(88555,3436)>25,'actual conditioned-law obstruction')
    reference_square=F(13,10)*F(15,12)*G
    require(reference_square==F(13,8)*G,'pre-deletion bound is attained')
    retained=F(len(direct_survivors),86*120)
    require(retained==F(859,1290),'actual retained mass')

    result={'status':'PASS','scope':'prescribed uniformly conditioned law, height one in 11 and 13',
            'old_classes':[list(v) for v in OLD],'old_histogram':{str(k):v for k,v in sorted(histogram.items())},
            'old_survivors':len(omega),'old_load_sum':sum(A.values()),
            'old_squared_sum':sum(a*a for a in A.values()),
            'max_cross_sum':max_cross_load,'max_mean_sum':max_linear_load,
            'criterion_cylinder_maximizers':cylinders,
            'criterion_intercept':str(intercept),'criterion_slope':str(slope),
            'criterion_unique_fixed_point':str(zstar),'global_lipschitz_upper':str(lipschitz),
            'criterion_at_30':str(intercept+30*slope),
            'original_47_classes':[list(v) for v in sorted(classes)],'test_center':center,
            'actual_survivors':len(direct_survivors),'actual_squared_load_sum':direct_square,
            'actual_conditioned_moment':str(actual),'actual_retained_mass':str(retained),
            'survivor_histogram':[
                {'A':a,'factor':factor,'count':count} for (a,factor),count in sorted(cells.items())],
            'warning':'Not an obstruction to arbitrary supported laws and not an odd covering system.'}
    return result


def rectangle_hinge_observation_gap():
    """Reconstruct two full labelled tests with equal coarse data and unequal hinges."""
    F = Fraction
    old = ((3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
           (21,16),(35,24),(63,25),(105,19),(315,109))
    residues = dict(old)
    old_ds = [d for d in range(1,316) if 315 % d == 0]
    fine_ds = [d for d in range(1,45046) if 45045 % d == 0]
    omega = [x for x in range(315) if all(x % d != a for d,a in old)]
    old45 = [x for x in range(45) if all(x % d != a for d,a in old[:5])]
    require(len(omega) == 86 and len(old45) == 17, "fixed shared old shape and count")
    A = {x:sum(x % d == 8 % d for d in old_ds) for x in omega}
    histogram = Counter(A.values())
    require(histogram == Counter({1:5,2:38,3:14,4:18,6:8,8:2,12:1}),
            "old load reconstructed from actual query cylinders")

    def combine(a,m,b,n):
        residue = a + m * (((b-a) * pow(m,-1,n)) % n)
        require(0 <= residue < m*n and residue % m == a and residue % n == b,
                "canonical CRT residue")
        return residue

    # All added nonunit old cofactors use a residue already absent from omega.
    # Only the unit mixed label removes one cell in every remaining rectangle.
    originals = list(old)
    for d in old_ds:
        originals.append((11*d, 0 if d == 1 else combine(residues[d],d,1,11)))
        originals.append((13*d, 0 if d == 1 else combine(residues[d],d,1,13)))
        a = 0 if d == 1 else residues[d]
        i,j = (10,12) if d == 1 else (1,1)
        originals.append((143*d,combine(combine(a,d,i,11),11*d,j,13)))
    require(len(originals) == 47 and sorted(d for d,a in originals) == fine_ds[1:],
            "one original congruence for every nonunit divisor of 45045")

    def test_layout(point):
        choices = []
        for d in old_ds:
            choices.extend(((d,8 % d),
                            (11*d,combine(8 % d,d,1,11)),
                            (13*d,combine(8 % d,d,1,13)),
                            (143*d,combine(combine(8 % d,d,point[0],11),11*d,point[1],13))))
        require(sorted(d for d,a in choices) == fine_ds, "complete original test labels")
        return sorted(choices)

    points = ((1,1),(2,2))
    tests = [test_layout(p) for p in points]
    direct = [x for x in range(45045) if all(x % d != a for d,a in originals)]
    require(len(direct) == 86*119 == 10234, "full-period actual survivor count")
    direct_loads = [[sum(y % d == a for d,a in test) for y in direct] for test in tests]
    direct_histograms = [Counter(loads) for loads in direct_loads]
    direct_hinges = [sum(max(a-6,0) for a in loads) for loads in direct_loads]

    def kernel(N,r,q,u,v,t,a,threshold):
        a0,a1,a2,a3 = a
        phi = lambda b:max(b-threshold,0)
        return ((N-r-q+u)*phi(a0) + (r-u)*phi(a0+a1) +
                (q-u)*phi(a0+a2) + u*phi(a0+a1+a2) +
                phi(a0+v*a1+t*a2+a3)-phi(a0+v*a1+t*a2))

    grid_points = []
    grid_histograms = [Counter(),Counter()]
    kernel_checks = 0
    for x in omega:
        per_old = [[],[]]
        for i in range(1,11):
            for j in range(1,13):
                if (i,j) == (10,12):
                    continue
                fine = combine(combine(x,315,i,11),3465,j,13)
                grid_points.append(fine)
                for index,point in enumerate(points):
                    # Compute from all original test labels, then check block concentration.
                    load = sum(fine % d == a for d,a in tests[index])
                    factor = 1+(i == 1)+(j == 1)+((i,j) == point)
                    require(load == A[x]*factor, "actual complete-label load equals four-block load")
                    per_old[index].append(load)
                    grid_histograms[index][load] += 1
        for index,(v,t) in enumerate(((1,1),(0,0))):
            for threshold in range(49):
                actual = sum(max(a-threshold,0) for a in per_old[index])
                require(kernel(119,12,10,1,v,t,(A[x],)*4,threshold) == actual,
                        "five-incidence hinge kernel equals actual cell sum")
                kernel_checks += 1
    require(sorted(grid_points) == direct, "CRT product and full-period support agree")
    require(grid_histograms == direct_histograms, "all full-load histograms agree")
    require(direct_hinges == [3998,3844], "threshold-six numerators")
    values = [F(v,len(direct)) for v in direct_hinges]
    require(values == [F(1999,5117),F(1922,5117)] and values[0]-values[1] == F(77,5117),
            "strict hinge gap at identical coarse observations")
    cap = F(40,31)
    density = min(cap,F(120,119))
    require(density == F(120,119) and density*F(119,120) == 1,
            "same actual clipped law is uniform on these survivors")
    return {
        "status":"PASS: actual complete labels, full period and independent CRT grid",
        "scope":"failure of exact hinge determination by shared shape/count and four old block functions",
        "original_classes":[list(v) for v in sorted(originals)],
        "old_classes":[list(v) for v in old],
        "old_shape":"root1_same_other_column", "old45_survivors":len(old45),
        "old315_survivors":len(omega),
        "old_load_histogram":{str(k):v for k,v in sorted(histogram.items())},
        "same_four_old_blocks":"A00=A10=A01=A11=sum_{d|315} 1[x=8 mod d]",
        "actual_grid":{"m":10,"n":12,"k":1,"Ngrid":119,
                       "clipped_density":str(density),"old_marginal":"1"},
        "original_class_count":len(originals),"survivors":len(direct),
        "threshold":6,
        "tests":[{"mixed_point":list(point),"classes":[list(v) for v in test],
                  "incidences":{"r":12,"q":10,"u":1,"v":int(index == 0),"t":int(index == 0)},
                  "load_histogram":{str(k):v for k,v in sorted(direct_histograms[index].items())},
                  "hinge_numerator":direct_hinges[index],"hinge":str(values[index])}
                 for index,(point,test) in enumerate(zip(points,tests))],
        "hinge_difference":str(values[0]-values[1]),
        "kernel_thresholds_checked":[0,48],"kernel_equalities_checked":kernel_checks,
        "missing_information":"incidence of the actual mixed test point with its selected test row and column",
        "boundary":"The five-incidence kernel is exact for concentrated four-block tests; arbitrary labelled layouts require their actual cylinder arrangement or a justified concentration upper bound. This is not a refutation of supported-law or hinge upper bounds."
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
    lift_result = matching_height_lift()
    variable_head = varying_hole_head(deletion_result, signed_result)
    result = {
        "rectangle_hinge_observation_gap": rectangle_hinge_observation_gap(),
        "shared_count_clipped_head": shared_count_clipped_head(old_cases, deletion_result, signed_result),
        "variable_axis_clipping": variable_axis_clipped_head(expected["variable_axis_clipping"]["witnesses"], deletion_result, signed_result),
        "signed_conditioning_obstruction": signed_conditioning_obstruction(),
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
        "uniform315_energy_rebate_obstruction": uniform315_energy_rebate_obstruction(signed_result),
        "two_prime_block_grid_comparison": two_prime_block_grid_comparison(),
        "two_prime_block_gap": two_prime_block_gap_regression(),
        "punctured_grid_nonuniform_transfer": punctured_grid_nonuniform_transfer(signed_result),
        "matching_hole_common_lambda": matching_hole_common_lambda(),
        "matching_height_lift": lift_result,
        "arbitrary_hole_degree_symbolic": arbitrary_hole_degree_symbolic(),
        "varying_hole_head": variable_head,
        "arbitrary_holes12_tail17": arbitrary_holes12_tail17(variable_head["rows"][-1]),
        "matching_height_tail17": matching_height_tail17(deletion_result, lift_result),
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
                      "block_gap_regressions": result["two_prime_block_gap"]["grid_coefficient_cases"],
                      "nonuniform_block_factor": result["punctured_grid_nonuniform_transfer"]["Gamma_and_tensorization_constant"],
                      "matching_hole_symbolic_identities": len(result["matching_hole_common_lambda"]["symbolic_identities"]),
                      "matching_height_tail17_Gamma": result["matching_height_tail17"]["Gamma_upper"],
                      "arbitrary_holes12_tail17_Gamma": result["arbitrary_holes12_tail17"]["Gamma_upper"],
                      "shared_count_clipped_Gamma": result["shared_count_clipped_head"]["actual_rectangle_refinement"]["Gamma_upper"],
                      "shared_count_branches": result["shared_count_clipped_head"]["shared_branches_verified"],
                      "conditioned_3465_actual_second": result["conditioned_3465_comparison"]["actual_second_moment_upper"]}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("marked_head_profile_certificate.json"))
    args = parser.parse_args()
    verify(json.loads(args.certificate.read_text()))


if __name__ == "__main__":
    main()
