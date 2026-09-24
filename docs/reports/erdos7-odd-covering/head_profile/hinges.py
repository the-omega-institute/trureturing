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


from head_profile.base import *

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


def actual_rectangle_hinge_profile(witnesses, shared, old, original_cases):
    """Check rectangle hinge duals and transfer them on the existing SC branches."""
    F = Fraction
    knots = list(range(4, 13))
    require(len(witnesses) == len(knots), 'nine rectangle hinge dual witnesses')
    geometries = []
    for m, n in product(range(1, 11), range(1, 13)):
        off = (m-1)*(n-1)
        for k in range(min(12, m*n-1)+1):
            left = max(0, k-off)
            geometries.append((max(93, m*n-k), k, off-min(k, off),
                               n-1-min(left, n-1), m-1-max(0, left-n+1),
                               n-1-max(0, left-m+1), m-1-min(left, m-1)))
    require(len(geometries) == 1372, 'complete nonempty rectangle geometry')
    checks = []
    for threshold, witness in zip(knots, witnesses):
        require(set(witness) == {'threshold', 'denominator', 'constant_numerator',
                                'load_hinge_numerators', 'hole_hinge_numerators'},
                'rectangle dual witness fields')
        denominator = witness['denominator']
        constant = witness['constant_numerator']
        weights = witness['load_hinge_numerators']
        holes = witness['hole_hinge_numerators']
        require(witness['threshold'] == threshold and type(denominator) is int
                and denominator > 0 and type(constant) is int,
                'integer rectangle dual scale and threshold')
        require(len(weights) == 4 and all(len(v) == 12 for v in weights)
                and len(holes) == 12, 'rectangle dual coefficient dimensions')
        require(all(type(v) is int and v >= 0 for row in weights+[holes] for v in row),
                'nonnegative integer rectangle dual weights')
        costs = [[sum(w*max(x-t, 0) for t, w in enumerate(row))
                  for x in range(13)] for row in weights]
        hole_costs = [sum(w*max(k-t, 0) for t, w in enumerate(holes))
                      for k in range(13)]
        minimum_rhs = constant+sum(row[1] for row in costs)
        require(minimum_rhs >= 0, 'empty fibres: minimum full dual RHS is nonnegative')
        point = weights[3]
        point_knots = [t for t, w in enumerate(point) if w]
        require(point[0] == 0 and point_knots and min(point_knots) >= 1
                and 93*sum(point) >= denominator,
                'point-load endpoint reduction and terminal slope')
        # Before its first knot the cost is constant and the target increases.
        # Between knots the target minus the linear cost is convex in d.
        # Beyond the last knot its slope is <=1/93, paid by the dual cost.
        phi = [max(x-threshold, 0) for x in range(49)]
        inputs = []
        for a, b, c in product(range(1, 13), repeat=3):
            dual = constant+costs[0][a]+costs[1][b]+costs[2][c]
            inputs.append((b <= c, phi[a], phi[a+b], phi[a+c],
                           [(phi[a+b+c+d], dual+costs[3][d]) for d in point_knots]))
        checked = 0
        minimum_slack = None
        for den, k, base, row_bc, col_bc, row_cb, col_cb in geometries:
            hole_cost = hole_costs[k]
            for b_le_c, pa, pab, pac, corners in inputs:
                row, col = (row_bc, col_bc) if b_le_c else (row_cb, col_cb)
                rest = base*pa+row*pab+col*pac
                for corner, dual in corners:
                    slack = den*(dual+hole_cost)-denominator*(rest+corner)
                    require(slack >= 0, 'actual rectangle hinge dual integer inequality')
                    if minimum_slack is None or slack < minimum_slack:
                        minimum_slack = slack
                    checked += 1
        checks.append({'threshold':threshold, 'point_load_endpoints':point_knots,
                       'integer_inequalities_verified':checked,
                       'minimum_integer_slack':minimum_slack,
                       'minimum_empty_fibre_dual_numerator':minimum_rhs})
    require(sum(v['integer_inequalities_verified'] for v in checks) == 26078976,
            'complete nine-threshold endpoint-reduced integer checks')
    high_numerators = (10, 7, 4, 3, 2, 1, 0)
    require(len(shared['cases']) == len(old['cases']) == len(original_cases) == 6,
            'same six canonical old shapes for hinge transfer')
    clip = F(40, 31)
    require(F(shared['clip']) == clip, 'same clipping constant for all hinge knots')
    cases = []
    branches = []
    for sc, old_case, original in zip(shared['cases'], old['cases'], original_cases):
        shape = sc['shape']
        require(shape == old_case['shape'] == original['shape'],
                'same branch indexing for existing hinge bounds')
        minimum = original['survivor_count_range_inclusive'][0]
        require([minimum*F(v) for v in original['profile'][6:13]]
                == list(high_numerators), 'existing complete-profile high-hinge numerators')
        old_hinges = list(map(F, old_case['hinge_bounds_at_0_through_5']))
        rows = []
        for source in sc['rows']:
            count = source['survivors']
            mean = F(source['mean_upper'])
            theta = [mean, mean-1, F(source['hinge2_upper']), old_hinges[3],
                     F(source['hinge4_upper']), old_hinges[5]]
            theta += [F(v, count) for v in high_numerators]
            require(len(theta) == 13 and all(v >= 0 for v in theta),
                    'canonical existing same-branch hinge bounds')
            low_mass = 1-(17*theta[2]+4*theta[4])/93
            high = clip*F(89, 4800)*mean
            survival = low_mass-high
            require(low_mass == F(source['low_mass_lower'])
                    and survival == F(source['full_mass_lower']) > 0,
                    'same-branch high-load addition and full normalization')
            low = []
            full = []
            for witness in witnesses:
                numerator = F(witness['constant_numerator'])
                numerator += sum(w*theta[t] for row in witness['load_hinge_numerators']
                                 for t, w in enumerate(row))
                numerator += sum(w*theta[t]
                                 for t, w in enumerate(witness['hole_hinge_numerators']))
                bound = numerator/witness['denominator']
                require(bound >= 0, 'nonnegative averaged rectangle hinge bound')
                low.append(bound)
                full.append((bound+high)/survival)
            row = {'survivors':count, 'low_hinge_upper_at_4_through_12':list(map(str, low)),
                   'full_hinge_upper_at_4_through_12':list(map(str, full))}
            rows.append(row)
            branches.append((shape, count, low, full))
        cases.append({'shape':shape, 'rows':rows})
    require(len(branches) == 144, 'all existing common shape/count branches transferred')
    low_maxima = [max(row[2][j] for row in branches) for j in range(9)]
    full_maxima = [max(row[3][j] for row in branches) for j in range(9)]
    worst = [[{'shape':row[0], 'survivors':row[1]} for row in branches
              if row[3][j] == full_maxima[j]] for j in range(9)]
    return {'scope':'ordinary exact-arithmetic hinge bounds for the same actual clipped survivor law; full original 357 part divides 315; arbitrary finite 11/13 heights; no Lean or tail conclusion',
            'clip':str(clip), 'thresholds':knots, 'witnesses':witnesses,
            'pointwise_dual_checks':checks, 'nonempty_grid_counts_verified':len(geometries),
            'integer_inequalities_verified':sum(v['integer_inequalities_verified'] for v in checks),
            'full_domain_inequalities_certified':9*len(geometries)*12**4,
            'shared_branches_verified':len(branches), 'cases':cases,
            'universal_low_hinge_upper_at_4_through_12':list(map(str, low_maxima)),
            'universal_full_hinge_upper_at_4_through_12':list(map(str, full_maxima)),
            'full_hinge_maximizing_branches_at_4_through_12':worst,
            'interpolation':'adjacent certified knots may be joined linearly to upper-bound the convex actual hinge; the resulting upper curve is not asserted to be a probability comparator'}


def fixed_count_joint_cost_comparison(old_cases):
    """Bound two joint convex costs at N=80,81,82 using labelled deletion unions.

    Standard library only. Jbar(A) uses old hinge maxima, never A x B pairs.
    Every original mixed7 label is inactive or belongs to one of at most five
    nonzero7digit blocks. A block deletes a union of its old45 cylinders.
    Anchored partition DP minimizes the deleted cost at its exact cardinality.
    """
    from fractions import Fraction
    from itertools import product

    def require(condition, message):
        if not condition:
            raise RuntimeError(message)

    shape, points, _, expected_layouts = old_cases[0]
    require(shape == 'root1_same_other_column' and len(points) == 17
            and expected_layouts == 4760, 'first canonical shape for fixed-count costs')
    moduli = (3, 5, 9, 15, 45)
    cylinders = [[sum(1 << i for i, x in enumerate(points) if x % d == a)
                  for a in sorted({x % d for x in points})] for d in moduli]
    unions = [{0}]
    for subset in range(1, 32):
        bit = subset & -subset
        label = bit.bit_length() - 1
        unions.append({old | cylinder for old in unions[subset ^ bit]
                       for cylinder in [0] + cylinders[label]})
    require(len(unions[31]) == 2164 and sum(map(len, unions)) == 8919,
            'all labelled cylinder subset unions')
    mask_indices = {mask: tuple(i for i in range(17) if mask & (1 << i))
                    for mask in unions[31]}
    layouts = [tuple(1 + sum(bool(mask & (1 << i)) for mask in choices)
                     for i in range(17)) for choices in product(*cylinders)]
    require(len(layouts) == expected_layouts, 'all old45 test layouts')
    hinge_sums = [tuple(sum(max(v - t, 0) for v in load) for t in range(7))
                  for load in layouts]
    maxima = [max(row[t] for row in hinge_sums) for t in range(7)]
    require(maxima == [42, 25, 11, 5, 2, 1, 0], 'old45 hinge maxima including zero tail')
    costs = ({1: 1, 2: 2, 3: 16, 6: 74}, {1: 1, 3: 9, 4: 2})
    survivor_counts = (80, 81, 82)
    deleted_counts = (22, 21, 20)
    targets = ((1986, 1986, 1992), (728, 728, 732))
    max_deleted = max(deleted_counts)
    cost_rows = []
    for cost, target in zip(costs, targets):
        table = [sum(weight * max(v - t, 0) for t, weight in cost.items())
                 for v in range(7)]
        screened = exact = 0
        minimum_exact_slacks = [None] * 3
        for load, hinges_a in zip(layouts, hinge_sums):
            values = [table[v] for v in load]
            joint_upper = sum(weight * min(hinges_a[s] + maxima[t - s]
                                          for s in range(t + 1))
                              for t, weight in cost.items())
            total = 5 * sum(values) + joint_upper
            ordered = sorted(values * 5)
            cheap_loss = [sum(ordered[:deleted]) for deleted in deleted_counts]
            for eta in set([0] + values):
                positive = [max(eta - value, 0) for value in values]
                cap = sum(max(sum(positive[i] for i in mask_indices[mask])
                              for mask in group) for group in cylinders)
                cheap_loss = [max(loss, eta * deleted - cap)
                              for loss, deleted in zip(cheap_loss, deleted_counts)]
            if all(total - loss <= bound for loss, bound in zip(cheap_loss, target)):
                screened += 1
                continue
            exact += 1
            mask_cost = {mask: sum(values[i] for i in indices)
                         for mask, indices in mask_indices.items()}
            blocks = []
            for group in unions:
                by_count = {}
                for mask in group:
                    size, value = mask.bit_count(), mask_cost[mask]
                    if size not in by_count or value < by_count[size]:
                        by_count[size] = value
                blocks.append(by_count)
            dp = [{0: 0}] + [{} for _ in range(31)]
            for subset in range(1, 32):
                anchor = subset & -subset
                first = subset
                while first:
                    if first & anchor:
                        for left_size, left_value in blocks[first].items():
                            for right_size, right_value in dp[subset ^ first].items():
                                size = left_size + right_size
                                value = left_value + right_value
                                if size <= max_deleted and (size not in dp[subset]
                                                            or value < dp[subset][size]):
                                    dp[subset][size] = value
                    first = (first - 1) & subset
            for index, (deleted, bound, cheap) in enumerate(zip(deleted_counts, target, cheap_loss)):
                require(deleted in dp[31], 'every checked fixed deletion count is feasible')
                loss = dp[31][deleted]
                require(loss >= cheap, 'exact original-label deletion refines the cheap lower bound')
                slack = bound - (total - loss)
                require(slack >= 0, 'fixed-count joint convex cost upper bound')
                old = minimum_exact_slacks[index]
                minimum_exact_slacks[index] = slack if old is None else min(old, slack)
        require(screened + exact == expected_layouts and minimum_exact_slacks == [0, 0, 0],
                'all layouts discharged with active exact comparisons')
        cost_rows.append({
            'hinge_weights': {str(k): v for k, v in cost.items()},
            'numerator_upper': list(target),
            'mean_upper': [str(Fraction(value, count)) for value, count in zip(target, survivor_counts)],
            'cheap_screened_layouts': screened,
            'exact_partition_layouts': exact,
            'minimum_exact_slacks': minimum_exact_slacks,
        })
    require([row['exact_partition_layouts'] for row in cost_rows] == [72, 120],
            'screened candidate cardinalities')
    return {
        'shape': shape,
        'law': 'uniform on actual complete old315 survivors',
        'old_test_layouts': expected_layouts,
        'survivor_counts': list(survivor_counts),
        'deleted_counts': list(deleted_counts),
        'maximum_old_hinge_sums_at_0_through_6': maxima,
        'union_counts_by_label_subset': list(map(len, unions)),
        'costs': cost_rows,
    }


def fixed_count_hinge_refinement(costs, shared, old, profile):
    """Use actual labelled deletion costs in the same-law threshold-six dual."""
    F = Fraction
    weights = ({1: 1, 2: 2, 3: 16, 6: 74}, {1: 1, 3: 9, 4: 2},
               {2: 1, 3: 7, 4: 2}, {2: 1})
    witness = profile['witnesses'][2]
    require(witness['threshold'] == 6 and witness['constant_numerator'] == 0,
            'the verified threshold-six rectangle dual')
    scale = witness['denominator']
    require(all(F(value, scale) == F(cost.get(t, 0), 93)
                for row, cost in zip(witness['load_hinge_numerators'], weights)
                for t, value in enumerate(row))
            and all(F(value, scale) == (F(7, 1984) if t == 8 else 0)
                    for t, value in enumerate(witness['hole_hinge_numerators'])),
            'the joint costs match the verified dual exactly')
    require([row['hinge_weights'] for row in costs['costs']]
            == [{str(t): value for t, value in cost.items()} for cost in weights[:2]],
            'the recomputed labelled-deletion costs match their consumers')
    require(len(shared['cases']) == len(old['cases']) == len(profile['cases']) == 6,
            'all six canonical shapes in the fixed-count transfer')
    branches = []
    improved = []
    for sc, previous, geometric in zip(shared['cases'], old['cases'], profile['cases']):
        require(sc['shape'] == previous['shape'] == geometric['shape'],
                'same shapes in joint-cost and geometric bounds')
        old_hinges = list(map(F, previous['hinge_bounds_at_0_through_5']))
        require(len(sc['rows']) == len(geometric['rows']), 'same survivor-count branches')
        for source, baseline in zip(sc['rows'], geometric['rows']):
            count = source['survivors']
            require(count == baseline['survivors'], 'same actual old survivor count')
            mean = F(source['mean_upper'])
            theta = [mean, mean-1, F(source['hinge2_upper']), old_hinges[3],
                     F(source['hinge4_upper']), old_hinges[5]]
            theta += [F(v, count) for v in (10, 7, 4, 3, 2, 1, 0)]
            caps = [sum(v*theta[t] for t, v in cost.items()) for cost in weights]
            raw = sum(caps)/93 + F(7, 1984)*theta[8]
            require(raw == F(baseline['low_hinge_upper_at_4_through_12'][2]),
                    'unrefined joint costs reproduce the canonical rectangle bound')
            if sc['shape'] == costs['shape'] and count in costs['survivor_counts']:
                index = costs['survivor_counts'].index(count)
                for j in range(2):
                    caps[j] = min(caps[j], F(costs['costs'][j]['numerator_upper'][index], count))
            refined_raw = sum(caps)/93 + F(7, 1984)*theta[8]
            high = F(shared['clip'])*F(shared['high_reference_mass_per_old_mean'])*mean
            survival = F(source['full_mass_lower'])
            require(survival > 0 and refined_raw <= raw,
                    'positive same-branch normalization and valid refinement')
            full = (refined_raw+high)/survival
            require(full <= F(baseline['full_hinge_upper_at_4_through_12'][2]),
                    'same-law full-height hinge refinement')
            row = {'shape':sc['shape'], 'survivors':count,
                   'old_joint_cost_upper':list(map(str, caps)),
                   'low_hinge6_upper':str(refined_raw), 'full_hinge6_upper':str(full)}
            branches.append(row)
            if refined_raw < raw:
                improved.append({'shape':sc['shape'], 'survivors':count})
    maximum = max(F(row['full_hinge6_upper']) for row in branches)
    require(len(branches) == 144 and len(improved) == 3
            and maximum == F(26114497, 32685768) < F(4, 5),
            'complete exact all-height hinge-six bound below four fifths')
    return {'scope':profile['scope'], 'fixed_count_joint_costs':costs,
            'shared_branches_verified':len(branches), 'branches':branches,
            'improved_branches':improved,
            'universal_full_hinge6_upper':str(maximum),
            'gap_below_four_fifths':str(F(4, 5)-maximum),
            'full_hinge6_maximizing_branches':[
                {'shape':row['shape'], 'survivors':row['survivors']}
                for row in branches if F(row['full_hinge6_upper']) == maximum],
            'prime17_threshold6_charge_upper':str(maximum/10),
            'interpolation':'replace the threshold-six knot in the rectangle profile by this upper bound; adjacent-knot interpolation is valid for the convex actual hinge, without asserting a probability comparator'}


def joint_cost_hinge_refinement(old_cases, shared, old, profile, fixed):
    """Keep one old layout and labelled deletion cost for each whole convex cost."""
    from itertools import accumulate
    from math import gcd
    F = Fraction
    costs, assignments = [], []
    for witness in profile['witnesses']:
        terms = []
        for row in witness['load_hinge_numerators'] + [witness['hole_hinge_numerators']]:
            scale = gcd(*row)
            normal = tuple(v // scale for v in row) if scale else (0,) * 12
            if normal not in costs:
                costs.append(normal)
            terms.append((costs.index(normal), scale))
        assignments.append(terms)
    require(len(costs) == 32 and len(assignments) == 9,
            'all normalized test and activation costs from the rectangle duals')
    require(len(old_cases) == len(shared['cases']) == len(old['cases']) == len(profile['cases']) == 6,
            'six old shapes in the joint convex-cost transfer')
    cases, branches = [], []
    checks = layouts_checked = 0
    for case_index, (shape, points, _, expected) in enumerate(old_cases):
        n = len(points)
        sc = shared['cases'][case_index]
        previous = old['cases'][case_index]
        require(shape == sc['shape'] == previous['shape'] == profile['cases'][case_index]['shape'],
                'same actual old shape in every joint-cost bound')
        groups = [[tuple(i for i, x in enumerate(points) if x % d == a)
                   for a in sorted({x % d for x in points})] for d in MODULI]
        layouts = []
        for cylinders in product(*groups):
            load = [1] * n
            for cylinder in cylinders:
                for i in cylinder:
                    load[i] += 1
            layouts.append(tuple(load))
        require(len(layouts) == expected, 'complete effective old test layouts for joint costs')
        layouts_checked += expected
        hs = [tuple(sum(max(v-t, 0) for v in a) for t in range(13)) for a in layouts]
        maxima = [max(h[t] for h in hs) for t in range(13)]
        counts = [source['survivors'] for source in sc['rows']]
        deletions = [6*n-count for count in counts]
        numerators = []
        for cost in costs:
            table = [sum(w*max(v-t, 0) for t, w in enumerate(cost)) for v in range(13)]
            nonzero = [(t, w) for t, w in enumerate(cost) if w]
            tops = [0] * len(counts)
            for a, h in zip(layouts, hs):
                values = [table[v] for v in a]
                joint = sum(w*min(h[s]+maxima[t-s] for s in range(t+1)) for t, w in nonzero)
                total = 5*sum(values)+joint
                least = [0] + list(accumulate(sorted(values*5)))
                label_bounds = []
                for eta in set([0] + values):
                    positive = [max(eta-v, 0) for v in values]
                    cap = sum(max(sum(positive[i] for i in c) for c in group) for group in groups)
                    label_bounds.append((eta, cap))
                for j, deleted in enumerate(deletions):
                    loss = max([least[deleted]] + [eta*deleted-cap for eta, cap in label_bounds])
                    tops[j] = max(tops[j], total-loss)
                    checks += 1
            numerators.append(tops)
        old_hinges = list(map(F, previous['hinge_bounds_at_0_through_5']))
        rows = []
        for j, source in enumerate(sc['rows']):
            count, mean = source['survivors'], F(source['mean_upper'])
            theta = [mean, mean-1, F(source['hinge2_upper']), old_hinges[3],
                     F(source['hinge4_upper']), old_hinges[5]]
            theta += [F(v, count) for v in (10, 7, 4, 3, 2, 1, 0)]
            full = []
            for wi, witness in enumerate(profile['witnesses']):
                chosen = []
                for role, (cost_index, scale) in enumerate(assignments[wi]):
                    separate = sum(v*theta[t] for t, v in enumerate(costs[cost_index]))*scale
                    cap = min(F(numerators[cost_index][j]*scale, count), separate)
                    joint_fixed = fixed['fixed_count_joint_costs']
                    if (witness['threshold'] == 6 and shape == joint_fixed['shape']
                            and count in joint_fixed['survivor_counts'] and role < 2):
                        index = joint_fixed['survivor_counts'].index(count)
                        known = joint_fixed['costs'][role]['numerator_upper'][index]
                        # fixed_count_hinge_refinement verifies the factor 1/93 in this dual.
                        cap = min(cap, F(known*witness['denominator'], 93*count))
                    chosen.append(cap)
                low = (witness['constant_numerator']+sum(chosen))/witness['denominator']
                high = F(shared['clip'])*F(shared['high_reference_mass_per_old_mean'])*mean
                survival = F(source['full_mass_lower'])
                require(low >= 0 and survival > 0, 'joint-cost nonnegativity and same-branch survival')
                full.append((low+high)/survival)
            baseline = list(map(F, profile['cases'][case_index]['rows'][j]['full_hinge_upper_at_4_through_12']))
            require(all(a <= b for a, b in zip(full, baseline)), 'every whole-cost hinge refines the old bound')
            rows.append({'survivors':count, 'full_hinge_upper_at_4_through_12':list(map(str, full))})
            branches.append((shape, count, full))
        cases.append({'shape':shape, 'survivor_counts':counts,
                      'normalized_cost_numerator_upper':numerators, 'rows':rows})
    maxima = [max(row[2][j] for row in branches) for j in range(9)]
    require(layouts_checked == 27720 and len(branches) == 144
            and maxima[2] == F(321137, 403528) < F(fixed['universal_full_hinge6_upper']),
            'complete joint-cost profile and strict threshold-six improvement')
    return {'scope':profile['scope'], 'thresholds':profile['thresholds'],
            'normalized_hinge_costs':[list(row) for row in costs],
            'normalized_cost_count':len(costs), 'old_layouts_verified':layouts_checked,
            'layout_cost_count_bounds_verified':checks, 'shared_branches_verified':len(branches),
            'cases':cases, 'universal_full_hinge_upper_at_4_through_12':list(map(str, maxima)),
            'full_hinge_maximizing_branches_at_4_through_12':[
                [{'shape':shape, 'survivors':count} for shape, count, full in branches if full[j] == value]
                for j, value in enumerate(maxima)],
            'prime17_threshold6_charge_upper':str(maxima[2]/10),
            'interpolation':profile['interpolation']}


def joint_cost_branch_tail17(shared, old, joint):
    """Certify unrestricted tail continuation for one actual full-fibre old branch."""
    from runpy import run_path
    F = Fraction
    a = run_path(str((Path(__file__).resolve().parents[1] / 'verify_star_block_obstruction.py')))
    b = run_path(str((Path(__file__).resolve().parents[1] / 'verify_finite_continuation.py')))
    def ceildiv(x,y):
     require(y>0,'positive denominator');return -((-x)//y)
    S=10**24
    up=lambda q:ceildiv(F(q).numerator*S,F(q).denominator)
    shape='root2_same_other_column';N=96
    sc=shared;source=next(r for c in sc['cases'] if c['shape']==shape for r in c['rows'] if r['survivors']==N)
    survival_head=F(source['full_mass_lower']);clip=F(sc['clip']);old_g=F(source['square_upper']);chi=F(sc['square_reference_factor'])
    MF=F(source['same_law_first_upper']);GF=1+(old_g-1+clip*(chi-1)*old_g-F(9,496)*old_g-F(19,496))/survival_head
    require(MF==F(1134400,266709) and GF==F(35754161,1333545),'canonical branch moments')
    C=up(MF);G=up(GF);ell=survival_head/clip
    knots=next(r['full_hinge_upper_at_4_through_12'] for c in joint['cases'] if c['shape']==shape for r in c['rows'] if r['survivors']==N)
    H={t:up(F(x)) for t,x in zip(range(4,13),knots)}
    k=6;D=k*(k-1)
    low_coefficient=D*S-(2*k+1)*(C-S)+(G-S)
    require(0<=low_coefficient<=D*S,'middle moment correction coefficient')
    X={int(k):F(p) for k,p in old['auxiliary_atoms'].items()}
    oldmean=sum(x*p for x,p in X.items())
    def p_factor(p,f):return F(p-2,p-1) if f==1 else F(1,p**(f-1))
    # Positive reference convolution; no subtraction of nearly equal moments.
    L=80
    fp11=[None]+[p_factor(11,f) for f in range(1,L+1)]
    fp13=[None]+[p_factor(13,f) for f in range(1,L+1)]
    y=[0]*(12*L*L+1)
    for x,mass in X.items():
     for f in range(1,L+1):
      for g in range(1,L+1):y[x*f*g]+=up(mass*fp11[f]*fp13[g])
    tail=call=0;yc=[0]*len(y)
    for j in range(len(y)-1,-1,-1):
     yc[j]=call;tail+=y[j];call+=tail
    # E[N_p; N_p>L] is the exact geometric tail mean.
    def tail_mean(p):return F(1,p**(L-1))*(F(L+1,p-1)+F(1,(p-1)**2))
    error=up(oldmean*(F(157,144)*tail_mean(11)+F(111,100)*tail_mean(13)))
    ref=[ceildiv((v+error)*ell.denominator,ell.numerator) for v in yc]
    # At r=3 the generic density domination gives this affine upper bound.
    # Use the positive convolution itself, so the same rounding controls both sides.
    Rmean=3*S+ref[3]
    require(Rmean>=C,'reference bound above the fixed affine baseline')
    def correction(T,n):
     # Upper bound for n*Psi(T/n)-C*n/S+T, scaled by S. Psi>=C-t by definition.
     subtract=C*n-T*S
     if T<=3*n:
      rc=n*(Rmean-C)
     else:
      j,r=divmod(T,n)
      rc=(n-r)*ref[j]+r*ref[j+1]-subtract
     if T*(2*k+1)<=n*(k*k+k+1):
      mc=ceildiv(low_coefficient*(T-n),D)
     else:
      j=max(k+1,2*T//n)
      if T*(2*j+1)>n*(j*j+j+1):j+=1
      mc=ceildiv((G-S)*(j*n-T),j*j-1)-subtract
     result=min(rc,mc)
     if 4*n<=T<=12*n:
      j,r=divmod(T,n)
      gc=n*H[12] if j==12 else (n-r)*H[j]+r*H[j+1]
      result=min(result,gc-subtract)
     return max(0,result)
    runs=((17,4),(19,5),(31,8),(41,12),(61,16),(73,24),(113,32),(151,48),
          (211,64),(229,72),(293,96),(419,128),(449,144),(577,192),(809,256),
          (883,288),(1153,384),(1601,512),(1787,576),(2377,768),(3271,1024),
          (3719,1152),(5051,1536),(7019,2048),(8117,2304),(8191,3072))
    B=30011;primes=list(b['segmented_primes'](0,B));choices=[];run_index=0
    for q in primes:
     if q<17:continue
     if q<=8191:
      while q>runs[run_index][0]:run_index+=1
      T=runs[run_index][1]
     else:T=1+3*(q-2)//8
     choices.append((q,T))
    require(all(1<T<q-1 for q,T in choices),'normalized kernel domain')
    cap=max(T for q,T in choices)
    w=[0]*(cap+1);w[1]=S;mean=S;second=G;charge=0
    rows=[];corr_cache={}
    for idx,(q,T) in enumerate(choices):
     s=q-1-T
     if T not in corr_cache:
      corr_cache[T]=[0]+[correction(T,n) for n in range(1,T)]
     corr=corr_cache[T]
     numerator=C*mean-T*S*S+sum(w[n]*corr[n] for n in range(1,T))
     require(numerator>=0,'nonnegative charge numerator upper')
     step=ceildiv(numerator,S*s);charge+=step
     require(charge<S,'strict positive survival at every prefix')
     second=ceildiv(second*((q-1)*s+3*q-1),(q-1)*s)
     if idx+1<len(choices):
      w=a['stoploss_product_update'](w,a['stoploss_atom_bounds'](q,F(q-1,s),cap,S),S)
      mean=ceildiv(mean*(s+1),s)
     if q in (17,997,8191,B):
      rows.append({'q':q,'T':T,'charge_upper':str(F(charge,S)), 'second_upper':str(F(second,S))})
     # Only the current repeated threshold and future states are useful.
     if idx+1<len(choices) and choices[idx+1][1]!=T:del corr_cache[T]
    gamma=1+F(second-S,S-charge);stop=b['stopping_threshold'](len(primes))
    require(gamma<stop,'strict exact stopping inequality')
    output={'scope':'ordinary exact directed arithmetic; root2_same_other_column,N96 supported head and AP2/AP5/AP6 required','scale':S,'shape':shape,'old_survivors':N,'head_mean_upper':str(MF),'head_square_upper':str(GF),'head_reference_density_fraction':str(ell),'head_hinge_upper_at_4_through_12':knots,'first_tail_prime':17,'last_prime':B,'global_prime_index':len(primes),'steps_verified':len(choices),'prefix_threshold_runs':[list(row) for row in runs],'later_threshold_formula':'1+floor(3*(q-2)/8)','retained_product_states':cap,'reference_factor_cutoff':L,'reference_tail_mean_scaled_upper':error,'total_charge_upper':str(F(charge,S)),'second_upper':str(F(second,S)),'survival_lower':str(F(S-charge,S)),'Gamma_upper':str(gamma),'stopping_lower':str(stop),'stopping_margin':str(stop-gamma),'checkpoints':rows}
    old_classes=[(3,0),(9,4),(5,0),(15,11),(45,2),(7,0)]+[(7*d,0) for d in MODULI]
    points=old_head(2,'same_other_column')[0]
    survivors=[x for x in range(315) if all(x%d!=a for d,a in old_classes)]
    require(len(points)==16 and len(survivors)==96 and
            all((x in survivors)==(x%45 in points and x%7!=0) for x in range(315)),
            'actual complete original family realizes the full-fibre branch')
    output['actual_old_family']=[list(row) for row in old_classes]
    output['actual_old_survivors_verified']=len(survivors)
    return output
