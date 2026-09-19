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
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
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


def common_rectangle_moment_transfer(mean, square, survival, coefficients):
    """Transfer moments on one old law using the checked rectangle coefficients."""
    F = Fraction
    mean, square, survival = map(F, (mean, square, survival))
    require(mean >= 1 and square >= 1 and 0 < survival <= 1,
            'common rectangle transfer has valid moments and positive mass')
    square_extra = F(coefficients['square_extra_coefficient_sum'])
    high_square = F(coefficients['high_square_coefficient'])
    positive_first = F(coefficients['positive_first_coefficient'])
    first_saving = F(coefficients['first_numerator_saving'])
    square_numerator = square-1+(square_extra+high_square)*square
    first_numerator = mean-1+positive_first*mean-first_saving
    require(square_numerator > 0 and first_numerator > 0,
            'positive common rectangle numerators before mass replacement')
    return {'Gamma_upper':str(1+square_numerator/survival),
            'same_law_first_upper':str(1+first_numerator/survival)}


def common_rectangle_moment_bounds(shared, diagonal):
    """Check one common PSD diagonal and the same-law first-moment saving.

    After removing the old-marginal term h*a^2, the actual low square
    is bounded by (f/120)*A^T B A, where B has rows
    (0,n,m,1), (n,n,1,1), (m,1,m,1), (1,1,1,1).
    All allocations and deleted-cell patterns obey this bound.  A checked
    diagonal dominates B for the largest allowed f in each rectangle;
    convex combination with the nonnegative diagonal covers every smaller f.
    """
    F = Fraction
    clip = F(shared['clip'])
    require(clip == F(40, 31), 'common rectangle uses the existing clipped law')
    caps = tuple(map(F, diagonal))
    require(len(caps) == 4 and all(c > 0 for c in caps),
            'four positive common diagonal coefficients')
    first_caps = (clip/10, clip/12, clip/120)
    first_sum = F(0)
    first_maximizers = []
    rectangles = grids = reconstruction_entries = 0
    smallest_pivots = [None]*4
    for m, n in product(range(1, 11), range(1, 13)):
        max_holes = min(12, m*n-1)
        density = min(clip, F(120, m*n-max_holes))
        b = ((0,n,m,1), (n,n,1,1), (m,1,m,1), (1,1,1,1))
        matrix = [[(caps[i] if i == j else 0)-density*b[i][j]/120
                   for j in range(4)] for i in range(4)]
        lower = [[F(i == j) for j in range(4)] for i in range(4)]
        pivots = [F(0)]*4
        for i in range(4):
            pivots[i] = matrix[i][i]-sum(lower[i][j]**2*pivots[j]
                                       for j in range(i))
            require(pivots[i] > 0, 'common rectangle diagonal positive LDL pivot')
            smallest_pivots[i] = (pivots[i] if smallest_pivots[i] is None
                                  else min(smallest_pivots[i], pivots[i]))
            for r in range(i+1, 4):
                lower[r][i] = (matrix[r][i]-sum(lower[r][j]*pivots[j]*lower[i][j]
                                               for j in range(i)))/pivots[i]
        for i, j in product(range(4), repeat=2):
            require(matrix[i][j] == sum(lower[i][r]*pivots[r]*lower[j][r]
                                       for r in range(4)),
                    'common rectangle exact LDL reconstruction')
            reconstruction_entries += 1
        rectangles += 1
        for k in range(max_holes+1):
            f = min(clip, F(120, m*n-k))
            require(0 < f <= density, 'every actual rectangle density is dominated')
            q = (f*n/120, f*m/120, f/120)
            require(all(x <= y for x, y in zip(q, first_caps)),
                    'actual rectangle first-moment coordinate caps')
            require(sum(q) <= F(11, 48), 'actual rectangle first-moment sum cap')
            if sum(q) > first_sum:
                first_sum, first_maximizers = sum(q), []
            if sum(q) == first_sum:
                first_maximizers.append([m, n, k])
            grids += 1
    saving = sum(first_caps)-first_sum
    require(rectangles == 120 and grids == 1372 and first_sum == F(11, 48)
            and saving == F(9, 496), 'complete common rectangle domain and first saving')
    coefficients = {
        'square_extra_coefficient_sum':str(sum(caps)),
        'high_square_coefficient':str(clip*(F(shared['square_reference_factor'])-F(13, 8))),
        'positive_first_coefficient':str(clip*(F(shared['reference_auxiliary_mean'])-1)),
        'first_numerator_saving':str(saving),
    }
    cases = []
    all_rows = []
    for index, case in enumerate(shared['cases']):
        rows = []
        for old_row in case['rows']:
            row = {'survivors':old_row['survivors'], **common_rectangle_moment_transfer(
                old_row['mean_upper'], old_row['square_upper'],
                old_row['full_mass_lower'], coefficients)}
            rows.append(row)
            all_rows.append((index, row))
        cases.append({'shape':case['shape'], 'rows':rows})
    require(len(all_rows) == 144, 'all existing common shape/count moment transfers')
    gamma_shape, gamma = max(all_rows, key=lambda item: F(item[1]['Gamma_upper']))
    mean_shape, mean = max(all_rows, key=lambda item: F(item[1]['same_law_first_upper']))
    return {
        'scope':'same existing clipped law and previous hinge bounds; arbitrary low axis and point patterns and finite 11/13 heights; full original 357 part divides 315; no new tail or Lean conclusion',
        'clip':str(clip), 'diagonal_witness':list(map(str, caps)), **coefficients,
        'positive_definite_rectangles_verified':rectangles,
        'ldl_reconstruction_entries_verified':reconstruction_entries,
        'ldl_pivot_lower_bounds':list(map(str, smallest_pivots)),
        'first_moment_grid_triples_verified':grids,
        'low_first_coordinate_caps':list(map(str, first_caps)),
        'low_first_coefficient_sum_upper':str(first_sum),
        'maximizing_first_grid_counts':first_maximizers,
        'shared_branches_verified':len(all_rows), 'cases':cases,
        'Gamma_upper':gamma['Gamma_upper'], 'worst_shape':gamma_shape,
        'worst_survivors':gamma['survivors'],
        'same_law_first_upper':mean['same_law_first_upper'],
        'worst_first_shape':mean_shape, 'worst_first_survivors':mean['survivors'],
    }


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
