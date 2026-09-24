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
