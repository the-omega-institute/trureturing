#!/usr/bin/env python3
"""Exact scope checks for the reused six-shape head and shallow extension.

This is ordinary finite verification, not Lean verification.  The six constants are existing repository results;
their threshold-one finite inequalities are independently reconstructed here.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product, combinations
from math import prod
from pathlib import Path
import json


def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)


OLD = (3, 9, 5, 15, 45)
QUERY = (3, 5, 9, 15, 45)
HEAD = tuple(c for c in range(1, 316) if 315 % c == 0)
ALL45 = (1 << 45) - 1
MASKS = {m: tuple(sum(1 << x for x in range(a, 45, m))
                  for a in range(m)) for m in OLD}
CATEGORIES = ('same_other_column', 'other_same_column', 'other_other_column')
CONSTANTS = ((77, F(185, 86)), (78, F(178, 85)), (78, F(178, 85)),
             (75, F(2)), (74, F(157, 77)), (74, F(157, 77)))
SQUARES = (F(1091, 82), F(1103, 85), F(1103, 85),
           F(965, 76), F(993, 77), F(993, 77))


def crt45(a9, a5):
    return next(x for x in range(a9, 45, 9) if x % 5 == a5)


def canonical(root, category):
    other = 3 - root
    row, col = {'same_other_column': (root, 2),
                'other_same_column': (other, 1),
                'other_other_column': (other, 2)}[category]
    a15 = next(x for x in range(root, 15, 3) if x % 5 == 1)
    phases = (0, 4, 0, a15, crt45(row, col))
    union = 0
    for m, a in zip(OLD, phases):
        union |= MASKS[m][a]
    return phases, ALL45 ^ union


CANONICAL = {canonical(r, c)[1]: (r, c) for r, c in product((1, 2), CATEGORIES)}
need(len(CANONICAL) == 6, 'six distinct canonical old survivors')


def prune(phases):
    union = 0
    chosen = []
    moved = []
    original_prefix = 0
    for m, a in zip(OLD, phases):
        oldmask = MASKS[m][a]
        original_prefix |= oldmask
        if oldmask & ~union == 0:
            live = ALL45 ^ union
            need(live != 0, 'each redundant move has an actual live point')
            first = (live & -live).bit_length() - 1
            a = first % m
            moved.append(m)
        union |= MASKS[m][a]
        need(original_prefix & ~union == 0, 'no original deletion is uncovered')
        chosen.append(a)
    return tuple(chosen), ALL45 ^ union, tuple(moved)


def normalize(phases):
    a3, a9, a5, a15, a45 = phases
    short = a9 % 3
    need(short != a3, 'pruned 9 is outside the forbidden 3 root')
    long = next(r for r in range(3) if r not in (a3, short))
    rootmap = {a3: 0, short: 1, long: 2}
    pi9 = {}
    for oldroot in range(3):
        newroot = rootmap[oldroot]
        olds = list(range(oldroot, 9, 3))
        news = list(range(newroot, 9, 3))
        if oldroot == short:
            pi9[a9] = 4
            olds.remove(a9)
            news.remove(4)
        if a45 % 3 == oldroot:
            need(a45 % 9 in olds, 'effective45 avoids forbidden9')
            target = newroot
            pi9[a45 % 9] = target
            olds.remove(a45 % 9)
            news.remove(target)
        pi9.update(zip(olds, news))
    pi5 = {a5: 0, a15 % 5: 1}
    need(len(pi5) == 2, 'effective15 avoids pure5')
    if a45 % 5 != a15 % 5:
        need(a45 % 5 != a5, 'effective45 avoids pure5')
        pi5[a45 % 5] = 2
    pi5.update(zip((r for r in range(5) if r not in pi5),
                   (r for r in range(5) if r not in pi5.values())))
    perm = tuple(crt45(pi9[x % 9], pi5[x % 5]) for x in range(45))
    need(len(set(perm)) == 45, 'one common45 permutation is bijective')
    return perm


def audit_all_originals():
    cases = Counter()
    moved = Counter()
    normalizations = {}
    assignments = 0
    for original in product(*(range(m) for m in OLD)):
        phases, support, changed = prune(original)
        assignments += 1
        moved.update(changed)
        if phases not in normalizations:
            perm = normalize(phases)
            image = sum(1 << perm[x] for x in range(45) if support >> x & 1)
            need(image in CANONICAL, 'one common normalization lands in six cases')
            for m in QUERY:
                for a, mask in enumerate(MASKS[m]):
                    image_mask = sum(1 << perm[x] for x in range(a, 45, m))
                    target_a = perm[a] % m
                    need(image_mask == MASKS[m][target_a],
                         'normalization preserves every numerical divisor cylinder')
            normalizations[phases] = CANONICAL[image]
        root, category = normalizations[phases]
        need(support.bit_count() == (17 if root == 1 else 16), 'old support size')
        cases[f'root{root}_{category}'] += 1
    need(assignments == 91125, 'all actual complete45 original phase assignments')
    return {'complete45_original_assignments': assignments,
            'distinct_pruned_normalizations': len(normalizations),
            'assignments_by_final_shape': dict(sorted(cases.items())),
            'redundant_replacements_by_numerical_modulus': dict(sorted(moved.items())),
            'scope': 'Every complete45 family; missing slots first padded. '
                     'All7-containing originals and all outside projections remain actual '
                     'and are transported by this one common permutation.'}


def recheck_mean_column():
    rows = []
    for (root, category), (Nmin, c1), square in zip(
            product((1, 2), CATEGORIES), CONSTANTS, SQUARES):
        phases, support = canonical(root, category)
        points = [x for x in range(45) if support >> x & 1]
        n = len(points)
        masks = [sorted({mask & support for mask in MASKS[d]} - {0}) for d in QUERY]
        index_cylinders = [[tuple(i for i, x in enumerate(points) if mask >> x & 1)
                            for mask in group] for group in masks]
        maxima = [max(mask.bit_count() for mask in group) for group in masks]
        M1 = sum(maxima)
        need(6 * n - M1 == Nmin, 'inherited minimum315 count from five cylinder caps')
        p, q = c1.numerator, c1.denominator
        sp, sq = square.numerator, square.denominator
        loads = [[1 + sum(mask >> x & 1 for mask in choices) for x in points]
                 for choices in product(*masks)]
        Q = max(sum(a * a for a in A) for A in loads)
        count = 0
        min_slack = None
        min_square_slack = None
        for A in loads:
            weights = [max(p - q * (a - 1), 0) for a in A]
            # D2 at t=1, with exact max_B sum(A+B-1)=sum(A)+M1.
            lhs = q * (6 * sum(A) - 5 * n + M1)
            lhs += sum(max(sum(weights[i] for i in cylinder) for cylinder in group)
                       for group in index_cylinders)
            slack = 6 * n * p - lhs
            need(slack >= 0, 'every exact threshold-one deletion-sensitive cap inequality')
            min_slack = slack if min_slack is None else min(min_slack, slack)
            # Independently reconstruct D4, the existing shape-specific square column.
            R = sum(A) + sum(max(sum(A[i] for i in cylinder) for cylinder in group)
                             for group in index_cylinders)
            weights2 = [max(sp - sq * a * a, 0) for a in A]
            lhs2 = sq * (6 * sum(a * a for a in A) + 2 * R + Q)
            lhs2 += sum(max(sum(weights2[i] for i in cylinder) for cylinder in group)
                        for group in index_cylinders)
            slack2 = 6 * n * sp - lhs2
            need(slack2 >= 0, 'every exact deletion-sensitive square cap inequality')
            min_square_slack = slack2 if min_square_slack is None else min(min_square_slack, slack2)
            count += 1
        need(count == (4760 if root == 1 else 4480), 'complete old nonempty query layouts')
        need(min_slack == 0, 'inherited relaxation constant is attained in finite cap check')
        need(min_square_slack == 0, 'inherited square relaxation constant has zero finite slack')
        rows.append({'shape': f'root{root}_{category}', 'old_survivors': n,
                     'Nmin': Nmin, 'c1': str(c1), 'layouts_checked': count,
                     'minimum_scaled_slack': min_slack,
                     'square_bound': str(square), 'square_minimum_scaled_slack': min_square_slack,
                     'cylinder_maxima_in_3_5_9_15_45_order': maxima})
    need(sum(row['layouts_checked'] for row in rows) == 27720, 'total selected-column checks')
    return rows


def shallow_bound(B, mean_rows):
    P = prod(q - 1 for q in B)
    Q = prod(B)
    A = sum(P // (q - 1) for q in B)
    V = Q - P - A
    supports = [T for size in range(len(B) + 1) for T in combinations(B, size)]
    labels = [c * prod(T) for c, T in product(HEAD, supports) if c * prod(T) > 1]
    need(len(labels) == len(set(labels)) == 12 * 2 ** len(B) - 1,
         'one occurrence of every complete shallow numerical modulus')
    need(V == sum(P // prod(q - 1 for q in T) for T in supports if len(T) >= 2),
         'multi-support coefficient is exact unnormalized live-root cardinality')
    results = []
    for row in mean_rows:
        c = F(row['c1'])
        values = []
        for N in range(row['Nmin'], 6 * row['old_survivors'] + 1):
            M = (c * N).numerator // (c * N).denominator
            bound = (P - V) * N - (A + V) * M
            need(bound == P * N - A * M - V * (N + M),
                 'all singleton and multi-support loads use the same supported head')
            values.append((bound, N))
        z, argmin = min(values)
        results.append({'shape': row['shape'], 'minimum_lower_bound': z,
                        'argmin_N': argmin,
                        'density_lower': str(F(z, 315 * Q)),
                        'integer_N_values_checked': len(values),
                        'continuous_gate': str((F(P - V) - (A + V) * c) / P)})
    minimum = min(row['minimum_lower_bound'] for row in results)
    return {'outside_primes': B, 'pure_live_root_product': P,
            'outside_period': Q, 'period': 315 * Q,
            'single_coefficient': A, 'multi_coefficient': V,
            'complete_shallow_labels': len(labels),
            'nonunit_head_labels': 11, 'pure_outside_labels': len(B),
            'other_singleton_labels': 11 * len(B),
            'multi_support_labels': 12 * (2 ** len(B) - len(B) - 1),
            'shape_bounds': results,
            'uniform_signed_lower': minimum,
            'uniform_density_lower_if_positive': str(F(minimum, 315 * Q)) if minimum > 0 else None}


def calculate():
    pruning = audit_all_originals()
    means = recheck_mean_column()
    bounds = [shallow_bound(B, means) for B in
              ((11, 13, 17, 19), (11, 13, 17, 19, 23), (11, 13, 17, 19, 23, 29))]
    need([b['uniform_signed_lower'] for b in bounds] == [648934, 5759930, -55195845],
         'exact all-shape lower values through19/23/29')
    need(min(r['minimum_lower_bound'] for r in bounds[2]['shape_bounds'][3:]) == 38887530,
         'all long-root shapes remain positive through29')
    moment_factor = prod(1 + F(3, q - 1) for q in bounds[1]['outside_primes'])
    need(moment_factor == F(43225, 16896), 'punctured-product complete-query square factor')
    moment_rows = []
    for head, shallow23 in zip(means, bounds[1]['shape_bounds']):
        delta = F(shallow23['continuous_gate'])
        need(delta > 0, 'one actual restricted shallow23 carrier has positive mass')
        G = F(head['square_bound']) * moment_factor / delta
        t = next(k for k in range(1, 29) if G <= k * k)
        need((t - 1) ** 2 < G <= t ** 2, 'least integer complete-query mean upper')
        remaining29 = 29 - t
        count29 = shallow23['minimum_lower_bound'] * remaining29
        need(remaining29 > 0, 'same-carrier29 extension leaves positive root count')
        moment_rows.append({'shape': head['shape'], 'mass23_lower': str(delta),
                            'Gamma23_upper': str(G), 'mean23_upper_integer': t,
                            'nonunit29_deletion_load_upper': t - 1,
                            'remaining29_roots_per_carrier_point_lower': remaining29,
                            'survivor29_count_lower': count29,
                            'density29_lower': str(F(count29, bounds[2]['period'])),
                            'all_height29_mass_lower': str(1 - F(t, 28)),
                            'all_height29_density_lower':
                                str(F(shallow23['minimum_lower_bound'], bounds[1]['period'])
                                    * (1 - F(t, 28)))})
    need([r['mean23_upper_integer'] for r in moment_rows] == [19, 17, 17, 15, 16, 16],
         'all six sharp integer roundings of the reused moment upper')
    uniform29 = min(r['survivor29_count_lower'] for r in moment_rows)
    need(uniform29 == 57599300, 'uniform all767 shallow phase lower count through29')
    all_height29_density = min(F(r['all_height29_density_lower']) for r in moment_rows)
    need(all_height29_density == F(52363, 9464546),
         'uniform arbitrary last-prime29 height density from the same23 source')
    tail29_31 = F(29, 28) * F(31, 30) - 1
    need(tail29_31 == F(59, 840) and 1 - 19 * tail29_31 == F(-281, 840),
         'two adjacent new primes fail only this sufficient union bound')
    haar132 = sum((F(1, c * prod(T)) for c in HEAD
                   for size in range(2, 5) for T in combinations((11, 13, 17, 19), size)), F(0))
    need(haar132 == F(22256, 373065), 'weaker unconditional132 Haar debit')
    need(F(16, 247) - haar132 == F(24832, 4849845), 'weaker59-then-Haar bridge')
    output = {'scope': 'Ordinary proof plus exact finite checks. No Lean verification. '
                       'All original phases are simultaneous and arbitrary. '
                       'Core through23:3-exponent at most2 and all other exponents at most1. '
                       'One last prime q>=29 may have arbitrary finite height. '
                       'For shallow29 the explicit767-label count also holds. '
                       'Negative direct union bounds are not covering examples.',
              'pruning': pruning, 'rechecked_existing_mean_column': means,
              'complete_shallow_bounds': bounds,
              'square_moment29_extension': {'product_square_factor_through23': str(moment_factor),
                                            'rows': moment_rows, 'uniform_survivor_count': uniform29,
                                            'period': bounds[2]['period'],
                                            'uniform_density_lower': str(F(uniform29, bounds[2]['period'])),
                                            'all_height_last_prime_at_least29_density_lower': str(all_height29_density),
                                            'finite_new_prime_set_criterion':
                                                't_i*(product_(p in new primes) p/(p-1)-1)<1',
                                            'two_prime_29_31_worst_mean_gate': str(1 - 19 * tail29_31)},
              'weaker_191_via_59_and_unconditional_Haar132':
                  {'59_density_lower': '16/247', 'Haar132_upper': str(haar132),
                   '191_density_lower': str(F(16, 247) - haar132), 'survivor_count': 74496}}
    return output


def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix(".json").read_text())
        need(retained==result,"retained result agrees with complete pruning and shared-source continuation")
        print(rendered,end="")
    else:
        args.output.write_text(rendered)


if __name__=="__main__":main()
