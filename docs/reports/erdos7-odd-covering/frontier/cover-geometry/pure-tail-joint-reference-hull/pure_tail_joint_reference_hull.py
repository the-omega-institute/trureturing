#!/usr/bin/env python3
"""Common pure-tail convex hull for leaf masses and density references.

Self-contained exact arithmetic with explicit checks, including under -O.
The general and all-height statements are ordinary proofs in Report602;
this producer verifies their finite source instances and comparison data.
No Lean or positive all-phase continuation gate is claimed.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import json
from math import prod
from pathlib import Path

CHECKS = {}
CHECK_COUNTS = Counter()


def require(name, condition):
    CHECK_COUNTS[name] += 1
    if not condition:
        raise ArithmeticError('certificate failed: ' + name)
    CHECKS[name] = True


def joint(groups, masses, prime, deficit):
    leaves = {}
    densities = []
    for group, mass in zip(groups, masses):
        denominator = len(group) - sum((deficit[m] for m in group), F(0))
        densities.append(mass * prime**2 / denominator)
        leaves.update({m: mass * (1 - deficit[m]) / denominator for m in group})
    return leaves, densities


def decompose(groups, masses, prime, cap, deficit):
    indices = [m for group in groups for m in group]
    require('general_partition', len(indices) == len(set(indices))
            and set(indices) == set(deficit) and all(groups))
    require('general_probability_domain', len(groups) == len(masses)
            and min(masses) > 0 and sum(masses) == 1
            and 0 < cap <= 1 and cap < min(map(len, groups))
            and min(deficit.values()) >= 0 and sum(deficit.values()) <= cap)
    zero = dict.fromkeys(indices, F(0))
    base = joint(groups, masses, prime, zero)
    endpoints = {}
    weights = {}
    for group in groups:
        total = sum((deficit[m] for m in group), F(0))
        for m in group:
            weights[m] = deficit[m] * (len(group) - cap) / (cap * (len(group) - total))
            endpoint_deficit = dict(zero)
            endpoint_deficit[m] = cap
            endpoints[m] = joint(groups, masses, prime, endpoint_deficit)
    base_weight = 1 - sum(weights.values())
    require('nonnegative_convex_weights', base_weight >= 0 and min(weights.values()) >= 0)
    recovered_leaves = {m: base_weight * base[0][m]
                        + sum(weights[k] * endpoints[k][0][m] for k in indices)
                        for m in indices}
    recovered_density = [base_weight * base[1][j]
                         + sum(weights[k] * endpoints[k][1][j] for k in indices)
                         for j in range(len(groups))]
    actual = joint(groups, masses, prime, deficit)
    require('same_weights_recover_joint_vector', actual == (recovered_leaves, recovered_density))
    require('comparison_points_are_probabilities', all(min(point[0].values()) >= 0
            and sum(point[0].values()) == 1 for point in [base] + list(endpoints.values())))
    return actual, base_weight, weights


def indexed_points(prime, zero):
    size = prime * (prime - 1)
    leaves = [m for m in range(size) if m != zero]
    groups = [leaves] if prime == 3 else [[m for m in leaves if m // prime == j]
                                       for j in range(prime - 1)]
    masses = [F(1)] if prime == 3 else [F(1, prime - 1)] * (prime - 1)
    cap = F(1, prime - 1)
    result = []
    for deficient in [None] + leaves:
        deficit = {m: cap if m == deficient else F(0) for m in leaves}
        (v, beta), base_weight, weights = decompose(groups, masses, prime, cap, deficit)
        require('indexed_point_density_cap', max(beta) <= (F(2) if prime == 3 else F(5, 3)))
        result.append(dict(deficient_leaf=deficient,
                           leaf_masses=[v.get(m, F(0)) for m in range(size)],
                           density_references=beta))
    return dict(zero_leaf=zero, points=result)


def actual_source(prime, height, phases):
    require('literal_pure_inventory', height >= 2 and all(1 <= e <= height
            and 0 <= a < prime**e for e, a in phases.items()))
    excluded = phases.get(1, prime - 1)
    roots = [r for r in range(prime) if r != excluded]
    original_zero = phases.get(2)
    if original_zero is not None and original_zero % prime != excluded:
        zero = original_zero
        zero_kind = 'actual-live'
    else:
        zero = min(roots)
        zero_kind = 'aux-absent' if original_zero is None else 'aux-root-null'
    leaves = [r + prime * k for r in roots for k in range(prime) if r + prime * k != zero]
    groups = [leaves] if prime == 3 else [[m for m in leaves if m % prime == r] for r in roots]
    masses = [F(1)] if prime == 3 else [F(1, 4)] * 4
    survivors = [x for x in range(prime**height) if x % prime != excluded
                 and x % (prime**2) != zero
                 and all(x % (prime**e) != a for e, a in phases.items())]
    counts = Counter(x % (prime**2) for x in survivors)
    unit = prime**(height - 2)
    deficit = {m: 1 - F(counts[m], unit) for m in leaves}
    finite_tail = sum((F(prime**2, prime**e) for e in phases if e >= 3), F(0))
    require('one_common_actual_union_budget', 0 <= sum(deficit.values()) <= finite_tail
            <= F(1, prime - 1))
    (v, beta), base_weight, weights = decompose(groups, masses, prime, F(1, prime - 1), deficit)
    group_of = {m: j for j, group in enumerate(groups) for m in group}
    totals = [sum(counts[m] for m in group) for group in groups]
    atoms = {x: masses[group_of[x % (prime**2)]] / totals[group_of[x % (prime**2)]]
             for x in survivors}
    require('source_normalized_and_originals_avoided', sum(atoms.values()) == 1
            and all(all(x % (prime**e) != a for e, a in phases.items()) for x in atoms))
    require('actual_leaf_masses_and_density', all(v[m] == masses[group_of[m]] * F(counts[m], totals[group_of[m]])
            for m in leaves) and beta == [mass * F(prime**height, n) for mass, n in zip(masses, totals)])
    require('actual_density_bound', max(beta) <= (F(2) if prime == 3 else F(5, 3)))
    for e in range(2, height + 1):
        query = Counter()
        for x, mass in atoms.items():
            query[x % (prime**e)] += mass
        require('finite_cylinder_density_caps', all(mass <= beta[group_of[a % (prime**2)]] / prime**e
                for a, mass in query.items()))
    return dict(prime=prime, height=height, original_phases=phases,
                root_kind='actual' if 1 in phases else 'aux-absent', excluded_root=excluded,
                zero_kind=zero_kind, zero_residue=zero, live_leaf_residues=leaves,
                raw_deficit=deficit, leaf_masses=v, density_references=beta,
                base_weight=base_weight, endpoint_weights=weights)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    actual = []
    for p in (3, 5):
        fixtures = ({}, {1: p-1}, {2: 1}, {1: p-1, 2: 1},
                    {1: p-1, 2: p-1}, {1: 0, 2: 0},
                    {1: p-1, 2: 1, 3: 1, 4: 1},
                    {1: p-1, 2: 1, 3: 0, 4: p},
                    {1: p-1, 2: 1, 3: p-1, 4: p-1})
        for phases in fixtures:
            actual.append(actual_source(p, max(3, max(phases, default=1)), phases))
    require('actual_aux_cases_covered', {r['zero_kind'] for r in actual}
            == {'actual-live', 'aux-absent', 'aux-root-null'}
            and {r['root_kind'] for r in actual} == {'actual', 'aux-absent'})
    general = []
    groups = [list(range(2)), list(range(2, 5)), list(range(5, 9))]
    masses = [F(1, 6), F(1, 3), F(1, 2)]
    for cap in (F(1, 4), F(1, 2), F(3, 4), F(1)):
        for weights in ([0]*9, [1]+[0]*8, list(range(1, 10))):
            denominator = max(1, sum(weights))
            deficit = {m: cap * F(weights[m], denominator) for m in range(9)}
            value, base_weight, lambdas = decompose(groups, masses, 7, cap, deficit)
            general.append(dict(cap=cap, deficit=deficit, base_weight=base_weight,
                                endpoint_weights=lambdas, leaf_masses=value[0], density_references=value[1]))
    points = {p: [indexed_points(p, zero) for zero in range(p*(p-1))] for p in (3, 5)}
    require('comparison_point_counts', sum(len(row['points']) for row in points[3]) == 36
            and sum(len(row['points']) for row in points[5]) == 400)
    base = points[3][0]['points'][0]
    ends = points[3][0]['points'][1:]
    average_leaf = [sum(row['leaf_masses'][m] for row in ends)/5 for m in range(6)]
    average_density = sum(row['density_references'][0] for row in ends)/5
    require('density_reference_not_recoverable_from_leaf_masses', average_leaf == base['leaf_masses']
            and average_density == 2 and base['density_references'] == [F(9, 5)])
    tails = {}
    for p in (3, 5):
        x = F(1, p)
        original = x**3/(1-x)
        weighted = x**3*(7-5*x)/(1-x)**2
        require('all_height_geometric_coefficients', original == (F(1, 18) if p == 3 else F(1, 100))
                and weighted == (F(4, 9) if p == 3 else F(3, 40)))
        for h in (3, 4, 8):
            require('finite_prefix_and_infinite_remainder',
                    sum((x**e for e in range(3, h+1)), F(0)) + x**(h+1)/(1-x) == original
                    and sum(((2*e+1)*x**e for e in range(3, h+1)), F(0))
                    + x**(h+1)*((2*h+3)-(2*h+1)*x)/(1-x)**2 == weighted)
        tails[p] = dict(original_Haar_tail=original, weighted_query_Haar_tail=weighted)
    density = 2 * F(5, 3) * prod(F(p, p-2) for p in (7, 11, 13, 17, 19))
    require('original_global_density_preserved', density == F(3458, 405))
    require('optimized_vertex_choices_need_not_interpolate',
            max((2*F(0)-1)*d for d in (-1, 1)) == 1
            and max((2*F(1)-1)*d for d in (-1, 1)) == 1
            and max((2*F(1, 2)-1)*d for d in (-1, 1)) == 0)
    data = dict(schema='pure-tail-joint-reference-hull-v1',
                scope=dict(result='Joint convex containment of leaf masses and Haar-density references',
                           heights='Arbitrary finite pure families; all-height conclusions use the ordinary union-bound and geometric-series proof',
                           finite_gate_reduction='Fixed phase identities, q factors, retained cell mask, and one common theta',
                           excluded=['Positive all-phase gate', 'Interpolation of independently optimized theta',
                                     'Old64-template reduction across changing cell masks', 'Resolution of the remaining413 central labels',
                                     'Unrestricted Erdos7 resolution', 'Lean verification']),
                general_domain=dict(cap='0<Delta<=1 and Delta<min n_j',
                                    deficits='delta_m>=0; total<=Delta',
                                    group_masses='r_j>0; sum r_j=1'),
                comparison_points=points,
                counts=dict(ternary_per_zero=6,quinary_per_zero=20,ternary_total=36,
                            quinary_total=400,joint_comparisons_with_zero_identities=14400,
                            actual_finite_sources=len(actual),general_finite_allocations=len(general)),
                actual_source_checks=actual,general_allocations=general,
                deep_Haar_coefficients=tails,global_density=density,
                density_projection_witness=dict(same_leaf_masses=average_leaf,base_density=F(9,5),
                                                endpoint_average_density=average_density),
                checks=CHECKS,predicate_counts=dict(CHECK_COUNTS),predicate_evaluations=sum(CHECK_COUNTS.values()),
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(data), indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output),checks=len(CHECKS),
                         predicate_evaluations=sum(CHECK_COUNTS.values()),
                         comparison_points=436,actual_finite_sources=len(actual))))


if __name__ == '__main__':
    main()
