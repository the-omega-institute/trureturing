#!/usr/bin/env python3
"""Exact one-source certificate for shallow supports on the last three axes.

Reuses Report753's pinned complete uniform catalogue, then recomputes all
cylinder costs of 116 fixed integer laws. Weighted hinges use pointwise
domination by the same source's uniform hinge, not a sharp-weighted claim.
No numerical solver, search or optimality premise is used.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import argparse
import json


DEPENDENCIES = {'fibre_credit_depth_two_actual_joint_catalogue.cpp': 'a0da6f067b6e268ab24b46488c8a17e0225855d58667120530540918ff232f58', 'fibre_credit_depth_two_actual_joint_catalogue.py': 'b38e644c34558adcf7b4f56ceb6007aea18001a1e27569634e0860490750f3dc', 'fibre_credit_depth_two_actual_joint_catalogue.json': 'fb2093552efc1816c53727f75a6f84bcfee6c496d67bbf45ad002fa3a7375afc', 'fibre_credit_depth_two_last_three_weights.json': '9c7034042d71dbc425ffcf4c630f9bb5f9f7d27cf5d80b78fc2559c0e4c5a9c4'}
MODS = (3, 5, 9, 15, 45)
KAPPA48 = (0, 12, 24, 12, 42, 8, 8, 22, 36, 22, 57)
RHO = (F(1, 7), F(1, 7), F(1, 11), F(1, 13), F(1, 17))
FACTOR, MULTI, HAAR = F(27648, 17017), F(42, 2431), F(437, 49)


def check(value, message):
    if not value:
        raise ValueError(message)


def caps(points, r, weights):
    cylinders = [[tuple(i for i, x in enumerate(points) if x % d == a)
                  for a in range(d)] for d in MODS]
    return ([max(sum(r[i] * weights[i] for i in cell) for cell in group)
             for group in cylinders] + [sum(weights)] +
            [max(sum(weights[i] for i in cell) for cell in group)
             for group in cylinders])


def budget(cp, denominator, h4, h6, maximum):
    m = sum(cp)
    k = sum(a * b for a, b in zip(KAPPA48, cp))
    cost = (FACTOR * F(k, 48 * denominator) + MULTI * (1 + F(m, denominator))
            + RHO[0] * F(h4, denominator) + sum(RHO[1:]) * F(h6, denominator))
    cap = 315 * F(maximum, denominator) * HAAR
    reserve = 16723 * denominator - 576 * k - 294 * m - 2431 * h4 - 6288 * h6
    check((1 - cost) / cap == F(reserve, 47805615 * maximum),
          'exact integer reserve and paired Haar conversion')
    return {'D': denominator, 'M': m, 'K': k, 'H4_numerator_upper': h4,
            'H6_numerator_upper': h6, 'max_weight': maximum, 'G_lower': reserve,
            'cost_upper': str(cost), 'raw_Haar_cap': str(cap),
            'Haar_lower': str((1 - cost) / cap)}


def calculate():
    directory = Path(__file__).resolve().parent
    check(len(DEPENDENCIES) == 4, 'complete pinned input interface')
    for name, digest in DEPENDENCIES.items():
        check(sha256((directory / name).read_bytes()).hexdigest() == digest,
              'pinned last-three dependency: ' + name)
    data = json.loads((directory / 'fibre_credit_depth_two_actual_joint_catalogue.json').read_text())
    laws = json.loads((directory / 'fibre_credit_depth_two_last_three_weights.json').read_text())['rows']
    check(FACTOR == prod(1 + r for r in RHO), 'complete higher-core outside supports')
    check(MULTI == prod(1 + r for r in RHO[2:]) - 1 - sum(RHO[2:]),
          'all and only last-three shallow multioutside supports')
    check(HAAR == prod(F(p, p - a) for p, a in zip((11, 13, 17, 19, 23), (4, 6, 6, 6, 6))),
          'actual raw outside Haar cap')
    check(data['actual_source_count'] == 112893 and data['paired_group_count'] == 3193,
          'full inherited actual-source catalogue')
    required, shape_rows, nonexception_min = {}, [], None
    uniform_count = 0
    for shape, row in enumerate(data['rows']):
        points = row['old45_points']
        passed, failed, lower = 0, 0, None
        for n, m, k, j4, count, b in row['joint_groups']:
            cp = caps(points, [6 - v for v in b], [1] * len(b))
            value = budget(cp, n, j4, 10, 1)
            check(value['M'] == m and value['K'] == k, 'paired representative cylinder sums')
            exceptional = shape >= 4 and n == 75 and k == 1873 and m in (146, 147)
            check((F(value['cost_upper']) >= 1) == exceptional,
                  'exactly the named uniform sources require reweighting')
            if exceptional:
                check(j4 == 29, 'actual exceptional hinge numerator')
                failed += count
                continue
            passed += count
            bound = F(value['Haar_lower'])
            check(value['G_lower'] >= 2800, 'uniform actual-source integer reserve')
            lower = bound if lower is None else min(lower, bound)
            nonexception_min = bound if nonexception_min is None else min(nonexception_min, bound)
        for case in row['exceptional_hinge4']:
            key = (shape, tuple(case['b']))
            check(key not in required, 'distinct literal exceptional sources')
            required[key] = case
        check(failed == len(row['exceptional_hinge4']), 'every failed source explicitly retained')
        check(passed + failed == row['distinct_b_vectors'], 'complete shape accounting')
        uniform_count += passed
        shape_rows.append({'shape': shape, 'uniform_pass': passed, 'uniform_fail': failed,
                           'uniform_Haar_lower': str(lower)})
    assigned = {(law['shape'], tuple(law['b'])): law for law in laws}
    check(len(assigned) == len(laws) == len(required) == 116 and set(assigned) == set(required),
          'one fixed law for every actual exceptional source')
    weighted_rows, weighted_min, worst_cost = [], None, F(0)
    for law in laws:
        shape, b, weights = law['shape'], law['b'], law['weights']
        points = data['rows'][shape]['old45_points']
        check(len(b) == len(weights) == len(points), 'same actual row dimensions')
        check(all(type(w) is int and 0 <= w <= 120 for w in weights) and max(weights) > 0,
              'fixed nonzero nonnegative integer law')
        r, maximum = [6 - v for v in b], max(weights)
        denominator = sum(a * w for a, w in zip(r, weights))
        check(denominator > 0, 'actual probability denominator')
        # Nonnegative query summands allow v_x <= maximum pointwise.
        # The uniform maxima refer to this same b; no source is changed.
        h4 = maximum * required[(shape, tuple(b))]['H4_numerator']
        h6 = maximum * data['rows'][shape]['H6_numerator']
        cp = caps(points, r, weights)
        value = budget(cp, denominator, h4, h6, maximum)
        check(value['G_lower'] >= 57322 * maximum, 'weighted same-source reserve')
        cost, bound = F(value['cost_upper']), F(value['Haar_lower'])
        worst_cost = max(worst_cost, cost)
        weighted_min = bound if weighted_min is None else min(weighted_min, bound)
        weighted_rows.append({'shape': shape, 'b': b, 'cylinder_numerators': cp, **value})
    check(uniform_count == 112777, 'all nonexceptional sources')
    check(worst_cost == F(532900, 561561), 'worst assigned-law cost upper bound')
    check(weighted_min == F(57322, 47805615), 'paired weighted Haar lower bound')
    lower = min(nonexception_min, weighted_min)
    check(lower == F(560, 9561123) > F(1, 18000), 'uniform exact positive density')
    return {'scope': 'Arbitrary finite core3/5/7 heights; five ordered outside primes above7 at exponent at most1. Core-shallow supports are empty, singletons, or subsets of the last three outside axes. Higher-core supports arbitrary within this carrier.',
            'actual_source_count': 112893, 'paired_group_count': 3193,
            'uniform_source_count': uniform_count, 'weighted_source_count': len(laws),
            'outside_factor': str(FACTOR), 'last_three_multioutside_factor': str(MULTI),
            'outside_Haar_cap': str(HAAR), 'uniform_Haar_lower': str(nonexception_min),
            'weighted_Haar_lower': str(weighted_min), 'weighted_max_cost_upper': str(worst_cost),
            'Haar_survivor_lower': str(lower), 'strict_simple_lower': '1/18000',
            'weighted_hinges': 'Pointwise domination by the same actual source uniform maxima; upper bounds only.',
            'shape_rows': shape_rows, 'weighted_rows': weighted_rows,
            'dependency_hashes': DEPENDENCIES, 'lean_verification': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
              'retained result agrees with every paired last-three continuation')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
