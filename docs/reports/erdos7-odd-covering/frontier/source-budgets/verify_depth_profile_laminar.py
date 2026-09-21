#!/usr/bin/env python3
"""Rational LP witnesses and full-prefix law verification for laminar caps.

NumPy and SciPy discover finite LP solutions; exact Fraction checks certify
their primal/dual objectives and feasibility. Required checks survive -O.
"""
import argparse
import importlib.util
import json
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
from random import Random
import sys
sys.dont_write_bytecode=True
import numpy as np
from scipy.optimize import linprog
SOURCES=('certificate_io.py', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'frontier/source-budgets/depth_cap_bellman.py', 'frontier/source-budgets/capped_head_bellman.py', 'certificates/source_norms/source-budgets/capped_head_bellman.json')

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    if spec is None or spec.loader is None:
        raise RuntimeError('readable verification module')
    value=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

def certified_lp(costs, p, height, caps):
    """Use floating LP only for discovery; check rational primal and dual."""
    count = p ** height
    matrix = []
    bounds = []
    for e in range(1, height + 1):
        for a in range(p ** e):
            matrix.append([int(x % (p ** e) == a) for x in range(count)])
            bounds.append(caps[e])
    result = linprog(np.array([float(x) for x in costs]), A_ub=np.array(matrix),
                     b_ub=np.array([float(x) for x in bounds]),
                     A_eq=np.ones((1, count)), b_eq=np.array([1.]),
                     bounds=(0, None), method='highs')
    require(result.success, 'independent row LP success')
    primal = tuple(F(float(x)).limit_denominator(10 ** 9) for x in result.x)
    dual = tuple(F(float(x)).limit_denominator(10 ** 9) for x in result.ineqlin.marginals)
    eta = F(float(result.eqlin.marginals[0])).limit_denominator(10 ** 9)
    require(sum(primal) == 1 and all(x >= 0 for x in primal), 'exact LP mass/nonnegativity')
    require(all(sum(x * a for x, a in zip(primal, row)) <= cap for row, cap in zip(matrix, bounds)), 'exact LP cylinder feasibility')
    require(all(y <= 0 for y in dual), 'exact dual multiplier signs')
    require(all(eta + sum(y * row[j] for y, row in zip(dual, matrix)) <= cost for j, cost in enumerate(costs)), 'exact dual reduced costs')
    upper = sum(x * F(cost) for x, cost in zip(primal, costs))
    lower = eta + sum(y * cap for y, cap in zip(dual, bounds))
    require(upper == lower, 'exact matching LP primal-dual objectives')
    return upper


def random_profile(rng, p, height):
    caps = [F(1)]
    for e in range(1, height + 1):
        floor = F(1, p ** e)
        caps.append(floor + (min(caps[-1], F(1)) - floor) * F(rng.randrange(9), 8))
    return tuple(caps)


def audit_policy(problem):
    law = problem.expand_policy()
    require(sum(law.values()) == 1, 'joint law normalized')
    sizes = [p ** h for p, h in zip(problem.primes, problem.heights)]
    coefficients = [(problem.period // n) * pow(problem.period // n, -1, n) for n in sizes]
    bad = F(0)
    prefix_checks = 0
    for coordinates, mass in law.items():
        integer = sum(a * c for a, c in zip(coordinates, coefficients)) % problem.period
        require(all(integer % n == a for a, n in zip(coordinates, sizes)), 'original CRT reconstruction')
        if any(integer % n == residue % n for n, residue in problem.labels):
            bad += mass
    for axis, (p, h, caps) in enumerate(zip(problem.primes, problem.heights, problem.profiles)):
        rows = defaultdict(lambda: defaultdict(F))
        for coordinates, mass in law.items():
            rows[coordinates[:axis]][coordinates[axis]] += mass
        for row in rows.values():
            total = sum(row.values())
            for e in range(1, h + 1):
                masses = defaultdict(F)
                for a, mass in row.items():
                    masses[a % (p ** e)] += mass
                require(all(mass <= caps[e] * total for mass in masses.values()), 'actual full-prefix cylinder cap')
                prefix_checks += 1
    require(bad == problem.optimum(), 'actual original-label joint-law payoff')
    return len(law), prefix_checks


def dense_head_lp(problem):
    sizes = [p ** h for p, h in zip(problem.primes, problem.heights)]
    coefficients = [(problem.period // n) * pow(problem.period // n, -1, n) for n in sizes]
    row_count = 0

    def recurse(prefix):
        nonlocal row_count
        axis = len(prefix)
        if axis == len(sizes):
            integer = sum(a * c for a, c in zip(prefix, coefficients)) % problem.period
            return F(any(integer % n == residue % n for n, residue in problem.labels))
        costs = [recurse(prefix + (a,)) for a in range(sizes[axis])]
        row_count += 1
        return certified_lp(costs, problem.primes[axis], problem.heights[axis], problem.profiles[axis])

    result = recurse(())
    require(result == problem.optimum(), 'independent dense full-CRT LP matches compressed Bellman')
    return row_count


def calculate(base):
    global solver, require
    solver=load_module('laminar_candidate',base/'frontier/source-budgets/depth_cap_bellman.py')
    require=solver.require
    io=load_module('laminar_io',base/'certificate_io.py')
    literal_results=json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/capped_head_bellman.json'),object_pairs_hook=io._unique)['fixture_results']
    rng = Random(20260921)
    lp_cases = 0
    for p, h in [(2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (5, 1), (5, 2)]:
        for _ in range(24):
            caps = random_profile(rng, p, h)
            costs = [F(rng.randrange(-12, 18), 3) for _ in range(p ** h)]
            expected = certified_lp(costs, p, h, caps)
            actual, masses = solver.dense_row(costs, p, h, caps)
            require(expected == actual, 'dense marginal curve matches certified independent LP')
            require(sum(masses) == 1 and all(m >= 0 for m in masses), 'curve primal mass')
            for e in range(1, h + 1):
                for a in range(p ** e):
                    require(sum(masses[x] for x in range(a, p ** h, p ** e)) <= caps[e], 'curve primal capacities')
            lp_cases += 1

    cap = (F(1), F(1, 3), F(1, 3))
    clustered = [F(x % 3 != 0) for x in range(9)]
    dispersed = [F(x not in (0, 1, 2)) for x in range(9)]
    c = solver.dense_row(clustered, 3, 2, cap)[0]
    d = solver.dense_row(dispersed, 3, 2, cap)[0]
    require(sorted(clustered) == sorted(dispersed) and c == F(2, 3) and d == 0, 'equal histogram/unequal tree capacity optimum')
    require(certified_lp(clustered, 3, 2, cap) == c and certified_lp(dispersed, 3, 2, cap) == d, 'ancestry obstruction independently certified')

    labels_cases = []
    support_points = prefix_checks = full_lp_rows = 0
    for index in range(24):
        primes = (3, 5) if index % 2 == 0 else (5, 3)
        heights = (2, 1) if index % 3 == 0 else (1, 2)
        period = int(np.prod([p ** h for p, h in zip(primes, heights)]))
        moduli = [n for n in range(3, period + 1, 2) if period % n == 0]
        chosen = rng.sample(moduli, rng.randrange(1, len(moduli) + 1))
        labels = [(n, rng.randrange(n)) for n in chosen]
        profiles = [random_profile(rng, p, h) for p, h in zip(primes, heights)]
        problem = solver.HeadProblem(primes, heights, labels, profiles)
        points, checks = audit_policy(problem)
        support_points += points
        prefix_checks += checks
        full_lp_rows += dense_head_lp(problem)
        labels_cases.append({'primes': primes, 'heights': heights, 'labels': labels,
                             'profiles': [[str(x) for x in cap] for cap in profiles],
                             'optimum': str(problem.optimum()), 'support_points': points})

    regressions = []
    for count in (78, 154):
        name = ('numerical-order-counterexample-78' if count == 78
                else 'all-order-joint-atom-counterexample-154')
        data = next(row for row in literal_results if row['name'] == name)
        primes, heights, labels = data['primes'], data['heights'], data['original_labels']
        expected = F(data['numerator'], data['denominator'])
        problem = solver.HeadProblem(primes, heights, labels, solver.old_profiles(primes, heights))
        actual = problem.optimum()
        require(actual == expected, 'actual large flat-cap regression')
        regressions.append({'labels': count, 'minimum_bad_mass': str(actual), 'states': problem.value.cache_info().currsize})

    report = {'status': 'PASS', 'random_seed': 20260921, 'generic_row_lp_cases': lp_cases,
              'all_lp_comparisons_have_exact_rational_primal_dual_certificates': True,
              'ancestry_counterexample': {'clustered': str(c), 'dispersed': str(d)},
              'actual_policy_cases': len(labels_cases), 'actual_support_points': support_points,
              'actual_full_prefix_depth_checks': prefix_checks, 'independent_full_CRT_lp_rows': full_lp_rows,
              'flat_profile_regressions': regressions, 'small_cases': labels_cases,
              'source_sha256': {name:sha256(io.read_artifact_bytes(base/name)).hexdigest() for name in SOURCES},
              'producer_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}
    return json.loads(json.dumps(report))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('verification_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/depth_profile_laminar_verification.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact independent verification replay')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
