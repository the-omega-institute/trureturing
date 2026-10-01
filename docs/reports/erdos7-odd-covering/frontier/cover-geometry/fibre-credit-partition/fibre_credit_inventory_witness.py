#!/usr/bin/env python3
"""Verify a fixed-label obstruction to the FC inventory comparison.

Python 3.10+, standard library only. Required --input names one JSON fixture;
--output optionally names the result. No optimizer, network, directory search,
or actual congruence-class realization is used. All arithmetic is exact.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from math import isqrt, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_prime(n):
    return (type(n) is int and n >= 5 and
            all(n % k for k in range(2, isqrt(n) + 1)))


def total_cap(p, q):
    return 2 * (p - 1) * (q - 1) - abs(p - q) - 2


def root_cap(p, q):
    return (p - 1) * (q - 1) + min(p - 1, q - 1) - 1


def check(data):
    contract = data.get('capacity_contract', 'uniform')
    require(contract in ('uniform', 'actual-star-roots'), 'unknown capacity contract')
    actual_roots = contract == 'actual-star-roots'
    primes = tuple(data['primes'])
    heights = tuple(data['heights'])
    require(primes and all(is_prime(p) for p in primes), 'prime domain')
    require(tuple(sorted(set(primes))) == primes, 'distinct increasing primes')
    require(len(heights) == len(primes), 'one height per prime')
    require(all(type(h) is int and h >= 1 for h in heights), 'positive heights')
    limits = dict(zip(primes, heights))
    partition = frozenset(data.get('partition_A', []))
    require(actual_roots or 'partition_A' in data, 'uniform partition required')
    require(partition <= set(primes), 'partition outside source')
    threshold = Fraction(data['strict_upper_threshold'])
    require(threshold < 0, 'negative comparison threshold required')

    factors = {}
    assignments = {}
    counts = Counter()
    root_counts = Counter()
    square_counts = Counter()
    square_root_counts = Counter()
    max_exponents = Counter()
    label_checks = 0
    for item in data['selected_witness']:
        require(isinstance(item, list) and len(item) == 2, 'label/root record')
        d, root = item
        require(type(d) is int and d > 1, 'positive numerical cofactor')
        require(type(root) is int and root in (1, 2), 'root is 1 or 2')
        require(d not in factors, 'duplicate numerical cofactor')
        n = d
        powers = {}
        for p in primes:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            require(exponent <= limits[p], 'height exceeded')
            if exponent:
                powers[p] = exponent
                max_exponents[p] = max(max_exponents[p], exponent)
            if exponent >= 2:
                square_counts[p] += 1
                square_root_counts[p, root] += 1
        require(n == 1 and len(powers) >= 2, 'mixed supported cofactor required')
        factors[d] = powers
        assignments[d] = root
        for p, q in combinations(powers, 2):
            counts[p, q] += 1
            root_counts[p, q, root] += 1
            forced = powers[p] * powers[q] * prod(
                e + 1 for t, e in powers.items() if t not in (p, q))
            require(forced <= total_cap(p, q), 'individual-label CR9 exceeded')
            label_checks += 1
    require(factors, 'nonempty mixed inventory')

    closure_edges = 0
    for d, powers in factors.items():
        for p, exponent in powers.items():
            if len(powers) >= 3 or exponent >= 2:
                require(d // p in factors, 'missing mixed divisor')
                closure_edges += 1

    stars = {}
    star_counts = Counter()
    star_root_counts = Counter()
    for item in data['star_roots']:
        require(isinstance(item, list) and len(item) == 3, 'star record')
        p, e, root = item
        require(type(p) is int and p in limits, 'star prime')
        require(type(e) is int and 1 <= e <= limits[p], 'star height')
        require(type(root) is int and root in (1, 2), 'star root')
        require((p, e) not in stars, 'duplicate star numerical label')
        stars[p, e] = root
        if e >= 2:
            star_counts[p] += 1
            star_root_counts[p, root] += 1
    for p, emax in max_exponents.items():
        require(all((p, e) in stars for e in range(1, emax + 1)),
                'missing star forced by mixed divisor closure')
    for p, e in stars:
        require(all((p, k) in stars for k in range(1, e + 1)),
                'star chain not divisor-closed')

    pair_table = []
    for p, q in combinations(primes, 2):
        cap = total_cap(p, q)
        if actual_roots and (p, 1) in stars and (q, 1) in stars:
            cap -= int(stars[p, 1] != stars[q, 1])
        require(counts[p, q] <= cap, 'overlapping pair capacity')
        by_root = [root_counts[p, q, r] for r in (1, 2)]
        rcaps = [root_cap(p, q)] * 2
        if actual_roots:
            for r in (1, 2):
                yp = int(stars.get((p, 1)) == r)
                yq = int(stars.get((q, 1)) == r)
                a, b = p - 1 - yp, q - 1 - yq
                rcaps[r - 1] = a * b + min(a, b) - int(yp == yq == 0)
        require(all(c <= rc for c, rc in zip(by_root, rcaps)), 'pair root capacity')
        row = dict(pair=[p, q], count=counts[p, q], total_cap=cap,
                   root_counts=by_root, root_cap=root_cap(p, q))
        if actual_roots:
            row['root_caps'] = rcaps
        pair_table.append(row)
    square_table = []
    for p in primes:
        cap = 4 * p * p - 6 * p - (5 if actual_roots else 3)
        rcap = 2 * p * (p - 1) - 2
        total = square_counts[p] + star_counts[p]
        by_root = [square_root_counts[p, r] + star_root_counts[p, r]
                   for r in (1, 2)]
        require(total <= cap, 'square PI3 total capacity including stars')
        rcaps = [rcap] * 2
        if actual_roots:
            rcaps = [rcap - 2 * (p - 1) * int(stars.get((p, 1)) == r)
                     - int(stars.get((p, 2)) == r) for r in (1, 2)]
        require(all(c <= rc for c, rc in zip(by_root, rcaps)),
                'square PI3 root capacity')
        row = dict(prime=p, mixed=square_counts[p], stars=star_counts[p],
                   total=total, total_cap=cap, root_counts=by_root, root_cap=rcap)
        if actual_roots:
            row['root_caps'] = rcaps
        square_table.append(row)

    b = {}; c = {}
    for p, h in limits.items():
        denominator = (p - 2) * p ** h + 1
        b[p] = Fraction(p ** h - 1, denominator)
        c[p] = Fraction((p - 1) * p ** h, denominator)
    beta = {r: {p: b[p] if ((p in partition) == (r == 1)) else Fraction()
                for p in primes} for r in (1, 2)}
    if actual_roots:
        # These masses come from the SAME explicit star exponent/root metadata.
        # Actual blocked sets may be enlarged to their per-root cylinder budgets.
        beta = {r: {p: c[p] * sum((Fraction(1, p ** e)
                    for (q, e), t in stars.items() if q == p and t == r), Fraction())
                    for p in primes} for r in (1, 2)}
        for p, h in limits.items():
            require(beta[1][p] + beta[2][p] <= b[p], 'pooled source budget')
            for r in (1, 2):
                exponents = [e for (q, e), t in stars.items() if q == p and t == r]
                if exponents:
                    mass = sum((Fraction(1, p ** e) for e in exponents), Fraction())
                    tail = sum((Fraction(1, p ** e)
                                for e in range(min(exponents) + 1, h + 1)), Fraction())
                    require(beta[r][p] >= c[p] * (mass - tail) > 0,
                            'occupied-root source floor')

    def g(r, support):
        return prod((1 - beta[r][p] for p in primes if p not in support),
                    start=Fraction(1))

    carriers = {r: g(r, ()) for r in (1, 2)}
    # Expand product of (retained mass + exponent inventory) and subtract
    # the empty and singleton supports. This pays ALL 3-free mixed labels.
    free = {r: prod((1 - beta[r][p] + b[p] for p in primes), start=Fraction(1))
            - carriers[r] - sum((b[p] * g(r, (p,)) for p in primes), Fraction())
            for r in (1, 2)}
    selected = {1: Fraction(), 2: Fraction()}
    for d, powers in factors.items():
        r = assignments[d]
        selected[r] += g(r, powers) * prod((c[p] for p in powers),
                                          start=Fraction(1)) / d
    endpoints = [carriers[r] - free[r] - selected[r] for r in (2, 1)]
    require(all(v < threshold for v in endpoints), 'all-weight margin not met')
    expected = data.get('expected_endpoints')
    if expected is not None:
        require(endpoints == [Fraction(v) for v in expected], 'endpoint mismatch')

    result = dict(
        scope='Fixed-partition numerical/root relaxation; not an actual AP family, '
              'negative survivor mass, or counterexample to Erdos 7.',
        primes=primes, heights=heights, partition_A=sorted(partition),
        mixed_labels=len(factors), star_labels=len(stars),
        root_assignment_counts=dict(sorted(Counter(assignments.values()).items())),
        mixed_divisor_closure_edges=closure_edges, per_label_cr9_checks=label_checks,
        pair_constraints=len(pair_table), root_pair_constraints=2 * len(pair_table),
        square_constraints=len(square_table), root_square_constraints=2 * len(square_table),
        pair_table=pair_table, square_table=square_table,
        source_caps={p: str(c[p]) for p in primes},
        coordinate_budgets={p: str(b[p]) for p in primes},
        carrier_by_root={r: str(carriers[r]) for r in (1, 2)},
        free_charge_by_root={r: str(free[r]) for r in (1, 2)},
        selected_charge_by_root={r: str(selected[r]) for r in (1, 2)},
        endpoints=list(map(str, endpoints)), endpoint_decimals=list(map(float, endpoints)),
        strict_upper_threshold=str(threshold))
    if actual_roots:
        result.update(
            scope='Fixed actual-star metadata and numerical/root relaxation; '
                  'not an actual AP family, negative survivor mass, or Erdos 7 counterexample.',
            capacity_contract=contract,
            source_budget_by_root={r: {p: str(beta[r][p]) for p in primes}
                                   for r in (1, 2)})
        result.pop('partition_A')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(json.loads(args.input.read_text(encoding='utf-8')))
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output is None:
        print(rendered, end='')
    else:
        args.output.write_text(rendered, encoding='utf-8')


if __name__ == '__main__':
    main()
