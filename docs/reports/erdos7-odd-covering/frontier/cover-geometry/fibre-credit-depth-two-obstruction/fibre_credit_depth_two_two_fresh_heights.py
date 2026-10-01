#!/usr/bin/env python3
"""Exact common-source two-fresh-prime height certificate; ordinary proof, not Lean."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product, combinations
from math import prod
from pathlib import Path
import json
import runpy


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


DEPENDENCIES = {
    'fibre_credit_depth_two_uniform_shallow.py':
        '1f01fb1c704a48fddb7f0be9563635cbb4ea436ce1495d2e156fdfc3c0788de6',
    'fibre_credit_depth_two_uniform_shallow.json':
        'afc7b9a8167cf22e67885e427c865c5daa844eb3664b6ff7b684be56e3168591',
}


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] = result.get(exponent, 0) + coefficient
    return {e: c for e, c in result.items() if c}


def scale(polynomial, factor):
    return {e: c * factor for e, c in polynomial.items() if c * factor}


def mul(left, right):
    result = {}
    for e, c in left.items():
        for f, d in right.items():
            g = tuple(a + b for a, b in zip(e, f))
            result[g] = result.get(g, 0) + c * d
    return {e: c for e, c in result.items() if c}


def calculate():
    directory = Path(__file__).resolve().parent
    for filename, expected in DEPENDENCIES.items():
        need(sha256((directory / filename).read_bytes()).hexdigest() == expected,
             'pinned common-source dependency: ' + filename)
    source = runpy.run_path(str(directory / 'fibre_credit_depth_two_uniform_shallow.py'))
    verified = json.loads(json.dumps(source['calculate']()))
    retained = json.loads((directory / 'fibre_credit_depth_two_uniform_shallow.json').read_text())
    need(verified == retained, 'replayed all source inequalities, not merely a retained status')
    shallow = verified['complete_shallow_bounds'][1]
    density = F(shallow['uniform_density_lower_if_positive'])
    square = max(F(row['Gamma23_upper'])
                 for row in verified['square_moment29_extension']['rows'])
    need(density == F(104726, 6084351), 'one actual old carrier Haar lower')
    need(square == F(2607189975, 7283281) < 358, 'same-carrier complete-query square upper')

    head = [d for d in range(1, 316) if 315 % d == 0]
    outside = (11, 13, 17, 19, 23)
    supports = [t for k in range(6) for t in combinations(outside, k)]
    divisors = sorted(c * prod(t) for c, t in product(head, supports))
    need(len(divisors) == len(set(divisors)) == 384, 'complete numerical old divisor inventory')
    need(max(divisors) == shallow['period'] == 334639305, 'old core period')
    inventories = []
    for h, k in product(range(1, 5), repeat=2):
        groups = ([d for d in divisors if d > 1],
                  [d * 29**e for d, e in product(divisors, range(1, h + 1))],
                  [d * 31**f for d, f in product(divisors, range(1, k + 1))],
                  [d * 29**e * 31**f for d, e, f in
                   product(divisors, range(1, h + 1), range(1, k + 1))])
        labels = sum(groups, [])
        need(len(labels) == len(set(labels)) == 384 * (h + 1) * (k + 1) - 1,
             'old, unary and cross blocks retain each original numerical label once')
        inventories.append(dict(q_height=h, r_height=k, block_sizes=list(map(len, groups))))

    padding_cases = 0
    for (q, r), h, k in product(((29, 31), (31, 37), (97, 101)), range(1, 6), range(1, 6)):
        w = [F(q - 1, q**e) for e in range(1, h + 1)]
        z = [F(r - 1, r**f) for f in range(1, k + 1)]
        tq, tr = F(1, q**h), F(1, r**k)
        need(sum(w) + tq == sum(z) + tr == 1, 'finite unary weights with constant-one padding')
        cross_tail = 1 - (1 - tq) * (1 - tr)
        need(sum((a * b for a, b in product(w, z)), F(0)) + cross_tail == 1,
             'finite cross weights with constant-one padding')
        need(cross_tail >= 0, 'padding is a convex weight')
        padding_cases += 1

    one = {(0, 0, 0): 1}
    a, b, c = ({(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1})
    u, v = add(scale(one, 28), scale(a, -1)), add(b, scale(one, -1))
    p = mul(u, add(scale(one, 30), scale(b, -1)))
    left = add(scale(mul(a, a), 10), scale(mul(b, b), 10), mul(c, c),
               scale(p, 20), scale(c, -20))
    difference, shifted_c = add(u, scale(v, -1)), add(c, scale(one, -10))
    right = add(scale(one, 7750), scale(u, 20), scale(v, 20),
                scale(mul(difference, difference), 10), mul(shifted_c, shifted_c))
    need(left == right, 'polynomial identity for all real A,B,C, not sampled values')
    need(min(10 * 28**2 + 10 + 1, 10 + 10 * 30**2 + 1) == 7851 > 7750,
         'outside the nonnegative-u,v rectangle the direct cost suffices')
    expected_w = (7750 - 21 * square) / 20
    haar = density * expected_w / 840
    coarse = density * F(7750 - 21 * 358, 16800)
    need(expected_w > 0, 'positive common-source expected fibre numerator')
    need(haar == F(3549034855753, 14889516779972016) > F(1, 4200),
         'uniform two-fresh-height Haar lower')
    need(coarse == F(1518527, 6388568550) > F(1, 4250), 'coarse square358 lower')
    return dict(scope='All distinct odd nonunit moduli d*q^e*r^f, d|334639305; '
                      'two distinct fresh primes q>=29,r>=31; arbitrary simultaneous phases '
                      'and arbitrary finite e,f. Core v3<=2, every other core height<=1. '
                      'Ordinary proof and exact checks, not Lean or unrestricted Erdos7.',
                dependency_hashes=DEPENDENCIES, source_replayed=True,
                old_period=shallow['period'], old_haar_density_lower=str(density),
                common_query_square_upper=str(square), finite_inventories=inventories,
                finite_padding_cases=padding_cases, pointwise_threshold=7750,
                coefficient_W=20, outside_rectangle_cost_minimum=7851,
                identity_coefficients={','.join(map(str, e)): v for e, v in sorted(left.items())},
                expected_W_lower=str(expected_w), actual_haar_lower=str(haar),
                coarse_square358_haar_lower=str(coarse), simple_haar_lower='1/4200',
                simple_coarse_haar_lower='1/4250')


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with replayed source and analytic certificate')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
