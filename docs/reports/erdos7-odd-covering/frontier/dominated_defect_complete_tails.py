#!/usr/bin/env python3
"""Complete original35 load bounds on a Haar-dominated error measure.

The finite correction evaluates an infinite cap series exactly. It does
not truncate the original labels or assert an off-face covering bound.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/dominated_defect_complete_tails.json'
IO_PIN = '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def multiplicity(a, degree):
    require(a >= 0 and degree in (1, 2), 'Linear or quadratic ordered-tuple count')
    return (a+1)**degree-a**degree


def complete_prime_tail(prime, entrance, degree):
    """Sum ((a+1)^degree-a^degree)/prime^a, a>=entrance."""
    require(prime in (3, 5) and entrance >= 0 and degree in (1, 2), 'Original35 tail domain')
    q = F(1, prime)
    if degree == 1:
        return q**entrance/(1-q)
    return q**entrance*((2*entrance+1)/(1-q)+2*q/(1-q)**2)


def cap_series(mass, degree):
    """Exact complete sum Delta_k(a)Delta_k(b) min(mass,3^-a5^-b)."""
    mass = F(mass)
    require(0 <= mass <= 1 and degree in (1, 2), 'Haar-dominated mass in[0,1] and degree1/2')
    if not mass:
        return F(0)
    full = complete_prime_tail(3, 0, degree)*complete_prime_tail(5, 0, degree)
    correction, power3, a = F(0), 1, 0
    while F(1, power3) >= mass:
        power5, b = 1, 0
        while F(1, power3*power5) >= mass:
            correction += multiplicity(a, degree)*multiplicity(b, degree)*(F(1, power3*power5)-mass)
            power5 *= 5
            b += 1
        power3 *= 3
        a += 1
    return full-correction


def centered_bounds(mass):
    """Bounds for Z-1, Z^2-1 and (Z1-1)(Z2-1), respectively."""
    mass = F(mass)
    p1, p2 = cap_series(mass, 1), cap_series(mass, 2)
    return {'linear': p1-mass, 'quadratic': p2-mass,
            'mixed_centered': p2-2*p1+mass}


def complete_rows(mass, degree):
    """Independent evaluation by complete five tails and one three tail."""
    mass = F(mass)
    if mass == 0:
        return F(0)
    total, a, power3 = F(0), 0, 1
    while F(1, power3) >= mass:
        b, power5 = 0, 1
        while F(1, power3*power5) >= mass:
            b += 1
            power5 *= 5
        total += multiplicity(a, degree)*(mass*b**degree+complete_prime_tail(5, b, degree)/power3)
        a += 1
        power3 *= 3
    return total+complete_prime_tail(3, a, degree)*complete_prime_tail(5, 0, degree)


def haar_quantile(values, mass):
    """Exact maximum over all submeasures of finite uniform Haar, mass<=mass."""
    mass = F(mass)
    capacity, remaining, result = F(1, len(values)), mass, F(0)
    for value in sorted(values, reverse=True):
        take = min(capacity, remaining)
        result += take*value
        remaining -= take
        if remaining == 0:
            break
    require(remaining == 0, 'The finite Haar capacity contains the error mass')
    return result


def calculate():
    require(complete_prime_tail(3, 0, 1)*complete_prime_tail(5, 0, 1) == F(15, 8)
            and complete_prime_tail(3, 0, 2)*complete_prime_tail(5, 0, 2) == F(45, 8),
            'The complete original35 moments agree with57')
    masses = sorted({F(0), F(1), F(1, 520), F(1, 12000), F(1, 60000),
                     *(F(1, 10**j) for j in range(1, 10)), *(F(1, 15**j) for j in range(1, 9))})
    rows = []
    for mass in masses:
        bounds = centered_bounds(mass)
        require(min(bounds.values()) >= 0, 'Nonnegative centered cap bounds')
        for degree in (1, 2):
            require(cap_series(mass, degree) == complete_rows(mass, degree),
                    'Finite cap correction agrees with an independent full-tail partition')
        rows.append({'mass': mass, 'first': cap_series(mass, 1), 'second': cap_series(mass, 2), **bounds})
    for left, right in zip(rows, rows[1:]):
        require(all(left[k] <= right[k] for k in ('first', 'second', 'linear', 'quadratic', 'mixed_centered')),
                'Every sampled complete error bound is increasing with the shared mass')
    # Different residue choices for every original label of each finite test.
    height, period = 3, 3**3*5**3
    labels = [(a, b, 3**a*5**b) for a in range(height+1) for b in range(height+1)]
    layouts = [lambda a, b, d: 0, lambda a, b, d: (a*a+7*b+3*a*b+1) % d,
               lambda a, b, d: (11*a+5*b*b+2*a*b+2) % d]
    loads = [[sum(int(x % d == residue(a, b, d)) for a, b, d in labels)
              for x in range(period)] for residue in layouts]
    finite = []
    for mass in (F(1, period), F(1, 520), F(1, 100), F(1, 5), F(1)):
        bound = centered_bounds(mass)
        for i, load in enumerate(loads):
            for name, values in [('linear', [v-1 for v in load]), ('quadratic', [v*v-1 for v in load])]:
                exact = haar_quantile(values, mass)
                require(exact <= bound[name], 'Worst finite Haar-dominated defect obeys the complete bound')
                finite.append({'mass': mass, 'test': i, 'cost': name, 'exact_finite_quantile': exact, 'complete_upper': bound[name]})
        for i, j in ((0, 1), (0, 2), (1, 2)):
            exact = haar_quantile([(x-1)*(y-1) for x, y in zip(loads[i], loads[j])], mass)
            require(exact <= bound['mixed_centered'], 'Independent original-label tests share one dominated defect')
            finite.append({'mass': mass, 'tests': [i, j], 'cost': 'mixed_centered',
                           'exact_finite_quantile': exact, 'complete_upper': bound['mixed_centered']})
    nonlinearity = []
    for depth in range(1, 9):
        mass = F(1, 15**depth)
        lower_ratio = (depth+1)**2-1
        require(mass*lower_ratio <= centered_bounds(mass)['linear'], 'Nested-cylinder lower bound is retained')
        nonlinearity.append({'depth': depth, 'mass': mass, 'linear_error_per_mass_lower': lower_ratio})
    # The complete bound is concave in the defect mass, not a convex cost
    # for an unrestricted simplex-vertex maximization.
    total, slope = F(1, 5), F(3)
    candidates = []
    for omega in (F(0), F(1, 15), total):
        value = slope*(total-omega)+centered_bounds(omega)['linear']
        candidates.append({'omega': omega, 'other_defect': total-omega, 'value': value})
    require(candidates[1]['value'] > max(candidates[0]['value'], candidates[2]['value']),
            'An interior shared-budget point exceeds both vertices once a concave tail error is added')
    return {'schema': 'erdos7-dominated-defect-complete-tails-v1',
            'complete_first_moment': F(15, 8), 'complete_second_moment': F(45, 8),
            'exact_mass_rows': rows, 'finite_independent_test_height': height,
            'finite_haar_period': period, 'finite_quantile_checks': finite,
            'nested_cylinder_no_uniform_linear_constant': nonlinearity,
            'concave_tail_vertex_counterexample': {'budget': total, 'linear_slope': slope, 'points': candidates},
            'scope': 'Ordinary full-tail transfer for the positive part of an actual survivor excess dominated by raw35 Haar. Arbitrary independent original labels and complete infinite tails. Exact cap-series upper bounds are not asserted sharp; no forced27 transport, complete off-face numerator, new global K or unrestricted Erdos7 solution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Pinned certificate IO')
    io = module('dominated_defect_io', args.base/'certificate_io.py')
    result = encode(calculate())
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical complete defect-tail certificate')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    print('PASS: complete cap series,45 finite Haar quantile checks, and shared-budget vertex counterexample.')
    print('No uniform linear error constant; no new global comparison asserted.')


if __name__ == '__main__':
    main()
