#!/usr/bin/env python3
"""Exact checks for the common deleted-measure coupling theorem.

Standard library, readonly by default. --output writes exact rational data.
The ordinary proof supplies arbitrary families and complete exponent tails.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import sys
sys.dont_write_bytecode = True

PINS = {'frontier/source-budgets/source_cost_endpoint_attainment.py':
        '9c22b67d249f21e86e0292189c7808db023fd9c45090911f7c58bffa6b6d1ea2'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, name):
    path = base/name
    require(sha256(path.read_bytes()).hexdigest() == PINS[name], 'Pinned source '+name)
    spec = importlib.util.spec_from_file_location('deletion_parent', path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned helper')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def geometric_moment(p, order):
    if order == 0:
        return F(1)
    stirling = [[0]*(order+1) for _ in range(order+1)]
    stirling[0][0] = 1
    for n in range(1, order+1):
        for k in range(1, n+1):
            stirling[n][k] = k*stirling[n-1][k]+stirling[n-1][k-1]
    factorial, q, result = 1, F(1, p), F(0)
    for k in range(1, order+1):
        factorial *= k
        result += stirling[order][k]*factorial*q**(k-1)/(1-q)**k
    return result


def moments():
    M = {r: geometric_moment(3, r)*geometric_moment(5, r) for r in range(6)}
    H = {}
    for r, s in product((1, 2), repeat=2):
        H[r, s] = (M[r+s+1]-M[r+s]-M[r+1]+M[r]-M[s+1]+M[s]+M[1]-1)/5
    require(M[1] == F(15, 8) and M[2] == F(45, 8) and M[3] == F(3795, 128),
            'Complete nested-load first three moments')
    require(H[1, 1] == F(2227, 640), 'Centered linear mixed second-moment constant')
    return M, H


def finite_case(source, constructor, parent, height, mode, H):
    A, B, P = 3**height, 5**height, 7**height
    generator = random.Random(1700+height)
    old = []
    for x, y in product(range(A), range(B)):
        forbidden = False
        for a, b in product(range(height+1), repeat=2):
            if a+b == 0:
                continue
            aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
            if x % (3**aa) == ra and y % (5**bb) == rb:
                forbidden = True
                break
        if not forbidden:
            old.append((x, y))
    pure7 = (1 << P)-1
    for e in range(1, height+1):
        for z in range(6*7**(e-1), P, 7**e):
            pure7 &= ~(1 << z)
    pure_count = pure7.bit_count()
    labels = []
    for a, b, e in product(range(height+1), range(height+1), range(1, height+1)):
        if a+b == 0:
            continue
        if mode == 'canonical':
            j, aa, ra, bb, rb = constructor.mixed(a, b, 'off-diagonal')
            re = j*7**(e-1)
        elif mode == 'overlap':
            aa, bb, ra, rb, re = a, b, 0, 0, 0
        elif mode == 'cap-loss':
            _, aa, ra, bb, rb = constructor.mixed(a, b, 'off-diagonal')
            re = 6
        else:
            aa, bb = a, b
            ra, rb, re = generator.randrange(3**a), generator.randrange(5**b), generator.randrange(7**e)
        seven = sum(1 << z for z in range(re, P, 7**e)) & pure7
        labels.append((aa, ra, bb, rb, F(6, 5*7**e), seven))
    cap_mass = actual_sum_mass = deleted_mass = F(0)
    integrals = {name: [F(0), F(0)] for name in ('h4', 'h5', 'square', 'joint')}
    bounded_checks = 0
    for x, y in old:
        virtual, summed_actual, union = F(0), F(0), 0
        for a, ra, b, rb, u, seven in labels:
            if x % (3**a) == ra and y % (5**b) == rb:
                virtual += u
                summed_actual += F(seven.bit_count(), pure_count)
                union |= seven
        deleted = F(union.bit_count(), pure_count)
        require(0 <= deleted <= virtual, 'Pointwise true deleted measure below virtual cap measure')
        cap_mass += virtual/F(A*B)
        actual_sum_mass += summed_actual/F(A*B)
        deleted_mass += deleted/F(A*B)
        minus = 1+sum(x % (3**a) == 7 % (3**a) for a in range(1, height+1))
        plus = 1+int(x % 3 == 0)+sum(x % (3**a) == 3 for a in range(2, height+1))
        five = sum(y % (5**b) == 4 for b in range(1, height+1))
        Z, W = minus*(1+five), plus+five*minus
        values = {'h4': F(max(Z-4, 0)), 'h5': F(max(Z-5, 0)),
                  'square': F(max(W*W-16, 0))}
        values['joint'] = values['h4']/6+F(4, 33)*values['h5']+values['square']/100
        for name, value in values.items():
            integrals[name][0] += virtual*value/F(A*B)
            integrals[name][1] += deleted*value/F(A*B)
            for R in (F(1), F(3), F(10)):
                require((virtual-deleted)*min(R, value) <= R*(virtual-deleted),
                        'Bounded common-observable transfer')
                bounded_checks += 1
    dat = source.data(parent.parameter(height))
    s, D = dat[3:]
    require(s == F(len(old), A*B), 'Actual source mass')
    S, gap = s-deleted_mass, cap_mass-deleted_mass
    require(cap_mass <= s-D and 0 <= gap <= S-D, 'Complete source cap budget controls measure gap')
    cap_loss = cap_mass-actual_sum_mass
    overlap_loss = actual_sum_mass-deleted_mass
    require(cap_loss >= 0 and overlap_loss >= 0 and gap == cap_loss+overlap_loss,
            'Exact seven-cap loss plus overlap decomposition')
    if mode == 'cap-loss':
        require(deleted_mass == 0 and integrals['h4'][0] > 0 and integrals['h4'][1] == 0,
                'Counterexample to a deleted-load credit with the cap-loss penalty omitted')
    if mode == 'overlap':
        require(overlap_loss > 0, 'Deliberately overlapping original labels exercise union loss')
    alpha, beta = F(1, 6)+F(4, 33), F(1, 100)
    joint_M = alpha*alpha*H[1, 1]+2*alpha*beta*H[1, 2]+beta*beta*H[2, 2]
    for name, bound in (('h4', H[1, 1]), ('h5', H[1, 1]), ('square', H[2, 2]), ('joint', joint_M)):
        V, true = integrals[name]
        require((V-true)**2 <= bound*gap <= bound*(S-D), 'Uniform unbounded joint moment transfer')
        for R in (F(1), F(3), F(10)):
            require(V-true <= R*(S-D)+bound/(4*R), 'Rational dual form of common moment transfer')
    return {'height': height, 'mode': mode, 'S': S, 'D': D, 'virtual_mass': cap_mass,
            'deleted_mass': deleted_mass, 'measure_gap': gap, 'seven_cap_loss': cap_loss,
            'overlap_loss': overlap_loss, 'cost_integrals_virtual_then_true': integrals,
            'bounded_point_checks': bounded_checks, 'joint_second_moment_bound': joint_M}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    parent = load(base, 'frontier/source-budgets/source_cost_endpoint_attainment.py')
    source = parent.load(base, 'verify_joint_frontier.py', 'deletion_source')
    constructor = parent.load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'deletion_constructor')
    for path, pin in parent.PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Parent source pin: '+path)
    M, H = moments()
    cases = [finite_case(source, constructor, parent, 3, mode, H)
             for mode in ('canonical', 'overlap', 'cap-loss', 'scrambled')]
    result = {'schema': 'erdos7-common-deleted-measure-coupling-v1',
              'source_sha256': {**PINS, **parent.PINS}, 'nested_moments': M,
              'joint_cost_moment_constants': H, 'cases': cases,
              'scope': 'Exact finite probes and complete moment constants. Universal claims are supplied by the ordinary proof; no positive uniform gain or global K target is inferred from these probes.'}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true', help='Compare with the exact canonical certificate')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        certificate = args.base/'certificates/source_norms/cover-geometry/common_deleted_measure_coupling.json'
        require(json.loads(certificate.read_text()) == result, 'Exact canonical certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:four genuine original-label families, exact deleted/virtual measures, cap-overlap decomposition and joint linear/quadratic moment transfers.')
    print('Mixed moment constants:', result['joint_cost_moment_constants'])


if __name__ == '__main__':
    main()
