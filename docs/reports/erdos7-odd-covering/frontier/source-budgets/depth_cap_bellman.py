#!/usr/bin/env python3
"""Exact full-history Bellman optimization with p-adic cylinder capacities.

Original numerical modulus labels are fixed globally. Each conditional row
obeys the same deterministic depth profile; capacities are absolute row
masses, not parent-conditional probabilities. Arithmetic is rational.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import prod


def require(ok, message):
    if not ok:
        raise ValueError(message)


def validate_profile(p, height, profile):
    require(isinstance(p, int) and p >= 2 and all(p % d for d in range(2, 1 + int(p ** .5))), 'prime')
    require(isinstance(height, int) and height >= 1, 'height')
    caps = tuple(F(r) for r in profile)
    require(len(caps) == height + 1 and caps[0] == 1, 'profile shape/root')
    require(all(F(1, p ** e) <= caps[e] <= caps[e - 1] for e in range(1, height + 1)), 'monotone feasible profile')
    return caps


def homogeneous_capacities(p, caps):
    """Maximum mass of a complete homogeneous subtree rooted at each depth."""
    height = len(caps) - 1
    capacity = [F(0)] * (height + 1)
    capacity[height] = caps[height]
    for e in range(height - 1, -1, -1):
        capacity[e] = min(caps[e], p * capacity[e + 1])
    require(capacity[0] == 1, 'uniform witness makes root feasible')
    return tuple(capacity)


def truncate_curve(segments, capacity):
    """Infimal convolution of child curves, restricted to parent capacity.

Stable sorting keeps each child's equal-slope segment order. Each segment
is (slope, available mass, terminal homogeneous-subtree descriptor).
"""
    remaining = capacity
    result = []
    for slope, amount, descriptor in sorted(segments, key=lambda segment: segment[0]):
        taken = min(remaining, amount)
        if taken:
            result.append((slope, taken, descriptor))
            remaining -= taken
        if not remaining:
            break
    return tuple(result)


def compressed_row(p, height, caps, requirements, active, continuation, witness=False):
    """Optimize one row without enumerating all p**height leaves.

requirements[j] = (exponent, actual residue modulo p**exponent).
A terminal descriptor is (depth, residue, original matching label IDs).
Its assigned mass is distributed uniformly on that actual subtree.
"""
    capacities = homogeneous_capacities(p, caps)

    def visit(depth, residue, inherited, pending):
        hits = tuple(sorted(inherited + tuple(j for j in pending if requirements[j][0] == depth)))
        deeper = [j for j in pending if requirements[j][0] > depth]
        if not deeper:
            descriptor = (depth, residue, hits) if witness else None
            return ((continuation(hits), capacities[depth], descriptor),)
        require(depth < height, 'all original exponents resolved')
        children = defaultdict(list)
        power = p ** depth
        for j in deeper:
            children[(requirements[j][1] // power) % p].append(j)
        segments = []
        # Repeated constant subtrees can be pooled only before applying this
        # actual parent cap. Never pool across parents before their truncation.
        if not witness:
            missing = p - len(children)
            if missing:
                segments.append((continuation(hits), missing * capacities[depth + 1], None))
            for digit, child in sorted(children.items()):
                segments.extend(visit(depth + 1, residue + digit * power, hits, tuple(child)))
        else:
            for digit in range(p):
                segments.extend(visit(depth + 1, residue + digit * power, hits, tuple(children.get(digit, ()))))
        result = truncate_curve(segments, caps[depth])
        require(sum(segment[1] for segment in result) == capacities[depth], 'complete subtree capacity')
        return result

    curve = visit(0, 0, (), tuple(active))
    require(sum(amount for _, amount, _ in curve) == 1, 'actual normalized row')
    return sum((cost * amount for cost, amount, _ in curve), F(0)), curve


def dense_row(costs, p, height, profile):
    """Explicit leaf version, retaining a rational probability witness."""
    caps = validate_profile(p, height, profile)
    require(len(costs) == p ** height, 'dense leaf count')

    def visit(depth, residue):
        if depth == height:
            return ((F(costs[residue]), caps[depth], residue),)
        children = []
        for digit in range(p):
            children.extend(visit(depth + 1, residue + digit * p ** depth))
        return truncate_curve(children, caps[depth])

    curve = visit(0, 0)
    masses = [F(0)] * (p ** height)
    for _, mass, residue in curve:
        masses[residue] += mass
    return sum((F(cost) * mass for cost, mass in zip(costs, masses)), F(0)), tuple(masses)


class HeadProblem:
    def __init__(self, primes, heights, labels, profiles):
        self.primes = tuple(primes)
        self.heights = tuple(heights)
        self.labels = tuple(tuple(label) for label in labels)
        require(len(primes) == len(heights) == len(profiles) and len(set(primes)) == len(primes), 'coordinate shape')
        require(all(3 <= p <= 73 and p % 2 for p in primes), 'head prime range')
        self.profiles = tuple(validate_profile(p, h, r) for p, h, r in zip(primes, heights, profiles))
        require(len({n for n, _ in labels}) == len(labels), 'distinct original numerical moduli')
        self.period = prod(p ** h for p, h in zip(primes, heights))
        require(all(isinstance(n, int) and isinstance(a, int) and n > 1 and n % 2 and self.period % n == 0 for n, a in labels), 'actual head original labels')
        rows = []
        for n, a in labels:
            rest = n
            row = []
            for p in primes:
                e = 0
                while rest % p == 0:
                    e += 1
                    rest //= p
                row.append((e, a % (p ** e)))
            require(rest == 1, 'all original factors retained')
            rows.append(tuple(row))
        self.rows = tuple(rows)
        self.by_axis = tuple(tuple(row[axis] for row in rows) for axis in range(len(primes)))
        self.last_axis = tuple(max(i for i, (e, _) in enumerate(row) if e) for row in rows)
        self.value = lru_cache(None)(self._value)

    def _value(self, axis, active):
        if not active:
            return F(0)
        if any(self.last_axis[j] < axis for j in active):
            return F(1)
        require(axis < len(self.primes), 'terminal label payoff')
        return compressed_row(self.primes[axis], self.heights[axis], self.profiles[axis],
                              self.by_axis[axis], active, lambda hits: self.value(axis + 1, hits))[0]

    def optimum(self):
        return self.value(0, tuple(range(len(self.labels))))

    def row_witness(self, axis, active):
        return compressed_row(self.primes[axis], self.heights[axis], self.profiles[axis],
                              self.by_axis[axis], active, lambda hits: self.value(axis + 1, hits), True)

    def expand_policy(self):
        """Small-period verifier: expand an actual joint policy, not just scores."""
        require(self.period <= 100000, 'explicit witness restricted to small audit instances')

        def visit(axis, active, prefix, probability):
            if axis == len(self.primes):
                yield prefix, probability
                return
            if not active or any(self.last_axis[j] < axis for j in active):
                # Any legal row suffices after the event becomes constant.
                count = self.primes[axis] ** self.heights[axis]
                masses = [F(1, count)] * count
            else:
                optimum, curve = self.row_witness(axis, active)
                require(optimum == self.value(axis, active), 'witness matches optimum')
                count = self.primes[axis] ** self.heights[axis]
                masses = [F(0)] * count
                for _, mass, (depth, residue, _) in curve:
                    size = self.primes[axis] ** (self.heights[axis] - depth)
                    for a in range(residue, count, self.primes[axis] ** depth):
                        masses[a] += mass / size
            for a, mass in enumerate(masses):
                if mass:
                    hits = tuple(j for j in active if a % (self.primes[axis] ** self.rows[j][axis][0]) == self.rows[j][axis][1])
                    yield from visit(axis + 1, hits, prefix + (a,), probability * mass)

        return dict(visit(0, tuple(range(len(self.labels))), (), F(1)))


def flat_profile(p, height, atom_cap):
    return tuple(min(F(1), p ** (height - e) * F(atom_cap)) for e in range(height + 1))


def old_profiles(primes, heights):
    ks = [(3 ** h - 1) // 2 if p == 3 else ((p - 3) * p ** h + 2) // (p - 1) for p, h in zip(primes, heights)]
    return tuple(flat_profile(p, h, F(1, k)) for p, h, k in zip(primes, heights, ks))


# Canonical report IO; all mathematical checks remain active under Python -O.
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/source-budgets/depth_cap_bellman.json'
INPUT = 'frontier/source-budgets/depth_profile_head_input.json'
LABEL_SOURCE = 'frontier/source-budgets/capped_head_bellman.py'
SOURCES = ('certificate_io.py', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean', '../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Probability.lean', '../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean', '../../../Library/Arith/schroeder2026noncoverage.md', '../../../Library/Arith/balister2018covering.md', 'frontier/source-budgets/depth_profile_head_input.json', 'frontier/source-budgets/capped_head_bellman.py')


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable source module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_head_input(base):
    io = load_module('depth_profile_certificate_io', base/'certificate_io.py')
    record = json.loads(io.read_artifact_bytes(base/INPUT), object_pairs_hook=io._unique)
    require(set(record) == {'schema', 'head_label_source', 'head_label_factory',
                            'prime_order', 'heights', 'profiles'}, 'exact profile input fields')
    require(record['schema'] == 'depth-profile-head-input-v1', 'profile input schema')
    require(record['head_label_source'] == LABEL_SOURCE and
            record['head_label_factory'] == 'counterexample_154_labels', 'canonical literal head source')
    literal = load_module('depth_profile_original_labels', base/LABEL_SOURCE)
    labels = literal.counterexample_154_labels()
    require(len(labels) == 154, 'all 154 original labels retained')
    require(record['prime_order'] == [p for p in range(3, 74, 2) if literal.prime(p)],
            'all 20 odd head primes in numerical order')
    require(record['heights'] == [5, 3, 3, 2, 2, 2, 2] + [1]*13,
            'actual head prime-power heights')
    return io, record, labels


def calculate(base):
    io, record, labels = load_head_input(base)
    profiles = tuple(tuple(F(r) for r in row) for row in record['profiles'])
    problem = HeadProblem(record['prime_order'], record['heights'], labels, profiles)
    epsilon = problem.optimum()
    require(0 <= epsilon < F(2, 5), 'exact head mass below two fifths')
    result = dict(schema='depth-cap-bellman-v1',
                  scope='Fixed literal 154-label head with the supplied depth profile; exact full-prefix-law head-union optimum. This memoization key does not discard actual sampled coordinates or future cofactor information.',
                  prime_order=record['prime_order'], heights=record['heights'],
                  profiles=record['profiles'], original_label_count=len(labels),
                  original_label_source=LABEL_SOURCE,
                  original_labels_sha256=hashlib.sha256(json.dumps(labels,separators=(',',':')).encode()).hexdigest(),
                  original_period=problem.period, epsilon_exact=str(epsilon),
                  states=problem.value.cache_info().currsize,
                  source_sha256={name:hashlib.sha256(io.read_artifact_bytes(base/name)).hexdigest() for name in SOURCES},
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = load_module('depth_bellman_io', args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique),
                'exact depth-cap head certificate replay')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
