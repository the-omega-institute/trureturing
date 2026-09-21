#!/usr/bin/env python3
"""Exact arithmetic for the eight-prime core omitting 11.

This checks one ordinary source row, the new minimum-11 conditional-kernel
row, the existing rows with minima 31--53, and the shared attachment budget.
It imports only the pinned ordinary geometry helper.  No source verifier,
Lean checker, or unrestricted Erdős #7 claim is involved.
"""
from collections import defaultdict
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from hashlib import sha256
import json
from math import isqrt, prod
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parent
GEOMETRY_PATH = BASE / 'six_prime_prefix_geometry.json'
HELPER_PATH = BASE / 'six_prime_prefix_certificate.py'
GEOMETRY_SHA256 = '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'
HELPER_SHA256 = '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4'
assert sha256(GEOMETRY_PATH.read_bytes()).hexdigest() == GEOMETRY_SHA256
assert sha256(HELPER_PATH.read_bytes()).hexdigest() == HELPER_SHA256
geometry = json.loads(GEOMETRY_PATH.read_text())
spec = spec_from_file_location('six_prefix', HELPER_PATH)
helper = module_from_spec(spec)
spec.loader.exec_module(helper)


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def ck(children, cutoff):
    assert len(children) == 6 and len(set(children)) == 6
    b = [Q(1, q - 3) for q in children]
    products = [Q(1)] * 64
    for mask in range(1, 64):
        bit = mask & -mask
        products[mask] = products[mask ^ bit] * b[bit.bit_length() - 1]
    v = [Q(0)] + [products[mask] * (cutoff if mask.bit_count() == 1 else cutoff + 1)
                   for mask in range(1, 64)]
    z = [Q(1)] + [Q(0)] * 63
    for mask in range(1, 64):
        bit = mask & -mask
        value, support = z[mask ^ bit], mask
        while support:
            if support & bit:
                value -= v[support] * z[mask ^ support]
            support = (support - 1) & mask
        z[mask] = value
    L = sum((products[s] * z[63 ^ s] for s in range(1, 64)), Q(0))
    assert min(z) > 0 and L > 0
    return min(z), L, L / (2 * 3 ** cutoff * z[-1])


def multiplier_prefixes(primes, thresholds):
    table, mean, out = {1: Q(1)}, Q(1), []
    for p, t in zip(primes, thresholds):
        cap = Q(p - 1, p - 1 - t)
        out.append((dict(table), mean))
        nxt = defaultdict(Q)
        for m, weight in table.items():
            for new in range(m, 32, m):
                n = new // m
                probability = 1 - cap / p if n == 1 else cap * Q(p - 1, p ** n)
                assert probability >= 0
                nxt[new] += weight * probability
        table, mean = nxt, mean * (1 + cap / Q(p - 1))
    return out


def source_mass(primes, thresholds):
    nodes = sorted((a, b, c, -1, j, 0, 0, 0, -1)
                   for a in (1, 2) for b in (2, 4) for c in (a, 3 - a)
                   for j in range(1, 5))
    envelopes = []
    for node in nodes:
        a, b, c, _, j, *_ = node
        gamma = 3 * (a == 1) + (b % 3 == a % 3)
        reserve = Q(135, 4) + gamma + (9 - gamma) * (Q(c == a, 5) + Q(j == a, 20))
        envelopes.append((node, reserve, helper.envelope(geometry['batches'], a, b, c, j)))
    distributions = multiplier_prefixes(primes, thresholds)
    rows = []
    for node, reserve, (a0, whole, values) in envelopes:
        losses = []
        for p, t, (table, mean) in zip(primes, thresholds, distributions):
            small = {m: w for m, w in table.items() if m < t}
            below = sum(small.values(), Q(0))
            below_first = sum((m * w for m, w in small.items()), Q(0))
            numerator = (sum((m * w * values[Q(t, m)] for m, w in small.items()), Q(0))
                         + (mean - below_first) * whole - t * (1 - below) * a0)
            losses.append(helper.ceil_decimal(numerator / (p - 1 - t)))
        live = (reserve - sum(losses, Q(0))) / 135
        assert live > 0
        rows.append((node, live))
    return min(rows, key=lambda row: row[1])


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    assert geometry['source_doi'] == '10.5281/zenodo.22759614'
    assert geometry['source_archive_sha256'] == '9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c'
    assert geometry['source_verifier_sha256'] == 'e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135'
    assert geometry['source_geometry_cpp_sha256'] == '8d7ecf1981a413daf2d3835ebe2c046b20f03010f7ce24f247bd357136e24f04'
    assert geometry['schema'] == 'six-prime-prefix-geometry-input-v1'
    assert len(geometry['batches']) == 72
    source_primes = (7, 13, 17, 19, 23, 29)
    thresholds = (2, 4, 4, 8, 8, 12)
    minimum_source, source = source_mass(source_primes, thresholds)
    assert len(helper.BATCHES) == 72 and helper.QUERIES == 51840
    caps = (Q(1), Q(1)) + tuple(Q(p - 1, p - 1 - t)
                                for p, t in zip(source_primes, thresholds))
    D = prod(caps)
    assert source == Q(10237584019, 168750000000)
    assert D == Q(297, 20)

    s11_children = tuple(p for p in range(11, 100) if prime(p))[:6]
    min_z_11, L_11, k_11 = ck(s11_children, 4)
    assert s11_children == (11, 13, 17, 19, 23, 29)
    assert min_z_11 == Q(9483, 1863680)
    assert L_11 == Q(5801, 116480)
    assert k_11 == Q(46408, 768123)

    schedule = ((31, 19), (37, 23), (41, 26), (43, 28),
                (47, 30), (53, 30))
    attachment_sum = k_11 + Q(1, 2 ** 28)
    for s, t in schedule:
        children = tuple(p for p in range(s, 100) if prime(p))[:6]
        minimum_z, _, k_s = ck(children, t)
        attachment_sum += k_s
        assert minimum_z > 0

    margin = source - attachment_sum
    haar = margin / D
    assert margin > 0 and haar > Q(1, 2200000)

    alpha = {3: Q(1), 5: Q(1), 7: Q(3, 2), 13: Q(3, 2),
             17: Q(4, 3), 19: Q(9, 5), 23: Q(11, 7), 29: Q(7, 4)}
    ratios = {p: alpha[p] * Q(2, p - 1) * Q(3, p) ** 4 for p in alpha}
    assert max(ratios.values()) == 1
    assert all(r <= 1 for r in ratios.values())
    print('source_row=', source_primes, 'thresholds=', thresholds)
    print('source_mass=', source, 'joint_cap=', D, 'worst_vertex=', minimum_source[0])
    print('s11_children=', s11_children, 'cutoff=4', 'min_Z=', min_z_11,
          'L=', L_11, 'k11=', k_11)
    print('attachment_budget_s11_and_s>=31=', attachment_sum)
    print('weighted_margin=', margin, 'haar_lower_bound=', haar)
    print('alpha_Kp_over_k11=', ratios)


if __name__ == '__main__':
    main()
