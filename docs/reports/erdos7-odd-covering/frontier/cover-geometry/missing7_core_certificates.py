#!/usr/bin/env python3
"""Exact arithmetic for two eight-prime cores omitting 7.

The cases are exact core tuples. Coordinatewise larger later-prime tuples
need their own omitted-prime attachment budget and are outside this checker.
No source verifier, Lean checker, or unrestricted Erdos #7 claim is involved.
"""
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from hashlib import sha256
from math import prod
from pathlib import Path
import sys
import json

BASE = Path(__file__).resolve().parent
GEOMETRY = BASE / 'six_prime_prefix_geometry.json'
GEOMETRY_HELPER = BASE / 'six_prime_prefix_certificate.py'
SOURCE_HELPER = BASE / 'spine_book_certificate.py'
VARIABLE_HELPER = BASE / 'variable_eight_core_certificate.py'
GEOMETRY_SHA256 = '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'
GEOMETRY_HELPER_SHA256 = '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4'
SOURCE_HELPER_SHA256 = '601c9c94018ab960abe63a126c1cf0d96b84b6b335ef5630c84adfb113db44de'
VARIABLE_HELPER_SHA256 = '45b59fa2d0127d6dbaaa46a9dd4046bc0e4537888f864153f95f8496f500a7e6'
THRESHOLDS = (2, 4, 4, 8, 8, 12)


def load(name, path):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    assert sha256(GEOMETRY.read_bytes()).hexdigest() == GEOMETRY_SHA256
    assert sha256(GEOMETRY_HELPER.read_bytes()).hexdigest() == GEOMETRY_HELPER_SHA256
    assert sha256(SOURCE_HELPER.read_bytes()).hexdigest() == SOURCE_HELPER_SHA256
    assert sha256(VARIABLE_HELPER.read_bytes()).hexdigest() == VARIABLE_HELPER_SHA256
    geometry = json.loads(GEOMETRY.read_text())
    assert geometry['schema'] == 'six-prime-prefix-geometry-input-v1'
    assert len(geometry['batches']) == 72
    assert geometry['source_doi'] == '10.5281/zenodo.22759614'
    assert geometry['source_archive_sha256'] == '9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c'
    assert geometry['source_verifier_sha256'] == 'e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135'
    assert geometry['source_geometry_cpp_sha256'] == '8d7ecf1981a413daf2d3835ebe2c046b20f03010f7ce24f247bd357136e24f04'
    helper = load('missing7_geometry', GEOMETRY_HELPER)
    source = load('missing7_source', SOURCE_HELPER)
    variable = load('missing7_ck', VARIABLE_HELPER)
    nodes = sorted((a, b, c, -1, j, 0, 0, 0, -1)
                   for a in (1, 2) for b in (2, 4)
                   for c in (a, 3 - a) for j in range(1, 5))
    envelopes = []
    for node in nodes:
        a, b, c, _, j, *_ = node
        gamma = 3 * (a == 1) + (b % 3 == a % 3)
        reserve = Q(135, 4) + gamma + (9 - gamma) * (
            Q(c == a, 5) + Q(j == a, 20))
        envelopes.append((node, reserve,
                          helper.envelope(geometry['batches'], a, b, c, j)))

    cases = (
        ('missing7', (11, 13, 17, 19, 23, 29), Q(1, 8),
         Q(7332516433, 56250000000), Q(99, 8),
         ((31, 19), (37, 23), (41, 26), (43, 28), (47, 30), (53, 30))),
        ('missing7_11', (13, 17, 19, 23, 29, 31), Q(1, 6),
         Q(229603051201, 1350000000000), Q(264, 35),
         ((37, 23), (41, 26), (43, 28), (47, 30), (53, 30))),
    )
    for name, proxies, small_fee, expected_mass, expected_D, schedule in cases:
        source_row = source.source_mass(helper, envelopes, proxies, THRESHOLDS)
        mass = Q(source_row['mass_lower_bound'])
        caps = (Q(1), Q(1)) + tuple(
            Q(p - 1, p - 1 - t) for p, t in zip(proxies, THRESHOLDS))
        D = prod(caps)
        assert mass == expected_mass and D == expected_D
        fees = (Q(1), Q(3, 10)) + tuple(Q(2, p - 1) for p in proxies)
        assert all(alpha * fee <= 1 for alpha, fee in zip(caps, fees))
        tail = small_fee + Q(1, 2 ** 28)
        for minimum, cutoff in schedule:
            children = tuple(q for q in range(minimum, 200)
                             if variable.prime(q))[:6]
            row = variable.ck(children, cutoff)
            tail += Q(row['K3'])
            assert all(caps[i] * Q(2 * 3 ** cutoff,
                                   p ** cutoff * (p - 1)) <= 1
                       for i, p in enumerate((3, 5) + proxies))
        margin = mass - tail
        assert margin > 0 and margin / D > Q(1, 2200000)
        print(name)
        print('  mass=', mass, 'D=', D)
        print('  delta=', tail, '=', float(tail))
        print('  margin=', margin, 'haar=', margin / D,
              '=', float(margin / D))
    assert len(helper.BATCHES) == 72 and helper.QUERIES == 51840


if __name__ == '__main__':
    main()
