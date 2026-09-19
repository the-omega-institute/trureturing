#!/usr/bin/env python3
"""Exact finite source for simultaneous convex maxima and disjoint high loads."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import gcd, prod
from pathlib import Path
import argparse
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

DEFAULT_PROOF = 'profile-notes/338-simultaneous-convex-extremizers-can-have-disjoint-high-load-regions.md'
DEFAULT_CERTIFICATE = 'certificates/source_norms/source_pair_convex_extremizers.json'
SOURCES = (
    'certificate_io.py',
    'profile-notes/26-conditional-head-deletion-with-a-priced-arbitrary-cofactor-tail.md',
    'profile-notes/302-a-positive-actual-source-neighborhood-keeps-j-below403.md',
    'profile-notes/333-variable-full-haar-thresholds-retain-more-survivor-mass.md',
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Readable certificate IO')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def calculate(base, proof):
    io = module('convex_pair_certificate_io', base / 'certificate_io.py')
    factors = ((3, 2), (5, 1), (7, 1), (11, 1), (13, 1))
    Q = prod(p ** h for p, h in factors)
    divisors = tuple(sorted(prod(p ** e for (p, _), e in zip(factors, es))
                            for es in product(*(range(h + 1) for _, h in factors))))
    require(Q == 45045 and len(divisors) == 48 and len(set(divisors)) == 48,
            'Complete distinct original divisor inventory')
    forbidden = tuple((d, 0) for d in divisors if d > 1)
    require(len(forbidden) == 47 and all(d % 2 == 1 for d, _ in forbidden),
            'Distinct odd original forbidden moduli')
    survivors = tuple(x for x in range(Q) if all(x % d != a for d, a in forbidden))
    require(survivors == tuple(x for x in range(Q) if gcd(x, Q) == 1),
            'Original forbidden union leaves exactly the actual units')
    require(len(survivors) == 17280, 'Complete actual survivor inventory')
    require(all(x % 3 == 0 for x in range(Q) if x % 9 == 0),
            'Actual nine-class is ineffective, outside the required effective9 chart')
    residues = {j: tuple((d, j % d) for d in divisors) for j in (1, 2)}
    loads = {j: tuple(sum(x % d == a for d, a in residues[j]) for x in survivors)
             for j in (1, 2)}
    hist = {j: Counter(loads[j]) for j in (1, 2)}
    expected = {1: 4455, 2: 6246, 3: 1485, 4: 3006, 6: 1092, 8: 632,
                12: 274, 16: 59, 24: 28, 32: 2, 48: 1}
    require(hist[1] == hist[2] == expected, 'Both complete original-load histograms')
    positions = {x: k for k, x in enumerate(survivors)}
    require(all(loads[2][positions[(2*x) % Q]] == loads[1][k]
                for k, x in enumerate(survivors)), 'Actual source-preserving rotation')
    products = tuple(a*b for a, b in zip(loads[1], loads[2]))
    require(max(products) == 48, 'Sharp pointwise product bound')
    intersection = F(sum(a > 6 and b > 6 for a, b in zip(loads[1], loads[2])), len(survivors))
    high = {j: F(sum(a > 6 for a in loads[j]), len(survivors)) for j in (1, 2)}
    require(intersection == 0 and high[1] == high[2] == F(83, 1440),
            'Positive individual high mass with exactly zero common high mass')
    expected_hinges = {6: F(32,135), 8: F(263,2160), 12: F(3,80),
                       16: F(1,60), 18: F(113,8640), 24: F(1,432)}
    hinges = {t: F(sum(max(a-t, 0) for a in loads[1]), len(survivors))
              for t in expected_hinges}
    require(hinges == expected_hinges, 'Every displayed exact hinge value')
    coordinate_histograms = {}
    counts = Counter({1: 1})
    for p, h in factors:
        local = Counter(1 + sum(x % (p ** e) == 1 for e in range(1, h+1))
                        for x in range(p**h) if gcd(x, p) == 1)
        coordinate_histograms[str(p)] = dict(sorted(local.items()))
        nxt = Counter()
        for a, n in counts.items():
            for b, m in local.items():
                nxt[a*b] += n*m
        counts = nxt
    require(counts == hist[1], 'Independent CRT product reconstruction of all load counts')
    raw = io.read_artifact_bytes(proof)
    out = {
        'schema': 'erdos7-source-pair-convex-extremizers-v1',
        'scope': 'Exact finite original source and load arithmetic. Ordinary proof establishes simultaneous convex maximality among arbitrary original residues. Outside the effective9 source guard of333. No future bad-event intersection, raw333/335 upper attainment, or Lean claim.',
        'source_sha256': {p: sha256(io.read_artifact_bytes(base / p)).hexdigest() for p in SOURCES},
        'ordinary_proof': {'sha256': sha256(raw).hexdigest(), 'byte_count': len(raw)},
        'producer_sha256': sha256(io.read_artifact_bytes(Path(__file__))).hexdigest(),
        'modulus': Q,
        'factorization': factors,
        'original_forbidden_classes': forbidden,
        'original_test_residues': residues,
        'actual_source_size': len(survivors),
        'source_inventory_sha256': sha256(','.join(map(str, survivors)).encode()).hexdigest(),
        'effective9': False,
        'complete_load_histogram': dict(sorted(hist[1].items())),
        'coordinate_load_histograms': coordinate_histograms,
        'rotation_multiplier': 2,
        'pointwise_product_maximum': 48,
        'high_load_threshold': 6,
        'individual_high_masses': {j: str(v) for j, v in high.items()},
        'common_high_mass': str(intersection),
        'hinge_values': {t: str(v) for t, v in hinges.items()},
        'unresolved_tail': None,
        'tail_scope': 'Finite period with every divisor test; no exponent tail is omitted.',
    }
    # Normalize JSON object keys and sequence types before exact comparison.
    return io, json.loads(json.dumps(out), object_pairs_hook=io._unique)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--proof', type=Path)
    parser.add_argument('--certificate', type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    proof = args.proof or args.base / DEFAULT_PROOF
    certificate = args.certificate or args.base / DEFAULT_CERTIFICATE
    io, out = calculate(args.base, proof)
    if args.write:
        io.write_certificate_text(certificate, json.dumps(out, indent=2) + '\n')
    else:
        require(out == json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=io._unique),
                'Complete finite source certificate regenerates')
    print('PASS 47 forbidden classes; 48 original test labels; 17280 actual survivors; high masses 83/1440 each; intersection 0')


if __name__ == '__main__':
    main()
