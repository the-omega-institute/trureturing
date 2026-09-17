#!/usr/bin/env python3
"""Check rational sufficient parameters for the joint-load height lift.

Python 3.9+ standard library. This verifies only the displayed arithmetic.
The universal finite-base Gamma bounds are unproved hypotheses, not inputs
certified by this program. No float, solver, or external data is used.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

from fractions import Fraction
import json

PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
          37, 41, 43, 47, 53, 59, 61, 67, 71, 73)
TARGET = Fraction(138877, 1000)
CASES = ((Fraction(128), 71), (Fraction(130), 82),
         (Fraction(138), 543), (Fraction(69437, 500), 141476))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def height_bound(cost, height):
    """Return B, lambda and the bound (cost*B-lambda)/(1-lambda)."""
    cost = Fraction(cost)
    require(cost >= 1 and isinstance(height, int) and height >= 1,
            "cost and height must be at least one")
    k = height + 1
    symmetric = [Fraction(1)]
    growth = Fraction(1)
    for p in PRIMES:
        u = Fraction(1, p-1)
        v = Fraction(p+1, (p-1)**2)
        symmetric.append(Fraction(0))
        for j in range(len(symmetric)-1, 0, -1):
            symmetric[j] += u*symmetric[j-1]
        growth *= 1 + 2*u/k + v/k**2
    deletion = (cost-1)*sum(
        (symmetric[j]/(k**(2*j)-1) for j in range(1, len(symmetric))),
        Fraction(0))
    require(0 <= deletion < 1, "deletion bound does not certify survival")
    return growth, deletion, (cost*growth-deletion)/(1-deletion)


def main():
    actual = tuple(n for n in range(3, 74, 2)
                   if all(n % d for d in range(2, n)))
    require(PRIMES == actual, "prime support must be all odd primes through 73")
    results = []
    for cost, height in CASES:
        growth, deletion, bound = height_bound(cost, height)
        require(growth >= 1, "growth cannot be less than one")
        require(bound < TARGET, "sufficient parameter inequality failed")
        scale = 10**12
        lower = (bound.numerator*scale)//bound.denominator
        require(Fraction(lower, scale) <= bound < Fraction(lower+1, scale),
                "display interval does not enclose rational result")
        results.append({
            "unproved_base_cost": str(cost), "base_height": height,
            "full_height_bound_interval": [str(Fraction(lower, scale)),
                                           str(Fraction(lower+1, scale))],
            "strictly_below_target": True})
    print(json.dumps({
        "target": str(TARGET), "parameters": results,
        "scope": "Exact height-lifting parameter inequalities only. "
                 "Every universal finite-base cost remains unproved."
    }, indent=2))


if __name__ == "__main__":
    main()
