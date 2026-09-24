#!/usr/bin/env python3
"""Verify fixed rational parameters for one-stage smoothed height lifting.

Python 3.9+ standard library only. The four universal finite-base Gamma
bounds remain unproved. This checks the displayed arithmetic, not the
general congruence argument or a Lean formalization. No floating-point
search, solver, external data, or optimization-dependent assertions occur.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

from fractions import Fraction
import json
from math import prod


PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
          37, 41, 43, 47, 53, 59, 61, 67, 71, 73)
TARGET = Fraction(138877, 1000)
DISPLAY_SCALE = 10**12
CASES = (
    (Fraction(128), 52,
     (3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
     "138.556342372564"),
    (Fraction(130), 58,
     (3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
     "138.599521198059"),
    (Fraction(138), 185,
     (5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2),
     "138.872506575675"),
    (Fraction(69437, 500), 3118,
     (10, 7, 6, 5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3),
     "138.876998901712"),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def smoothed_bound(cost_old, cost_coarse, height, widths):
    """Return E, lambda_bar and (cost_old+cost_coarse*E-lambda_bar)/(1-lambda_bar)."""
    cost_old, cost_coarse = Fraction(cost_old), Fraction(cost_coarse)
    require(cost_old >= cost_coarse >= 1, "require C_H >= C_h >= 1")
    require(isinstance(height, int) and height >= 1,
            "the old height must be a positive integer")
    require(len(widths) == len(PRIMES), "one width is required per prime")
    require(all(isinstance(r, int) and 0 <= r < height for r in widths),
            "each width must leave a positive coarse height")

    ks = tuple(height - r + 1 for r in widths)
    infinite_factors, old_factors = [], []
    for p, k, r in zip(PRIMES, ks, widths):
        u = Fraction(1, p - 1)
        v = Fraction(p + 1, (p - 1)**2)
        u_old = sum((Fraction(1, p**t) for t in range(1, r + 1)), Fraction(0))
        v_old = sum((Fraction(2*t - 1, p**t) for t in range(1, r + 1)),
                    Fraction(0))
        require(u - u_old == Fraction(1, p**r * (p - 1)),
                "geometric first-moment tail mismatch")
        require(v - v_old == Fraction(1, p**r) * (Fraction(2*r, p - 1) + v),
                "geometric second-moment tail mismatch")
        old_factor = 1 + 2*u_old/k + v_old/k**2
        # Count the complete old-old coefficient box independently of its
        # closed geometric expression, including zero exponents.
        pair_sum = sum(
            (Fraction(1, p**max(t, s))
             / (k if t else 1) / (k if s else 1)
             for t in range(r + 1) for s in range(r + 1)), Fraction(0))
        require(pair_sum == old_factor, "old-old coefficient box mismatch")
        infinite_factors.append(1 + 2*u/k + v/k**2)
        old_factors.append(old_factor)

    extra = prod(infinite_factors) - prod(old_factors)
    require(extra >= 0, "the additional-pair coefficient cannot be negative")
    k_min = min(ks)
    denominator_majorant = Fraction(k_min**2, k_min**2 - 1)
    deletion = (cost_coarse - 1) * denominator_majorant * (
        prod(1 + Fraction(1, (p - 1)*k**2) for p, k in zip(PRIMES, ks)) - 1)
    require(0 <= deletion < 1, "deletion bound does not certify survival")
    bound = (cost_old + cost_coarse*extra - deletion) / (1 - deletion)
    return extra, deletion, bound


def main():
    actual = tuple(n for n in range(3, 74, 2)
                   if all(n % d for d in range(2, n)))
    require(PRIMES == actual, "prime support must be all odd primes through 73")
    results = []
    for cost, height, widths, upper_text in CASES:
        extra, deletion, bound = smoothed_bound(cost, cost, height, widths)
        require(bound < TARGET, "smoothed sufficient-parameter inequality failed")
        upper = Fraction(upper_text)
        lower = upper - Fraction(1, DISPLAY_SCALE)
        require(lower <= bound < upper, "display interval misses the exact result")
        results.append({
            "unproved_base_cost": str(cost),
            "base_height": height,
            "widths_in_prime_order": widths,
            "coarse_heights": tuple(height - r for r in widths),
            "smoothed_bound_interval": [str(lower), str(upper)],
            "upper_display_endpoint": upper_text,
            "additional_pair_coefficient_nonnegative": extra >= 0,
            "deletion_bound_below_one": deletion < 1,
            "strictly_below_target": bound < TARGET,
        })
    print(json.dumps({
        "prime_support": PRIMES,
        "target": str(TARGET),
        "parameters": results,
        "scope": "Exact smoothed height-lifting parameter inequalities only. "
                 "Every universal finite-base cost remains unproved; "
                 "the mathematical theorem is not Lean-verified.",
    }, indent=2))


if __name__ == "__main__":
    main()
