#!/usr/bin/env python3
"""Verify the exact finite BBMST continuation from F_21 = 138877/1000.

Python 3.9+ standard library only. No checkpoint, external file or resume input
is used. All arithmetic checks remain enabled under python -O.

For p = p_k, a = (3p-1)/(p-1)^2 and b = 1/(4(p-1)^2), the
recurrence is R(F) = (1+a/(1-delta))*F/(1-b*F/(delta*(1-delta))).
On a positive denominator it is increasing in F. The program checks every
chosen rational delta and rounds R(F) upward to a grid of 10^(-12).

The stopping threshold is a rational lower bound for
k*(log(k)+log(log(k))-3)^2. Positive atanh partial sums after exact
power-of-two reduction give the logarithm lower bounds; their positive
bracket is checked before squaring.

This verifies finite arithmetic conditional on the stated seed. It does not
prove the universal head bound or the analytic BBMST continuation theorem.
Exit codes: 0 stopping inequality verified; 2 not established in this finite
scope (or invalid CLI input); 1 arithmetic verification failure.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction
import json
from math import isqrt
import sys

GRID = 10**12
LOG_GRID = 10**18
LOG_TERMS = 24
SEED_K = 21
SEED_PRIME = 73
SEED_F = Fraction(138877, 1000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def segmented_primes(first, last, segment_odds=1_000_000):
    """Independent odd-only bytearray sieve, inclusive integer endpoints."""
    require(segment_odds > 0, "segment size must be positive")
    require(first >= 0 and last >= first, "invalid sieve endpoints")
    if first <= 2 <= last:
        yield 2
    root = isqrt(last)
    base_flags = bytearray(b"\x01") * (root + 1)
    base_flags[:min(2, root + 1)] = b"\x00" * min(2, root + 1)
    for p in range(2, isqrt(root) + 1):
        if base_flags[p]:
            base_flags[p*p:root+1:p] = b"\x00" * ((root-p*p)//p+1)
    base = [p for p in range(3, root + 1, 2) if base_flags[p]]
    first = max(3, first)
    first += (first % 2 == 0)
    for lo in range(first, last + 1, 2 * segment_odds):
        hi = min(lo + 2 * segment_odds, last + 1)
        count = (hi - lo + 1) // 2
        flags = bytearray(b"\x01") * count
        for p in base:
            if p*p >= hi:
                break
            start = max(p*p, ((lo+p-1)//p)*p)
            if start % 2 == 0:
                start += p
            if start < hi:
                offset = (start-lo)//2
                flags[offset::p] = b"\x00" * ((count-1-offset)//p+1)
        offset = flags.find(b"\x01")
        while offset >= 0:
            yield lo + 2 * offset
            offset = flags.find(b"\x01", offset + 1)


def log_lower(x):
    x = Fraction(x)
    require(x >= 1, "log lower-bound input must be at least one")
    exponent = (x.numerator // x.denominator).bit_length() - 1
    reduced = x / (2**exponent)
    require(1 <= reduced < 2, "invalid logarithm range reduction")

    def positive_series(y):
        t = (y-1)/(y+1)
        power = t
        value = Fraction(0)
        for j in range(LOG_TERMS):
            value += power/(2*j+1)
            power *= t*t
        return 2*value

    value = exponent*positive_series(Fraction(2)) + positive_series(reduced)
    return Fraction((value.numerator*LOG_GRID)//value.denominator, LOG_GRID)


def stopping_threshold(k):
    lower_log = log_lower(k)
    require(lower_log > 1, "log-log input must exceed one")
    bracket = lower_log + log_lower(lower_log) - 3
    require(bracket > 0, "stopping bracket must be positive")
    return k * bracket * bracket


def verify(prime_limit, check_stride, segment_odds):
    require(prime_limit >= SEED_PRIME, "prime limit must be at least 73")
    require(check_stride > 0, "check stride must be positive")
    require(segment_odds > 0, "segment size must be positive")
    seed_primes = list(segmented_primes(0, SEED_PRIME, segment_odds))
    require(len(seed_primes) == SEED_K and seed_primes[-1] == SEED_PRIME,
            "seed prime rank verification failed")
    k, prime = SEED_K, SEED_PRIME
    z = 138877 * (GRID // 1000)
    minimum_numerator = minimum_denominator = 1
    stopping_checks = 0
    threshold = None
    last_checked_k = None
    if prime_limit > SEED_PRIME:
        primes = segmented_primes(SEED_PRIME + 1, prime_limit, segment_odds)
    else:
        primes = ()
    for prime in primes:
        k += 1
        d = (prime - 1)**2
        a_numerator = 3*prime - 1
        denominator = d*z
        radicand_numerator = denominator + 4*a_numerator*(d+a_numerator)*GRID
        root = isqrt(radicand_numerator*denominator*GRID*GRID)//denominator
        if root*root*denominator < radicand_numerator*GRID*GRID:
            root += 1
        require((root-1)**2*denominator < radicand_numerator*GRID*GRID
                <= root*root*denominator, "square-root rounding failed")
        delta_numerator = (d+a_numerator)*GRID*GRID//(d*(GRID+root))
        require(0 < delta_numerator and 2*delta_numerator <= GRID,
                "inadmissible delta at k=" + str(k))
        margin_denominator = 4*d*delta_numerator*(GRID-delta_numerator)
        margin_numerator = margin_denominator - z*GRID
        require(margin_numerator > 0, "nonpositive denominator at k=" + str(k))
        if margin_numerator*minimum_denominator < minimum_numerator*margin_denominator:
            minimum_numerator, minimum_denominator = margin_numerator, margin_denominator
        # Exactly GRID*R(z/GRID), after algebraic cancellation.
        numerator = 4*z*delta_numerator*(d*(GRID-delta_numerator)+a_numerator*GRID)
        new_z = (numerator+margin_numerator-1)//margin_numerator
        require(new_z > z and 0 <= new_z*margin_numerator-numerator < margin_numerator,
                "upward rounding failed at k=" + str(k))
        z = new_z
        if k % check_stride == 0:
            threshold = stopping_threshold(k)
            last_checked_k = k
            stopping_checks += 1
            if z*threshold.denominator <= GRID*threshold.numerator:
                break
    # Always evaluate the actual endpoint, including scopes containing no new
    # prime and scopes ending between stride checks. No stale threshold fields.
    if last_checked_k != k:
        threshold = stopping_threshold(k)
        stopping_checks += 1
    f_upper = Fraction(z, GRID)
    gap = threshold - f_upper
    passed = gap >= 0
    return {
        "status": "stopping-inequality-verified" if passed else "not-established-in-finite-scope",
        "seed": {"k": SEED_K, "prime": SEED_PRIME, "F_upper": str(SEED_F)},
        "parameters": {"prime_limit": prime_limit, "check_stride": check_stride,
                       "segment_odds": segment_odds, "grid": GRID,
                       "log_terms": LOG_TERMS, "log_grid": LOG_GRID},
        "endpoint": {"k": k, "prime": prime, "F_upper": str(f_upper),
                     "stopping_threshold_lower": str(threshold), "gap": str(gap)},
        "verified_recurrence_steps": k-SEED_K,
        "stopping_checks": stopping_checks,
        "minimum_denominator_margin": str(Fraction(minimum_numerator, minimum_denominator)),
        "scope": "Exact finite recurrence, delta admissibility, denominator positivity, "
                 "upward rounding and endpoint stopping inequality from the stated seed. "
                 "Universal head bound and analytic BBMST theorem are separate obligations. "
                 "A finite-scope failure does not refute the seed or conjecture."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime-limit", type=int, default=239622407)
    parser.add_argument("--check-stride", type=int, default=1000)
    parser.add_argument("--segment-odds", type=int, default=1_000_000)
    args = parser.parse_args()
    if args.prime_limit < SEED_PRIME:
        parser.error("--prime-limit must be at least 73")
    if args.check_stride <= 0:
        parser.error("--check-stride must be positive")
    if args.segment_odds <= 0:
        parser.error("--segment-odds must be positive")
    try:
        result = verify(args.prime_limit, args.check_stride, args.segment_odds)
    except ValueError as error:
        print(json.dumps({"status": "verification-failed", "error": str(error)}), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "stopping-inequality-verified" else 2


if __name__ == "__main__":
    sys.exit(main())
