#!/usr/bin/env python3
"""Exact arithmetic certificate for the Erdős 699 i>=325 written theorem.

Default: rational constants, all 2675 finite index cutoffs, actual-binomial
inequalities, and small independent sieve controls. --symbolic additionally
checks Hermite identities with SymPy. --prime-gap reruns the ENTIRE prime
interval through 2**31 and its next prime, requiring NumPy. This computation
is a lemma in the written proof, not a sweep of all binomial triples.
No claim of independent mathematical review or of a whole solution of 699.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import comb, factorial, gcd, isqrt


def require(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)


def prime_mask(limit: int) -> bytearray:
    if limit < 2:
        raise ValueError("prime-mask limit must be at least 2")
    mask = bytearray(b"\x01") * (limit + 1)
    mask[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if mask[p]:
            size = (limit - p*p)//p + 1
            mask[p*p::p] = b"\x00" * size
    return mask


def constants() -> dict:
    # log z = 2 sum_{r>=0} t^(2r+1)/(2r+1), t=(z-1)/(z+1)>0.
    log2_lower = 2*(Q(1, 3) + Q(1, 81) + Q(1, 1215))
    log15_lower = 2*(Q(1, 5) + Q(1, 375) + Q(1, 15625))
    # Tail of exp(1), starting at 1/8!, is bounded geometrically.
    exp1_upper = sum((Q(1, factorial(r)) for r in range(8)), Q(0))
    exp1_upper += Q(9, 8*factorial(8))
    exp6_lower = sum((Q(6**r, factorial(r)) for r in range(12)), Q(0))
    require(exp1_upper < Q(87, 32), "upper bound on e")
    require(Q(87, 32)**8 < 3000, "log 3000 > 8")
    require(exp6_lower > 256, "log 256 < 6")
    require(log2_lower + 2*log15_lower > Q(3, 2), "log(9/2)>3/2")
    require(18*log2_lower > 12, "log 396738 > 12")
    require(Q(157, 21) < 11*log2_lower, "n/i < 2048")
    require(4*(1 + Q(6381, 5000)/8) < Q(116, 25), "u log i < 4.64")
    require(Q(116, 25)/8 == Q(29, 50), "u < .58")
    require((Q(116, 25)-Q(3, 2))/(1-Q(29, 50)) == Q(157, 21), "log ratio")
    require((3+Q(1, 256))*Q(6, 256)+Q(3, 256**2) < Q(1, 12), "Hermite constant")
    require(Q(1, 2)-Q(1, 8)+Q(1, 24) == Q(5, 12), "alternating log upper")
    return {"exact_rational_constants": True,
            "log2_lower": str(log2_lower), "exp1_upper": str(exp1_upper)}


def cutoffs() -> dict:
    mask = prime_mask(2999)
    count = 0
    checks = 0
    min_exponent = 2999
    for i in range(1, 3000):
        # count is pi(i-1), including at prime i.
        if i >= 325:
            exponent = i - 4*count
            require(exponent > 0, f"positive exponent at i={i}")
            require((i*(i+1))**i < (3*(2*i+1))**i * (1 << (31*exponent)),
                    f"exact finite row cutoff at i={i}")
            checks += 1
            min_exponent = min(min_exponent, exponent)
        count += mask[i]
    require(checks == 2675, "all boundary indices visited")
    return {"start_i": 325, "end_i": 2999, "exact_checks": checks,
            "row_cutoff": 1 << 31, "min_positive_exponent": min_exponent}


def binomial_checks(nmax: int) -> dict:
    actual = 0
    for n in range(6, nmax+1):
        values = [comb(n, r) for r in range(n//2+1)]
        hyperfactorial = 1
        for i in range(1, n//2):
            hyperfactorial *= i**i
            if i < 2:
                continue
            power = i*(i-1)//2
            for j in range(i+1, n//2+1):
                g = gcd(values[i], values[j])
                # Exact sharp-variance discriminant inequality, no real powers.
                require(g**(2*i-2)*hyperfactorial*(j*(n-j))**power
                        >= (n*n*(n-1))**power, "sharp actual gcd bound")
                actual += 1
    return {"actual_triples": actual, "actual_nmax": nmax}


def symbolic_checks() -> dict:
    import sympy as s
    x = s.Symbol("x")
    h0, h1 = s.Poly(1, x), s.Poly(x, x)
    hyperfactorial = 1
    for m in range(2, 13):
        h2 = s.Poly(x*h1.as_expr()-(m-1)*h0.as_expr(), x)
        hyperfactorial *= m**m
        require(h2.diff() == m*h1, "Hermite derivative")
        ode = h2.diff().diff()-s.Poly(x, x)*h2.diff()+m*h2
        require(ode.is_zero, "Hermite differential equation")
        require(h2.discriminant() == hyperfactorial, "Hermite discriminant")
        h0, h1 = h1, h2
    return {"symbolic_Hermite_degrees": [2, 12]}


def gap_sieve(endpoint: int, width: int = 6_000_000) -> dict:
    """Independent slice-marking implementation, with inclusive endpoints.

    The first prime strictly above endpoint is included in gap comparisons
    but excluded from pi(endpoint). An even width preserves odd segment starts.
    """
    if not 3 <= endpoint <= 10_000_000_000 or width < 2 or width % 2:
        raise ValueError("endpoint out of range or width not positive and even")
    import numpy as np
    last = endpoint + 4096
    root = isqrt(last)
    base_mask = np.ones(root+1, dtype=np.bool_)
    base_mask[:2] = False
    for p in range(2, isqrt(root)+1):
        if base_mask[p]:
            base_mask[p*p::p] = False
    base = np.flatnonzero(base_mask)[1:]  # omit 2: segments contain odd integers
    previous, count, best, left, right = 2, 1, 0, 0, 0
    first_above = None
    segments = 0
    for lo in range(3, last+1, width):
        hi = min(lo+width-1, last)
        mask = np.ones((hi-lo)//2+1, dtype=np.bool_)
        for p0 in base:
            p = int(p0)
            if p*p > hi:
                break
            start = max(p*p, -(-lo//p)*p)
            if start % 2 == 0:
                start += p
            mask[(start-lo)//2::p] = False
        primes = 2*np.flatnonzero(mask)+lo
        boundary = int(np.searchsorted(primes, endpoint, side="right"))
        count += boundary
        relevant = primes[:boundary+1]
        segments += 1
        if len(relevant):
            gaps = np.diff(np.concatenate((np.array([previous]), relevant)))
            index = int(np.argmax(gaps))
            if int(gaps[index]) > best:
                best = int(gaps[index])
                right = int(relevant[index])
                left = right-best
            previous = int(relevant[-1])
        if boundary < len(primes):
            first_above = int(primes[boundary])
            break
    require(first_above is not None, "padding did not reach a prime above endpoint")
    return {"endpoint": endpoint, "prime_count_to_endpoint": count,
            "first_prime_above": first_above, "max_consecutive_gap": best,
            "max_gap_left": left, "max_gap_right": right,
            "ordinary_integer_segment_width": width, "segments": segments}


def small_gap_controls() -> dict:
    # Trial division is intentionally separate from both sieve implementations.
    cases = 0
    for endpoint in (3, 4, 5, 8, 31, 32, 97, 100, 997, 1000):
        primes = []
        for p in range(2, endpoint+4097):
            if all(p % q for q in range(2, isqrt(p)+1)):
                primes.append(p)
                if p > endpoint:
                    break
        gaps = [b-a for a, b in zip(primes, primes[1:])]
        best = max(gaps)
        index = gaps.index(best)
        for width in (2, 14, 128):
            result = gap_sieve(endpoint, width)
            require(result["prime_count_to_endpoint"] == len(primes)-1, "small prime count")
            require(result["first_prime_above"] == primes[-1], "small last prime")
            require(result["max_consecutive_gap"] == best, "small maximal gap")
            require(result["max_gap_left"] == primes[index], "small max-gap endpoint")
            cases += 1
    return {"small_trial_vs_sieve_cases": cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nmax", type=int, default=70)
    parser.add_argument("--symbolic", action="store_true")
    parser.add_argument("--prime-gap", action="store_true")
    parser.add_argument("--gap-controls", action="store_true")
    args = parser.parse_args()
    if args.nmax < 6:
        parser.error("--nmax must be at least 6")
    result = {"constants": constants(), "cutoffs": cutoffs(),
              "binomial_checks": binomial_checks(args.nmax),
              "whole_699_solved": False, "independent_review": False}
    if args.symbolic:
        result.update(symbolic_checks())
    if args.gap_controls:
        result.update(small_gap_controls())
    if args.prime_gap:
        gap = gap_sieve(1 << 31)
        expected = {"prime_count_to_endpoint": 105097565,
                    "first_prime_above": 2147483659,
                    "max_consecutive_gap": 292,
                    "max_gap_left": 1453168141, "max_gap_right": 1453168433}
        for key, value in expected.items():
            require(gap[key] == value, f"full prime-gap certificate: {key}")
        result["full_prime_gap_certificate"] = gap
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
