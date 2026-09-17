#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
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
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product as cartesian_product
from math import gcd, isqrt, prod
from pathlib import Path
import argparse
import json

HEAD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
               37, 41, 43, 47, 53, 59, 61, 67, 71, 73)


from star_block.base import *

def support_rank_primes(limit):
    require(limit >= 2, "sieve limit must be at least two")
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p)//p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def pair_support_components(primes, q0, denominator=10 ** 12):
    """Upper bounds for sum a_v², sum a_v²(3A_v+2S_v), sum a_v²R_v.

    Each a_p=1/(p-1) is rounded upward individually. The third
    polynomial is represented as R=2 sum_(p<q) a_p a_q, so every
    coefficient used by the upward rounding is nonnegative.
    """
    A = S = R = T0 = T1 = T2 = count = 0
    for p in primes:
        if p < q0:
            continue
        a = (denominator + p - 2)//(p - 1)
        require(a*(p - 1) >= denominator, "reciprocal ceiling failed")
        a2 = a*a
        T0 += a2
        T1 += a2*(3*denominator*A + 2*S)
        T2 += a2*R
        R += 2*A*a
        A += a
        S += a2
        count += 1
    require(R == A*A - S, "ordered distinct-parent sum mismatch")
    return {
        "count": count,
        "T0": F(T0, denominator**2),
        "T1": F(T1, denominator**4),
        "T2": F(T2, denominator**4),
        "A0": F(A, denominator),
        "S0": F(S, denominator**2),
    }


def pair_support_bound(components, delta, G, cutoff=2 ** 20):
    require(0 < delta <= F(1, 2), "threshold outside capped-kernel range")
    require(G > 0 and cutoff > 0, "positive head bound and cutoff required")
    K = 1/(1 - delta)
    A, S = components["A0"], components["S0"]
    finite = components["T0"] + K*components["T1"] + K*K*components["T2"]
    tail = (2 + K*(6*A + 12 + 4*S + F(8, cutoff))
            + K*K*(2*A*A + 8*A + 12))/cutoff
    return {
        "K": K,
        "finite_moment_sum_upper": finite,
        "infinite_moment_tail_upper": tail,
        "loss_upper": G*(finite + tail)/(4*delta*(1 - delta)),
    }


def rank_two_tail_bounds():
    limit = 2 ** 20
    scale = 10 ** 12
    primes = support_rank_primes(limit)
    require(len(primes) == 82025, "rank-two prime count through 2^20")
    rows = []
    for head, cutoff, gamma, delta, target, expected in [
            ("complete_star_head", 79, F(177), F(2, 5), F(861, 1000),
             F(82616302964943401201866424605892182335718551607,
               96000000000000000000000000000000000000000000000)),
            ("arbitrary_357_head", 23, F(1889, 48), F(3, 8), F(947, 1000),
             F(6656641538266277932795352817051944900003690098417,
               7031250000000000000000000000000000000000000000000))]:
        components = pair_support_components(primes, cutoff, scale)
        result = pair_support_bound(components, delta, gamma, limit)
        require(result["loss_upper"] == expected < target < 1,
                "exact rank-two loss and strict threshold")
        rows.append({"head": head, "tail_prime_minimum": cutoff,
                     "Gamma_bound": str(gamma), "delta": str(delta),
                     "components": {key: str(value) if isinstance(value, F) else value
                                    for key, value in components.items()},
                     **{key: str(value) for key, value in result.items()},
                     "strict_target": str(target)})
    return {"prime_cutoff": limit, "rounding_scale": scale,
            "maximum_tail_support_per_original_modulus": 2,
            "sieve_prime_count": len(primes), "rows": rows,
            "scope": "Exact arithmetic for bounded original tail support; no graph restriction."}


def rank_three_tail_bounds():
    """Positive coefficient enumeration and an exact all-integer infinite tail."""
    limit = 2 ** 20
    scale = 10 ** 12
    primes = support_rank_primes(limit)
    require(len(primes) == 82025, "rank-three sieve count through 2^20")

    def ceiling(numerator, denominator):
        require(denominator > 0, "positive rounding denominator")
        return (numerator + denominator - 1) // denominator

    def poly_add(*terms):
        result = [F(0)] * max(map(len, terms))
        for term in terms:
            for degree, value in enumerate(term):
                result[degree] += value
        return result

    def poly_mul(left, right):
        result = [F(0)] * (len(left) + len(right) - 1)
        for i, x in enumerate(left):
            for j, y in enumerate(right):
                result[i + j] += x * y
        return result

    def poly_scale(term, value):
        return [value * x for x in term]

    # These moments solve M_k - sum_{j<=k} binom(k,j) M_j/2 = [k=0].
    # Verify via the shift identity instead of trusting a decimal tail estimate.
    from math import comb
    moments = [F(2), F(2), F(6), F(26), F(150)]
    for k, moment in enumerate(moments):
        shifted = sum((F(comb(k, j), 2) * moments[j] for j in range(k + 1)), F(0))
        require(moment - shifted == int(k == 0), "geometric power-sum identity")

    # Independent finite exponent-tuple expansion detects a support-count error.
    regression_count = 0
    for support_limit in (1, 2):
        small_primes = (3, 5, 7)
        cap = F(5, 3)
        coefficients = [[F(0)] * (support_limit + 1) for _ in range(support_limit + 1)]
        coefficients[0][0] = 1
        for prime in small_primes:
            a = sum((F(1, prime ** e) for e in (1, 2)), F(0))
            b = sum((F(1, prime ** max(e, f)) for e in (1, 2) for f in (1, 2)), F(0))
            old = coefficients
            coefficients = [row[:] for row in old]
            for i in range(support_limit + 1):
                for j in range(support_limit + 1):
                    coefficients[i][j] += cap * (
                        (a * old[i - 1][j] if i else 0)
                        + (a * old[i][j - 1] if j else 0)
                        + (b * old[i - 1][j - 1] if i and j else 0))
        tuples = [t for t in cartesian_product(range(3), repeat=3)
                  if sum(e > 0 for e in t) <= support_limit]
        direct = sum((prod(cap / p ** max(e, f) if max(e, f) else 1
                           for p, e, f in zip(small_primes, left, right))
                      for left in tuples for right in tuples), F(0))
        require(direct == sum(map(sum, coefficients)), "support polynomial matches actual exponent pairs")
        regression_count += len(tuples) ** 2

    rows = []
    for head, cutoff, gamma, delta, target in [
            ("head_divides_315", 17, F(1148, 71), F(3, 10), F(981, 1000)),
            ("head_divides_945", 19, F(3812, 179), F(7, 20), F(989, 1000))]:
        cap = 1 / (1 - delta)
        coefficients = [[0] * 3 for _ in range(3)]
        coefficients[0][0] = scale
        total = a_sum = b_sum = count = 0
        for prime in primes:
            if prime < cutoff:
                continue
            denominator = prime - 1
            a = ceiling(scale, denominator)
            b = ceiling(scale * (denominator + 2), denominator ** 2)
            square = ceiling(scale, denominator ** 2)
            total += ceiling(square * sum(map(sum, coefficients)), scale)
            old = coefficients
            coefficients = [row[:] for row in old]
            for i in range(3):
                for j in range(3):
                    increment = ((a * old[i - 1][j] if i else 0)
                                 + (a * old[i][j - 1] if j else 0)
                                 + (b * old[i - 1][j - 1] if i and j else 0))
                    coefficients[i][j] += ceiling(cap.numerator * increment,
                                                  cap.denominator * scale)
            a_sum += a
            b_sum += b
            count += 1
        # On (N 2^j, N 2^(j+1)], sum a_v^2 <= 1/(N 2^j).
        # The prefix sums increase by at most j+1 and j+1+2/(N-1).
        a_poly = [cap * (F(a_sum, scale) + 1), cap]
        b_poly = [cap * (F(b_sum, scale) + 1 + F(2, limit - 1)), cap]
        base = poly_add([1], a_poly, poly_scale(poly_mul(a_poly, a_poly), F(1, 2)))
        short = poly_add([1], a_poly)
        tail_poly = poly_add(poly_mul(base, base),
                             poly_mul(b_poly, poly_mul(short, short)),
                             poly_scale(poly_mul(b_poly, b_poly), F(1, 2)))
        tail = sum((coefficient * moment for coefficient, moment in zip(tail_poly, moments)), F(0)) / limit
        finite = F(total, scale)
        loss = gamma * (finite + tail) / (4 * delta * (1 - delta))
        require(loss < target < 1, "rank-three infinite-prime loss below one")
        rows.append({"head": head, "tail_prime_minimum": cutoff,
                     "maximum_tail_support_per_original_modulus": 3,
                     "Gamma_bound": str(gamma), "delta": str(delta),
                     "prime_count": count, "prefix_a_upper": str(F(a_sum, scale)),
                     "prefix_b_upper": str(F(b_sum, scale)),
                     "final_scaled_coefficient_matrix": coefficients,
                     "finite_sum_upper": str(finite), "dyadic_tail_polynomial": list(map(str, tail_poly)),
                     "infinite_tail_upper": str(tail), "loss_upper": str(loss),
                     "strict_target": str(target)})
    return {"prime_cutoff": limit, "rounding_scale": scale,
            "sieve_prime_count": len(primes), "geometric_power_sums": list(map(str, moments)),
            "finite_exponent_pair_regressions": regression_count, "rows": rows,
            "scope": "Exact certificate for the ordinary bounded-tail-support theorem; no graph restriction."}


def finite_support_switch_bounds():
    """Release every support restriction after a certified BBMST starting point."""
    from runpy import run_path
    continuation = run_path(str((Path(__file__).resolve().parents[1] / "verify_finite_continuation.py")))
    threshold_lower = continuation["stopping_threshold"]
    scale = 10 ** 12
    rows = []
    for head, first, gamma, delta, support, cutoff, expected_rank, seed_ceiling in [
            ("complete_star_head", 79, F(177), F(2, 5), 2, 8192, 1028, F(34474)),
            ("arbitrary_357_head", 23, F(1889, 48), F(3, 8), 2, 32768, 3512, F(160112)),
            ("head_divides_315", 17, F(1148, 71), F(3, 10), 3, 8192, 1028, F(28830)),
            ("head_divides_945", 19, F(3812, 179), F(7, 20), 3, 8192, 1028, F(34675))]:
        primes = support_rank_primes(cutoff)
        require(len(primes) == expected_rank >= 10, "BBMST theorem prime-index domain")
        cap = 1 / (1 - delta)
        coefficients = [[0] * support for _ in range(support)]
        coefficients[0][0] = scale
        total = 0
        full_product = scale
        for prime in primes:
            if prime < first:
                continue
            denominator = prime - 1
            a = (scale + denominator - 1) // denominator
            b = (scale * (denominator + 2) + denominator ** 2 - 1) // denominator ** 2
            square = (scale + denominator ** 2 - 1) // denominator ** 2
            total += (square * sum(map(sum, coefficients)) + scale - 1) // scale
            old = coefficients
            coefficients = [row[:] for row in old]
            for i in range(support):
                for j in range(support):
                    numerator = cap.numerator * (
                        (a * old[i - 1][j] if i else 0)
                        + (a * old[i][j - 1] if j else 0)
                        + (b * old[i - 1][j - 1] if i and j else 0))
                    divisor = cap.denominator * scale
                    coefficients[i][j] += (numerator + divisor - 1) // divisor
            factor = 1 + cap * F(3 * prime - 1, denominator ** 2)
            numerator = full_product * factor.numerator
            full_product = (numerator + factor.denominator - 1) // factor.denominator
            require(0 <= full_product * factor.denominator - numerator < factor.denominator,
                    "full Gamma product upward rounding")
        finite_moment = F(total, scale)
        loss = gamma * finite_moment / (4 * delta * (1 - delta))
        require(0 <= loss < 1, "positive actual prefix survivor mass")
        gamma_upper = gamma * F(full_product, scale)
        seed = gamma_upper / (1 - loss)
        threshold = threshold_lower(len(primes))
        require(seed < seed_ceiling < threshold, "strict BBMST continuation starting inequality")
        rows.append({"head": head, "tail_prime_minimum": first,
                     "maximum_tail_support_when_largest_prime_at_most_cutoff": support,
                     "largest_prime_cutoff": cutoff, "global_prime_index": len(primes),
                     "last_prime_at_most_cutoff": primes[-1],
                     "Gamma_head_bound": str(gamma), "delta_before_cutoff": str(delta),
                     "finite_moment_sum_upper": str(finite_moment),
                     "prefix_loss_upper": str(loss), "prefix_survivor_mass_lower": str(1 - loss),
                     "full_Gamma_product_upper": str(F(full_product, scale)),
                     "prefix_Gamma_upper": str(gamma_upper),
                     "continuation_seed_upper": str(seed), "strict_seed_ceiling": str(seed_ceiling),
                     "BBMST_threshold_lower": str(threshold), "strict_threshold_margin": str(threshold - seed),
                     "support_restriction_above_cutoff": None})
    return {"rounding_scale": scale, "rows": rows,
            "logarithm_bound_source": "verify_finite_continuation.py:stopping_threshold",
            "scope": "Exact finite premises for BBMST Theorem 6.1; arbitrary later support, exponents, and graph."}
