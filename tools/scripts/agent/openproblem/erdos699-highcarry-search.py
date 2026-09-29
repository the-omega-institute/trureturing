#!/usr/bin/env python3
"""Exact bounded high-carry search for the Erdős 699 i=3 reduction.

This program searches a finite range of M = 2^a * 3^epsilon.  It is not a
proof of Erdős 699.  For each admissible u it uses the exact bound (57), then
reconstructs t from the complete prime-power allocation for R(Mu-1); it never
scans 1 <= t < M/2 in the main search.  Every solution of both low-block
conditions (56) is then checked against every prime dividing binom(Mu, 3),
using independent Kummer-carry and Legendre valuations.

The five quotient labels are retained explicitly:

  q | Mu-1: j mod q = 0 or 1  <=>  q | t or q | M-t;
  q | Mu-2: j mod q = 0, 1, or 2
                                  <=>  q | t, M-2t, or M-t.

Only the Python standard library is used.  Primality and factorization are
deterministic for the enforced n < 2^64 range.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from functools import lru_cache
from math import comb, gcd
from pathlib import Path
from time import perf_counter


MR_BASES_64 = (2, 325, 9375, 28178, 450775, 9780504, 1795265022)
SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)


def valuation(x: int, p: int) -> int:
    exponent = 0
    while x % p == 0:
        exponent += 1
        x //= p
    return exponent


def retained_core(x: int) -> int:
    x >>= valuation(x, 2)
    if valuation(x, 3) == 1:
        x //= 3
    return x


def bound_57_holds(m: int, u: int) -> bool:
    """Exact squared form of (Mu-1)(Mu-2) <= sqrt(3) M^3."""
    product = (m * u - 1) * (m * u - 2)
    return product * product <= 3 * m**6


def maximum_u(m: int) -> int:
    lo, hi = 0, 1
    while bound_57_holds(m, hi):
        lo, hi = hi, 2 * hi
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if bound_57_holds(m, mid):
            lo = mid
        else:
            hi = mid
    return lo


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES_64:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_brent(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    for c in range(1, 100):
        y, r, g = 2, 1, 1
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            q = 1
            while k < r and g == 1:
                saved_y = y
                for _ in range(min(128, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += 128
            r *= 2
        if g == n:
            g = 1
            y = saved_y
            while g == 1:
                y = (y * y + c) % n
                g = gcd(abs(x - y), n)
        if g != n:
            return g
    raise RuntimeError(f"deterministic Pollard-Brent schedule failed for {n}")


@lru_cache(maxsize=None)
def factor_tuple(n: int) -> tuple[tuple[int, int], ...]:
    if not 1 <= n < 1 << 64:
        raise ValueError(f"factorization input outside deterministic 64-bit range: {n}")
    factors: list[int] = []
    stack = [n]
    while stack:
        x = stack.pop()
        if x == 1:
            continue
        for p in SMALL_PRIMES:
            if x % p == 0:
                factors.append(p)
                stack.append(x // p)
                break
        else:
            if is_prime(x):
                factors.append(x)
            else:
                divisor = pollard_brent(x)
                stack.extend((divisor, x // divisor))
    result: list[tuple[int, int]] = []
    for p in sorted(factors):
        if result and result[-1][0] == p:
            result[-1] = (p, result[-1][1] + 1)
        else:
            result.append((p, 1))
    return tuple(result)


def factor_dict(n: int) -> dict[int, int]:
    return dict(factor_tuple(n))


def prime_powers(n: int) -> tuple[int, ...]:
    return tuple(p**e for p, e in factor_tuple(n))


def divisors_from_prime_powers(powers: tuple[int, ...]):
    for mask in range(1 << len(powers)):
        divisor = 1
        for bit, q in enumerate(powers):
            if mask >> bit & 1:
                divisor *= q
        yield divisor


def reconstructed_t_values(m: int, u: int) -> tuple[int, ...]:
    """Reconstruct all t satisfying R(Mu-1) | t(M-t) by CRT allocation."""
    r1 = retained_core(m * u - 1)
    upper = (m - 1) // 2
    values: list[int] = []
    for left in divisors_from_prime_powers(prime_powers(r1)):
        right = r1 // left
        if right == 1:
            residue = 0
        else:
            residue = left * (m * pow(left, -1, right) % right)
        first = residue if residue > 0 else r1
        if first > upper:
            continue
        values.extend(range(first, upper + 1, r1))
    assert len(values) == len(set(values)), (m, u, values)
    return tuple(sorted(values))


def low_block_holds(m: int, u: int, t: int) -> bool:
    n = m * u
    x = t * (m - t)
    return x % retained_core(n - 1) == 0 and (
        x * (m - 2 * t)
    ) % retained_core(n - 2) == 0


def quotient_tests(m: int, u: int, t: int) -> list[dict[str, int | str | bool]]:
    """Return all residue-labelled full-prime-power tests behind (56)."""
    n, j = m * u, t * u
    tests: list[dict[str, int | str | bool]] = []
    definitions = (
        (1, {0: ("n-1:j=0", t), 1: ("n-1:j=1", m - t)}),
        (
            2,
            {
                0: ("n-2:j=0", t),
                1: ("n-2:j=1", m - 2 * t),
                2: ("n-2:j=2", m - t),
            },
        ),
    )
    for offset, labels in definitions:
        for p, exponent in factor_tuple(n - offset):
            if p == 2 or (p == 3 and exponent == 1):
                continue
            q = p**exponent
            residue = j % q
            label, target = labels.get(residue, ("invalid", 1))
            passed = residue in labels and target % q == 0
            tests.append(
                {
                    "offset": offset,
                    "p": p,
                    "q": q,
                    "j_mod_q": residue,
                    "label": label,
                    "passed": passed,
                }
            )
    return tests


def kummer_valuation(n: int, j: int, p: int) -> int:
    a, b, carry, count = j, n - j, 0, 0
    while a or b or carry:
        total = a % p + b % p + carry
        carry = int(total >= p)
        count += carry
        a //= p
        b //= p
    return count


def factorial_valuation(n: int, p: int) -> int:
    result = 0
    while n:
        n //= p
        result += n
    return result


def legendre_binomial_valuation(n: int, j: int, p: int) -> int:
    return (
        factorial_valuation(n, p)
        - factorial_valuation(j, p)
        - factorial_valuation(n - j, p)
    )


def binomial_three_factorization(n: int) -> dict[int, int]:
    result: dict[int, int] = {}
    for value in (n, n - 1, n - 2):
        for p, exponent in factor_tuple(value):
            result[p] = result.get(p, 0) + exponent
    result[2] -= 1
    result[3] -= 1
    result = {p: e for p, e in result.items() if e}
    assert all(e > 0 for e in result.values())
    product = 1
    for p, exponent in result.items():
        product *= p**exponent
    assert product == n * (n - 1) * (n - 2) // 6
    return dict(sorted(result.items()))


def audit_pair(m: int, u: int, t: int) -> dict:
    n, j = m * u, t * u
    factorization = binomial_three_factorization(n)
    valuations: dict[str, dict[str, int]] = {}
    gcd_value = 1
    for p, exponent in factorization.items():
        by_carries = kummer_valuation(n, j, p)
        by_legendre = legendre_binomial_valuation(n, j, p)
        assert by_carries == by_legendre, (n, j, p, by_carries, by_legendre)
        valuations[str(p)] = {
            "binom_n_3": exponent,
            "binom_n_j_kummer": by_carries,
            "binom_n_j_legendre": by_legendre,
        }
        gcd_value *= p ** min(exponent, by_legendre)
    tests = quotient_tests(m, u, t)
    quotient_passed = all(test["passed"] for test in tests)
    faithful = 3 < j <= n // 2 and all(
        data["binom_n_j_kummer"] == 0
        for p, data in valuations.items()
        if int(p) >= 3
    )
    return {
        "M": m,
        "u": u,
        "t": t,
        "n": n,
        "j": j,
        "binom_n_3": n * (n - 1) * (n - 2) // 6,
        "binom_n_3_factorization": {str(p): e for p, e in factorization.items()},
        "valuations": valuations,
        "quotient_tests": tests,
        "quotient_tests_passed": quotient_passed,
        "gcd_from_independent_legendre_valuations": gcd_value,
        "faithful_counterexample": faithful,
    }


def algebraic_allocation_assertions() -> dict[str, int]:
    """Exhaustively check the five modular equivalences on small units."""
    checks = 0
    labels_seen: set[str] = set()
    for q in (5, 7, 9, 11, 13, 25, 27, 49):
        for m in range(1, q):
            if gcd(m, q) != 1:
                continue
            inv_m = pow(m, -1, q)
            for t in range(q):
                for offset, allowed in ((1, (0, 1)), (2, (0, 1, 2))):
                    u = offset * inv_m % q
                    j_residue = t * u % q
                    if offset == 1:
                        equivalents = {0: t % q == 0, 1: (m - t) % q == 0}
                    else:
                        equivalents = {
                            0: t % q == 0,
                            1: (m - 2 * t) % q == 0,
                            2: (m - t) % q == 0,
                        }
                    for residue in allowed:
                        assert (j_residue == residue) == equivalents[residue]
                        checks += 1
                        if equivalents[residue]:
                            labels_seen.add(f"n-{offset}:j={residue}")
    expected = {
        "n-1:j=0",
        "n-1:j=1",
        "n-2:j=0",
        "n-2:j=1",
        "n-2:j=2",
    }
    assert labels_seen == expected
    return {"modular_equivalences": checks, "residue_labels_exercised": len(labels_seen)}


def run_controls() -> dict:
    allocation = algebraic_allocation_assertions()
    reconstruction_cases = 0
    for a in range(2, 10):
        for epsilon in (0, 1):
            m = (1 << a) * (3 if epsilon else 1)
            for u in range(1, maximum_u(m) + 1, 2):
                if gcd(m, u) != 1 or valuation(u, 3) == 1:
                    continue
                reconstructed = set(reconstructed_t_values(m, u))
                brute_first = {
                    t
                    for t in range(1, (m - 1) // 2 + 1)
                    if t * (m - t) % retained_core(m * u - 1) == 0
                }
                assert reconstructed == brute_first
                assert {t for t in reconstructed if low_block_holds(m, u, t)} == {
                    t for t in brute_first if low_block_holds(m, u, t)
                }
                reconstruction_cases += 1

    # Deliberately broken predicate: accepting only the n-1 low block labels
    # misclassifies this tuple.  The exact second low block rejects it.
    m, u, t = 16, 1, 5
    x = t * (m - t)
    broken_accepts = x % retained_core(m * u - 1) == 0
    exact_accepts = low_block_holds(m, u, t)
    assert broken_accepts and not exact_accepts

    known = audit_pair(10, 1, 5)
    assert known["gcd_from_independent_legendre_valuations"] == 12
    assert gcd(comb(10, 3), comb(10, 5)) == 12
    high_carry = audit_pair(57, 1, 22)
    assert low_block_holds(57, 1, 22)
    assert high_carry["quotient_tests_passed"]
    assert not high_carry["faithful_counterexample"]
    assert high_carry["valuations"]["5"]["binom_n_j_kummer"] == 1
    assert high_carry["valuations"]["7"]["binom_n_j_kummer"] == 1
    factor_samples = (1, 2, 3, 4, 97, 8051, 2**32 - 5, 9999999967)
    for sample in factor_samples:
        factors = factor_dict(sample)
        product = 1
        for p, exponent in factors.items():
            assert is_prime(p)
            product *= p**exponent
        assert product == sample

    return {
        **allocation,
        "reconstruction_cases": reconstruction_cases,
        "negative_control": {
            "predicate": "drop the R(Mu-2) low-block condition",
            "tuple": {"M": m, "u": u, "t": t},
            "broken_accepts": broken_accepts,
            "exact_rejects": not exact_accepts,
        },
        "known_gcd_control": {"n": 10, "j": 5, "gcd": 12},
        "higher_carry_control": {
            "tuple": {"M": 57, "u": 1, "t": 22, "n": 57, "j": 22},
            "all_five_quotient_labels_pass": True,
            "positive_kummer_valuations": {"5": 1, "7": 1},
            "excluded_reason": "M is not of the admissible smooth form",
        },
        "factorization_samples": len(factor_samples),
    }


def admissible_u(m: int, u: int) -> bool:
    return (
        u % 2 == 1
        and gcd(m, u) == 1
        and valuation(u, 3) != 1
        and bound_57_holds(m, u)
    )


def validate_range(amax: int) -> None:
    largest_m = 3 * (1 << amax)
    largest_n = largest_m * maximum_u(largest_m)
    if largest_n >= 1 << 64:
        raise ValueError(
            f"--amax={amax} reaches n={largest_n}, outside deterministic n < 2^64"
        )


def search(amax: int, diagnostic_limit: int) -> dict:
    validate_range(amax)
    started = perf_counter()
    counts = {
        "smooth_M_rows": 0,
        "odd_u_in_bound": 0,
        "admissible_u": 0,
        "r1_prime_power_allocations": 0,
        "reconstructed_t": 0,
        "reconstructed_with_j_ge_4": 0,
        "second_low_block_rejections": 0,
        "low_block_solutions": 0,
        "full_binomial_audits": 0,
        "faithful_counterexamples": 0,
    }
    ranges: list[dict[str, int]] = []
    diagnostics: list[dict] = []
    counterexamples: list[dict] = []
    largest_n_examined = 0
    largest_m = 0
    for a in range(2, amax + 1):
        for epsilon in (0, 1):
            m = (1 << a) * (3 if epsilon else 1)
            umax = maximum_u(m)
            row_admissible = 0
            row_reconstructed = 0
            row_low = 0
            counts["smooth_M_rows"] += 1
            counts["odd_u_in_bound"] += (umax + 1) // 2
            for u in range(1, umax + 1, 2):
                if not admissible_u(m, u):
                    continue
                row_admissible += 1
                counts["admissible_u"] += 1
                n = m * u
                largest_n_examined = max(largest_n_examined, n)
                powers = prime_powers(retained_core(n - 1))
                counts["r1_prime_power_allocations"] += 1 << len(powers)
                reconstructed = reconstructed_t_values(m, u)
                counts["reconstructed_t"] += len(reconstructed)
                row_reconstructed += len(reconstructed)
                for t in reconstructed:
                    if t * u < 4:
                        continue
                    counts["reconstructed_with_j_ge_4"] += 1
                    audit = audit_pair(m, u, t)
                    counts["full_binomial_audits"] += 1
                    if not low_block_holds(m, u, t):
                        counts["second_low_block_rejections"] += 1
                        continue
                    row_low += 1
                    counts["low_block_solutions"] += 1
                    assert audit["quotient_tests_passed"], audit
                    if audit["faithful_counterexample"]:
                        counts["faithful_counterexamples"] += 1
                        counterexamples.append(audit)
                    elif len(diagnostics) < diagnostic_limit:
                        diagnostics.append(audit)
            largest_m = max(largest_m, m)
            ranges.append(
                {
                    "a": a,
                    "epsilon": epsilon,
                    "M": m,
                    "u_min": 1,
                    "u_max_from_exact_57": umax,
                    "admissible_u": row_admissible,
                    "reconstructed_t": row_reconstructed,
                    "low_block_solutions": row_low,
                }
            )
            print(
                f"a={a} epsilon={epsilon} M={m} u<={umax} "
                f"admissible={row_admissible} reconstructed={row_reconstructed} low={row_low}",
                file=sys.stderr,
                flush=True,
            )
    elapsed = perf_counter() - started
    script_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return {
        "status": "PASS",
        "whole_solution": False,
        "faithful_counterexample_found": bool(counterexamples),
        "method": "exact (57) bound; R(Mu-1) prime-power CRT allocation; exact (56); five quotient labels; complete C(n,3) factorization; Kummer plus Legendre",
        "finite_range": {
            "a_min": 2,
            "a_max": amax,
            "epsilon": [0, 1],
            "largest_M": largest_m,
            "largest_n_examined": largest_n_examined,
            "per_row": ranges,
        },
        "counts": counts,
        "counterexample_candidates": counterexamples,
        "higher_carry_diagnostics": diagnostics,
        "strongest_invariant": {
            "name": "five-factor prime-power allocation",
            "statement": "each retained q|Mu-1 divides exactly one of t,M-t; each retained q|Mu-2 divides exactly one of t,M-2t,M-t; the five labelled classes are pairwise prime-power allocations whose product is R(Mu-1)R(Mu-2)",
            "novel_stronger_than_58": False,
            "note": "This is the exact allocation form behind (56), not a new uniform inequality beyond (58).",
        },
        "first_still_unproved": "For unbounded a, no admissible (M,u,t) satisfying the full i=3 conditions exists; even the universal no-solution claim for (58) remains unproved.",
        "limitations": "finite self-audit only; no Lean proof or independent review; a>a_max is unsearched; absence of a bounded candidate is not a proof",
        "elapsed_seconds": elapsed,
        "script_sha256": script_sha,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--amax", type=int, default=24)
    parser.add_argument("--diagnostic-limit", type=int, default=5)
    parser.add_argument("--self-test-only", action="store_true")
    args = parser.parse_args()
    if args.amax < 2:
        parser.error("--amax must be at least 2")
    if args.diagnostic_limit < 0:
        parser.error("--diagnostic-limit must be nonnegative")
    controls = run_controls()
    result = {
        "controls": controls,
        "search": None if args.self_test_only else search(args.amax, args.diagnostic_limit),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
