#!/usr/bin/env python3
"""Check a finite odd-lcm exclusion using pure-coordinate CRT bounds.

Python 3 standard library only; all arithmetic and comparisons are exact.
The retained filename also locates the earlier external-10000 bridge. The
current calculation starts at 1 and does not depend on that external theorem.
This checks a certificate of an ordinary proof, not a Lean proof.
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
from array import array
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import math


FIRST_UNRESOLVED = 11486475
BOUND = FIRST_UNRESOLVED - 1


def require(condition, message):
    if not condition:
        raise ValueError(message)


def factorization(n):
    factors = {}
    p = 3
    require(n > 0 and n % 2 == 1, "positive odd input")
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p += 2
    if n > 1:
        factors[n] = 1
    return factors


def sigma_sieve(limit):
    """At index n//2, sum all positive divisors of the odd integer n."""
    sums = array('Q', [1]) * ((limit + 1) // 2)
    for d in range(3, limit + 1, 2):
        for index in range(d // 2, len(sums), d):
            sums[index] += d
    return sums


def coordinate_data(factors):
    # P=p^h, U=sum_{e=1}^h p^(h-e), L=P-U.
    return [(p, p ** h, (p ** h - 1) // (p - 1),
             p ** h - (p ** h - 1) // (p - 1))
            for p, h in factors.items()]


def mixed_budget(coords):
    period = math.prod(row[1] for row in coords)
    surviving = math.prod(row[3] for row in coords)
    singleton = sum(u * (surviving // lower) for _, _, u, lower in coords)
    numerator = period - surviving - singleton
    require(numerator >= 0, "nonnegative mixed budget")
    return numerator, surviving


def best_two_block(coords):
    """Maximize the independent-block rebate, requiring both budgets <1."""
    best = (0, None)
    full = (1 << len(coords)) - 1
    for mask in range(1, full, 2):  # First coordinate in A; no duplicate partitions.
        a = [row for i, row in enumerate(coords) if mask & (1 << i)]
        b = [row for i, row in enumerate(coords) if not mask & (1 << i)]
        if min(len(a), len(b)) < 2:
            continue
        na, da = mixed_budget(a)
        nb, db = mixed_budget(b)
        if na >= da or nb >= db:
            continue
        rebate = na * nb  # da*db is the complete product denominator.
        if rebate > best[0]:
            best = (rebate, {
                "A": [row[0] for row in a], "B": [row[0] for row in b],
                "A_mixed_bound": str(Fraction(na, da)),
                "B_mixed_bound": str(Fraction(nb, db))})
    return best


def row(n, factors, use_blocks=False):
    coords = coordinate_data(factors)
    numerator, denominator = mixed_budget(coords)
    rebate, partition = best_two_block(coords) if use_blocks else (0, None)
    result = {
        "N": n,
        "factorization": {str(p): h for p, h in factors.items()},
        "pure_survivor_count_lower": denominator,
        "mixed_bound": str(Fraction(numerator, denominator)),
        "uncovered_count_lower": denominator - numerator + rebate}
    if use_blocks:
        result.update({"partition": partition,
                       "two_block_bound": str(Fraction(numerator - rebate, denominator))})
    return result


def compute():
    sigmas = sigma_sieve(FIRST_UNRESOLVED)
    count = perfect = 0
    digest = sha256()
    exceptions = []
    max_n = 1
    max_num, max_den = 0, 1
    for n in range(1, BOUND + 1, 2):
        sigma = sigmas[n // 2]
        if sigma < 2 * n:
            continue
        factors = factorization(n)
        coords = coordinate_data(factors)
        require(math.prod(p + u for _, p, u, _ in coords) == sigma,
                "sieve versus multiplicative divisor sum")
        count += 1
        perfect += sigma == 2 * n
        digest.update(f"{n}:{sigma}\n".encode('ascii'))
        numerator, denominator = mixed_budget(coords)
        if numerator < denominator:
            if numerator * max_den > max_num * denominator:
                max_n, max_num, max_den = n, numerator, denominator
            continue
        result = row(n, factors, use_blocks=True)
        require(result["uncovered_count_lower"] > 0, f"unresolved candidate {n}")
        exceptions.append(result)
    require(count == 23758 and perfect == 0, "abundant and perfect counts")
    require([item["N"] for item in exceptions] == [6891885], "pure-bound exceptions")
    require(sigmas[FIRST_UNRESOLVED // 2] >= 2 * FIRST_UNRESOLVED,
            "next obstruction is abundant")
    next_row = row(FIRST_UNRESOLVED, factorization(FIRST_UNRESOLVED), use_blocks=True)
    require(next_row["uncovered_count_lower"] <= 0, "stopping criterion")
    examples = [row(n, factorization(n)) for n in (315, 945, 45045)]
    require([item["uncovered_count_lower"] for item in examples] == [71, 179, 3915],
            "5040 odd-part and finite extension examples")
    golden_fiber = [5040, 10080, 15120, 20160, 30240, 60480]
    odd_parts = []
    for n in golden_fiber:
        while n % 2 == 0:
            n //= 2
        odd_parts.append(n)
    require(set(odd_parts) == {315, 945}, "odd parts of existing golden fiber")
    even_cover = [(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)]
    require(all(5040 % d == 0 for d, _ in even_cover), "even example divisors")
    require(all(any((x - a) % d == 0 for d, a in even_cover) for x in range(12)),
            "even covering example")
    return {
        "interval": [1, BOUND],
        "odd_abundant_candidates": count,
        "odd_perfect_candidates": perfect,
        "candidate_digest_format": "ASCII decimal N:sigma(N), newline, ascending N",
        "candidate_sha256": digest.hexdigest(),
        "pure_bound_exclusions": count - len(exceptions),
        "largest_successful_pure_bound": {"N": max_n, "bound": str(Fraction(max_num, max_den))},
        "two_block_exclusions": exceptions,
        "first_unresolved_by_these_criteria": next_row,
        "examples": examples,
        "golden_fiber_5040": golden_fiber,
        "golden_fiber_odd_parts": odd_parts,
        "even_cover": [{"modulus": d, "residue": a} for d, a in even_cover],
        "conclusion": f"hypothetical odd-cover lcm exceeds {BOUND}",
        "verification_boundary": "ordinary CRT proof and exact integer enumeration; not Lean formalized"}


def main():
    data = compute()
    path = (Path(__file__).resolve().parent / 'certificates/lcm_10000_bridge_certificate.json')
    require(json.loads(read_artifact_text(path, encoding="utf-8")) == data, "fixed lcm certificate")
    print(json.dumps({"result": "PASS", "candidates": data["odd_abundant_candidates"],
                      "pure_exclusions": data["pure_bound_exclusions"],
                      "two_block_exclusions": len(data["two_block_exclusions"]),
                      "finite_lcm_boundary": f"lcm > {BOUND}"}, sort_keys=True))


if __name__ == "__main__":
    main()
