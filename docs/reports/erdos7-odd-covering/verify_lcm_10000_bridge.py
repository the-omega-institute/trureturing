#!/usr/bin/env python3
"""Check the finite lcm bridge from the external 10000 theorem.

The arithmetic is standard-library exact integer arithmetic.  The two
capacity rows are direct instances of the kernel-checked `capacity_exclusion`
theorem in Mian--Siddique's Centurion source; this program checks their
decidable inequalities and enumerates the odd abundant candidates through
17325.  It does not duplicate that Lean theorem.
"""
from pathlib import Path
import json
import math
from fractions import Fraction


EXPECTED = (10395, 11025, 11655, 12285, 12705, 12915, 13545,
            14175, 14805, 15015, 15435, 16065, 16695, 17325)
P1_PRIMES = {3, 5, 7, 11}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(n):
    out = []
    root = math.isqrt(n)
    for d in range(1, root + 1):
        if n % d:
            continue
        out.append(d)
        if d * d != n:
            out.append(n // d)
    return sorted(out)


def factorization(n):
    factors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def capacity_row(n, tail):
    ds = divisors(n)
    lhs = sum(n // d for d in ds if d > 1 and d not in tail)
    product = math.prod(tail)
    rhs = (n // product) * math.prod(d - 1 for d in tail)
    require(all(n % d == 0 and d > 1 for d in tail), "capacity divisor")
    require(all(math.gcd(d, e) == 1 for i, d in enumerate(tail)
                for e in tail[i + 1:]), "capacity coprimality")
    require(lhs < rhs, "capacity inequality")
    return {"N": n, "T": list(tail), "left": lhs, "right": rhs,
            "gap": rhs - lhs}


def p1_supported(n):
    return all(p in P1_PRIMES or p >= 67 for p in factorization(n))


def sparse_supported(n):
    factors = factorization(n)
    tail = [p for p in factors if p >= 37]
    return all(p in {3, 5, 7} or p >= 37 for p in factors) and len(tail) <= 1


def compute():
    candidates = tuple(n for n in range(10001, 17326, 2)
                      if 2 * n <= sum(divisors(n)))
    require(candidates == EXPECTED, "odd abundant candidate list")
    rows = [capacity_row(15015, (3, 5, 7, 11, 13)),
            capacity_row(16065, (3, 5, 7, 17))]
    one_tail_loss = Fraction(1889, 48) * Fraction(1, 12) ** 2
    require(one_tail_loss == Fraction(1889, 6912) < 1,
            "single tail 13 load")
    p1 = [n for n in candidates if p1_supported(n)]
    sparse = [n for n in candidates if sparse_supported(n)]
    covered = set(p1) | set(sparse) | {row["N"] for row in rows} | {12285}
    require(covered == set(candidates), "finite bridge classification")
    return {
        "interval": [10001, 17325],
        "odd_abundant_candidates": list(candidates),
        "p1_supported_candidates": p1,
        "degree_two_single_tail_candidates": sparse,
        "external_capacity_rows": rows,
        "single_tail_12285_gamma_bound": "1889/48",
        "single_tail_12285_W_bound": "1/12",
        "single_tail_12285_loss": str(one_tail_loss),
        "only_unresolved_candidate": None,
        "factorizations": {
            str(n): {str(p): exponent for p, exponent in factorization(n).items()}
            for n in candidates},
        "conclusion": "hypothetical odd-cover lcm is 12285 or exceeds 17325",
    }


def main():
    path = Path(__file__).with_name("lcm_10000_bridge_certificate.json")
    data = compute()
    require(json.loads(path.read_text(encoding="utf-8")) == data,
            "fixed lcm bridge certificate")
    print(json.dumps({"result": "PASS", "candidates": len(data["odd_abundant_candidates"]),
                      "only_unresolved_candidate": data["only_unresolved_candidate"],
                      "finite_lcm_boundary": "lcm > 17325",
                      "capacity_gaps": [row["gap"] for row in data["external_capacity_rows"]]},
                     sort_keys=True))


if __name__ == "__main__":
    main()
