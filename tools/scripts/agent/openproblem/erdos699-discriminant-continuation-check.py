#!/usr/bin/env python3
"""Exact audits for sections 12-15 of ERDOS_699_BINOMIAL_COMMON_PRIME.md.

This checks identities, rational constants and negative controls. It is not
an exhaustive proof search, a Lean proof or an independent review.
Run: python erdos699-discriminant-continuation-check.py --nmax 100 --symbolic
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import comb, gcd, isqrt


def primes_through(limit: int) -> list[int]:
    if limit < 2:
        return []
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def integer_root(value: int, degree: int) -> int:
    if value < 0 or degree < 1:
        raise ValueError("nonnegative value and positive degree required")
    lo, hi = 0, 1 << ((value.bit_length() + degree - 1) // degree)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** degree <= value:
            lo = mid
        else:
            hi = mid - 1
    return lo


def finite_row_bound(i: int) -> int:
    t = len(primes_through(i - 1))
    if i <= 4 * t:
        raise ValueError("this bound requires i > 4*pi(i-1)")
    quotient = (i * (i + 1)) ** i // (2 * i + 1) ** i
    return integer_root(quotient, i - 4 * t)


def orbit_coefficients(n: int, i: int, j: int) -> list[int]:
    if not (2 <= i < j <= n // 2):
        raise ValueError("requires 2 <= i < j <= n/2")
    return [(-1) ** h * comb(j, h) * comb(n - h, i - h)
            for h in range(i + 1)]


def rational_constants() -> dict:
    # log(2) > 2*(1/3 + (1/3)^3/3 + (1/3)^5/5) > 0.693.
    lower_log2 = 2 * sum((Q(1, 3) ** (2*k + 1)) / (2*k + 1)
                         for k in range(3))
    assert lower_log2 > Q(693, 1000)
    # log(3/2)>2/5 follows from the positive atanh series.
    # 400000 > 2^18*(3/2), so log(400000)>12.8.
    assert 400000 > 2**18 * Q(3, 2)
    assert 18 * lower_log2 + Q(2, 5) > Q(64, 5)
    # log(152)=7*log(2)+log(19/16)>7*log(2)+6/35>5.02.
    assert 7 * lower_log2 + Q(6, 35) > Q(251, 50)
    C = Q(6381, 5000)  # 1.2762, Dusart Theorem 6.9, equation (6.5).
    small_u = 4 / Q(251, 50) * (1 + C / Q(251, 50))
    assert small_u == Q(62962, 63001) < 1
    assert 4 * (1 + C / Q(64, 5)) < Q(22, 5)
    ratio_log_upper = (Q(22, 5) - Q(2, 5)) / (1 - Q(22, 5) / Q(64, 5))
    assert ratio_log_upper == Q(128, 21) < 9 * lower_log2
    assert 25 * Q(64, 5)**2 == 4096
    groups = [(121,127,30), (128,131,31), (132,137,32),
              (138,139,33), (140,149,34), (150,151,35)]
    primes = primes_through(151)
    for left, right, t in groups:
        for i in range(left, right + 1):
            assert sum(p < i for p in primes) == t and i > 4*t
    assert Q(27,32) < Q(485,512)**2
    assert 1024**2 < 3*630**2
    return {"logarithm_constants": "proved with rational lower bounds",
            "small_prime_count_groups": groups,
            "large_i_threshold": 400000, "counterexample_ratio_bound": 512,
            "external_inputs": "Dusart 2010, Proposition 6.8 and Theorem 6.9 (6.5); not reproved by this checker"}


def audit(nmax: int, symbolic: bool) -> dict:
    count = incidence_count = 0
    for n in range(6, nmax + 1):
        row = [comb(n,j) for j in range(n//2 + 1)]
        for j in range(3, n//2 + 1):
            for i in range(2,j):
                count += 1
                g = gcd(row[i], row[j])
                assert g**4 * i**i >= (2*(n-1))**i
                mu = Q(j,n)
                e1 = i*mu
                e2 = Q(i*(i-1)*j*(j-1), 2*n*(n-1))
                variance = e1**2 - 2*e2 - i*mu**2
                assert variance == Q(i*(i-1),n-1)*mu*(1-mu)
                if n <= 32 and i <= 6:
                    P = orbit_coefficients(n,i,j)
                    divisor = row[i] // g
                    for h, coefficient in enumerate(P):
                        incidence_count += 1
                        assert coefficient % divisor == 0
                        assert row[j]*abs(coefficient) == row[i]*comb(i,h)*comb(n-h,j-h)
    bounded = []
    for i in (121,122,128,152,200):
        t = len(primes_through(i-1))
        bound = finite_row_bound(i)
        lhs_factor, rhs = (2*i+1)**i, (i*(i+1))**i
        assert lhs_factor*bound**(i-4*t) <= rhs
        assert lhs_factor*(bound+1)**(i-4*t) > rhs
        bounded.append({"i":i,"pi_i_minus_1":t,"n_bound":str(bound)})
    for a in range(7,81):
        A = 2**a
        B = (A - (-1)**a)//3
        assert (A - (-1)**a) % 3 == 0
        Z = A//2-B
        assert gcd(A,B) == 1 and B % 2 == 1 and 3 < B < A//2
        assert 784*(A-1)**3 < 27*A**4
        assert B**3 > A*A and 4*Z**3 > A*A
        assert abs(A-3*B) == 1
        assert 4*abs(A-3*B)**3 <= 4*A*A-27*A
    result = {"whole_solution":False, "all_general_bound_triples":count,
              "incidence_coefficient_checks":incidence_count,
              "exact_finite_row_examples":bounded,
              "new_band_negative_control_exponents":[7,80],
              **rational_constants()}
    if symbolic:
        import sympy as s
        A,B,d,c,x,u,v = s.symbols("A B d c x u v")
        den = (A*d-1)*(A*d-2)
        F = A/c*x**3-3*B/c*x**2+3*B*(B*d-1)/(c*(A*d-1))*x-B*(B*d-1)*(B*d-2)/(c*den)
        ell = 3*B*(A-B)/(A*d-1)
        k = B*(A-B)*(A-2*B)/den
        E = A*u-B*v
        assert s.factor(c*A*A*F-((A*x-B)**3-ell*(A*x-B)-2*k)) == 0
        assert s.factor(c*A*A*v**3*F.subs(x,u/v)-(E**3-ell*E*v**2-2*k*v**3)) == 0
        disc_checks = 0
        for n in range(6,23):
            for j in range(3,n//2+1):
                for i in range(2,min(j,6)):
                    P = orbit_coefficients(n,i,j)
                    g = gcd(comb(n,i),comb(n,j))
                    divisor = comb(n,i)//g
                    pol = sum((coefficient//divisor)*x**(i-h) for h,coefficient in enumerate(P))
                    disc = int(s.discriminant(pol,x))
                    assert disc > 0
                    assert disc**2 * (2*(n-1))**(i*(i-1)) <= g**(4*i-4)*i**(i*(i-1))
                    disc_checks += 1
        result["symbolic_norm_identities"] = True
        result["exact_general_discriminants"] = disc_checks
    result["status"] = "all exact checks passed"
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nmax",type=int,default=100)
    parser.add_argument("--symbolic",action="store_true")
    args = parser.parse_args()
    if args.nmax < 6:
        parser.error("--nmax must be at least 6")
    print(json.dumps(audit(args.nmax,args.symbolic),indent=2))


if __name__ == "__main__":
    main()
