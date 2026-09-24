#!/usr/bin/env python3
"""Exact audits for the Erdős 699 i=3 research note.

NOT a proof of Erdős 699 and NOT an exhaustive counterexample search.
Uniform proofs: docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md.
Usage: python erdos699-cubic-obstruction-check.py [--nmax 200] [--symbolic]
Only --symbolic requires SymPy; the other tests use the standard library.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import comb, gcd
from typing import Sequence


def valuation(value: int, prime: int) -> int:
    if value <= 0 or prime < 2:
        raise ValueError("valuation requires a positive integer and prime >= 2")
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def binomial_valuation(n: int, j: int, prime: int) -> int:
    if not (0 <= j <= n) or prime < 2:
        raise ValueError("invalid binomial-valuation arguments")
    result, power = 0, prime
    while power <= n:
        result += n // power - j // power - (n - j) // power
        power *= prime
    return result


def discriminant(coefficients: Sequence[int | Q]) -> int | Q:
    if len(coefficients) != 4:
        raise ValueError("four descending cubic coefficients required")
    a, b, c, d = coefficients
    return b*b*c*c - 4*a*c**3 - 4*b**3*d - 27*a*a*d*d + 18*a*b*c*d


def evaluate(coefficients: Sequence[int | Q], x: Q) -> Q:
    result = Q(0)
    for coefficient in coefficients:
        result = result*x + coefficient
    return result


def orbit_polynomial(n: int, j: int) -> tuple[int, int, int, int]:
    if not (3 < j <= n // 2):
        raise ValueError("requires 3 < j <= n/2")
    return comb(n, 3), -j*comb(n-1, 2), (n-2)*comb(j, 2), -comb(j, 3)


def power_of_two_exponent(value: int) -> int | None:
    if value <= 0 or value & (value - 1):
        return None
    return value.bit_length() - 1


def smooth_parameters(n: int, j: int) -> tuple[int, int, int, int, int] | None:
    """Return (A,B,d,c,a), or None if A is not c*2^a, c=1 or 3, a>=2."""
    d = gcd(n, j)
    A, B = n // d, j // d
    c = 3 if A % 3 == 0 else 1
    a = power_of_two_exponent(A // c)
    if a is None or a < 2:
        return None
    return A, B, d, c, a


def canonical_polynomial(A: int, B: int, d: int, c: int) -> tuple[Q, Q, Q, Q]:
    n = A*d
    D = (n-1)*(n-2)
    return (Q(A, c), Q(-3*B, c),
            Q(3*B*(B*d-1), c*(n-1)),
            Q(-B*(B*d-1)*(B*d-2), c*D))


def cube_root_floor(value: int) -> int:
    if value < 0:
        raise ValueError("nonnegative value required")
    lo, hi = 0, 1 << ((value.bit_length() + 2)//3)
    while lo < hi:
        mid = (lo + hi + 1)//2
        if mid**3 <= value:
            lo = mid
        else:
            hi = mid - 1
    return lo


def max_d_for_exponent(a: int, epsilon: int) -> int:
    """Exact maximum d allowed by 784*(3^eps*2^a*d-1)^3 < 27*2^(4a)."""
    if a < 2 or epsilon not in (0, 1):
        raise ValueError("requires a>=2 and epsilon in {0,1}")
    rhs = 27*(1 << (4*a))
    largest_n = 1 + cube_root_floor((rhs - 1)//784)
    return largest_n // ((3**epsilon)*(1 << a))


def audit(nmax: int) -> dict:
    pair_count = smooth_count = 0
    for n in range(8, nmax+1):
        for j in range(4, n//2+1):
            pair_count += 1
            P = orbit_polynomial(n, j)
            for h in range(4):
                coefficient = sum(
                    comb(n-j, r)*comb(j, 3-r)*comb(3-r, h-r)*(-1)**(3-h)
                    for r in range(h+1)
                )
                assert coefficient == P[3-h]
            Cnj, Cn3 = comb(n, j), comb(n, 3)
            for h in range(4):
                coefficient = comb(n-h, 3-h)*comb(j, h)
                assert Cnj*coefficient == Cn3*comb(3, h)*comb(n-h, j-h)
            common = gcd(Cn3, Cnj)
            divisor = Cn3 // common
            assert all(coefficient % divisor == 0 for coefficient in P)
            H = tuple(coefficient // divisor for coefficient in P)
            exact_disc = Q(j*j*(j-1)*(n-j)**2*(n-j-1)*(n-2)**2*(n-1), 12)
            assert discriminant(P) == exact_disc
            assert discriminant(H) > 0
            assert 16*(n-1)**3 <= 27*common**4
            parameters = smooth_parameters(n, j)
            if parameters is None:
                continue
            smooth_count += 1
            A, B, d, c, a = parameters
            t = valuation(d, 2)
            assert all(coefficient % (1 << t) == 0 for coefficient in P)
            assert valuation(Cn3, 2) == a+t
            assert valuation(comb(j, 3), 2) >= t
            F = canonical_polynomial(A, B, d, c)
            assert F == tuple(Q((1 << a)*coefficient, Cn3) for coefficient in P)
            expected = Q(108*B*B*(A-B)**2*(B*d-1)*((A-B)*d-1),
                         c**4*(A*d-2)**2*(A*d-1)**3)
            assert discriminant(F) == expected
            Z = Q(A, 2)-B
            D = (A*d-1)*(A*d-2)
            kappa = Q(Z*(4*d*d*Z*Z-3*A*d+2), D)
            assert 4*c*evaluate(F, Q(1, 2)) == kappa
            assert 4*Z**3-A*A*kappa == Q(Z*(3*A*d-2)*(A*A-4*Z*Z), D)
    negative_F = canonical_polynomial(16, 5, 1, 1)
    assert negative_F == (Q(16), Q(-15), Q(4), Q(-2, 7))
    assert gcd(comb(16, 3), comb(16, 5)) == 112
    relaxed = (16, -23, 9, -1)
    signs = [evaluate(relaxed, q) for q in (Q(0), Q(1,4), Q(1,2), Q(1))]
    assert signs[0] < 0 < signs[1] and signs[2] < 0 < signs[3]
    assert discriminant(relaxed) == 229
    assert all(evaluate(relaxed, Q(1, denom)) != 0 for denom in (2,4,8,16))
    controls = []
    for n, j, primes, expected_gcd in (
        (1872, 35, (5,11,17), 1167504),
        (6512, 126, (5,7,31), 42399632),
    ):
        vals = [binomial_valuation(n, j, p) for p in primes]
        assert vals == [0,0,0]
        actual_gcd = gcd(comb(n,3), comb(n,j))
        assert actual_gcd == expected_gcd
        controls.append({"n":n, "j":j, "tested_primes":primes,
                         "valuations":vals, "gcd":actual_gcd})
    A, B, d, k = 76672, 26775, 1, 5255
    assert B*(A-B)*(A-2*B) == k*(A*d-1)*(A*d-2)
    assert [binomial_valuation(A,B,p) for p in (3,5,7,11,17,41)] == [3,2,1,1,1,2]
    assert binomial_valuation(A,B,599) == binomial_valuation(A,3,599) == 1
    cutoffs = []
    for a in (5,6,10,20,36,37,60,100):
        for eps in (0,1):
            bound = max_d_for_exponent(a,eps)
            A = (3**eps)*(1 << a)
            rhs = 27*(1 << (4*a))
            if bound:
                assert 784*(A*bound-1)**3 < rhs
            assert 784*(A*(bound+1)-1)**3 >= rhs
            cutoffs.append({"a":a, "epsilon":eps, "d_max":bound})
    return {"status":"all exact checks passed", "nmax":nmax,
            "nonvacuous_admissible_pairs":pair_count,
            "smooth_denominator_pairs":smooth_count,
            "controls":controls, "exact_d_cutoffs":cutoffs,
            "whole_solution":False,
            "limitations":"Identity audit, not a proof of the conjecture or a replay of the issue's large searches."}


def symbolic_audit() -> dict:
    try:
        import sympy as s
    except ImportError as exc:
        raise SystemExit("--symbolic requires SymPy; omit it for standard-library checks") from exc
    A,B,d,c,x,Z = s.symbols("A B d c x Z")
    D = (A*d-1)*(A*d-2)
    F = A/c*x**3-3*B/c*x**2+3*B*(B*d-1)/(c*(A*d-1))*x-B*(B*d-1)*(B*d-2)/(c*D)
    expected = 108*B**2*(A-B)**2*(B*d-1)*((A-B)*d-1)/(c**4*(A*d-2)**2*(A*d-1)**3)
    assert s.factor(s.discriminant(F,x)-expected) == 0
    midpoint = Z*(4*d**2*Z**2-3*A*d+2)/(4*c*D)
    assert s.factor(F.subs(x,s.Rational(1,2)).subs(B,A/2-Z)-midpoint) == 0
    L,M,N,R = s.symbols("L M N R")
    f = L*x**3+M*x**2+N*x+R
    omega, theta = L*x, L*x**2+M*x
    for relation in (omega**2+M*omega-L*theta,
                     omega*theta+N*omega+L*R,
                     theta**2+R*omega+N*theta+M*R):
        assert s.rem(relation,f,x) == 0
    return {"symbolic_discriminant":True,"symbolic_midpoint":True,
            "symbolic_order_multiplication":True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nmax",type=int,default=200)
    parser.add_argument("--symbolic",action="store_true")
    args = parser.parse_args()
    if args.nmax < 8:
        parser.error("--nmax must be at least 8")
    result = audit(args.nmax)
    if args.symbolic:
        result.update(symbolic_audit())
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
