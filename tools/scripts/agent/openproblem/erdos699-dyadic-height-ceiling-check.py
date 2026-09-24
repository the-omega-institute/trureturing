#!/usr/bin/env python3
"""Exact self-audit for sections 29-32 of the Erdős 699 theory volume.

Checks actual rational binomial identities, synthetic dyadic controls,
constant exponents, and the six-point proof data. --symbolic requires SymPy.
This does not certify the external height theorem, a whole conjecture
solution, or an independent review. The all-degree bound has a written
proof; finite symbolic degrees are regression tests, not its justification.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import gcd
from typing import Sequence


def discriminant(v: Sequence[Q]) -> Q:
    if len(v) != 4:
        raise ValueError("four descending cubic coefficients required")
    a, b, c, d = v
    return b*b*c*c - 4*a*c**3 - 4*b**3*d - 27*a*a*d*d + 18*a*b*c*d


def is_power_two(value: int) -> bool:
    return value > 0 and value & (value - 1) == 0


def exact_audit(nmax: int, amax: int) -> dict:
    pairs = smooth = positive_midpoint = 0
    for n in range(8, nmax + 1):
        for j in range(4, n // 2 + 1):
            pairs += 1
            v = (Q(1), Q(-3*j, n), Q(3*j*(j-1), n*(n-1)),
                 Q(-j*(j-1)*(j-2), n*(n-1)*(n-2)))
            # This identity is non-vacuously checked without (H).
            ell0 = Q(3*j*(n-j), n*n*(n-1))
            k0 = Q(j*(n-j)*(n-2*j), n**3*(n-1)*(n-2))
            assert discriminant(v) == 4*ell0**3 - 108*k0**2
            d = gcd(n, j)
            A, B = n // d, j // d
            c = 3 if A % 3 == 0 else 1
            h = A // c
            if not is_power_two(h) or h < 4:
                continue
            smooth += 1
            a = h.bit_length() - 1
            F = tuple(h*z for z in v)
            ell = Q(3*B*(A-B), n-1)
            k = Q(B*(A-B)*(A-2*B), (n-1)*(n-2))
            Delta = discriminant(F)
            assert ell**3 - 27*k*k == c**6 * (1 << (2*a-2)) * Delta
            q, r = divmod(a - 1, 3)
            x, y = ell / (1 << (2*q)), k / (1 << (3*q))
            assert x**3 - 27*y*y == c**6 * 4**r * Delta
            Z = Q(A, 2) - B
            kappa = Z - 2*k*d*d
            if kappa > 0:
                positive_midpoint += 1
                assert 8*c**8*kappa*Delta**2 < 729*k**3
            # No assertion that F, ell, k, or Delta are integral here.

    synthetic = 0
    branches: set[tuple[int, int]] = set()
    # Algebraic controls only: k is a cube, so these are NOT counterexamples.
    for a in range(2, amax + 1):
        q, r = divmod(a - 1, 3)
        for c in (1, 3):
            scale = c**6 * (1 << (2*a-2))
            for s in (1, 3, 5):
                ell, k = 3*s*s + scale, s**3
                raw = ell**3 - 27*k*k
                assert raw % scale == 0
                Delta = raw // scale
                assert Delta >= 49 and ell % 2 == k % 2 == 1
                x, y = Q(ell, 1 << (2*q)), Q(k, 1 << (3*q))
                assert x.denominator == 1 << (2*q)
                assert y.denominator == 1 << (3*q)
                assert x**3 == 27*y*y + c**6*4**r*Delta
                # Height in Q is log(max(abs(numerator),denominator)).
                assert max(abs(y.numerator), y.denominator) >= 1 << (3*q)
                branches.add((c, r))
                synthetic += 1
    assert len(branches) == 6
    # Omitting oddness invalidates the claimed exact denominator.
    assert Q(2, 1 << 9).denominator != 1 << 9
    # Constant zero would give a repeated root, outside the height theorem.
    assert -108*0 == 0 and all(-108*D != 0 for D in (1, 49, 100))

    assert 14*3**3*2**3*2 == 6048
    assert 3*3**2*2**2 == 108
    assert 8*3**2*2**3 == 576
    assert 1 + 3*6048 + 108 + 4*576 == 20557
    assert 6*576 == 3456
    assert 20557 - 3*288 == 19693
    assert 6048 + 6*288 == 7776
    assert 3456 - 9*288 == 864
    assert 3*288 == 864
    assert 576*3 == 1728
    assert 19693 > 0 and 7776 + 864 == 8640
    C, Gamma = {}, {}
    for c in (1, 3):
        C[c] = 2**20557 * 3**6048 * c**3456
        Gamma[c] = 2**19693 * 3**7776 * c**864
        assert C[c] == 2 * 24**6048 * 2**108 * (16*c**6)**576
        assert Q(C[c]) * Q(729, 8*c**9)**288 == Gamma[c]
    assert C[3] == 2**20557 * 3**9504
    # Finite sample checks of the exact scalar manipulation, not of heights.
    for Delta in (49, 81, 229, 1000):
        for c in (1, 3):
            threshold = 3 + C[c]*Delta**576
            assert threshold > 3 and (threshold-3) == C[c]*Delta**576

    vertices = ((0, 0), (0, 2), (2, 2))
    midpoints = ((0, 1), (1, 2), (1, 1))
    sides = ((1, 0, 0), (-1, 1, 0), (0, 1, -2))
    inner = ((1, 0, -1), (-1, 1, -1), (0, 1, -1))
    on = lambda line, pt: line[0]*pt[0] + line[1]*pt[1] + line[2] == 0
    for line in sides:
        assert sum(on(line, pt) for pt in vertices) == 2
        assert sum(on(line, pt) for pt in midpoints) == 1
    for line in inner:
        assert sum(on(line, pt) for pt in vertices) == 0
        assert sum(on(line, pt) for pt in midpoints) == 2
    assert [sum(on(line, p) for line in sides) for p in vertices] == [2]*3
    assert [sum(on(line, p) for line in sides) for p in midpoints] == [1]*3
    assert [sum(on(line, p) for line in inner) for p in midpoints] == [2]*3
    # Weighted inequalities: twice the side bound + three times inner bound.
    assert 2*9 + 3*6 == 36
    assert 2*5 + 3*2 == 16
    assert 2*2 + 3*4 == 16
    assert 2*3 + 3*3 == 15 <= 16
    sharp_orders = [3*(D//4) + (0, 0, 1, 2)[D % 4] for D in range(1, 17)]
    assert sharp_orders == [3*D//4 for D in range(1, 17)]
    return {"status": "passed", "actual_rational_pairs": pairs,
            "smooth_denominator_pairs": smooth,
            "positive_midpoint_pairs": positive_midpoint,
            "synthetic_dyadic_controls": synthetic,
            "covered_c_r_branches": sorted(branches),
            "six_line_incidence_checks": 6,
            "sharp_orders_D1_to_16": sharp_orders,
            "constants_checked": True,
            "external_height_theorem_reproved": False,
            "whole_solution": False}


def symbolic_audit() -> dict:
    try:
        import sympy as s
    except ImportError as exc:
        raise SystemExit("--symbolic requires SymPy") from exc
    U, W, T, x = s.symbols("U W T x")
    Phi = (W*(W-T)*(W-2*T), -3*U*(W-T)*(W-2*T),
           3*U*(U-T)*(W-2*T), -U*(U-T)*(U-2*T))
    pts = ((0,0), (0,2), (2,2), (0,1), (1,2), (1,1))
    assert all(z.subs({U:u, W:w, T:1}) == 0 for u,w in pts for z in Phi)
    f = sum(Phi[r]*x**(3-r) for r in range(4))
    expected = 108*T**3*U**2*(W-U)**2*(W-2*T)**2*(U-T)*(W-U-T)*(W-T)
    assert s.expand(s.discriminant(f, x)-expected) == 0
    residual = s.expand((expected/(108*T**3)).subs(T, 1))
    for u,w in pts:
        shifted = s.Poly(residual.subs({U:U+u, W:W+w}, simultaneous=True), U,W)
        assert min(sum(mon) for mon,_ in shifted.terms()) == 4
    a,b,c,d = Phi
    low2, low3 = s.factor(b*b-3*a*c), s.factor(2*b**3-9*a*b*c+27*a*a*d)
    order = lambda z: min(mon[2] for mon,_ in s.Poly(z,U,W,T).terms())
    assert order(a) == 0 and order(low2) == 1 and order(low3) == 2
    assert order(s.expand(expected)) == 3
    for D in range(1, 9):
        q,r = divmod(D,4)
        polynomial = expected**q * (1,a,low2,low3)[r]
        assert order(s.expand(polynomial)) == 3*D//4
    # An identically zero cubic relation cannot serve as a positive integer.
    relation = 6*a*c*c + 9*a*c*d - 9*a*b*d - b*b*c - 6*b*b*d + b*c*c
    assert s.expand(relation) == 0
    ell,k,A,c0,z,B = s.symbols("ell k A c0 z B")
    F = ((A*z-B)**3 - ell*(A*z-B)-2*k)/(c0*A*A)
    assert s.factor(s.discriminant(F,z) - (4*ell**3-108*k*k)/(c0**4*A*A)) == 0
    # The six-point proof is all-degree: algebra of its weighted inequalities.
    D,aa,bb,e = s.symbols("D aa bb e")
    assert s.expand(2*(9*D-5*aa-2*bb)+3*(6*D-2*aa-4*bb)) == 36*D-16*aa-16*bb
    return {"symbolic_discriminant_scaling": True,
            "symbolic_six_base_points": 6,
            "symbolic_sharp_residual_multiplicity": 4,
            "symbolic_sharp_orders_D1_to_8": True,
            "zero_relation_negative_control": True,
            "all_degree_proof_by_sampling": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nmax", type=int, default=160)
    parser.add_argument("--amax", type=int, default=80)
    parser.add_argument("--symbolic", action="store_true")
    args = parser.parse_args()
    if args.nmax < 8 or args.amax < 2:
        parser.error("requires nmax>=8 and amax>=2")
    result = exact_audit(args.nmax, args.amax)
    if args.symbolic:
        result.update(symbolic_audit())
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
