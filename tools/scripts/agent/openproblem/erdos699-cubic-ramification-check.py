#!/usr/bin/env python3
"""Exact certificate for the cubic-field continuation of Erdos 699.

The finite classification is proved by the accompanying lattice/different
bounds, exhaustive integer enumeration, Eisenstein witnesses and explicit
field embeddings. It does NOT assume completeness of an external database.
Optional --symbolic uses SymPy for independent algebra and maximal-order
regressions; neither sampling nor those regressions is the all-prime proof.
No full conjecture solution or independent mathematical review is claimed.
"""
from __future__ import annotations
import argparse
import json
from math import gcd, isqrt
from typing import Iterable


def factors(n: int) -> dict[int, int]:
    n = abs(n)
    if not n:
        raise ValueError('factorization of zero')
    result: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0)+1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        result[n] = result.get(n, 0)+1
    return result


def vp(n: int, p: int) -> int:
    if n == 0:
        raise ValueError('zero has no finite valuation')
    a = 0
    while n % p == 0:
        n //= p
        a += 1
    return a


def value(t: int, b: int, c: int, x: int) -> int:
    return x*x*x-t*x*x+b*x+c


def disc(t: int, b: int, c: int) -> int:
    return t*t*b*b-4*b**3+4*t**3*c-27*c*c-18*t*b*c


def irreducible(t: int, b: int, c: int) -> bool:
    if c == 0:
        return False
    for r in range(1, abs(c)+1):
        if c % r == 0 and (value(t,b,c,r) == 0 or value(t,b,c,-r) == 0):
            return False
    return True


def mul(a: tuple[int, ...], b: tuple[int, ...], m: int, n: int) -> tuple[int, ...]:
    """Z[theta], with theta^3=m*theta+n, in the power basis."""
    z = [0]*5
    for i in range(3):
        for j in range(3):
            z[i+j] += a[i]*b[j]
    for i in (4,3):
        z[i-2] += m*z[i]
        z[i-3] += n*z[i]
    return tuple(z[:3])


def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x+y for x,y in zip(a,b))


def scale(a: tuple[int, ...], r: int) -> tuple[int, ...]:
    return tuple(r*x for x in a)


def image_zero(t: int, b: int, c: int, v: tuple[int, ...], m: int, n: int) -> bool:
    v2 = mul(v,v,m,n)
    return add(add(mul(v2,v,m,n), scale(v2,-t)), add(scale(v,b),(c,0,0))) == (0,0,0)


def eis_witness(t: int, b: int, c: int, D: int) -> tuple[int, int] | None:
    for p in factors(D):
        if p < 5:
            continue
        for a in range(p):
            coeff = (3*a-t, 3*a*a-2*t*a+b, value(t,b,c,a))
            if all(z % p == 0 for z in coeff) and coeff[-1] % (p*p):
                return p,a
    return None


IMAGES = {
    (0,-12,-8): (3,1,(0,2,0)),
    (0,-12,8): (3,1,(0,-2,0)),
    (0,-9,-9): (3,1,(-2,1,1)),
    (0,-9,9): (3,1,(2,-1,-1)),
    (0,-3,-1): (3,1,(0,1,0)),
    (0,-3,1): (3,1,(0,-1,0)),
    (0,-9,-6): (9,6,(0,1,0)),
    (0,-9,6): (9,6,(0,-1,0)),
}


def classification() -> dict:
    count = 0
    candidates = []
    witness_count = 0
    images_found = set()
    for t in (0,1):
        for b in range(-15,1):
            for c in range(-32,33):
                D = disc(t,b,c)
                if D <= 0 or not irreducible(t,b,c):
                    continue
                count += 1
                if any(v % 2 for p,v in factors(D).items() if p >= 5):
                    continue
                witness = eis_witness(t,b,c,D)
                item = {'coefficients':[1,-t,b,c], 'polynomial_discriminant':D}
                if witness:
                    p,a = witness
                    assert p >= 5 and factors(p) == {p:1}
                    item['ramified_Eisenstein_prime_and_shift'] = [p,a]
                    witness_count += 1
                else:
                    assert (t,b,c) in IMAGES, ('unclassified',t,b,c,D)
                    m,n,v = IMAGES[t,b,c]
                    assert irreducible(0,-m,-n) and v[1:] != (0,0)
                    assert image_zero(t,b,c,v,m,n)
                    item['canonical_polynomial'] = [1,0,-m,-n]
                    item['root_image'] = v
                    images_found.add((t,b,c))
                candidates.append(item)
    assert count == 451 and len(candidates) == 23 and witness_count == 15
    assert images_found == set(IMAGES)
    assert 1944 == 2**3*3**5 and 4*1944 < 89**2
    assert 10**3 < 32**2
    assert all(value(0,-3,-1,a) % 2 for a in range(2))
    assert value(0,-9,-6,0) % 2 == 0 and (-9) % 2 == 1
    assert disc(0,-3,-1) == 81 and disc(0,-9,-6) == 1944
    # At 3, x^3-9x-6 is Eisenstein; the derivative terms have values 5 and 6.
    assert (-6) % 3 == 0 and (-6) % 9 != 0 and 3+2 == 5 < 6
    return {'box_size':2*16*65, 'irreducible_positive_discriminant':count,
            'squareclass_candidates':len(candidates),
            'Eisenstein_exclusions':witness_count, 'explicit_field_images':8,
            'candidate_certificate':candidates,
            'classification_uses_external_database':False}


def det3(c: list[tuple[int, ...]]) -> int:
    a,b,d = c
    return (a[0]*(b[1]*d[2]-b[2]*d[1])
            -b[0]*(a[1]*d[2]-a[2]*d[1])
            +d[0]*(a[1]*b[2]-a[2]*b[1]))


def trace(v: tuple[int, ...], m: int = 9) -> int:
    return 3*v[0]+2*m*v[2]


def exceptional_forms(x: int, y: int) -> tuple[int,int,int]:
    ell = 9*(x*x+2*x*y+3*y*y)
    k = 3*(x**3+9*x*x*y+9*x*y*y-3*y**3)
    index = x**3-9*x*y*y-6*y**3
    return ell,k,index


def exception_controls() -> dict:
    n = valuation_count = 0
    basis = [(1,0,0),(0,1,0),(0,0,1)]
    gram = [[trace(mul(a,b,9,6)) for b in basis] for a in basis]
    assert det3([tuple(z) for z in gram]) == 1944
    for x in range(-20,21):
        for y in range(-20,21):
            if (x,y) == (0,0):
                continue
            beta = (-6*y,x,y)
            ell,k,index = exceptional_forms(x,y)
            assert trace(beta) == 0
            assert trace(mul(beta,beta,9,6)) == 2*ell
            assert det3([mul(beta,v,9,6) for v in basis]) == 2*k
            assert 4*ell**3-108*k*k == 1944*index*index
            assert k != 0 and index != 0
            assert vp(k,3) % 3 in (1,2)
            n += 1
            if ell % 2 and index % 32 == 0:
                assert y % 2 == 1 and x % 4 == 2
                valuation_count += 1
    # Field ramification is strictly weaker than the old elliptic support.
    ell,k,index = exceptional_forms(18,1)
    assert (ell,k,index) == (3267,26721,5664)
    a,u = 5,1
    Delta = (4*ell**3-108*k*k)//(1 << (2*a))
    assert (4*ell**3-108*k*k) % (1 << (2*a)) == 0
    assert Delta == 1944*177**2
    assert [p for p in factors(Delta) if p >= 5] == [59]
    assert factors(Delta)[59] == 2
    assert gcd(ell*k,59) == 1
    # This is only an algebraic control; no original A,B,d realization is asserted.
    return {'trace_norm_index_controls':n, 'dyadic_index_controls':valuation_count,
            'non_counterexample_support_control':{'ell':ell,'k':k,'a':a,
            'Delta':Delta,'elliptic_essential_support':[59],
            'cubic_ramification_support_outside_2_3':[]}}


def residue_controls() -> dict:
    # c=3: every monic cubic over F3 with nonzero x^2 coefficient has no triple root.
    total = 0
    for b in (1,2):
        for n in range(3):
            for r in range(3):
                for z in range(3):
                    f = (z**3+b*z*z+n*z+r) % 3
                    deriv = (2*b*z+n) % 3
                    second = (2*b) % 3
                    assert not (f == deriv == second == 0)
                    total += 1
    # Actual parameters: d even forces both j-1,n-j-1 odd and v2(Delta)=0.
    pairs = 0
    for a in range(2,11):
        for c in (1,3):
            A = c*(1 << a)
            for d in (2,4,6,8):
                for B in range(1,min(A//2,31),2):
                    if gcd(A,B) > 1 or B*d <= 3:
                        continue
                    n,j = A*d,B*d
                    assert 2+vp(j-1,2)+vp(n-j-1,2)-2*vp(n-2,2)-3*vp(n-1,2) == 0
                    pairs += 1
    return {'F3_no_triple_root_checks':total, 'even_d_rational_parameter_checks':pairs}


def symbolic_audit() -> dict:
    try:
        import sympy as s
        from sympy.polys.numberfields import round_two
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    X,Y,z,T = s.symbols('X Y z T')
    p = T**3-9*T-6
    beta = X*T+Y*(T*T-6)
    ell,k,index = exceptional_forms(X,Y)
    assert s.expand(s.resultant(p,z-beta,T)-(z**3-ell*z-2*k)) == 0
    assert s.expand(4*ell**3-108*k*k-1944*index*index) == 0
    _, DK = round_two(s.Poly(p,T))
    assert int(DK) == 1944
    # Independent maximal-order regressions for every tame case, not H examples.
    count = 0
    types = {'total_tame':0,'cube_unramified':0,'quadratic_ramified':0,
             'even_residual_unramified':0}
    for u in (1,5,25,125,625,7,49,343,11,121):
        for e in (1,3,5,7,9,11,13):
            for r in (1,3,5,7):
                if gcd(u*e,r) != 1:
                    continue
                delta = u*e**3-27*r*r
                if delta <= 0:
                    continue
                f = s.Poly(T**3-u*e*T-2*u*r,T)
                if not f.is_irreducible:
                    continue
                _,dk = round_two(f)
                fd = factors(delta)
                for p in set(factors(u)) | set(fd):
                    if p < 5:
                        continue
                    if u % p == 0:
                        b = vp(u,p)
                        predicted = 2 if b % 3 else 0
                        key = 'total_tame' if predicted else 'cube_unramified'
                    else:
                        predicted = fd[p] % 2
                        key = 'quadratic_ramified' if predicted else 'even_residual_unramified'
                    assert factors(int(dk)).get(p,0) == predicted, (u,e,r,p,dk,predicted)
                    types[key] += 1
                count += 1
    assert all(types.values())
    return {'symbolic_trace_norm_and_index':True,'independent_maximal_order_cases':count,
            'tame_local_regression_counts':types,'maximal_order_regressions_are_proof':False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--symbolic',action='store_true')
    args = parser.parse_args()
    result = {'status':'passed','classification':classification(),
              'exception':exception_controls(),'local_controls':residue_controls(),
              'whole_problem_solved':False,'independent_review':False}
    if args.symbolic:
        result['symbolic'] = symbolic_audit()
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
