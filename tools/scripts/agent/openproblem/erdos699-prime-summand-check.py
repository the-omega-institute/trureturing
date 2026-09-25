#!/usr/bin/env python3
"""Exact audit of the original-parameter prime-summand exclusion for Erdos 699.

For i=3 a hypothetical counterexample has a normalized integral irreducible
cubic F. Combining its discriminant with a nonzero integral block value
forces both j/gcd(n,j) and (n-j)/gcd(n,j) to be odd composite numbers.
The all-parameter conclusion uses the written proof and the prior cubic
lemmas, not finite sampling. No whole-problem or independent-review claim.

Written proof (prior hypotheses: theory sections 2-5):
Let d=gcd(n,j), A=n/d=c*2**a, B=j/d, C=A-B and s=c*d.
For q | gcd(n-1,j), n=q*H+1,j=q*J, T=-H**3*F(J/H) is a
positive integer. Put theta=(n-j-1)*(n-j)/((n-2)*(n-1)).
An exact identity gives Delta*T=108*J**3*theta**2*(1-theta)/s**5.
Since 4/27-theta**2*(1-theta)=(theta-2/3)**2*(theta+1/3),
Delta*T<=16*J**3/s**5. The complement uses -F(1-X), same Delta.

Remove the single factor 3 from n-1 only when v3(n-1)=1; call
the resulting odd number R1. Complete low prime-power blocks give
R1 | B*C. Set qB=gcd(R1,B), qC=gcd(R1,C); qB*qC=R1.
Using Delta>=49 with q=qB and its complementary qC yields
49*c**5*d**2 <=16*(B/qB)**3 and <=16*(C/qC)**3.
Each odd cofactor is >=3. If qB=1 then C>=3*R1>=n-1,
contradicting C=A-B<=n-3; symmetrically qC>1. Both B and C
are odd composite. Thus j=2**b or 2**b*p (p odd prime), j>=4,
is excluded for ALL n>=2*j. No b or p search bound is used.
For odd m>1 in j=2**b*m, with p0 its smallest prime, any
counterexample must also satisfy 49*4**b<=16*(m/p0)**3.
This does not eliminate arbitrary composite B,C or the remaining i>=4.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from math import comb, gcd, isqrt


def prime(n: int) -> bool:
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def oddpart(n: int) -> int:
    if n <= 0:
        raise ValueError('positive integer required')
    return n // (n & -n)


def odd_divisors(n: int) -> list[int]:
    out: set[int] = set()
    for t in range(1, isqrt(n) + 1):
        if n % t == 0:
            if t & 1:
                out.add(t)
            if (n // t) & 1:
                out.add(n // t)
    return sorted(out)


def disc(v: tuple[Q, Q, Q, Q]) -> Q:
    a,b,c,d=v
    return b*b*c*c - 4*a*c**3 - 4*b**3*d - 27*a*a*d*d + 18*a*b*c*d


def vpbinom(n: int, j: int, p: int) -> int:
    total, power = 0, p
    while power <= n:
        total += n // power - j // power - (n-j) // power
        power *= p
    return total


def audit(nmax: int) -> dict:
    pairs = block_values = prime_summand_pairs = thin_column_pairs = 0
    old_uncovered_column_pairs = 0
    witness_checks = 0
    extra_column_pairs = 0
    sharp_cases = []
    max_scaled_product = Q(0)
    # Both halves are used to check the complement argument, always j,n-j>=4.
    for n in range(8, nmax + 1):
        cn3 = comb(n,3)
        for j in range(4, n-3):
            g = gcd(cn3,comb(n,j))
            s = Q(n,g)
            F=(Q(g),Q(-3*g*j,n),Q(3*g*j*(j-1),n*(n-1)),
               Q(-g*j*(j-1)*(j-2),n*(n-1)*(n-2)))
            assert all(x.denominator == 1 for x in F)
            D = disc(F)
            assert D > 0 and D.denominator == 1
            pairs += 1
            for q in odd_divisors(gcd(n-1,j)):
                H,J=(n-1)//q,j//q
                assert 0 < J < H
                T=-sum(F[t]*J**(3-t)*H**t for t in range(4))
                expected=Q(J*(H-J)*(2*H-J),1)/(s*(n-2))
                assert T == expected and T >= 1 and T.denominator == 1
                exact_product=(Q(108*J**3*(H-J)**2*(2*H-J)
                                 *(q*(H-J)+1)**2*(q*J-1),1)
                               /(s**5*H**3*(q*H-1)**3))
                assert D*T == exact_product
                # Strict rational comparisons; no floating-point extrema.
                t=Q(J,H)
                f=t*(1-t)**2*(2-t)
                assert f == (1-t)**2*(1-(1-t)**2)
                assert 4*f <= 1
                assert D*T < 108*J**3*f/s**5 <= 27*J**3/s**5
                theta=Q((n-j-1)*(n-j),(n-2)*(n-1))
                assert 0 < theta < 1
                assert D*T == 108*J**3*theta**2*(1-theta)/s**5
                assert Q(4,27)-theta**2*(1-theta) == (theta-Q(2,3))**2*(theta+Q(1,3))
                assert D*T <= 16*J**3/s**5
                # Independent integer form of the final inequality.
                assert D*T*n**5 <= 16*g**5*J**3
                max_scaled_product=max(max_scaled_product,D*T*s**5/J**3)
                if D*T*s**5/J**3 == 16 and len(sharp_cases)<4:
                    sharp_cases.append([n,j,q])
                block_values += 1
            if 2*j > n:
                continue
            d=gcd(n,j)
            B,C=j//d,(n-j)//d
            thin=oddpart(j)==1 or prime(oddpart(j))
            reduced_prime=prime(B) or prime(C)
            if thin:
                thin_column_pairs += 1
                # This count only illustrates that the old j-1 condition is narrower.
                m=oddpart(j-1)
                count=0
                for p in range(3,isqrt(m)+1,2):
                    if m%p==0:
                        count+=1
                        while m%p==0:m//=p
                if m>1:count+=1
                old_uncovered_column_pairs += count>=2
            if reduced_prime:
                prime_summand_pairs += 1
            m=oddpart(j)
            extra=False
            if m>1:
                p0=next((p for p in range(3,isqrt(m)+1,2) if m%p==0),m)
                two=j//m
                extra=49*two**2>16*(m//p0)**3
                extra_column_pairs+=extra
            if thin or reduced_prime or extra:
                assert oddpart(g)>1
                p=next(p for p in range(3,isqrt(g)+1,2) if g%p==0) if any(
                    g%p==0 for p in range(3,isqrt(g)+1,2)) else oddpart(g)
                # Independent Legendre audit of a concrete shared odd prime.
                assert prime(p) and vpbinom(n,3,p)>0 and vpbinom(n,j,p)>0
                witness_checks+=1
    # Primality cannot be weakened to 'odd prime power' in the proof:
    # gcd(25,5)=5 is a proper nontrivial divisor, so no primality dichotomy.
    assert gcd(25,5)==5 and not prime(25)
    # The normalized cubic at this true non-counterexample is not integral.
    n,j=128,31
    v=(Q(n),Q(-3*j),Q(3*j*(j-1),n-1),Q(-j*(j-1)*(j-2),(n-1)*(n-2)))
    assert any(x.denominator != 1 for x in v)
    assert oddpart(gcd(comb(n,3),comb(n,j)))>1
    return {
        'status':'passed', 'nmax':nmax,
        'actual_pairs_both_halves':pairs,
        'discriminant_times_integral_block_values':block_values,
        'original_half_prime_reduced_summand_pairs':prime_summand_pairs,
        'original_half_oddpart_one_or_prime_pairs':thin_column_pairs,
        'thin_pairs_with_at_least_two_odd_primes_in_j_minus_one':old_uncovered_column_pairs,
        'explicit_shared_prime_legendre_crosschecks':witness_checks,
        'additional_two_adic_column_pairs':extra_column_pairs,
        'sharp_constant_controls_n_j_q':sharp_cases,
        'largest_scaled_product':str(max_scaled_product),
        'sharp_uniform_upper_bound':16,
        'all_parameter_proof_by_sampling':False,
        'whole_problem_solved':False,
    }


def symbolic() -> dict:
    try:
        import sympy as S
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    n,j,q,H,J,s,X,t=S.symbols('n j q H J s X t')
    F=(n*X**3-3*j*X**2+3*j*(j-1)/(n-1)*X
       -j*(j-1)*(j-2)/((n-1)*(n-2)))/s
    D=S.discriminant(F,X)
    expected_D=(108*j**2*(n-j)**2*(j-1)*(n-j-1)
                /(s**4*(n-2)**2*(n-1)**3))
    assert S.factor(D-expected_D)==0
    at_block=S.factor((-H**3*F.subs(X,J/H)).subs({n:q*H+1,j:q*J}))
    assert S.factor(at_block-J*(H-J)*(2*H-J)/(s*(q*H-1)))==0
    product=S.factor(D.subs({n:q*H+1,j:q*J})*at_block)
    target=108*J**3*(H-J)**2*(2*H-J)*(q*(H-J)+1)**2*(q*J-1)/(s**5*H**3*(q*H-1)**3)
    assert S.factor(product-target)==0
    assert S.expand(t*(1-t)**2*(2-t)-(1-t)**2*(1-(1-t)**2))==0
    # Strictness of the two rational estimates follows from positive differences.
    assert S.expand((q*H-1)-(q*(H-J)+1)) == q*J-2
    assert S.expand(J*(q*H-1)-H*(q*J-1)) == H-J
    theta=(n-j-1)*(n-j)/((n-2)*(n-1))
    rhs=(108*(j/q)**3*theta**2*(1-theta)/s**5).subs({n:q*H+1,j:q*J})
    assert S.factor(product-rhs)==0
    assert S.factor(S.Rational(4,27)-t*t*(1-t)-(t-S.Rational(2,3))**2*(t+S.Rational(1,3)))==0
    # q | B, J=d*v, s=c*d yields the reduced cofactor version.
    c,d,v=S.symbols('c d v', nonzero=True)
    assert S.cancel((16*J**3/s**5).subs({J:d*v,s:c*d}))==16*v**3/(c**5*d**2)
    return {'symbolic_formulas':'passed','extremum_proved_algebraically':True}


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--nmax',type=int,default=250)
    p.add_argument('--symbolic',action='store_true')
    args=p.parse_args()
    if args.nmax<8:p.error('--nmax must be at least 8')
    out=audit(args.nmax)
    if args.symbolic:out.update(symbolic())
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
