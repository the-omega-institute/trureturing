#!/usr/bin/env python3
"""Exact audits for the Erdos 699 central-divisor/twist continuation.

No full solution or independent review is claimed. The 83 realization
certificate uses the external upper count in Cremona--Lingham (2007),
section 5.1. Its pairs were selected from von Kanel--Matschke's 2015 data,
CC BY-NC 3.0, source Git blob ae99430519ac37dae02a6512e4fccbde53858801:
https://github.com/bmatschke/solving-classical-diophantine-equations/blob/master/elliptic-curve-database/curves__S_2_p_pMax250.txt
The selection normalizes the c6 sign. All realizations are directly checked;
the complete-classification upper bound is NOT proved by this script.
Only --symbolic requires SymPy. Other arithmetic is standard-library exact.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import comb, gcd
import json

MODELS_23 = (
 (1174752,1273266432),(51705,11757069),(52704,12099456),(6624,539136),
 (1440,54648),(945,29079),(2592,132192),(1872,81216),(1728,72576),
 (1440,55296),(153,1917),(864,25920),(1008,32832),(225,3537),
 (7648,706816),(288,5184),(297,5589),(432,10368),(864,31104),
 (576,17280),(657,22329),(288,6912),(1296,77760),(432,15552),
 (144,3456),(4545,622431),(304,13760),(144,5184),(160,8704),
 (144,8640),(144,12096),(144,29376),(0,216),(-32,2816),
 (-752,150976),(-32,640),(-135,4941),(-288,13824),(-432,15552),
 (-80,1216),(-288,6912),(-32,224),(-144,1728),(-288,3456),
 (-63,351),(-368,4672),(-432,5184),(-288,1728),(-135,243),
 (-207,297),(-48,0),(1296,15552),(144,864),(1377,26001),
 (112,640),(432,5184),(288,3456),(208,2240),(1296,36288),
 (864,20736),(160,1664),(432,7776),(160,1792),(112,1088),
 (297,4779),(2592,124416),(1168,38080),(432,8640),(352,6400),
 (208,2944),(720,19008),(513,11583),(528,12096),(1120,37376),
 (7776,684288),(1696,69760),(1008,31968),(1552,61120),(3088,171584),
 (5913,454653),(31072,5477120),(18448,2505664),(260496,132954048),
)


def val(n: int, p: int) -> int:
    if n == 0 or p < 2:
        raise ValueError('nonzero integer and p>=2 required')
    n = abs(n)
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer


def factors(n: int) -> dict[int, int]:
    if n <= 0:
        raise ValueError('positive integer required')
    out: dict[int,int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p,0)+1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = out.get(n,0)+1
    return out


def part23(n: int) -> bool:
    if n == 0:
        return False
    n = abs(n)
    for p in (2,3):
        while n % p == 0:
            n //= p
    return n == 1


def cube_split(n: int) -> tuple[int, int]:
    u0 = s = 1
    for p, exponent in factors(n).items():
        q,r = divmod(exponent,3)
        u0 *= p**r
        s *= p**q
    assert n == u0*s**3
    return u0,s


def model_certificate() -> dict:
    js: dict[Q, tuple[int,int]] = {}
    for c4,c6 in MODELS_23:
        raw = c4**3-c6*c6
        assert raw != 0 and raw % 1728 == 0
        assert part23(raw//1728)
        # Independent integral realization, not a claim about a minimal model.
        aa,bb = -27*c4,-54*c6
        disc = -16*(4*aa**3+27*bb**2)
        assert disc == 6**12*(raw//1728) and part23(disc)
        j = Q(1728*c4**3,raw)
        assert Q((-48*aa)**3,disc) == j
        assert j not in js
        js[j]=(c4,c6)
    assert len(js) == 83
    positive = [j for j in js if j>1728]
    assert len(positive) == 32
    values = [(val(j.numerator,2)-val(j.denominator,2),j) for j in positive]
    minimum,witness = min(values)
    assert minimum == -9 and witness == Q(1193859,512)
    return {'distinct_realized_j':len(js), 'j_above_1728':len(positive),
            'min_v2_j_above_1728':minimum,'attaining_j':str(witness),
            'external_upper_count_assumed':83,
            'complete_classification_reproved':False}


def binom_val(n: int, j: int, p: int) -> int:
    total=0
    power=p
    while power<=n:
        total+=n//power-j//power-(n-j)//power
        power*=p
    return total


def low_exponent_certificate() -> dict:
    # The classification gives a<=8. Enumerate all d allowed by the OLD bound.
    rows=set()
    for a in range(2,9):
        for c in (1,3):
            A=c*(1<<a);d=1
            while 784*(A*d-1)**3 < 27*(1<<(4*a)):
                rows.add(A*d)
                d+=1
    assert rows == {32,64,128,256,512}
    witnesses={32:(31,),64:(31,7),128:(127,),256:(127,5),512:(73,17)}
    count=0
    for n in sorted(rows):
        cn3=comb(n,3)
        for p in witnesses[n]:
            assert cn3%p==0 and factors(p)=={p:1}
        for j in range(4,n//2+1):
            assert any(binom_val(n,j,p)>0 for p in witnesses[n])
            common=gcd(cn3,comb(n,j))
            assert common//(common & -common)>1
            count+=1
    assert count==481
    return {'rows':sorted(rows),'all_admissible_j_checked':count,
            'scope':'all remaining rows after a<=8 and the cubic bound'}


def synthetic_valuation_audit() -> dict:
    count=local=twists=0
    # These controls satisfy the algebraic identities, not all original hypotheses.
    for u in (1,5,7,25,49,125,343,625,3125,15625,42875):
        for r in (1,7,11,13):
            if gcd(u,r)!=1:continue
            for e in range(1,16,2):
                if gcd(e,r)!=1:continue
                W0=u*e**3-27*r*r
                if W0<=0 or W0%4:continue
                a=2;c=1;delta=W0//4
                ell,k=u*e,u*r
                D=u*u*delta
                assert ell**3-27*k*k==4*D
                u0,s=cube_split(u)
                ellf,kf=u0*s*e,u0*r
                Wf=ellf**3-27*kf*kf
                assert Wf==4*u0*u0*delta
                jf=Q(1728*ellf**3,Wf)
                assert jf==Q(1728*ell**3,ell**3-27*k*k)>1728
                assert val(jf.numerator,2)-val(jf.denominator,2)==8-2*a-val(delta,2)
                primes=set(factors(u*r*delta*e))|{5,7,11,13,17}
                df=64*Wf
                for p in primes:
                    if p<5:continue
                    local+=1
                    if u%p==0:
                        assert val(D,p)==2*val(u,p) and delta%p
                    if r%p==0:
                        assert ell%p and D%p
                    if delta%p==0:
                        assert (u*r*e)%p and ellf%p
                        assert val(jf.numerator,p)-val(jf.denominator,p)==-val(delta,p)
                    alpha=factors(u0).get(p,0)
                    if alpha:
                        assert alpha in (1,2) and val(df,p)==2*alpha
                        # All possible valuations of ANY rational twist, modulo12.
                        for parity in (0,1):
                            assert (2*alpha+6*parity)%12 !=0
                            twists+=1
                    elif delta%p:
                        assert df%p
                count+=1
    # Original E bad at5, its displayed quadratic twist good at5.
    u,r,e=125,11,3
    ell,k=u*e,u*r
    ellf,kf=15,11
    W=ell**3-27*k*k;Wf=ellf**3-27*kf*kf
    assert W==125**2*108 and Wf==108
    assert val(64*W,5)==6 and (64*Wf)%5
    assert part23(64*Wf) and Q(1728*ell**3,W)==54000
    # Same arithmetic example has a=2. It is NOT an Erdos counterexample.
    assert W//4==u*u*27
    assert Q(1728*ellf**3,Wf)==54000
    # A rational discriminant multiple of u^2 alone is insufficient if r shares u.
    assert gcd(5,5)!=1
    return {'synthetic_algebraic_controls':count,'prime_valuation_checks':local,
            'all_twist_parity_checks':twists,
            'strict_twist_control':{'ell':ell,'k':k,'ell_flat':ellf,'k_flat':kf,
                                   'removed_prime':5,'j':54000},
            'controls_are_counterexamples':False}


def symbolic_audit() -> dict:
    import sympy as s
    U,V,e,r,x,y,t=s.symbols('U V e r x y t',nonzero=True)
    u=U*V**3;ell=u*e;k=u*r
    ellf=U*V*e;kf=U*r
    assert s.expand(ellf**3-27*kf*kf-U**2*(u*e**3-27*r*r))==0
    # Twist parameter V, followed by x=V^2*X,y=V^3*Y.
    original_twist=y*y-x**3+V*V*ell*x-2*V**3*k
    transformed=s.expand(original_twist.subs({x:V*V*x,y:V**3*y})/V**6)
    assert s.expand(transformed-(y*y-x**3+ellf*x-2*kf))==0
    assert s.factor(ellf**3/(ellf**3-27*kf*kf)-ell**3/(ell**3-27*k*k))==0
    assert 14*3**3*2**3==3024
    assert 3*3**2*2**2==108
    assert 8*3**2*2**3==576
    assert 108+5*576==2988
    return {'symbolic_twist_and_scaling':True,'symbolic_discriminant_identity':True,
            'symbolic_j_invariance':True,'height_exponents_checked':True}


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--symbolic',action='store_true')
    args=p.parse_args()
    result={'status':'passed','models':model_certificate(),
            'low_exponents':low_exponent_certificate(),
            'local_twists':synthetic_valuation_audit(),
            'whole_solution':False,'independent_review':False}
    if args.symbolic:result.update(symbolic_audit())
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
