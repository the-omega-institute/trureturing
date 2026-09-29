#!/usr/bin/env python3
"""Independent exact arithmetic consumer for the uniform depth-two source.

The complete star-vertex minimum is supplied by the paired C++ producer.
This consumer independently evaluates its minimizing response with ALL ordered
mixed-support role choices, then computes full-height moments and prime tails.
All guards remain active under optimized Python. No Lean claim is made.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod
import json
import argparse
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


P=(5,7,11,13,17,19,23)
WEIGHTS=(33,33,28,28,28)
MINIMIZER=((1,2),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1))


def block_partitions(h,k):
    if not h:return int(k==0)
    if not k:return 0
    return sum(comb(h-1,j-1)*block_partitions(h-j,k-1) for j in range(2,h+1))


def response(layout):
    single=tuple(tuple(1+int((l>=2)==bool(r))+int(l==t) for l in range(5))
                 for r in range(2)for t in range(5))
    # Keep the ordered10^k choices; this does not use the C++ orbit reduction.
    coeff={k:tuple(tuple(prod(single[i][l] for i in indices) for l in range(5))
                    for indices in product(range(10),repeat=k)) for k in range(1,4)}
    numerator=0;terms=0
    for mask in range(128):
        h=mask.bit_count()
        if mask and h<2:continue
        values=tuple(WEIGHTS[l]*prod(P[i]-2-int((l>=2)==bool(layout[i][0]))-int(l==layout[i][1])
                     for i in range(7) if not mask>>i&1) for l in range(5))
        if not mask:
            numerator=sum(values);continue
        for k in range(1,4):
            count=block_partitions(h,k)
            if not count:continue
            choices=[sum(v*c for v,c in zip(values,c)) for c in coeff[k]]
            numerator += count*(min(choices) if k%2==0 else -max(choices))
            terms+=1
    return F(numerator,sum(WEIGHTS)*prod(p-2 for p in P)),terms


def a4(p):
    t=F(1,p-1)
    return 15*t+50*t*t+60*t**3+24*t**4


def calculate(enumeration):
    need(enumeration['samples']==929408 and enumeration['canonical_leaf_patterns']==7261,
         "complete canonical source-vertex count")
    need(enumeration['weight_a']==33 and enumeration['weight_b']==28,
         "one fixed weight law is used for every vertex")
    need(enumeration['negative_samples']==0 and enumeration['minimum_numerator']==2263036 and
         enumeration['denominator']==1192826250,"certified global source minimum")
    need(tuple(map(tuple,enumeration['layout']))==MINIMIZER,"canonical minimizing vertex")
    direct,terms=response(MINIMIZER)
    mass=F(1131518,596413125)
    need(direct==mass,"ordered-role independent evaluation of minimizing response")
    # Burnside count for S2xS3 acting on five-leaf words of length7.
    leaf_orbits=(5**7+3*3**7+2*2**7+3**7+3)//12
    need(leaf_orbits==7261 and leaf_orbits*2**7==929408,"independent leaf-orbit count")
    need(5**7*2**7==10000000,"entire raw star-vertex inventory")
    base=(7,11,13,17,19,23)
    t=tuple(F(1,q-4)for q in base)
    base_cap=3*(prod(1+x for x in t)-1-sum(t))
    need(base_cap==F(184697,233415)<1,"one-clique Shearer base region")
    first=max(sum(WEIGHTS[:2]),sum(WEIGHTS[2:]))/F(sum(WEIGHTS))
    leaf=F(max(WEIGHTS),sum(WEIGHTS))
    need(first==F(14,25) and leaf==F(11,50),"same ternary law's root and leaf caps")
    ternary_fourth=1+15*first+216*leaf
    need(ternary_fourth==F(1423,25),"complete ternary fourth-query factor")
    fourth=ternary_fourth*prod(1+F(p-1,p-2)*a4(p)for p in P)
    need(fourth==F(83957323825075240180209923,277054053281280000000),"raw joint fourth envelope")
    B,ell,delta,r=2000,6,F(2,7),21
    need(B>=286 and ell>=4 and 3**ell<=B and 4*ell>=r,"analytic prime-tail range")
    need(all(c<=comb(r,j)for j,c in enumerate((F(1),F(21),F(70),F(84),F(168,5)))),
         "complete fourth growth polynomial")
    tau=F(21609,10240)*F(73,71)**r*F(B,(B-1)**4)*sum(
        F(factorial(r),factorial(r-j)*(3*ell)**j)for j in range(r+1))
    final=mass-fourth*tau
    need(final>F(1,5000),"uniform depth-two source complete-tail margin")
    no3=(5,7,11,13,17,19,23,29)
    b=tuple(F(1,p-2)for p in no3)
    no3mass=2+sum(b)-prod(1+x for x in b)
    no3fourth=prod(1+F(p-1,p-2)*a4(p)for p in no3)
    no3final=no3mass-no3fourth*tau
    need(no3final>F(1,5000),"missing-three branch uses the same2000 cutoff")
    return dict(status="exact_arithmetic_passed_not_Lean",
                nonternary_benchmark=P,leaf_weights=[F(x,sum(WEIGHTS))for x in WEIGHTS],
                raw_star_vertices=10000000,canonical_vertices=929408,leaf_orbits=leaf_orbits,
                direct_ordered_role_response=direct,direct_response_terms=terms,
                minimum_layout=MINIMIZER,source_mass_lower=mass,
                base_clique_complement_cap_sum=base_cap,
                ternary_root_cap=first,ternary_leaf_cap=leaf,
                ternary_fourth_factor=ternary_fourth,raw_fourth_upper=fourth,
                tail=dict(cutoff=B,ell=ell,delta=delta,growth=r,factor=tau),
                final_mass_lower=final,final_mass_decimal=float(final),simple_lower=F(1,5000),
                missing_three=dict(primes=no3,mass=no3mass,fourth=no3fourth,
                                   final=no3final,final_decimal=float(no3final)),
                proof_boundary="Source completion, one-clique Shearer validity, separate concavity, and prefix transport are ordinary mathematical arguments. The analytic tail imports Report734's stated prime-product input.",
                scope="At most8 actual support primes at most2000; only originals wholly on those small primes require v3<=2. All later original phases, finite heights, mixed supports and finite tail lengths are unrestricted.")


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument('--enumeration',type=Path,
                        default=Path(__file__).with_name('uniform_depth2_source_enumeration.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    enumeration=json.loads(args.enumeration.read_text())
    result=json.loads(json.dumps(calculate(enumeration),default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    else:
        need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),
             'fresh depth-two source result equals retained exact data')
    print(json.dumps({k:result[k] for k in
                     ('raw_star_vertices','canonical_vertices','source_mass_lower','final_mass_decimal')},indent=2))
