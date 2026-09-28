#!/usr/bin/env python3
"""Finite diagnostics for the conditional four-coordinate response packet.

The fixtures are probability models, not asserted odd-covering families.
The general criterion is proved in the paired manuscript.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json

N=4
MASK=15
SUPPORTS=tuple(d for d in range(1,16) if d.bit_count()>=2)
PAIRS=tuple((d,MASK^d) for d in SUPPORTS if d.bit_count()==2 and d<(MASK^d))


def need(x,msg):
    if not x:raise RuntimeError(msg)


def mul(xs):return prod(xs,start=F(1))


def response(m,kappa,unqueried):
    val=mul(m[i] for i in range(4) if unqueried>>i&1)
    val-=sum((kappa[d]*mul(m[i] for i in range(4) if unqueried>>i&1 and not d>>i&1)
             for d in SUPPORTS if d&unqueried==d),F(0))
    if unqueried==15:
        val+=sum((kappa[a]*kappa[b] for a,b in PAIRS),F(0))
    return val


def fixture(name,rare,m,inflate):
    states=tuple(product((0,1),repeat=4))
    weights={x:mul(m[i]*(rare[i] if x[i] else 1-rare[i]) for i in range(4)) for x in states}
    # All support events use their actual all-one cylinder. Their
    # intersections overlap; only complementary pairs are independent.
    def bad(x,d):return all(x[i] for i in range(4) if d>>i&1)
    actual={d:mul(m[i]*rare[i] for i in range(4) if d>>i&1) for d in SUPPORTS}
    kappa={d:min(mul(m[i] for i in range(4) if d>>i&1),inflate*actual[d]) for d in SUPPORTS}
    survivors={x:p for x,p in weights.items() if not any(bad(x,d) for d in SUPPORTS)}
    a=sum(survivors.values(),F(0))
    z=response(m,kappa,15)
    need(0<z<=a,'positive response below the actual common survivor mass')
    kernel={x:p*z/a for x,p in survivors.items()}
    count=0
    for T in range(16):
        H=response(m,kappa,15^T)
        need(H>0,'all declared response marginals positive')
        for bits in product((0,1),repeat=T.bit_count()):
            idx=[i for i in range(4) if T>>i&1]
            observed=dict(zip(idx,bits))
            mass=sum((p for x,p in kernel.items() if all(x[i]==v for i,v in observed.items())),F(0))
            ref=mul(m[i]*(rare[i] if v else 1-rare[i]) for i,v in observed.items())
            need(mass<=H*ref,'same thinned actual kernel obeys every marginal domination')
            count+=1
    return dict(name=name,response_mass=str(z),actual_avoidance_mass=str(a),marginal_atom_checks=count)


def calculate():
    checks=0
    for flags in product((0,1),repeat=len(SUPPORTS)):
        a=dict(zip(SUPPORTS,flags))
        upper=sum(flags)-sum(a[d]*a[e] for d,e in PAIRS)
        need(int(any(flags))<=upper,'three complementary-pair bundles upper-bound actual union')
        checks+=1
    fixtures=[
        fixture('actual caps',(F(1,7),F(1,5),F(1,6),F(1,8)),
                (F(2,3),F(3,4),F(4,5),F(5,6)),F(1)),
        fixture('inflated caps',(F(1,9),F(1,8),F(1,7),F(1,6)),
                (F(4,5),F(5,6),F(6,7),F(7,8)),F(3,2)),
    ]
    # Boundary rows are discarded without any division.
    m=(F(0),F(3,4),F(4,5),F(5,6))
    kap={d:F(0) for d in SUPPORTS}
    need(response(m,kap,15)==0,'zero unary row yields zero retained response')
    m=(F(1),)*4
    kap={d:F(0) for d in SUPPORTS};kap[3]=F(1)
    need(response(m,kap,15)==0,'saturated complementary pair boundary')
    qb=(11,13,17,19)
    outside=mul(1+F(1,q-2) for q in qb)-1
    deep_coeff=F(7,4)*((1+F(1,3))*(1+F(1,5))-(1+F(4,15))*(1+F(6,35)))
    tau=F(227,2100)+deep_coeff*outside
    need(deep_coeff==F(61,300) and outside==F(69,187) and tau==F(17978,98175),
         'complete head-deep tail across all outside supports')
    out=dict(scope='Finite probability diagnostics and exact full-tail arithmetic for a conditional175-cell joint sufficient criterion; no uniform positive nine-prime gate asserted.',
             pointwise_union_checks=checks,fixtures=fixtures,
             boundary_checks=2,head_cells=5*5*7,conditional_response_supports=16,
             query_modes_including_unit=27*16,nonunit_modes=27*16-1,
             outside_support_sum=str(outside),cross_head_deep_coefficient=str(deep_coeff),
             total_head_deep_tail=str(tau),
             evidence='Ordinary proof and exact finite checks, not new Lean verification.')
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
        need(retained==result,'retained result agrees with exact replay')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':
    main()
