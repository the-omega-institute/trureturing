#!/usr/bin/env python3
"""Exact clipped common-allocation obstruction for fixed five-leaf weights.

Two complete rational allocations are checked by a matching recurrence.
The full geometric product hinge is evaluated exactly at every breakpoint.
No solver, floating optimality, actual covering or Lean premise is used.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import prod
from pathlib import Path
import argparse,json

P=(5,7,11,13,17,19,23)
SS=tuple(s for s in range(128)if s.bit_count()>=2)
DEN=prod(p-2 for p in P)
COUNT=0


def need(ok,msg):
    global COUNT
    COUNT+=1
    if not ok:raise ValueError(msg)


def responses(candidate):
    need(len(candidate['stars'])==7 and len(candidate['support_colors'])==120,'complete common allocation')
    mass=[]
    for p,parts in zip(P,candidate['stars']):
        need(all(F(w)>=0 for w,role in parts) and sum(F(w)for w,role in parts)==1,'common star probability')
        need(all(len(role)==2 and role[0]in(0,1)and role[1]in range(5)for w,role in parts),'valid star root and leaf roles')
        mass.append(tuple(F(p-2)-sum(F(w)*(int((l>=2)==bool(r))+int(l==t))for w,(r,t)in parts)for l in range(5)))
    colors={};fractional=[]
    for s,spec in zip(SS,candidate['support_colors']):
        row=((spec,F(1)),)if isinstance(spec,int)else tuple((j,F(w))for j,w in spec)
        need(all(j in range(10) and w>=0 for j,w in row) and sum(w for j,w in row)==1,'one root-leaf role probability per full support')
        need(len({j for j,w in row})==len(row),'unique role entries')
        if len(row)>1:fractional.append(s)
        root=tuple(sum(w for j,w in row if j//5==r)for r in (0,1))
        leaf=tuple(sum(w for j,w in row if j%5==t)for t in range(5))
        need(sum(root)==sum(leaf)==1,'shared root and leaf marginals')
        colors[s]=tuple(1+root[int(l>=2)]+leaf[l]for l in range(5))
    result=[]
    for l in range(5):
        @lru_cache(None)
        def Z(s):
            if not s:return F(1)
            bit=s&-s;i=bit.bit_length()-1
            out=mass[i][l]*Z(s^bit);part=s^bit
            while part:
                block=bit|part
                out-=colors[block][l]*Z(s^block)
                part=(part-1)&(s^bit)
            return out
        result.append(Z(127)/DEN)
    need(tuple(result)==tuple(map(F,candidate['expected_leaf_responses'])),'exact full signed leaf responses')
    need(all(x>=0 for x in result),'clipping preserves this candidate exactly')
    return tuple(result),fractional


def hinge_coefficients():
    # Complete nonternary mean plus every atom below28; no upper-tail truncation.
    atoms={1:F(1)}
    for p in P:
        following={}
        for x,prob in atoms.items():
            for j in range(1,28//x+1):
                if x*j>=28:break
                previous=F(1)if j==1 else F(p-1,(p-2)*p**(j-1))
                tail=F(p-1,(p-2)*p**j)
                following[x*j]=following.get(x*j,F(0))+prob*(previous-tail)
        atoms=following
    coefficients={}
    for j in range(1,28):
        ternary=(F(1),F(-1),F(0))if j==1 else (F(0),F(1),F(-1))if j==2 else (F(0),F(0),F(2,3**(j-2)))
        for x,prob in atoms.items():
            if x*j>=28:continue
            coefficients[x*j]=tuple(old+prob*value for old,value in zip(coefficients.get(x*j,(F(0),)*3),ternary))
    C=prod(F(p-1,p-2)for p in P);hinges=[]
    for h in range(1,28):
        row=[C-h,C,F(3,2)*C]
        for x,co in coefficients.items():
            if x<h:row=[old+(h-x)*value for old,value in zip(row,co)]
        hinges.append(tuple(value/(28-h)for value in row))
    return tuple(hinges)


def calculate(certificate):
    need(certificate['schema']=='clipped-common-source-obstruction-v1' and tuple(certificate['primes'])==P,'certificate schema and numerical primes')
    need(len(certificate['candidates'])==2 and [row['name']for row in certificate['candidates']]==['A','B'],'two declared common allocations')
    need(len(SS)==120 and sum(not(s&t)for s,t in combinations(SS,2))==546 and
         sum(not(s&t or s&u or t&u)for s,t,u in combinations(SS,3))==210,'complete signed120/546/210 polynomial')
    RA,fracA=responses(certificate['candidates'][0]);RB,fracB=responses(certificate['candidates'][1])
    need(RA[2:]==(F(0),)*3 and RB[:3]==(F(0),)*3,'three exact zero leaves in each common allocation')
    U=sum(RA[:2]);V=sum(RB[2:])/3
    need(U>0 and V>0,'positive surviving slopes')
    crossing=V/(U+2*V);height=U*crossing
    need(F(1,4)<crossing<F(1,2),'upper-envelope crossing after one quarter')
    knots=(F(0),F(1,5),F(1,4),crossing,F(1,2))
    hinges=hinge_coefficients();endpoint_rows=[];slacks=[]
    for a in knots:
        b=(1-2*a)/3;r=max(2*a,3*b);v=max(a,b)
        envelope=min(U*a,V*(1-2*a))
        values=[]
        for h,(constant,dr,dv)in enumerate(hinges,1):
            required=constant+dr*r+dv*v
            need(required>envelope+F(1,1000),'every hinge threshold exceeds the clipped envelope at each breakpoint')
            values.append((required,h));slacks.append((required-envelope,a,h))
        threshold,h=min(values)
        endpoint_rows.append(dict(a=a,root_cap=r,leaf_cap=v,envelope=envelope,
                                  required_mass=threshold,minimizing_integer_h=h,gap=threshold-envelope))
    worst=min(slacks)
    a792=F(525243426,2350861343);at792=U*a792
    need(at792<F(2252652,100000000),'fixed792 weighting fails even after clipping')
    return dict(status='exact arithmetic passed; ordinary proof, not Lean',
                response_A=RA,response_B=RB,fractional_supports_A=fracA,fractional_supports_B=fracB,
                line_A_slope=U,line_B_intercept=V,line_B_slope=-2*V,
                envelope_crossing=crossing,envelope_height=height,envelope_height_decimal=float(height),
                optimal792_weight_clipped_upper=at792,optimal792_weight_clipped_upper_decimal=float(at792),
                endpoint_rows=endpoint_rows,minimum_gap=worst[0],minimum_gap_decimal=float(worst[0]),
                minimum_gap_weight=worst[1],minimum_gap_h=worst[2],uniform_gap_lower=F(1,1000),
                exact_endpoint_inequalities=135,checked_count=COUNT,
                scope='All globally fixed five-leaf weights in the complete relaxed star-plus-mixed allocation domain, leafwise clipped signed-polynomial lower certificate paired with the stated cap-based product hinge. Relabeling within the two root groups gives24 complete common allocations. No actual family realization, survivor-mass upper bound, optimality of the envelope, or unrestrictedErdos7 resolution.')


def encode(x):
    if isinstance(x,F):return str(x)
    raise TypeError(type(x).__name__)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name(Path(__file__).stem+'_certificate.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate(json.loads(args.certificate.read_text())),default=encode))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained result equals fresh exact computation')
        print('clipped common-source obstruction: exact arithmetic passed')

if __name__=='__main__':main()
