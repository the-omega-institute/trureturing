#!/usr/bin/env python3
"""Exact fixed-weight optimum and its full-query hinge limitation.

Consumes the complete signed-128-bit star-vertex scan. Independently forms
supporting affine pieces directly from all ten role choices, without the
producer's leaf-vector rearrangement. No Lean verification is claimed.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod, factorial
from pathlib import Path
import argparse
import json

P=(5,7,11,13,17,19,23)
ROLES=tuple(tuple(1+int((l>=2)==bool(r))+int(l==t) for l in range(5))
            for r in range(2) for t in range(5))
SUPPORTS=tuple(s for s in range(128) if s.bit_count()>=2)
EDGES=tuple((s,t) for s,t in combinations(SUPPORTS,2) if not s&t)
DEG={s:sum(s in edge for edge in EDGES) for s in SUPPORTS}
COEFF={k:tuple(sorted(set(tuple(prod(c[l] for c in cs) for l in range(5))
                         for cs in product(ROLES,repeat=k)))) for k in (1,2,3)}
A=((1,2),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1))
B=((0,0),(1,2),(1,3),(1,4),(1,3),(1,4),(1,4))
ASTAR=F(525243426,2350861343)
UPPER=F(64160977192969114,8019923683316269725)
SCALE=572
BASE_DEN=prod(p-2 for p in P)


def need(ok,msg):
    if not ok: raise ValueError(msg)


def partitions(n,k):
    table=[[0]*(k+1) for _ in range(n+1)]
    table[0][0]=1
    for h in range(1,n+1):
        for j in range(1,k+1):
            table[h][j]=j*table[h-1][j]+((h-1)*table[h-2][j-1] if h>=2 else 0)
    return table[n][k]


def add(x,y):return x[0]+y[0],x[1]+y[1]
def mul(x,z):return x[0]*z,x[1]*z
def at(x,a):return x[0]+x[1]*a


def supporting_line(layout,a):
    rows={s:tuple(prod(P[i]-2-int((l>=2)==bool(layout[i][0]))-int(l==layout[i][1])
                       for i in range(7) if not s>>i&1) for l in range(5))
          for s in range(128)}
    def affine(s,c):
        av=sum(rows[s][l]*c[l] for l in (0,1))
        bv=sum(rows[s][l]*c[l] for l in (2,3,4))
        return bv,3*av-2*bv
    first={s:tuple(affine(s,c) for c in ROLES) for s in SUPPORTS}
    total=mul(affine(0,(1,)*5),SCALE)
    for s in SUPPORTS:
        if not DEG[s]:total=add(total,mul(max(first[s],key=lambda v:at(v,a)),-SCALE))
    for s,t in EDGES:
        choices=[]
        for i,ci in enumerate(ROLES):
            for j,cj in enumerate(ROLES):
                pair=mul(affine(s|t,tuple(ci[l]*cj[l] for l in range(5))),SCALE)
                choices.append(add(add(pair,mul(first[s][i],-SCALE//DEG[s])),
                                   mul(first[t][j],-SCALE//DEG[t])))
        total=add(total,min(choices,key=lambda v:at(v,a)))
    for s in SUPPORTS:
        count=partitions(s.bit_count(),3)
        if count:
            choices=tuple(affine(s,c) for c in COEFF[3])
            total=add(total,mul(max(choices,key=lambda v:at(v,a)),-SCALE*count))
    return tuple(F(x,3*SCALE*BASE_DEN) for x in total)


def direct_response(layout,a):
    # Separate evaluation of the baseline plus nonnegative shared credits.
    weights=(a,a)+((1-2*a)/3,)*3
    den=prod(x.denominator for x in weights)
    wi=tuple(int(x*den) for x in weights)
    rows={s:tuple(wi[l]*prod(P[i]-2-int((l>=2)==bool(layout[i][0]))-int(l==layout[i][1])
                           for i in range(7) if not s>>i&1) for l in range(5))
          for s in range(128)}
    first={s:tuple(sum(rows[s][l]*c[l] for l in range(5)) for c in ROLES) for s in SUPPORTS}
    mx={s:max(v) for s,v in first.items()}
    baseline=sum(rows[0])
    for s in SUPPORTS:
        for k in (1,2,3):
            count=partitions(s.bit_count(),k)
            if count:
                vals=[sum(rows[s][l]*c[l] for l in range(5)) for c in COEFF[k]]
                baseline+=count*(-max(vals) if k%2 else min(vals))
    credit=0
    for s,t in EDGES:
        pv=[[sum(rows[s|t][l]*ci[l]*cj[l] for l in range(5))
             for cj in ROLES] for ci in ROLES]
        low=min(map(min,pv))
        gain=min(SCALE*(pv[i][j]-low)+SCALE//DEG[s]*(mx[s]-first[s][i])
                 +SCALE//DEG[t]*(mx[t]-first[t][j]) for i in range(10) for j in range(10))
        need(gain>=0,'nonnegative shared deficit credit')
        credit+=gain
    return dict(baseline=F(baseline,den*BASE_DEN),
                credit=F(credit,SCALE*den*BASE_DEN),
                refined=F(SCALE*baseline+credit,SCALE*den*BASE_DEN))


def hinge_floor():
    # Comparator with separately universal minima root cap 1/2, leaf cap1/5.
    # This need not be a physically attainable five-leaf weighting.
    def tail(p,e):
        if e==0:return F(1)
        if p==3:return F(1,2) if e==1 else F(1,5*3**(e-2))
        return F(p-1,(p-2)*p**e)
    atoms={1:F(1)}
    for p in (3,)+P:
        next_atoms={}
        for x,px in atoms.items():
            for j in range(1,28//x+1):
                value=x*j
                if value>=28:break
                mass=tail(p,j-1)-tail(p,j)
                next_atoms[value]=next_atoms.get(value,F(0))+px*mass
        atoms=next_atoms
    mean=F(9,5)*prod(F(p-1,p-2) for p in P)
    rows=[]
    for h in range(1,28):
        hinge=mean-h+sum((h-j)*p for j,p in atoms.items() if j<h)
        need(hinge>0,'positive complete hinge')
        rows.append(dict(h=h,hinge=hinge,required_mass=hinge/(28-h)))
    best=min(rows,key=lambda row:row['required_mass'])
    need(sum(row['required_mass']==best['required_mass'] for row in rows)==1 and best['h']==16,
         'unique hinge ratio minimum at16')
    need(best['required_mass']>F(9,400),'universal required mass greater than9/400')
    need(best['required_mass']>UPPER,'fixed weight optimum below comparator requirement')
    return dict(root_cap=F(1,2),leaf_cap=F(1,5),mean=mean,
                rows=rows,best=best,minimum_decimal=float(best['required_mass']),subthreshold_atoms=atoms)


def calculate(scan):
    need(scan['complete'] is True and scan['visits']==929408 and
         scan['raw_vertices']==10000000,'complete vertex coverage')
    need(scan['refined']==722 and scan['cutoff_denominator']==100,'certified baseline shortcut')
    need(scan['old_min_numerator']==222646444984111,'baseline comparison at optimal weight')
    need(scan['refined_min_numerator']==256643908771876456 and
         scan['refined_denominator']==32079694733265078900,'exact scan numerator and denominator')
    need(tuple(map(tuple,scan['layout']))==B,'canonical minimizer')
    need(F(scan['refined_min_numerator'],scan['refined_denominator'])==UPPER<F(1,100),
         'global minimum is refined and equals the upper certificate')
    wa,wb=1575730278,1300374491
    absolute_baseline=sum(prod(P[i]-2 for i in range(7) if not s>>i&1)*
                          (int(s==0)+sum(partitions(s.bit_count(),k)*3**k for k in (1,2,3)))
                          for s in range(128))
    need(absolute_baseline==18728919 and
         (2*wa+3*wb)*absolute_baseline==132087275019834651<2**63,
         'signed64 baseline arithmetic range')
    plus=supporting_line(A,ASTAR);minus=supporting_line(B,ASTAR)
    need(plus==(F(-301906006,3411483075),F(1473412322,3411483075)),
         'increasing supporting line')
    need(minus==(F(44178103,310134825),F(-9023647,14995530)),
         'decreasing supporting line')
    need(plus[1]>0>minus[1] and 0<ASTAR<F(1,2),'opposing slopes inside weight interval')
    cross=(minus[0]-plus[0])/(plus[1]-minus[1])
    need(cross==ASTAR and at(plus,cross)==at(minus,cross)==UPPER,'exact affine upper intersection')
    direct_a=direct_response(A,ASTAR);direct_b=direct_response(B,ASTAR)
    need(direct_a['refined']==direct_b['refined']==UPPER,'independent direct response at both profiles')
    need(F(1,5)<ASTAR<F(1,4),'optimum inside middle cap segment')
    ratio_derivatives={
        'plus_below_one_fifth':plus[1]*88-plus[0]*(-174),
        'plus_one_fifth_to_optimum':plus[1]*16-plus[0]*186,
        'minus_optimum_to_one_quarter':minus[1]*16-minus[0]*186,
        'minus_above_one_quarter':minus[1]-minus[0]*246}
    need(all(v>0 for k,v in ratio_derivatives.items() if k.startswith('plus')) and
         all(v<0 for k,v in ratio_derivatives.items() if k.startswith('minus')),
         'supporting-line-to-fourth-factor ratios increase left of optimum and decrease right')
    floor=hinge_floor()
    def a4(p):
        t=F(1,p-1)
        return 15*t+50*t*t+60*t**3+24*t**4
    r=max(2*ASTAR,1-2*ASTAR);v=max(ASTAR,(1-2*ASTAR)/3)
    factor3=1+15*r+216*v
    fourth=factor3*prod(1+F(p-1,p-2)*a4(p) for p in P)
    need(fourth==F(1995816314082394584902043010164181,6513156637804234575590400000),
         'same unnormalized all-height fourth comparator')
    def tail_factor(cutoff):
        ell=0
        while 3**(ell+1)<=cutoff:ell+=1
        need(cutoff>=286 and ell>=4 and 4*ell>=21,'analytic prime-tail range')
        return F(21609,10240)*F(2*ell*ell+1,2*ell*ell-1)**21*F(cutoff,(cutoff-1)**4)*sum(
            F(factorial(21),factorial(21-j)*(3*ell)**j) for j in range(22))
    tau=tail_factor(1200);remaining=UPPER-fourth*tau
    need(remaining>F(1,10000),'complete1200 tail retains positive distorted mass')
    no3=P+(29,)
    no3mass=2+sum(F(1,p-2) for p in no3)-prod(1+F(1,p-2) for p in no3)
    no3fourth=prod(1+F(p-1,p-2)*a4(p) for p in no3)
    no3remaining=no3mass-no3fourth*tau
    need(no3remaining>F(1,10000),'missing-three branch at same cutoff')
    first_positive=next(c for c in range(729,1301) if UPPER-fourth*tail_factor(c)>0)
    first_3000=next(c for c in range(729,1301) if UPPER-fourth*tail_factor(c)>F(1,3000))
    need(first_positive==1193 and first_3000==1211,'integer cutoff transition in validell6 window')
    return dict(status='exact_arithmetic_passed_not_Lean',optimal_a=ASTAR,
                optimal_b=(1-2*ASTAR)/3,uniform_response=UPPER,
                uniform_response_decimal=float(UPPER),supporting_lines=dict(plus=plus,minus=minus),
                ratio_certificate=dict(derivative_numerators=ratio_derivatives,optimal_mass_over_fourth=UPPER/fourth),
                profiles=dict(A=A,B=B),direct=dict(A=direct_a,B=direct_b),hinge_floor=floor,
                tail=dict(cutoff=1200,ell=6,delta=F(2,7),growth=21,root_cap=r,leaf_cap=v,
                          ternary_fourth_factor=factor3,raw_fourth=fourth,factor=tau,
                          remaining=remaining,remaining_decimal=float(remaining),simple_lower=F(1,10000),
                          missing_three_remaining=no3remaining,first_positive_integer_cutoff=first_positive,
                          first_one_over3000_integer_cutoff=first_3000),
                enumeration=dict(raw_vertices=10000000,canonical_vertices=929408,
                                 refined_vertices=722,skip_baseline=F(1,100)),
                scope='Exact optimum for one globally fixed five-leaf weight vector in the Report791 equal-degree pair-deficit template. Symmetrization reduces arbitrary fixed weights to (a,a,b,b,b). The hinge limitation concerns the source-mass certificate and cap-based comparator together, not actual survivor mass or every possible source. Unrestricted Erdos7 remains open.')


def encode(x):
    if isinstance(x,F):return str(x)
    raise TypeError(type(x).__name__)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--enumeration',type=Path,default=Path(__file__).with_name(Path(__file__).stem+'_enumeration.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate(json.loads(args.enumeration.read_text())),default=encode))
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.write_result:args.write_result.write_text(text)
    else:
        recorded=json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result==recorded,'retained exact result equals fresh computation')
        print('depth-two fixed-weight optimum: exact arithmetic passed')

if __name__=='__main__':main()
