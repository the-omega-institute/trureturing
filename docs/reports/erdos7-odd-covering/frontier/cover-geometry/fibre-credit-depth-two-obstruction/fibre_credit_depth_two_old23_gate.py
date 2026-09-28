#!/usr/bin/env python3
"""Exact all-domain target19100 using the fixed six-direction hinge dual."""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
from pathlib import Path
from collections import Counter
from bisect import bisect_right
from hashlib import sha256
import json

DEPENDENCIES={'fibre_credit_depth_two_six_fresh_heights.json': '0f2d3de762fe183103ba4a01165f6138f59dfc1991a8d40831423ce16e06db35'}
D=256
LAMBDA_STEPS=4096
MAX_NODES=3000000

def require(ok,msg):
    if not ok:raise RuntimeError(msg)

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        require(sha256((directory/name).read_bytes()).hexdigest()==digest,
                'pinned preceding fixed six-direction certificate: '+name)
    previous=json.loads((directory/'fibre_credit_depth_two_six_fresh_heights.json').read_text())
    fixed=dict(previous['fixed_penalties'])
    require(fixed['target']==19000,'unchanged earlier fixed coefficients')
    fixed['target']=19100
    for key in ('unary_expected_cost','total_expected_cost','target_minus_cost'):
        fixed.pop(key,None)
    R=tuple(fixed['capacities']);thresholds=tuple(fixed['thresholds']);coeffs=tuple(tuple(row) for row in fixed['unary_hinge_coefficient_numerators']);knots=tuple(fixed['Y_knots'])
    require(fixed['kappa']=='1/5000' and fixed['coefficient_denominator']==100 and fixed['target']==19100,'fixed rational candidate')
    require(R==(28,30,36,40,42,46) and len(coeffs)==6 and all(len(row)==len(thresholds) for row in coeffs),'six unary penalties')
    require(all(c>=0 for row in coeffs for c in row),'convex nondecreasing unary penalties')
    TARGET=19100;E=5000*LAMBDA_STEPS
    slopes=tuple(a+b for a,b in zip(knots,knots[1:]));comps=tuple(combinations(range(6),4));corners=tuple(product((0,1),repeat=6))
    active_terms=tuple(tuple((t,c) for t,c in zip(thresholds,row) if c) for row in coeffs)
    def unary_num(a,den):return sum(c*max(a[i]-t*den,0) for i in range(6) for t,c in active_terms[i])
    def bdata(u):
        P=prod(u)
        if min(u)>0:return P,tuple(P//u[i]//u[j] for i,j in combinations(range(6),2))
        return P,tuple(prod(u[i] for i in J) for J in comps)
    def pair_selection(T,bs,den):return tuple(knots[bisect_right(slopes,(T*b)//(E*den**4))] for b in bs)
    def center_lambda(center):
        den=2*D;u=tuple(R[i]*den-center[i] for i in range(6));P,bs=bdata(u)
        def derivative(T):
            vv=pair_selection(T,bs,den)
            return P-den**2*sum(b*v for b,v in zip(bs,vv))
        if derivative(0)<=0:return 0
        if derivative(LAMBDA_STEPS)>=0:return LAMBDA_STEPS
        lo=0;hi=LAMBDA_STEPS
        while hi-lo>1:
            md=(lo+hi)//2
            if derivative(md)>0:lo=md
            else:hi=md
        def value(T):
            vv=pair_selection(T,bs,den)
            return T*(P-den**2*sum(b*v for b,v in zip(bs,vv)))+E*den**6*sum(v*v for v in vv)
        return max((lo,hi),key=value)
    nodes=0;leaves=0;volume=0;depth_counts=Counter();branch_counts=Counter()
    stack=[((D,)*6,tuple(r*D for r in R),0)]
    E_D5=E*D**5;E_D6=E*D**6;rhs=TARGET*100*E_D6
    while stack:
        low,high,depth=stack.pop();nodes+=1
        if unary_num(low,D)+1500*D>=TARGET*100*D:
            accepted=True;branch='unary-and-lambda-zero'
        else:
            center=tuple(low[i]+high[i] for i in range(6));T=center_lambda(center)
            # Choose one actual affine piece at the center; it supports the convex unary penalty globally.
            unary_slopes=tuple(sum(c for t,c in active_terms[i] if center[i]>=t*2*D) for i in range(6))
            unary_intercept=-sum(c*t for i in range(6) for t,c in active_terms[i] if center[i]>=t*2*D)
            accepted=True;branch='supporting-affine-and-concave-corners'
            for bits in corners:
                a=tuple(high[i] if bits[i] else low[i] for i in range(6));u=tuple(R[i]*D-a[i] for i in range(6));P,bs=bdata(u)
                vv=pair_selection(T,bs,D)
                line=sum(unary_slopes[i]*a[i] for i in range(6))+unary_intercept*D
                lhs=line*E_D5+100*T*(P-D**2*sum(b*v for b,v in zip(bs,vv)))+100*E_D6*sum(v*v for v in vv)
                if lhs<rhs:
                    accepted=False;break
        if accepted:
            leaves+=1;volume+=prod(high[i]-low[i] for i in range(6));depth_counts[depth]+=1;branch_counts[branch]+=1
        else:
            widths=tuple(high[i]-low[i] for i in range(6));j=max(range(6),key=lambda k:widths[k]);mid=(low[j]+high[j])//2
            require(widths[j]>1,'exact grid exhausted: '+str((low,high,depth,'lambda',T,'corner',a,'lower',F(lhs,100*E_D6))))
            high1=list(high);high1[j]=mid;low2=list(low);low2[j]=mid
            stack.append((tuple(low2),high,depth+1));stack.append((low,tuple(high1),depth+1))
        require(nodes<=MAX_NODES,'node cap exceeded before full coverage')
    full_volume=prod((r-1)*D for r in R)
    require(volume==full_volume and nodes==2*leaves-1,'complete binary enclosure and exact volume')
    outside=min(F(sum(c*max(R[i]-t,0) for t,c in active_terms[i]),100)+15 for i in range(6))
    require(outside>=TARGET,'outside box follows from one unary penalty and lambda0 pair baseline')
    out={'scope':'Exact all-real scalar gate19100 with the earlier six-direction coefficients. No new-source density is computed here; ordinary, not Lean.',
         'fixed_penalties':fixed,'dependency_hashes':DEPENDENCIES,
         'grid_denominator':D,'lambda_steps':LAMBDA_STEPS,'target':TARGET,
         'nodes':nodes,'leaves':leaves,'depths':dict(sorted(depth_counts.items())),
         'branches':dict(branch_counts),'box_volume':prod(r-1 for r in R),
         'accepted_volume_numerator':str(volume),'full_volume_numerator':str(full_volume),
         'outside_lower':str(outside),'complete_exact_enclosure':True}
    return out
def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        require(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
                'retained result agrees with old23 scalar gate19100')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':main()
