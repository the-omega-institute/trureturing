#!/usr/bin/env python3
"""Exact height-lifting formulas and a fixed-component joint-cost obstruction.
Standard library only; writes stdout only. No Lean certification.
These calculations grant the distinct-label residual premise of Chapter09;
429's abstract projection-source theorem does not itself supply that premise.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import runpy
from math import isqrt
from collections import defaultdict
import json

SCALE = 10**30

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sqrt_interval(x):
    require(x >= 0, 'nonnegative radicand')
    k = isqrt(x.numerator * SCALE**2 // x.denominator)
    lo, hi = F(k, SCALE), F(k+1, SCALE)
    require(lo*lo <= x < hi*hi, 'rational square-root enclosure')
    return lo, hi

def display(interval):
    lo, hi = interval
    scale = 10**15
    a = lo.numerator*scale // lo.denominator
    b = -(-hi.numerator*scale // hi.denominator)
    return [str(F(a, scale)), str(F(b, scale))]

def lambda_interval(c, k7=None):
    roots = sqrt_interval(c)
    answer=[]
    for s in roots:
        q=F(1,4)*min(s/2,c/4,(c-1)/3)
        if k7 is not None:
            d=F(k7)
            q+=F(1,6)*min(s/d,c/d**2,(c-1)/(d**2-1))
            q+=F(1,24)*min(s/(2*d),c/(4*d**2),(c-1)/(4*d**2-1))
        answer.append(q)
    return tuple(answer)

def lift(c, extra, lambdas, coarse=None):
    coarse = c if coarse is None else coarse
    lo,hi=lambdas
    require(0 <= lo <= hi < 1, 'positive survivor denominators')
    numerator=c+coarse*extra
    require(numerator >= 1, 'monotonicity in lambda')
    return ((numerator-lo)/(1-lo),(numerator-hi)/(1-hi))

def extra(K,h):
    require(1 <= h <= K, 'coarse height within seed')
    k=F(h+1); r=K-h
    infinity=1+F(1,3)/k+F(2,9)/k**2
    old=1+2*sum((F(1,7**i) for i in range(1,r+1)),F())/k
    old+=sum((F(2*i-1,7**i) for i in range(1,r+1)),F())/k**2
    E=F(43,32)*infinity-old
    require(infinity >= old >= 1 and E >= F(11,32), 'unavoidable five-height cost')
    return E

def square_load(point, phases):
    row,y=point
    divisors=(1,5,7,35,49,245)[:len(phases)]
    count=0
    for d,a in zip(divisors,phases):
        if d%5:
            count+=int(y%d==a)
        else:
            count+=int(row==a%5 and y%(d//5)==a%(d//5))
    return count*count

def check_law(law, rows, b):
    require(sum(law.values())==1 and all(w>0 for w in law.values()),'probability')
    require(all(r in rows and 0<=y<49 for r,y in law),'literal support')
    for j in range(3):
        masses=defaultdict(F)
        for (_,y),w in law.items():
            masses[y%7**j]+=w
        require(max(masses.values())<=F(1,b**j),'whole-prefix cap')

def fixed_component_obstruction():
    fixture = runpy.run_path(str(Path(__file__).with_name('fixed_cap_mixture_boundary.py')))['boundary_payload']()
    require(fixture['height']==2, 'height-two fixture')
    expected_keys=('full','12','13','14','23','24','34')
    require(tuple(fixture['laws'])==expected_keys, 'all seven original components')
    laws={}
    for name,entries in fixture['laws'].items():
        law={}
        for row,y,mass in entries:
            require((row,y) not in law, 'distinct fixture atoms')
            law[row,y]=F(mass)
        laws[name]=law
    layouts=tuple(tuple(item['phases']) for item in fixture['theta'])
    require(layouts==((0,1,0,21,0,196),(0,2,1,22,1,197),(0,3,2,23,2,198)),
            'all original layout phases retained')
    require(all(F(item['weight'])==F(1,3) for item in fixture['theta']), 'equal common layout weights')
    result={}
    w=F(16099,10080); target=F(152,15)
    for name,law in laws.items():
        check_law(law,(1,2,3,4) if name=='full' else tuple(map(int,name)),5 if name=='full' else 3)
        high=sum((mass*square_load(point,L) for L in layouts for point,mass in law.items()),F())/3
        low=sum((mass*square_load(point,L[:4]) for L in layouts for point,mass in law.items()),F())/3
        result[name]=(high,low,high+w*low)
    require(tuple(v[:2] for v in result.values())==
            ((F(26,5),F(22,5)),(F(20,3),F(5)),(F(20,3),F(5)),
             (F(46,9),F(4)),(F(20,3),F(5)),(F(46,9),F(4)),(F(46,9),F(4))),
            'literal high/coarse component prices')
    lower=min(v[2] for v in result.values())
    require(lower==F(28979,2520) and lower-target==F(3443,2520),'strict mixture obstruction')
    # This is a lower witness for every mixture of these fixed laws only.
    return {'prices':result,'min_joint_price':lower,'target':target,'gap':lower-target}

def partitions(n):
    def rec(word):
        if len(word)==n:
            yield word
        else:
            for a in range(max(word)+2):
                yield from rec(word+(a,))
    yield from rec((0,))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compact',action='store_true')
    args=parser.parse_args()
    C=F(46,9)
    require(F(43,32)==1+F(1,4)+F(3,32),'five coefficient')
    lower5=lift(C,F(11,32),lambda_interval(C))
    require(lower5[0]>9,'new height-two seed misses all-height nine target')
    x=9-F(43,32)*C
    require(x==F(307,144) and C-x*x==F(11735,20736)>0,'exact no-nine comparison')
    sqlo,sqhi=sqrt_interval(F(790))
    critical=(16*(sqlo-4)**2/F(1849),16*(sqhi-4)**2/F(1849))
    require(critical[1]<C,'necessary seed threshold')
    seeds={1:F(4),2:C,3:F(146409,26585),4:F(1716541,301925)}
    values={}
    for K,c in seeds.items():
        values[K]={h:display(lift(c,extra(K,h),lambda_interval(c,h+1))) for h in range(1,K+1)}
        if K>=2:
            require(c>=C,'all displayed higher seeds exceed height-two seed')
    k1=lift(F(4),extra(1,1),lambda_interval(F(4),2))
    require(k1[0]==k1[1]==F(2212,207)>9,'exact height-one baseline')
    require(extra(2,1)==F(935,2016),'K2 smoothing extra')
    coarse_four=lift(F(4),extra(2,1),lambda_interval(F(4),2))
    require(coarse_four[0]==coarse_four[1]==F(13684,1449)
            and coarse_four[0]-9==F(643,1449),'all coarse costs at least four fail S2')
    a=F(17,120); E=extra(2,1)
    require(a==F(1,12)+F(1,18)+F(1,360),'lambda coefficient for coarse C<=4')
    root_threshold=(9-C+8*a)/(E+8*a)
    require(root_threshold==F(50624,16099),'same-law root threshold')
    require(E+8*a==F(16099,10080) and 9+8*a==F(152,15),'joint half-plane')
    require(F(16,5)-root_threshold==F(4464,80495)>0,'rectangle root lower gap')
    # Uniform centered root-layout mixture on a 3x5 rectangle costs 16/5 at every point.
    for point in product((1,2,3),range(5)):
        total=0
        for row,y in product((1,2,3),range(5)):
            phase=next(z for z in range(35) if z%5==row and z%7==y)
            total+=square_load(point,(0,row,y,phase))
        require(F(total,15)==F(16,5),'every root law has the rectangle lower bound')
    ps=list(partitions(6))
    equal=sum(word[2]==word[3] for word in ps)
    require(len(ps)==203 and equal==52 and (len(ps)+equal)*4**5==261120,'independent paired-layout orbit count')
    # A freely chosen law on the same full carrier meets the target.
    full_high=F(7,4)*sum((F(2*j+1,7**j) for j in range(3)),F())
    full_low=F(7,4)*sum((F(2*j+1,7**j) for j in range(2)),F())
    require(full_high==F(75,28) and full_low==F(5,2),'full-carrier product-law values')
    require(full_high+F(16099,10080)*full_low<F(152,15),'free source law not refuted')
    require(F(18,5)+F(16099,10080)*F(16,5)<F(152,15),'rectangle joint tradeoff remains feasible')
    print(json.dumps({'scope':'conditional Chapter09 arithmetic and an actual fixed-component counterexample; not Lean; not an E7 head-extraction theorem',
        'five_only_optimistic_all_height_bound':display(lower5),
        'necessary_seed_C_for_target9':display(critical),
        'S1_full_two_prime_bounds':values,
        'S2_K2_root_threshold':root_threshold,
        'S2_joint_halfplane':{'high_coefficient':1,'coarse_coefficient':F(16099,10080),'target':F(152,15),'coarse_regime':'1<=C_h<=4, same original law'},
        'fixed_component_obstruction':fixed_component_obstruction(),
        'paired_layout_columns':261120,
        'free_full_carrier_costs':(full_high,full_low),
        'verification':'exact Fraction identities, rational root intervals, literal original predicates; not Lean'},default=str,indent=None if args.compact else 2))

if __name__=='__main__':
    main()
