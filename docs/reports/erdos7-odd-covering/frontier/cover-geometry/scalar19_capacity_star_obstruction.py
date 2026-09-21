#!/usr/bin/env python3
"""Exact finite-horizon capacities of the inherited T6 scalar recurrence."""
from fractions import Fraction as F
from math import isqrt
from decimal import Decimal, localcontext
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

CERTIFICATE = "certificates/source_norms/cover-geometry/scalar19_capacity_star_obstruction.json"
PINS = {
 "certificates/star_survivor_obstruction_certificate.json": "423c440beceb2805b69905c0f07aece3a6412eb453f673648b10d11fbd95a1e8",
 "problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md": "4bdbb770b9d1f11abec52ba6fd3f814e81e5ea5da7a93e7a5c125af85dccc32d",
 "problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md": "e7bfef78a6774051abee44bc1888fa27be24ad3786eeca0bb8f91ff57a440dc7",
}

PRIMES=(23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127)
GRID=10**36

def require(ok, msg):
    if not ok: raise ValueError(msg)

def root_interval(x):
    n=isqrt(x.numerator*GRID*GRID//x.denominator)
    lo,hi=F(n,GRID),F(n+1,GRID)
    require(lo*lo<=x<hi*hi,'Integer square root enclosure')
    return lo,hi

def capacity_interval(p,H):
    a=F(3*p-1,(p-1)**2); b=F(1,4*(p-1)**2)
    s,t=root_interval(H*b*(a+H*b))
    return H/(1+a+2*H*b+2*t),H/(1+a+2*H*b+2*s)

def rounded_interval(lo,hi):
    return F(lo.numerator*GRID//lo.denominator,GRID),F(-((-hi.numerator*GRID)//hi.denominator),GRID)

def forward(p,f):
    a=F(3*p-1,(p-1)**2); b=F(1,4*(p-1)**2)
    lo,hi=root_interval(1+a*(1+a)/(b*f))
    d=(1+a)/(1+(lo+hi)/2)
    D=1-b*f/(d*(1-d))
    require(0<d<=F(1,2) and D>0,'Strict original T6 domain')
    out=(1+a/(1-d))*f/D
    rounded=F(-((-out.numerator*GRID)//out.denominator),GRID)
    require(rounded>=out,'Directed upward forward bound')
    return rounded,{'prime':p,'input':str(f),'delta':str(d),'denominator':str(D),'output_upper':str(rounded)}

def calculate():
    require(PRIMES==tuple(n for n in range(23,128) if all(n%d for d in range(2,isqrt(n)+1))),
            'Every consecutive prime from23 through127')
    rows=[]
    for end,q in enumerate(PRIMES):
        lo=hi=F((q-1)**2)
        backward=[]
        for p in reversed(PRIMES[:end]):
            lo2=capacity_interval(p,lo)[0];hi2=capacity_interval(p,hi)[1]
            lo,hi=rounded_interval(lo2,hi2)
            backward.append({'prime':p,'capacity_lower':str(lo),'capacity_upper':str(hi)})
        require(0<lo<=hi and hi-lo<F(1,10**30),'Positive sharp directed capacity interval')
        seed=F(lo.numerator*10**12//lo.denominator-1,10**12)
        f=seed;steps=[]
        for p in PRIMES[:end+1]:
            f,record=forward(p,f);steps.append(record)
        if q==29:
            require(F(271244178927890,10**12)<lo<=hi<F(271244178927891,10**12),'Matches existing exact 23 to 29 boundary')
        rows.append({'through_prime':q,'seed_capacity_lower':str(lo),'seed_capacity_upper':str(hi),'backward':backward,'forward_seed':str(seed),'forward_steps':steps})
    require(all(F(a['seed_capacity_lower'])>F(b['seed_capacity_upper']) for a,b in zip(rows,rows[1:])),'Every additional required prime strictly reduces capacity')
    return {'schema':'erdos7-scalar19-finite-capacities-v1','method':'Existing all-height T6 with arbitrary continuous delta in (0,1/2]','rows':rows,'scope':'Exact finite-horizon scalar-method feasibility; no actual-family lower bound or unrestricted continuation claim.'}

def source_data(base):
    spec=importlib.util.spec_from_file_location('scalar_star_io',base/'certificate_io.py')
    io=importlib.util.module_from_spec(spec);spec.loader.exec_module(io)
    for rel,pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/rel)).hexdigest()==pin,'Pinned mathematical source '+rel)
    star=json.loads(io.read_artifact_bytes(base/'certificates/star_survivor_obstruction_certificate.json'))
    head=(3,5,7,11,13,17,19)
    require(star['height_3']==31 and star['height_other']==8 and star['tree_depth']==8 and star['scale']==10000,'Original finite star heights and potential scale')
    rows=[r for r in star['rows'] if r['prime']<=19]
    require(tuple(r['prime'] for r in rows)==head,'All seven original head primes')
    B=F(1);D=F(32**2)
    for row in rows:
        p=row['prime']
        require(row['side_children']==(1 if p==3 else p-3),'Original side-child tree supports')
        B*=F(row['m'],star['scale'])
        if p>3:D*=F(p+2,p-1)
    lower=min(D/100,99*B/100)
    require(D==F(12103,2) and lower==99*B/100 and lower>F(53718,1000),'Both actual-star branches exceed the uniform lower')
    return io,{'head_primes':list(head),'height3':31,'other_heights':8,'original_coordinate_floors':[r['m'] for r in rows],'branch_a_potential':str(D),'branch_b_potential_lower':str(B),'mixture_weight_a':'1/100','mixture_weight_b':'99/100','uniform_gamma_lower':str(lower)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io,star=source_data(args.base)
    data=calculate()
    data['source_sha256']=PINS
    data['actual_star']=star
    L=F(star['uniform_gamma_lower'])
    failures=[row for row in data['rows'] if F(row['seed_capacity_upper'])<L]
    require(failures and failures[0]['through_prime']==101,'First tested finite horizon excluded by this actual-star lower')
    row=failures[0]
    data['first_obstructed_horizon']=101
    data['star_lower_minus_capacity_upper']=str(L-F(row['seed_capacity_upper']))
    data['scope']='The existing actual finite star family forces every supported19 law above the exact capacity of the inherited full-height worst-case scalar T6 through101, even with continuous controls. This excludes an unqualified universal scalar restart at19. Family-aware skipping, finite-height bounds, joint estimates and actual noncoverage are not refuted; the star itself has explicit survivors.'
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(data,indent=2)+'\n')
    else:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))==data,'Exact finite capacities, forward controls and actual-star comparison')
    with localcontext() as ctx:
        ctx.prec=32
        for q in (29,73,97,101,127):
            row=next(r for r in data['rows'] if r['through_prime']==q)
            x=F(row['seed_capacity_lower'])
            print('through prime',q,'capacity lower',Decimal(x.numerator)/Decimal(x.denominator))
        print('actual-star uniform Gamma19 lower',Decimal(L.numerator)/Decimal(L.denominator))
    print('PASS:23 finite horizons; exact backward intervals;276 original forward steps; actual scalar-route obstruction')

if __name__=='__main__':
    main()
