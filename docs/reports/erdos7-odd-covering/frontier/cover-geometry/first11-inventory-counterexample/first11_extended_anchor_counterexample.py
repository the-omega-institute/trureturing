#!/usr/bin/env python3
"""Extend Report558's literal old combs, preserving its first11 table and query.
Coarse residue signatures retain exact conditional tail masses, checked
against direct single-coordinate enumeration at the finite witness.
The existing table is read as data; no other producer is executed.
"""
from fractions import Fraction as F
from collections import defaultdict, Counter
from itertools import product
from math import prod
from pathlib import Path
import argparse, ast, json, hashlib

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=Path(__file__).with_name('first11_inventory_counterexample.py'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
text=args.source.read_text(encoding='utf-8')
node=next(n for n in ast.parse(text).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='TABLE' for t in n.targets))
TABLE=ast.literal_eval(node.value)
SLOTS=[(a,b,r5,r7,g) for a,b,*rows in TABLE for r5,r7,g in rows]
T5=[4,14,14,14];D5=[3]*4;T7=[5,19,19,19];D7=[6]*4
checks={}
def require(name,cond):
    checks[name]=bool(cond)
    if not cond: raise ValueError(name)
def comb(p,h): return F(1,p-1) if h is None else (1-F(1,p**h))/(p-1)
def coordinate_base(p):
    ans=Counter()
    for x in range(p**4):
        if any(x%(p**e) in (p**(e-1),2*p**(e-1)) for e in range(1,5)): continue
        bits=sum(1<<i for i,(a,b,r5,r7,g) in enumerate(SLOTS) if x%(p**(a if p==5 else b))==(r5 if p==5 else r7))
        tt=T5 if p==5 else T7; dd=D5 if p==5 else D7
        tq=sum(x%(p**e)==tt[e-1] for e in range(1,5))
        dq=sum(x%(p**e)==dd[e-1] for e in range(1,5))
        mixed=any(x%(p**e) in tuple(c*p**(e-1) for c in ([3] if p==5 else [3,4])) for e in range(1,5))
        ans[(bits,tq,dq,mixed,x==0)]+=1
    return ans
BASE={p:coordinate_base(p) for p in (5,7)}
def coordinate(p,h):
    out=defaultdict(F)
    for (bits,tq,dq,mixed,zero),count in BASE[p].items():
        mass=F(count,p**4)
        if zero:
            tail=comb(p,None if h is None else h-4)
            mc=1 if p==5 else 2
            out[bits,tq,dq,True]+=mass*mc*tail
            out[bits,tq,dq,False]+=mass*(1-(2+mc)*tail)
        else: out[bits,tq,dq,mixed]+=mass
    return {k:v for k,v in out.items() if v}

def pure_coordinate(p,w): return (w,w+F(1,p-1),lambda n:w-F(1,p) if n==1 else F(p-1,p**n))
def capped_coordinate(p,c): return (F(1),1+c/F(p-1),lambda n:1-c/F(p) if n==1 else c*F(p-1,p**n))
def hinge(coords,t):
    val=prod(x[1] for x in coords)-t*prod(x[0] for x in coords)
    for ns in product(range(1,t),repeat=len(coords)):
        n=prod(ns)
        if n<t: val+=(t-n)*prod(x[2](v) for x,v in zip(coords,ns))
    return val
def pa(x,y):
    coords=[pure_coordinate(5,x),pure_coordinate(7,y)]
    mass=x*y-F(1,12); charges={}
    for p,t,c,a in ((11,2,F(5,3),F(1,3)),(13,2,F(3,2),F(1,4)),(17,4,F(2),F(1,4)),(19,4,F(9,5),F(1,5))):
        charges[p]=hinge(coords,t); mass-=a*charges[p]; coords.append(capped_coordinate(p,c))
    return mass,hinge(coords,3),charges
T=F(257,51)
def gap(x,y):
    m,phi,_=pa(x,y)
    return (T-2)*m-phi
basegap=gap(F(1,2),F(2,3)); kreq=-basegap/(T-2)
A5=2*(gap(F(1),F(2,3))-basegap)
A7=3*(gap(F(1,2),F(1))-basegap)
A57=6*(gap(F(1),F(1))-basegap-A5/2-A7/3)
require('target_constant',kreq==F(6168733163201163811,1650097635185615616000))

def evaluate(h,h11):
    tag=f'H={h},H11={h11}'
    left=coordinate(5,h);right=coordinate(7,h)
    x=sum(left.values(),F());y=sum(right.values(),F())
    mix5=sum(v for k,v in left.items() if k[-1]);mix7=sum(v for k,v in right.items() if k[-1])
    require(tag+'_pure_masses',x==1-2*comb(5,h) and y==1-2*comb(7,h))
    require(tag+'_mixed_masses',mix5==comb(5,h) and mix7==2*comb(7,h))
    profiles=defaultdict(F)
    for (b5,t5,d5,m5),v5 in left.items():
        for (b7,t7,d7,m7),v7 in right.items():
            if m5 and m7: continue
            active=b5&b7
            colors=0
            for i,(_,_,_,_,g) in enumerate(SLOTS):
                if active>>i&1: colors|=1<<g
            require_pure=((colors>>3&1) and (colors>>6&1) and not(colors>>9&1))
            if not require_pure: raise ValueError('wrong pure/query colors')
            profiles[(colors,t5,d5,t7,d7)]+=v5*v7
    oldmass=sum(profiles.values(),F());mixedmass=mix5*mix7
    require(tag+'_oldmass',oldmass==x*y-mixedmass)
    beta4=comb(11,4);beta_pure=comb(11,h11)
    newmass=F();queryhinge=F();hist=defaultdict(F)
    for (colors,t5,d5,t7,d7),mass in profiles.items():
        K=colors.bit_count();g=1-(K-2)*beta4-2*beta_pure
        hden=min(F(5,3),1/g)
        L0=1+t5+d7+d5*d7;M=1+t5+d7+d5*t7
        raw=max(L0-2,0)*g+M*beta4-(F(1,11) if L0==1 else F())
        newmass+=mass*hden*g;queryhinge+=mass*hden*raw;hist[K]+=mass
    _,phi,charges=pa(x,y)
    loss=oldmass-newmass;S11=charges[11]/3-loss
    d5=x-F(1,2);d7=y-F(2,3)
    credit=(A5*d5+A7*d7+A57*d5*d7)/(T-2)+F(1,12)-mixedmass
    score=credit+S11+(charges[13]-queryhinge)/4
    result={'H':h,'H11':h11,'old_pure5_mass':x,'old_pure7_mass':y,'old_mixed_mass':mixedmass,'old_mass':oldmass,'lambda11_mass':newmass,'Delta11':loss,'F11':charges[11],'S11':S11,'F13':charges[13],'Hquery':queryhinge,'credit':credit,'score':score,'kreq':kreq,'failure_margin':kreq-score,'profiles_count':len(profiles),'histK':dict(hist)}
    if h==h11==4:
        require('recover_report558_oldmass',oldmass==F(53759,214375))
        require('recover_report558_queryhinge',queryhinge==F(112300666826237333,616568590178165625))
        require('recover_report558_S11',S11==F(20023321,143807895000))
        require('recover_report558_credit',credit==F(18036721551129456405721,27793832042657713032000000))
        require('recover_report558_repaired_margin',score-kreq==F(33476345951531543898470383,67665083232531474385696000000))
    return result

rows=[]
for h in (4,5,6,7,8,10,20,None):
    for h11 in ((4,) if h==4 else (4,h)):
        row=evaluate(h,h11);rows.append(row)
        print('H',h,'H11',h11,'credit',float(row['credit']),'S11',float(row['S11']),'F13-Hq',float(row['F13']-row['Hquery']),'score',float(row['score']),'failure',float(row['failure_margin']))


# Direct one-coordinate scans at the concrete H=5 witness independently
# validate the coarse tail weights without a joint 5^5*7^5 scan.
for p in (5,7):
    counts=Counter()
    tt=T5 if p==5 else T7; dd=D5 if p==5 else D7
    for z in range(p**5):
        if any(z%(p**e) in (p**(e-1),2*p**(e-1)) for e in range(1,6)): continue
        bits=sum(1<<i for i,(a,b,r5,r7,g) in enumerate(SLOTS) if z%(p**(a if p==5 else b))==(r5 if p==5 else r7))
        tq=sum(z%(p**e)==tt[e-1] for e in range(1,5))
        dq=sum(z%(p**e)==dd[e-1] for e in range(1,5))
        mixed=any(z%(p**e) in tuple(c*p**(e-1) for c in ([3] if p==5 else [3,4])) for e in range(1,6))
        counts[bits,tq,dq,mixed]+=1
    direct={k:F(v,p**5) for k,v in counts.items()}
    require('direct_H5_coordinate_'+str(p),direct==coordinate(p,5))

def crt(parts):
    parts=[(m,r%m) for m,r in parts if m>1]
    modulus=prod(m for m,r in parts)
    residue=sum(r*(modulus//m)*pow(modulus//m,-1,m) for m,r in parts)%modulus
    if any(residue%m!=r for m,r in parts): raise ValueError('CRT failure')
    return {'modulus':modulus,'residue':residue,'components':parts}
originals=[]
for p in (5,7):
    for e in range(1,6):
        for color in (1,2): originals.append(crt([(p**e,color*p**(e-1))]))
for a,b in product(range(1,6),repeat=2):
    for color7 in (3,4): originals.append(crt([(5**a,3*5**(a-1)),(7**b,color7*7**(b-1))]))
require('actual_old_original_count',len(originals)==70)
for a,b,r5,r7,g in SLOTS:
    for c in range(1,5):
        originals.append(crt([(5**a,r5),(7**b,r7),(11**c,(g+1)*11**(c-1)-1)]))
queries=[]
for a,b,c in product(range(5),repeat=3):
    if not(a or b or c): continue
    if a and b: r5=D5[a-1];r7=(T7 if c else D7)[b-1]
    else: r5=T5[a-1] if a else 0;r7=D7[b-1] if b else 0
    parts=[(5**a,r5),(7**b,r7)]
    if c: parts.append((11**c,9))
    queries.append(crt(parts))
counts=Counter(x['modulus'] for x in originals)
require('actual270_originals135_labels',len(originals)==270 and len(counts)==135)
require('actual_exactly_two_per_label',set(counts.values())=={2})
require('actual270_distinct_modulus_residue_pairs',len({(x['modulus'],x['residue']) for x in originals})==270)
require('query124_distinct_labels',len(queries)==124 and len({x['modulus'] for x in queries})==124)
require('all_CRT_normalized_odd_nonunit',all(x['modulus']>1 and x['modulus']%2==1 and 0<=x['residue']<x['modulus'] for x in originals+queries))
witness=next(row for row in rows if row['H']==5 and row['H11']==4)
require('finite_anchorcredit_refutation',witness['failure_margin']>0)

def encode(v):
    if isinstance(v,F): return str(v)
    if isinstance(v,dict): return {str(k):encode(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [encode(x) for x in v]
    return v
result={'source_table_sha256':hashlib.sha256(text.encode()).hexdigest(),'TABLE':TABLE,'NC4':{'A5':A5,'A7':A7,'A57':A57,'kreq':kreq},'rows':rows,'candidate_originals':originals,'fixed124_query':queries,'checks':checks,'scope':'finite fixed globally phased at-most-two-copy originals; fixed124query; refutes only anchorcredit+two-row-saving criterion when margin positive; infinite H is a limit diagnostic'}
args.output.write_text(json.dumps(encode(result),indent=2)+'\n',encoding='utf-8')
print(json.dumps({'passed_checks':len(checks),'finite_score':str(witness['score']),
                  'failure_margin':str(witness['failure_margin']),
                  'json_sha256':hashlib.sha256(args.output.read_bytes()).hexdigest()}))
