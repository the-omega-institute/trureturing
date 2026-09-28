#!/usr/bin/env python3
"""Four explicit191-original layouts on two fixed heads; exact joint packets, no LP."""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json,hashlib

BIG=(11,13,17,19)
LEAVES=(4,7,2,5,8) # actual pure0mod3 and1mod9 removed
ROOTS=((0,1),(2,3,4))
W=(F(1,4),F(1,4),F(1,6),F(1,6),F(1,6))
LIVE5=tuple(range(1,5));LIVE7=tuple(range(1,7))
SUPPORTS=tuple(d for d in range(1,16) if d.bit_count()>=2)
PAIRS=tuple((d,15^d) for d in SUPPORTS if d.bit_count()==2 and d<(15^d))
COFACTORS=tuple((h,a,b,3**h*5**a*7**b) for h,a,b in product(range(3),range(2),range(2)))
HEAD_LAYOUTS=(
    ('opposite_root',((3,0),(9,1),(5,0),(7,0),(15,11),(45,2),(21,1),(63,58),(35,3),(105,74),(315,187)),F(47663,23808)),
    ('same_root',((3,0),(9,1),(5,0),(7,0),(15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)),F(18015,8704)),
)
TAU=F(17978,98175)
TARGET=F(566,49)


def need(x,msg):
    if not x:raise RuntimeError(msg)


def mul(xs):return prod(xs,start=F(1))


def crt(components):
    x,m=0,1
    for n,a in sorted(components.items()):
        x+=m*((a-x)*pow(m,-1,n)%n);m*=n
    need(all(x%n==a for n,a in components.items()),'one actual CRT phase')
    return x%m,m


def head_accept(u,components):
    l,r,s=u
    return all((LEAVES[l]%q if q in (3,9) else r if q==5 else s)==a
               for q,a in components.items())


def response(m,k,V):
    z=mul(m[i] for i in range(4) if V>>i&1)
    z-=sum((k[d]*mul(m[i] for i in range(4) if V>>i&1 and not d>>i&1)
            for d in SUPPORTS if d&V==d),F(0))
    if V==15:z+=sum((k[d]*k[e] for d,e in PAIRS),F(0))
    return z


def shifted_head(h,a,b,c,shift,head_layout):
    old=head_layout.get(c,{})
    r={}
    if h==1:r[3]=1+((old.get(3,1)-1)+shift)%2
    if h==2:
        leaf_index=LEAVES.index(old[9]) if old.get(9) in LEAVES else 0
        r[9]=LEAVES[(leaf_index+shift)%5]
    if a:r[5]=1+((old.get(5,1)-1)+shift)%4
    if b:r[7]=1+((old.get(7,1)-1)+shift)%6
    return r


def build(name,head_layout):
    originals=[(*crt(comp),comp,{}) for comp in head_layout.values()]
    originals += [(0,q,{}, {q:0}) for q in BIG]
    outside=[]
    for D in range(1,16):
        for ci,(h,a,b,c) in enumerate(COFACTORS):
            if c==1 and D.bit_count()==1:continue
            if name=='aligned':head=head_layout.get(c,{}).copy()
            elif name=='spread':head=shifted_head(h,a,b,c,D+ci,head_layout)
            else:raise RuntimeError('unknown fixed outside layout')
            roots={q:(1 if name!='spread' else 1+(3*D+2*ci+i)%(q-1))
                   for i,q in enumerate(BIG) if D>>i&1}
            value,modulus=crt(head|roots)
            need(modulus==c*prod(q for i,q in enumerate(BIG) if D>>i&1),'original full numerical label')
            outside.append((D,head,roots))
            originals.append((value,modulus,head,roots))
    need(len(originals)==191 and len({m for _,m,_,_ in originals})==191,'191 distinct original odd labels')
    return originals,outside


def conditional_data(name,head_pairs):
    head_layout={}
    for modulus,value in head_pairs:
        components={}
        if modulus%9==0:components[9]=value%9
        elif modulus%3==0:components[3]=value%3
        for q in (5,7):
            if modulus%q==0:components[q]=value%q
        need(crt(components)==(value,modulus),'literal head original phase')
        head_layout[modulus]=components
    originals,outside=build(name,head_layout)
    cells={}
    legal=positive=0
    for u in product(range(5),LIVE5,LIVE7):
        if any(head_accept(u,c) for n,c in head_layout.items() if n not in (3,9,5,7)):
            continue
        legal+=1
        active={D:[] for D in range(1,16)}
        for D,head,roots in outside:
            if head_accept(u,head):active[D].append(roots)
        allowed=[set(range(1,q))-{v[q] for v in active[1<<i]} for i,q in enumerate(BIG)]
        m=tuple(F(len(allowed[i]),q-1) for i,q in enumerate(BIG))
        k={}
        for D in SUPPORTS:
            ids=[i for i in range(4) if D>>i&1]
            patterns={tuple(v[BIG[i]] for i in ids) for v in active[D]
                      if all(v[BIG[i]] in allowed[i] for i in ids)}
            k[D]=F(len(patterns),prod(BIG[i]-1 for i in ids))
            need(k[D]<=mul(m[i] for i in ids),'actual union cap on same unary survivor product')
        z=response(m,k,15)
        if z<=0:continue
        positive+=1
        hs=tuple(response(m,k,15^T) for T in range(16))
        need(all(v>0 for v in hs),'all conditional response supports positive')
        cells[u]=hs
    return originals,cells,legal,positive


def run(name,head_name,head_pairs,scalar_minimum):
    originals,cells,legal,positive=conditional_data(name,head_pairs)
    source=sum((W[u[0]]*hs[0]/24 for u,hs in cells.items()),F(0))
    # Uniform live-root rho makes first and deep modes proportional;
    # this exactly groups the same27 head mode upper screens.
    c5=F(1,4)+F(1,15);c7=F(1,6)+F(1,35)
    complete=F(0)
    for T in range(16):
        coefficient=mul(F(1,q-2) for i,q in enumerate(BIG) if T>>i&1)
        for ports in ((tuple(range(5)),),ROOTS,tuple((l,) for l in range(5))):
            matrices=[[[sum((W[l]*cells.get((l,r,s),(F(0),)*16)[T] for l in port),F(0))
                        for s in LIVE7] for r in LIVE5] for port in ports]
            whole=max(sum((v for row in a for v in row),F(0)) for a in matrices)/24
            q5=max(sum(a[i],F(0)) for a in matrices for i in range(4))*c5/6
            q7=max(sum((a[i][j] for i in range(4)),F(0)) for a in matrices for j in range(6))*c7/4
            both=max(v for a in matrices for row in a for v in row)*c5*c7
            complete+=coefficient*(whole+q5+q7+both)
    k=complete-source
    need(k>=0,'nonunit query cost')
    need(source>TAU and TARGET*(source-TAU)>k,'strict gate for this actual common-source layout')
    payload=[{'a':a,'m':m} for a,m,_,_ in sorted(originals,key=lambda x:x[1])]
    digest=hashlib.sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest()
    return dict(head_layout=head_name,head_originals=head_pairs,head_scalar_minimum_from_separate_certificate=str(scalar_minimum),
        direct_nine_prime_target='8038/4235',layout=name,original_count=len(originals),original_phase_sha256=digest,
        actual_originals=payload,head_pure_live_cells=120,head_seven_label_legal_cells=legal,
        positive_conditional_cells=positive,S=str(source),S_decimal=float(source),
        full_generic_tail=str(TAU),S_minus_generic_tail=str(source-TAU),
        S_minus_generic_tail_decimal=float(source-TAU),actual_head_deep_tail='0',
        K=str(k),K_decimal=float(k),generic_tail_gate=str(TARGET*(source-TAU)-k),
        generic_tail_gate_decimal=float(TARGET*(source-TAU)-k),
        actual_zero_tail_gate=str(TARGET*source-k),
        actual_zero_tail_gate_decimal=float(TARGET*source-k))


def calculate():
    cases=[run(layout,head,pairs,minimum) for head,pairs,minimum in HEAD_LAYOUTS for layout in ('aligned','spread')]
    out=dict(scope='Four explicitly specified finite191-original odd families using the two literal scalar-obstructed heads with all nonternary exponents1 and ternary exponent<=2. f is the actual seven-label legal mask. No global profile assertion, LP or phase scan.',
             pure_originals='0mod3,1mod9,0mod5,0mod7,0mod11,0mod13,0mod17,0mod19',
             query_target=str(TARGET),cases=cases)
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
