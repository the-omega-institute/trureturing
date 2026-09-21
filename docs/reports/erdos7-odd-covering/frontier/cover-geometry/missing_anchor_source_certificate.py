#!/usr/bin/env python3
"""Exact source-row audit for selected eight-prime cores missing 3 and/or 5.

This is deliberately conditional.  It checks the pinned ordinary source rows,
exact marginal-cap products, Chapter-31 conditional-kernel arithmetic for the
missing-5 outside-root placement, and the resulting rational margins.  It does
not prove the source transport for a target anchor permutation, the root
orientation/gluing lemma, or unrestricted Erdos--Selfridge #7.
"""
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from hashlib import sha256
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import json

BASE = Path(__file__).resolve().parent
GEOM=BASE/'six_prime_prefix_geometry.json'; GH=BASE/'six_prime_prefix_certificate.py'; SH=BASE/'spine_book_certificate.py'; VH=BASE/'variable_eight_core_certificate.py'
SHA={
 'geometry':'0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1',
 'geometry_helper':'3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4',
 'source_helper':'601c9c94018ab960abe63a126c1cf0d96b84b6b335ef5630c84adfb113db44de',
 'variable_helper':'45b59fa2d0127d6dbaaa46a9dd4046bc0e4537888f864153f95f8496f500a7e6',
}

def load(name,path):
    sp=spec_from_file_location(name,path); m=module_from_spec(sp); sp.loader.exec_module(m); return m

def prime(n): return n>1 and all(n%d for d in range(2,int(n**.5)+1))

def assert_inputs():
    for name,p in [('geometry',GEOM),('geometry_helper',GH),('source_helper',SH),('variable_helper',VH)]:
        got=sha256(p.read_bytes()).hexdigest(); assert got==SHA[name], (name,got)
    g=json.loads(GEOM.read_text()); assert g['schema']=='six-prime-prefix-geometry-input-v1'; assert len(g['batches'])==72
    return g,load('ordinary_geometry',GH),load('ordinary_source',SH),load('ck_rows',VH)

def source_env(g,h):
    nodes=sorted((a,b,c,-1,j,0,0,0,-1) for a in (1,2) for b in (2,4) for c in (a,3-a) for j in range(1,5))
    env=[]
    for node in nodes:
        a,b,c,_,j,*_=node; gamma=3*(a==1)+(b%3==a%3)
        reserve=Q(135,4)+gamma+(9-gamma)*(Q(c==a,5)+Q(j==a,20))
        env.append((node,reserve,h.envelope(g['batches'],a,b,c,j)))
    return env

def ck(E,children,cutoff):
    """Chapter-31 (SV4--SV9) exact Z/L/K row at expense E."""
    assert len(children)==6 and tuple(sorted(children))==tuple(children)
    b=[Q(1,3-Q(6,5)*E) if q==5 else Q(1,q-2-2*E) for q in children]
    n=len(children); v={}
    for mask in range(1,1<<n):
        S=tuple(i for i in range(n) if mask>>i&1); bs=Q(1)
        for i in S: bs*=b[i]
        v[S]=bs*(cutoff+(len(S)>=2))
    Z={():Q(1)}
    for mask in range(1,1<<n):
        inds=tuple(i for i in range(n) if mask>>i&1); first=inds[0]
        z=Z[tuple(i for i in inds if i!=first)]
        sub=mask
        while sub:
            if sub>>first&1:
                S=tuple(i for i in inds if sub>>i&1); rem=tuple(i for i in inds if not sub>>i&1)
                z-=v[S]*Z[rem]
            sub=(sub-1)&mask
        Z[inds]=z
    L=Q(0)
    for mask in range(1,1<<n):
        S=tuple(i for i in range(n) if mask>>i&1); rem=tuple(i for i in range(n) if not mask>>i&1); bs=Q(1)
        for i in S: bs*=b[i]
        L+=bs*Z[rem]
    full=tuple(range(n)); assert min(Z.values())>0 and L>0
    return {'min_Z':min(Z.values()),'L':L,'K':L/(2*3**cutoff*Z[full]),'children':children,'cutoff':cutoff,'expense':E}

def source_row(source,h,env,q,T):
    row=source.source_mass(h,env,q,T); m=Q(row['mass_lower_bound'])
    D=prod([Q(1),Q(1)]+[Q(p-1,p-1-t) for p,t in zip(q,T)])
    return {'later_primes':q,'thresholds':T,'mass':m,'joint_cap':D,'haar_mass':m/D,'worst_node':row['worst_node']}

def fee(p):
    if p==5:return Q(7,24)
    if p==7:return Q(1,8)
    if p==11:return Q(1,24)
    if p==13:return Q(1,48)
    return Q(1,2**((p-1)//2))

def ck_rows(variable,start):
    sched={13:5,17:8,19:10,23:13,29:16,31:19,37:23,41:26,43:28,47:30,53:30}
    out={}
    for s,t in sched.items():
        if s>=start:
            children=tuple(q for q in range(s,200) if prime(q))[:6]
            out[s]=Q(variable.ck(children,t)['K3'])
    return out

def main(output):
    g,h,source,variable=assert_inputs(); env=source_env(g,h)
    F=Q(1493,3072); f5=fee(5); rho=Q(1,3)
    # Target cores and transport maps are recorded, but the map theorem is not
    # reproved here.  Anchors are source (3,5), later coordinates are q.
    rows={}
    rows['missing_3']={'core':(5,7,11,13,17,19,23,29),'anchor_target':(5,7),
      'source':source_row(source,h,env,(11,13,17,19,23,29),(2,4,4,8,8,12))}
    rows['missing_5']={'core':(3,7,11,13,17,19,23,29),'anchor_target':(3,7),
      'source':source_row(source,h,env,(11,13,17,19,23,29),(4,4,4,8,8,12))}
    rows['missing_3_5']={'core':(7,11,13,17,19,23,29,31),'anchor_target':(7,11),
      'source':source_row(source,h,env,(13,17,19,23,29,31),(2,4,4,8,8,12))}
    # Core fee reserve excludes root 3 itself; these are the exact F*-sum f(core)
    # amounts used by the Chapter-31 root-budget form.
    for key,info in rows.items():
        core=info['core']; E=F-sum((fee(p) for p in core if p!=3),Q())
        info['F_star']=F; info['core_fee_sum']=sum((fee(p) for p in core if p!=3),Q()); info['outside_expense']=E
        if 5 not in core:
            info['rho']=rho
            info['strict_descendant_bound']=E-(1-rho)*f5
            info['five_absent_bound']=E-f5
    # Missing-3 has no missing-5 placement; all noncore minima begin at 31.
    r3=rows['missing_3']; k31=ck_rows(variable,31); B31=sum(k31.values(),Q())+Q(1,2**28)
    r3['large_attachment_budget_from_31']=B31; r3['mass_minus_large_budget']=r3['source']['mass']-B31
    # Missing-5 direct and dual-missing rows use the exact strict outside-root
    # proxy, cutoff 1, after deleting 5's fee.  This is the §8 placement form.
    for key, children in [('missing_5',(5,31,37,41,43,47)),('missing_3_5',(5,37,41,43,47,53))]:
        r=rows[key]; out=ck(r['five_absent_bound'],children,1); r['outside_root_ck']=out
        r['immediate_root_bound']=r['five_absent_bound']+out['K']; r['immediate_margin']=r['source']['mass']-r['immediate_root_bound']
        r['strict_margin']=r['source']['mass']-r['strict_descendant_bound']; r['absent_margin']=r['source']['mass']-r['five_absent_bound']
    # Exact regression anchors.
    assert rows['missing_3']['source']['mass']==Q(7332516433,56250000000)
    assert rows['missing_3']['source']['joint_cap']==Q(99,8)
    assert rows['missing_5']['source']['mass']==Q(164282173,1171875000)
    assert rows['missing_5']['source']['joint_cap']==Q(33,2)
    assert rows['missing_3_5']['source']['mass']==Q(229603051201,1350000000000)
    assert rows['missing_3_5']['source']['joint_cap']==Q(264,35)
    assert rows['missing_3']['mass_minus_large_budget']>0
    assert rows['missing_5']['strict_margin']>0 and rows['missing_5']['absent_margin']>0 and rows['missing_5']['immediate_margin']>0
    assert rows['missing_3_5']['strict_margin']>0 and rows['missing_3_5']['absent_margin']>0 and rows['missing_3_5']['immediate_margin']>0
    out={'schema':'missing-anchor-eight-core-source-audit-v1','scope':'Conditional exact source rows and Chapter-31 fee arithmetic for selected proxy cores missing 3 and/or 5. Does not prove anchor transport, root orientation, block-tree gluing, or unrestricted Erdos--Selfridge #7.','input_sha256':SHA,'F_star':F,'f5':f5,'rho':rho,'rows':{}}
    def enc(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,tuple):return list(x)
        if isinstance(x,dict):return {k:enc(v) for k,v in x.items()}
        return x
    out=enc(out); out['rows']={k:enc(v) for k,v in rows.items()}
    output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    for k,r in rows.items():
        print(k,'m=',r['source']['mass'],'D=',r['source']['joint_cap'],'E=',r['outside_expense'])
        for fld in ('mass_minus_large_budget','strict_margin','absent_margin','immediate_margin'):
            if fld in r: print(' ',fld,r[fld],float(r[fld]))
        if 'outside_root_ck' in r: print(' K=',r['outside_root_ck']['K'],float(r['outside_root_ck']['K']))
    print('wrote', output)
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=BASE/'missing_anchor_source_certificate.json')
    args=parser.parse_args()
    main(args.output)
