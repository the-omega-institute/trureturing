#!/usr/bin/env python3
"""Heuristic discovery for Report568's fixed-threshold counterexample.

Requires NumPy for phase selection. Each selected table is evaluated with
exact fractions on the same actual prefix before the next row is searched.
The fixed input and standard-library actual_four_union_counterexample.py
provide the retained certificate independently of this heuristic search.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from collections import defaultdict,Counter
import argparse,json,random,math,numpy as np
P=argparse.ArgumentParser();P.add_argument('--out',default='/tmp/e7-actual-four-union-search');P.add_argument('--height',type=int,default=2);P.add_argument('--restarts',type=int,default=5);P.add_argument('--sweeps',type=int,default=15);args=P.parse_args()
H=args.height
canonical=Path(__file__).with_name('actual_root_union_consumers.json')
ref=json.loads(canonical.read_text());caps={11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)};Ks={11:5,13:6,17:9,19:10};T=F(257,51)

def vcats(p):
    return [(0,1,F(1,p)),(0,2,F(1,p)),(0,-1,F(p-3,p))]+[(v,0,F(p-1,p**(v+1))) for v in range(1,H)]+[(H,0,F(1,p**H))]
def newval(p,u):
    return [(0,F(p-1-u,p))]+[(v,F(p-1,p**(v+1))) for v in range(1,H)]+[(H,F(1,p**H))]
def seed_source():
    weights=defaultdict(F);j11=F();j13=F();m11=F();m13=F()
    for (v5,r5,w5),(v7,r7,w7) in product(vcats(5),vcats(7)):
        w=w5*w7;u11=2*(1+(r5==1))*(1+(r7==1));u13=2*(1+(r5==2))*(1+(r7==2))
        d11=min(caps[11],F(11,11-u11));d13=min(caps[13],F(13,13-u13))
        s11=d11*F(11-u11,11);s13=d13*F(13-u13,13)
        j11+=w*max(0,u11-Ks[11]);j13+=w*s11*max(0,u13-Ks[13]);m11+=w*s11;m13+=w*s11*s13
        for (v11,w11),(v13,w13) in product(newval(11,u11),newval(13,u13)):
            weights[v5,v7,v11,v13]+=w*d11*w11*d13*w13
    if not (j11==F(3,35) and j13==F(2,35) and sum(weights.values())==m13):raise ValueError('seed common law')
    return dict(weights),{'x':'1','y':'1','lambda0':'1','lambda11':str(m11),'lambda13':str(m13),'J11':str(j11),'J13':str(j13),'seed11_old':[1,1],'seed13_old':[2,2]}

def evaluate(q,weights,exps,colors):
    masks=[sum(1<<int(c) for c in row) for row in colors];hist=defaultdict(F);j=F();mass=F();nxt=defaultdict(F)
    for v,w in weights.items():
        mask=0
        for e,m in zip(exps,masks):
            if all(a<=b for a,b in zip(e,v)):mask|=m
        u=mask.bit_count();hist[u]+=w;j+=w*max(u-Ks[q],0)
        density=min(caps[q],F(q,q-u));mass+=w*density*F(q-u,q)
        if q<19:
            for nv,nw in newval(q,u):nxt[(*v,nv)]+=w*density*nw
    return {'J':str(j),'J_decimal':float(j),'lambda_after':str(mass),'lambda_after_decimal':float(mass),'union_histogram':{str(u):str(w) for u,w in sorted(hist.items())}},dict(nxt)

def search(q,weights):
    dim=len(next(iter(weights)));exps=list(product(range(H+1),repeat=dim));atoms=list(weights);w=np.array([float(weights[v]) for v in atoms]);N=len(atoms);Q=len(exps);R=q-1
    inc=np.all(np.array(exps)[None,:,:]<=np.array(atoms)[:,None,:],axis=2)
    bylabel=[np.flatnonzero(inc[:,j]) for j in range(Q)];pairs=np.array(list(combinations(range(R),2)));pair_index={tuple(p):i for i,p in enumerate(pairs)}
    rng=random.Random(25092500+q);best=-1;bestcolors=None;progress=[]
    ideal=float(np.dot(w,np.maximum(np.minimum(R,2*inc.sum(axis=1))-Ks[q],0)))
    print('q',q,'source',sum(w),'atoms',N,'labels',Q,'ideal_nonzero_root_upper',ideal,flush=True)
    for restart in range(args.restarts):
        if restart==0:
            axes=(1,2,4,7,3);nc=R//2
            colors=[]
            for e in exps:
                z=0
                for a,t in zip(axes,e):z^=(a*t)
                c=z%nc;colors.append((2*c,2*c+1))
            colors=np.array(colors)
        elif restart==1:
            colors=np.array([(2*(sum((2*i+1)*t for i,t in enumerate(e))%(R//2)),2*(sum((2*i+1)*t for i,t in enumerate(e))%(R//2))+1) for e in exps])
        else:colors=pairs[[rng.randrange(len(pairs)) for _ in exps]].copy()
        counts=np.zeros((N,R),dtype=np.int16)
        for j in range(Q):
            ix=bylabel[j];counts[ix,colors[j,0]]+=1;counts[ix,colors[j,1]]+=1
        for sweep in range(args.sweeps):
            changed=False;order=list(range(Q));rng.shuffle(order)
            for j in order:
                ix=bylabel[j]
                if not len(ix):continue
                p,r=colors[j];counts[ix,p]-=1;counts[ix,r]-=1
                used=counts[ix]>0;nused=used.sum(axis=1)
                union=nused[:,None]+(~used[:,pairs[:,0]])+(~used[:,pairs[:,1]])
                scores=(np.maximum(union-Ks[q],0)*w[ix,None]).sum(axis=0)
                old=pair_index[p,r];mx=float(scores.max());ties=np.flatnonzero(scores>=mx-1e-17)
                chosen=old if old in ties else int(ties[rng.randrange(len(ties))])
                if chosen!=old:changed=True
                p,r=pairs[chosen];colors[j]=p,r;counts[ix,p]+=1;counts[ix,r]+=1
            if not changed:break
        score=float(np.dot(w,np.maximum((counts>0).sum(axis=1)-Ks[q],0)));progress.append([restart,sweep+1,score]);print('q',q,'restart',restart,'sweeps',sweep+1,'J',score,flush=True)
        if score>best:best=score;bestcolors=colors.copy()
    exact,nxt=evaluate(q,weights,exps,bestcolors)
    if abs(exact['J_decimal']-best)>=1e-12:raise ValueError('selected table exact evaluation')
    exact.update({'old_exponents':[list(e) for e in exps],'global_nonzero_current_roots':(bestcolors+1).tolist(),'height':H,'search_seed':25092500+q,'search_restarts':args.restarts,'maximum_sweeps':args.sweeps,'ideal_nonzero_root_upper_float':ideal,'source_atoms':len(weights)})
    return exact,nxt

weights,seed=seed_source()
r17,w17=search(17,weights);r19,w19=search(19,w17)
# Interpolate the bilinear PA corner quantities exactly at actual x,y.
x=F(seed['x']);y=F(seed['y']);u=2*x-1;v=3*y-2
cornerweights=[(1-u)*(1-v),(1-u)*v,u*(1-v),u*v]
phi=sum((a*F(c['Phi']) for a,c in zip(cornerweights,ref['PA_corners'])),F())
rows={11:{'J':seed['J11']},13:{'J':seed['J13']},17:r17,19:r19}
for r in ref['root_consumers']:
    q=r['q'];alpha=sum((a*F(c['alpha']) for a,c in zip(cornerweights,r['corners'])),F());tau=F(q)/caps[q]*(alpha-phi/(T-2));fixed=F(r['strict_root_excess_integral_threshold']);j=F(rows[q]['J'])
    rows[q].update({'fixed_threshold':str(fixed),'parameter_threshold':str(tau),'parameter_threshold_decimal':float(tau),'fixed_margin':str(j-fixed),'fixed_margin_decimal':float(j-fixed),'parameter_margin':str(j-tau),'exceeds_fixed':j>fixed,'exceeds_parameter':j>tau})
# Expand all literal original numerical labels and globally fixed CRT phases.
originals=[]
def add_original(primes,exps,residues):
    moduli=[p**e for p,e in zip(primes,exps) if e];rr=[r for e,r in zip(exps,residues) if e];m=math.prod(moduli);a=sum(r*(m//n)*pow(m//n,-1,n) for n,r in zip(moduli,rr))%m
    originals.append({'modulus':m,'residue':a,'prime_exponents':dict((str(p),e) for p,e in zip(primes,exps) if e)})
for q in [11,13]:
    op=seed['seed'+str(q)+'_old']
    for (a,b),roots in zip([(0,0),(1,0),(0,1),(1,1)],[(1,2),(3,4),(5,6),(7,8)]):
        for root in roots:add_original([5,7,q],[a,b,1],[op[0],op[1],root])
for q,old in [(17,[5,7,11,13]),(19,[5,7,11,13,17])]:
    row=rows[q]
    for exps,roots in zip(row['old_exponents'],row['global_nonzero_current_roots']):
        for root in roots:add_original(old+[q],exps+[1],[0]*len(old)+[root])
mult=Counter(o['modulus'] for o in originals);checks={'maximum_two_copies':max(mult.values())<=2,'all_moduli_odd_above_one':all(o['modulus']>1 and o['modulus']%2 for o in originals),'all_phases_in_range':all(0<=o['residue']<o['modulus'] for o in originals),'all_fixed_thresholds_exceeded':all(r['exceeds_fixed'] for r in rows.values()),'prefix_mass_matches':sum(weights.values())==F(seed['lambda13']),'row17_actual_law_propagated':sum(w17.values())==F(r17['lambda_after'])}
if not all(v for k,v in checks.items() if k!='all_fixed_thresholds_exceeded'):raise ValueError('actual family consistency')
finalmass=F(r19['lambda_after']);ratio=2+phi/finalmass
out={'statement':'One literal globally fixed finite two-copy family, all actual union integrals evaluated on its own sequential unnormalized PA law.','source':seed,'rows':{str(q):r for q,r in rows.items()},'Phi':str(phi),'lambda_final':str(finalmass),'PA_query_bound':str(ratio),'PA_query_bound_decimal':float(ratio),'target':str(T),'original_count':len(originals),'distinct_modulus_count':len(mult),'originals':originals,'checks':checks,'scope':'Float coordinate search selects a single global phase table; all displayed integrals and decisions are then exact rational finite arithmetic. No optimality or Lean claim. Crossing fixed thresholds alone only refutes that sufficient-candidate disjunction, not PA or the covering conjecture.'}
fixed={'format':'actual-four-union-colors-v1','height':H,'seed_old_roots':{'11':[1,1],'13':[2,2]},'roots':{str(q):rows[q]['global_nonzero_current_roots'] for q in (17,19)}}
Path(args.out+'.input.json').write_text(json.dumps(fixed,indent=2)+'\n')
Path(args.out+'.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'source':seed,'rows':{str(q):{k:r[k] for k in ['J','fixed_margin_decimal','parameter_threshold_decimal','exceeds_fixed','exceeds_parameter']} for q,r in rows.items()},'lambda_final':str(finalmass),'query':float(ratio),'count':len(originals),'checks':checks},indent=2),flush=True)
