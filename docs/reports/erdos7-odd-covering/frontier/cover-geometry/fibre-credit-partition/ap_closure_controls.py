"""Exact finite controls for globally phased AP approximants of token arrays.

Explicit witness paths only. No phase, weight, or array search.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--witness',action='append',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
HEADS=(5,7)
PRIVATE=(11,13,17,19,23,29,31,37,41)
PRIMES=HEADS+PRIVATE
HEIGHTS=(1,2,4,8)
checks=0
stats={'prefix_pairs':0,'literal_coordinate_models':0,'witnesses':0,
       'finite_families':0,'crt_originals':0,'nested_old_phases':0,
       'completion_originals':0,'uncovered_original_tests':0}


def need(ok,msg):
    global checks
    checks+=1
    if not ok:
        raise ValueError(msg)


def word_value(p,digits):
    return sum(d*p**k for k,d in enumerate(digits))


def private_prefix(q,role,e):
    return word_value(q,[6]*(e-1)+[role])


def head_prefix(p,role,e):
    if role=='pure':
        digits=[p-1] if e==1 else [p-2]+[p-1]*(e-2)+[0]
    else:
        digits=[0] if e==1 else [1]+[p-1]*(e-2)+[0]
    return word_value(p,digits)


def crt(coordinates):
    modulus=prod(coordinates)
    residue=sum(a*(modulus//m)*pow(modulus//m,-1,m) for m,a in coordinates.items())%modulus
    need(all(residue%m==a for m,a in coordinates.items()),'One exact CRT phase matches every coordinate')
    return modulus,residue


def finite_parameters(p,n):
    A=sum(F(1,p**e) for e in range(1,n+1))
    c=1/(1-A)
    b=c*A
    t=F(1,p**n)
    need(A==(1-t)/(p-1) and c==F(p-1)/(p-2+t) and b==(1-t)/(p-2+t),
         'Finite pure normalization and actual token mass')
    need(c/F(p-1)-b==t/(p-2+t)>0,'Actual finite token differs from full geometric allowance')
    need(c<=F(p-1,p-2) and b<F(1,p-2),'Actual finite caps strictly below limiting saturation')
    return A,c,b


def head_parameters(p,n):
    A,c,b=finite_parameters(p,n)
    a=c/p
    deep=c*(A-F(1,p))
    short=a-deep
    ell=[F(0) if i==p-1 else short if i==p-2 else a for i in range(p)]
    deletion=[a if i==0 else deep if i==1 else F(0) for i in range(p)]
    active=[v-m for v,m in zip(ell,deletion)]
    need(sum(ell)==1 and sum(deletion)==b and sum(active)==1-b,'Actual head source and star carrier totals')
    need(all(v>=0 for v in active) and active[0]==active[p-1]==0,'Actual stable zero rows')
    return ell,deletion,active


# Prefix checks compare residues modulo the shorter prefix, not just counts.
for p in PRIMES:
    roles=range(6) if p in PRIVATE else ('pure','star')
    prefixes=[]
    for role in roles:
        for e in range(1,9):
            a=private_prefix(p,role,e) if p in PRIVATE else head_prefix(p,role,e)
            need(0<=a<p**e,'Canonical finite prefix representative')
            prefixes.append((role,e,a))
    for (_,e,a),(_,f,b) in combinations(prefixes,2):
        need(a%p**min(e,f)!=b%p**min(e,f),'Distinct role/depth cylinders are disjoint')
        stats['prefix_pairs']+=1
    # Independent coordinate enumeration at two small heights.
    for n in (1,2):
        union={role:set() for role in roles}
        for role in roles:
            for e in range(1,n+1):
                a=private_prefix(p,role,e) if p in PRIVATE else head_prefix(p,role,e)
                union[role].update(x for x in range(p**n) if x%p**e==a)
        A,c,b=finite_parameters(p,n)
        for role in roles:
            need(F(len(union[role]),p**n)==A,'Literal present role Haar mass')
        pure=union[0] if p in PRIVATE else union['pure']
        survivor=set(range(p**n))-pure
        need(F(p**n,len(survivor))==c,'Literal conditional density cap')
        if p in PRIVATE:
            need(len(set().union(*union.values()))==sum(map(len,union.values())),
                 'Six literal private unions jointly disjoint')
            for role in range(1,6):
                need(F(len(union[role]&survivor),len(survivor))==b,'Literal conditioned private token mass')
        else:
            ell,loss,active=head_parameters(p,n)
            for i in range(p):
                row={x for x in range(p**n) if x%p==i}
                need(F(len(row&survivor),len(survivor))==ell[i],'Literal common head row law')
                need(F(len(row&union['star']&survivor),len(survivor))==loss[i],
                     'Literal head star loss from actual prefixes')
        stats['literal_coordinate_models']+=1


def construct_family(n,rows,masks):
    registry={}
    def put(coords):
        m,a=crt(coords)
        need(m>1 and m%2==1 and m not in registry,'Each odd nonunit modulus appears exactly once')
        registry[m]=a
        stats['crt_originals']+=1
    put({3:0})
    for p in PRIMES:
        for e in range(1,n+1):
            pure=head_prefix(p,'pure',e) if p in HEADS else private_prefix(p,0,e)
            star=head_prefix(p,'star',e) if p in HEADS else private_prefix(p,1,e)
            put({p**e:pure})
            put({3:1 if p==5 else 2,p**e:star})
    for t,q in enumerate(PRIVATE):
        for e in range(1,n+1):
            for p,free_role,selected_role,free_col,selected_col,mask_col in (
                (5,2,4,0,1,0),(7,3,5,2,3,1)):
                put({p:rows[t][free_col],q**e:private_prefix(q,free_role,e)})
                root=1 if (masks[mask_col]>>t)&1 else 2
                put({3:root,p:rows[t][selected_col],q**e:private_prefix(q,selected_role,e)})
    need(len(registry)==58*n+1,'Finite source/group original count')
    return registry


def actual_arrays(n,rows,masks):
    arrays={r:{p:[] for p in HEADS} for r in (1,2)}
    raw={r:{p:[] for p in HEADS} for r in (1,2)}
    gs={}
    for t,q in enumerate(PRIVATE):
        _,c,b=finite_parameters(q,n)
        gs[q]={1:F(1),2:1-b}
        need(gs[q][2]>=F(q-3,q-2)>0,'Uniform positive private conditional denominator')
        for p,free_col,selected_col,mask_col in ((5,0,1,0),(7,2,3,1)):
            sr=1 if (masks[mask_col]>>t)&1 else 2
            for r in (1,2):
                v=[F(0)]*p
                v[rows[t][free_col]]+=b
                if r==sr:
                    v[rows[t][selected_col]]+=b
                raw[r][p].append(v)
                arrays[r][p].append([value/gs[q][r] for value in v])
        for r in (1,2):
            need(sum(arrays[r][5][-1])+sum(arrays[r][7][-1])<1,
                 'Actual disjoint roles give nonnegative paired survivor factors')
    return arrays,raw,gs


results=[]
for path in args.witness:
    source=Path(path).read_bytes()
    data=json.loads(source)
    if 'final_rows' in data and 'final_masks' in data:
        schema='bounded_joint_result'
        rows,masks=data['final_rows'],data['final_masks']
    elif 'common_rows' in data and 'masks' in data:
        schema='first_layer_witness'
        rows,masks=data['common_rows'],data['masks']
    else:
        raise ValueError('Unrecognized fixed token witness schema')
    need(tuple(data['private_primes'])==PRIVATE and len(rows)==len(PRIVATE),'Declared token prime order')
    need(all(len(row)==4 and 0<=row[0]<5 and 0<=row[1]<5 and 0<=row[2]<7 and 0<=row[3]<7
             for row in rows),'Physical head addresses')
    need(len(masks)==2 and all(0<=mask<1<<len(PRIVATE) for mask in masks),'One selected root per token')
    target={r:{p:[[F(v) for v in row] for row in data['arrays'][str(r)][str(p)]]
               for p in HEADS} for r in (1,2)}
    for p in HEADS:
        c=F(p-1,p-2)
        ell=[F(0) if i==p-1 else F(1,p) if i==p-2 else c/p for i in range(p)]
        deletion=[c/p if i==0 else F(1,p*(p-2)) if i==1 else F(0) for i in range(p)]
        need(ell==list(map(F,data['common_head_laws'][str(p)])),'Prefix limit equals stored common head law')
        for r in (1,2):
            active=(p==5 and r==1) or (p==7 and r==2)
            loss=deletion if active else [F(0)]*p
            need(loss==list(map(F,data['head_star_losses'][str(r)][str(p)])),
                 'Prefix limit equals stored star loss')
            need([v-m for v,m in zip(ell,loss)]==list(map(F,data['head_weights'][str(r)][str(p)])),
                 'Prefix limit equals stored actual head weights')
    for t,q in enumerate(PRIVATE):
        b=F(1,q-2)
        for p,fi,si,mi in ((5,0,1,0),(7,2,3,1)):
            sr=1 if (masks[mi]>>t)&1 else 2
            for r in (1,2):
                lim=[F(0)]*p
                lim[rows[t][fi]]+=b
                if r==sr:
                    lim[rows[t][si]]+=b
                g=F(1) if r==1 else 1-b
                need([v/g for v in lim]==target[r][p][t],'All-depth actual prefix limit matches stored raw-array normalization')
    prior={}
    prior_error=None
    height_results=[]
    uncovered_mod,uncovered=crt({3:1,5:2,7:2,**{q:7 for q in PRIVATE}})
    for n in HEIGHTS:
        family=construct_family(n,rows,masks)
        need(all(family[m]==a for m,a in prior.items()),'Nested family retains every old global phase')
        stats['nested_old_phases']+=len(prior)
        for m,a in family.items():
            need(uncovered%m!=a,'Common integer avoids every constructed original')
            stats['uncovered_original_tests']+=1
        arrays,raw,gs=actual_arrays(n,rows,masks)
        error=max(abs(arrays[r][p][t][i]-target[r][p][t][i])
                  for r in (1,2) for p in HEADS for t in range(len(PRIVATE)) for i in range(p))
        if prior_error is not None:
            need(error<prior_error,'Actual normalized token arrays approach the target along tested truncations')
        for t,q in enumerate(PRIVATE):
            power=F(1,q**n)
            bound=2*(q-1)*power/((q-3)*(q-3+2*power))
            need(all(abs(arrays[r][p][t][i]-target[r][p][t][i])<=bound
                     for r in (1,2) for p in HEADS for i in range(p)),
                 'Explicit uniform token convergence bound')
        head_error=F(0)
        for p in HEADS:
            ell,loss,active=head_parameters(p,n)
            for r in (1,2):
                v=active if ((p==5 and r==1) or (p==7 and r==2)) else ell
                targetw=list(map(F,data['head_weights'][str(r)][str(p)]))
                head_error=max(head_error,max(abs(a-b) for a,b in zip(v,targetw)))
                need([a==0 for a in v]==[a==0 for a in targetw],'Zero-row pattern stable under actual truncation')
        registry_hash=sha256(json.dumps(sorted(family.items()),separators=(',',':')).encode()).hexdigest()
        height_results.append({'height':n,'original_count':len(family),'phase_registry_sha256':registry_hash,
                               'max_head_weight_error':str(head_error),'max_normalized_array_error':str(error),
                               'max_normalized_array_error_decimal':float(error)})
        prior,prior_error=family,error
        stats['finite_families']+=1
    # Small examples of the full finite-box completion; do not enumerate its large box.
    sample_exponents=({5:1,7:1},{5:2,11:1},{7:2,13:2},{11:1,13:1},
                      {5:1,11:1,13:1},{5:1,7:1,17:1},{5:2,7:2,11:1},
                      {p:1 for p in PRIMES})
    completion=construct_family(2,rows,masks)
    for exponents in sample_exponents:
        for selected in (False,True):
            coords={p**e:(p-1 if p in HEADS else 0) for p,e in exponents.items()}
            if selected:
                coords[3]=1
            m,a=crt(coords)
            need(m not in completion,'Completion does not overwrite a registered source or group label')
            completion[m]=a
            need(all(a%p==(p-1 if p in HEADS else 0) for p in exponents),
                 'Every added original lies in present pure first-row holes')
            need(uncovered%m!=a,'Same integer also avoids the completed mixed originals')
            stats['completion_originals']+=1
    # Literal finite cap sums for the four relevant nongroup support shapes.
    finite_cap={p:finite_parameters(p,2)[1] for p in PRIMES}
    finite_b={p:finite_parameters(p,2)[2] for p in PRIMES}
    for D in ((5,11),(7,13),(5,7),(11,13),(5,7,11)):
        literal=F(0)
        for exp in product((1,2),repeat=len(D)):
            depth=dict(zip(D,exp))
            grouped=len(D)==2 and any(h in D and q in D and depth[h]==1 for h in HEADS for q in PRIVATE)
            if not grouped:
                literal+=prod((finite_cap[p]/p**depth[p] for p in D),start=F(1))
        if len(D)==2 and D[0] in HEADS and D[1] in PRIVATE:
            h,q=D
            formula=(finite_b[h]-finite_cap[h]/h)*finite_b[q]
        else:
            formula=prod((finite_b[p] for p in D),start=F(1))
        need(literal==formula,'AP9 finite nongroup cap inventory uses actual finite bN and shallow exclusion')
    results.append({'witness_path':path,'witness_sha256':sha256(source).hexdigest(),'schema':schema,
                    'heights':height_results,'common_uncovered_integer':str(uncovered),
                    'uncovered_first_digit_period':str(uncovered_mod)})
    stats['witnesses']+=1

result={
    'contract':'Exact finite controls for a nested globally phased AP-family approximation to the fixed head and four-token signature domain. Closure only; no covering system or simultaneous remainder-max realization.',
    'checks':checks,'statistics':stats,'results':results,
    'limits':[
        'Each tested approximant is finite; the all-height object is only used to define a limiting signature.',
        'Actual finite token mass c_N sum_(e<=N)p^-e differs from full allowance c_N/(p-1).',
        'The complete finite remainder roster and old-certificate uniform convergence are ordinary proved constructions, not a new breakpoint search.',
        'Only small completion samples are instantiated; the full 2*(N+1)^11-1 roster is not enumerated.',
        'No rerun of the old breakpoint checker, new array search or Lean build.',
    ],
}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'statistics':stats,'output':args.output}))
