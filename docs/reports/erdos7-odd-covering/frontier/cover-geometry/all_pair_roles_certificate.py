#!/usr/bin/env python3
"""Exact common-theta certificate for all120 pair central roles.

The64 branches fix one aligned edge profile. Separate concavity extends
one common witness to all three exponent types on all ten edges.
"""
import argparse, importlib.util, json
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm
from pathlib import Path

THETA_DENOMINATOR=2**24
THETA_NUMERATORS=(10694693,12456216,14611741,16777216,11557478,11557478,10892491,14421682,13813346,6837092,8804584,6418709,10892491,8862779)
REFERENCE=(9,11,9,9,27,18,18,27,27,27)
ANCHOR_SELECTORS=(
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (3, 1, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3),
    (3, 3, 3, 3, 5, 5, 3, 4, 3, 3, 3, 4, 5, 5, 3, 4, 3, 3, 3, 4, 5, 5, 3, 4, 5, 5, 3, 4, 5, 5, 5, 4),
    (3, 3, 3, 3, 5, 5, 3, 4, 3, 3, 3, 4, 5, 5, 3, 4, 3, 3, 3, 4, 5, 5, 3, 4, 5, 5, 3, 4, 5, 5, 5, 4),
    (1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (3, 1, 2, 2, 3, 3, 3, 2, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3),
    (2, 2, 2, 2, 4, 4, 2, 3, 2, 2, 2, 3, 4, 4, 2, 3, 2, 2, 2, 2, 4, 4, 2, 3, 4, 4, 2, 3, 4, 4, 4, 3),
    (2, 2, 2, 2, 4, 4, 2, 3, 2, 2, 2, 3, 4, 4, 2, 3, 2, 2, 2, 2, 4, 4, 2, 3, 4, 4, 2, 3, 4, 4, 4, 3),
    (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
    (4, 5, 4, 2, 7, 3, 7, 2, 4, 5, 4, 2, 3, 3, 3, 3, 4, 5, 4, 2, 7, 3, 3, 3, 7, 3, 7, 3, 3, 3, 3, 3),
    (7, 7, 2, 2, 9, 4, 2, 8, 7, 7, 2, 8, 4, 4, 2, 3, 7, 7, 2, 2, 9, 4, 2, 3, 9, 4, 2, 3, 4, 4, 4, 3),
    (7, 7, 7, 2, 9, 4, 2, 8, 7, 7, 2, 8, 4, 4, 2, 3, 7, 7, 2, 2, 9, 4, 2, 3, 9, 4, 2, 3, 4, 4, 4, 3),
    (2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
    (8, 9, 4, 2, 7, 3, 7, 2, 11, 5, 4, 2, 3, 3, 3, 3, 11, 5, 4, 2, 7, 3, 3, 3, 7, 3, 7, 3, 3, 3, 3, 3),
    (12, 11, 7, 2, 9, 4, 2, 8, 7, 7, 2, 8, 4, 4, 2, 3, 7, 7, 2, 2, 9, 4, 2, 3, 9, 4, 2, 3, 4, 4, 4, 3),
    (12, 11, 7, 2, 9, 4, 2, 8, 7, 7, 2, 8, 4, 4, 2, 3, 7, 7, 2, 2, 9, 4, 2, 3, 9, 4, 2, 3, 4, 4, 4, 3),
)
PIN606_JSON='f9f05ef34e1b4f395e766ad2391e902c92a4bdb8ab0334b6cd118d8fb13ad620'
PIN606_PRODUCER='88ebec773924ddd558157b2eada7be8a27c0265149f48054e8327113ecb56e17'
ROLES=tuple(product(range(2),range(4),range(2),range(4)))
PROFILES=tuple(tuple(int(i==R)+int(j==C)+int((i,j)==(I,J)) for i,j in product(range(2),range(4))) for R,C,I,J in ROLES)

class Checks:
    def __init__(self):self.values={};self.evaluations=0
    def require(self,name,p):
        self.evaluations+=1
        if not p:raise ArithmeticError(name)
        self.values[name]=True

def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def read_source(path,checks):
    raw=path.read_bytes();p=path.with_suffix('.py');code=p.read_bytes()
    checks.require('pinned606_data',sha256(raw).hexdigest()==PIN606_JSON)
    checks.require('pinned606_producer',sha256(code).hexdigest()==PIN606_PRODUCER)
    spec=importlib.util.spec_from_file_location('square_role_envelope',p)
    previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
    lib,obj,w,v,d3,d5,L,W,c,alpha,record=previous.source_inputs(path.with_name('actual_pair_activation_certificate.json'),checks)
    primary,secondary,kappa=previous.weights(lib)
    G,cells,region=previous.universal_box(lib,kappa,checks)
    blocks=previous.BLOCKS; reps=[block[0] for block in blocks]
    roots=[4*(l//3)+m//5 for l,m in reps]
    g=[[G[T][20*l+m] for l,m in reps] for T in range(32)]
    mass=[sum(w[l]*v[m] for l,m in block) for block in blocks]
    theta=[F(n,THETA_DENOMINATOR) for n in THETA_NUMERATORS]
    checks.require('common14_dyadic_theta',len(theta)==len(blocks)==14 and min(theta)>=0 and max(theta)<=1)
    selectors=[]
    for e3,e5 in product(range(4),repeat=2):
        rows=[];seen=set()
        for left in lib.selectors(6,3,w,[d3/2]*2,e3):
            for right in lib.selectors(20,5,v,[3*d/5 for d in d5],e5):
                ls=dict(left);rs=dict(right)
                row=tuple(sum(ls.get(l,0)*rs.get(m,0) for l,m in block) for block in blocks)
                if row not in seen:seen.add(row);rows.append(row)
        selectors.append(rows)
    coefs=[(1-c)*loss+c*query for loss,query in zip(L,W)]
    checks.require('all_query_coefficients_nonnegative',min(coefs)>=0)
    checks.require('same120_pair_inventory',len([x for x in obj['retained_inventory'] if x['kind']=='pair'])==120)
    source=dict(report606=path.name,report606_sha256=PIN606_JSON,report606_producer_sha256=PIN606_PRODUCER,report604=record)
    return lib,kappa,g,roots,mass,theta,selectors,coefs,c,alpha,region,source

class Factory:
    def __init__(self,lib,kappa,g,roots):
        self.lib=lib;self.kappa=kappa;self.g=g;self.roots=roots
        self.base=[];self.der=[];self.pair=[]
        for T in range(32):
            b=g[T].copy();der=[[F()]*14 for _ in range(10)];pair={}
            for e,mask in enumerate(lib.EDGE_MASKS):
                if T&mask:continue
                for j in range(14):b[j]-=kappa[e]*g[T|mask][j];der[e][j]-=kappa[e]*g[T|mask][j]
            for e,f in lib.MATCHINGS:
                em,fm=lib.EDGE_MASKS[e],lib.EDGE_MASKS[f]
                if T&(em|fm):continue
                vec=[kappa[e]*kappa[f]*z for z in g[T|em|fm]]
                pair[e,f]=vec
                for j,x in enumerate(vec):b[j]+=x;der[e][j]+=x;der[f][j]+=x
            self.base.append(b);self.der.append(der);self.pair.append(pair)
    def coefficients(self,T,d):
        c=sum(x*y for x,y in zip(self.base[T],d))
        unary=[[F() for _ in range(8)] for _ in range(10)];pairs={}
        for e in range(10):
            for j,r in enumerate(self.roots):unary[e][r]+=self.der[T][e][j]*d[j]
        for ef,vec in self.pair[T].items():
            coef=[F()]*8
            for j,r in enumerate(self.roots):coef[r]+=vec[j]*d[j]
            pairs[ef]=coef
        return c,unary,pairs
    def polynomial(self,T,d):return integer_polynomial(*self.coefficients(T,d))

def linear_profiles(vec):
    rows=(sum(vec[:4]),sum(vec[4:]));cols=tuple(vec[c]+vec[c+4] for c in range(4))
    return [rows[R]+cols[C]+vec[4*I+J] for R,C,I,J in ROLES]

def integer_polynomial(c,u,v):
    den=c.denominator
    for row in u:
        for x in row:den=lcm(den,x.denominator)
    for row in v.values():
        for x in row:den=lcm(den,x.denominator)
    const=c.numerator*(den//c.denominator)
    unary=[linear_profiles([x.numerator*(den//x.denominator) for x in row]) for row in u]
    pairs={}
    for ef,row in v.items():
        coeff=[x.numerator*(den//x.denominator) for x in row]
        if not any(coeff):continue
        pairs[ef]=[linear_profiles([x*y for x,y in zip(profile,coeff)]) for profile in PROFILES]
    return const,unary,pairs,den

def upper_numerators(polynomial):
    """All-domain and all64 first-edge-branch upper bounds over denominator2D."""
    c,u,v,D=polynomial
    work=[[2*x for x in row] for row in u]
    rest=[[2*x for x in row] for row in u]
    incident={}
    for (e,f),A in v.items():
        rows=[max(row) for row in A];cols=[max(col) for col in zip(*A)]
        work[e]=[x+y for x,y in zip(work[e],rows)]
        work[f]=[x+y for x,y in zip(work[f],cols)]
        if e==0:incident[f]=A
        elif f==0:incident[e]=[list(col) for col in zip(*A)]
        else:
            rest[e]=[x+y for x,y in zip(rest[e],rows)]
            rest[f]=[x+y for x,y in zip(rest[f],cols)]
    global_upper=2*c+sum(max(row) for row in work)
    if global_upper<=0:return global_upper,None
    branches=[]
    for r in range(64):
        val=2*c+2*u[0][r]
        for e in range(1,10):
            if e in incident:val+=max(x+2*y for x,y in zip(rest[e],incident[e][r]))
            else:val+=max(rest[e])
        branches.append(val)
    return global_upper,branches

def restrict(polynomial,r):
    c,u,v,D=polynomial
    c+=u[0][r];u=[row.copy() for row in u];u[0]=[0]*64;pairs={}
    for (e,f),A in v.items():
        if e==0:u[f]=[x+y for x,y in zip(u[f],A[r])]
        elif f==0:u[e]=[x+A[i][r] for i,x in enumerate(u[e])]
        else:pairs[e,f]=A
    return c,u,pairs,D

def evaluate(p,roles):
    c,u,v,D=p
    return F(c+sum(u[e][r] for e,r in enumerate(roles))+sum(A[roles[e]][roles[f]] for (e,f),A in v.items()),D)

def lower_one_sweep(polynomial,checks):
    c,u,v,D=polynomial
    u=[row.copy() for row in u];pairs={ef:[row.copy() for row in A] for ef,A in v.items()}
    before=evaluate((c,u,pairs,D),REFERENCE)
    for (e,f),A in pairs.items():
        full=[[x+u[e][i]+u[f][j] for j,x in enumerate(row)] for i,row in enumerate(A)]
        ue=[min(row)//2 for row in full]
        uf=[min(col)//2 for col in zip(*full)]
        new=[[x-ue[i]-uf[j] for j,x in enumerate(row)] for i,row in enumerate(full)]
        checks.require('integer_reparameterization_pair_nonnegative',min(min(row) for row in new)>=0)
        pairs[e,f]=new;u[e]=ue;u[f]=uf
    checks.require('one_sweep_reference_value_conserved',evaluate((c,u,pairs,D),REFERENCE)==before)
    return F(c+sum(min(row) for row in u)+sum(min(min(row) for row in A) for A in pairs.values()),D)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=Path(__file__).with_name('arbitrary_square_pair_roles.json'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();checks=Checks()
    lib,kappa,g,roots,mass,theta,selectors,coefs,c,alpha,region,source=read_source(args.source,checks)
    factory=Factory(lib,kappa,g,roots)
    checks.require('64_profile_role_bijection',len(set(ROLES))==64 and all(min(p)>=0 and max(p)<=3 for p in PROFILES))
    ref_H=[]
    for T in range(32):
        row=[]
        for j,r in enumerate(roots):
            z=factory.base[T][j]
            z+=sum(factory.der[T][e][j]*PROFILES[REFERENCE[e]][r] for e in range(10))
            z+=sum(vec[j]*PROFILES[REFERENCE[e]][r]*PROFILES[REFERENCE[f]][r] for (e,f),vec in factory.pair[T].items())
            row.append(z)
        ref_H.append(row)
    ds=[[F()]*14 for _ in range(32)]
    ds[0]=[(1-c)*m*t for m,t in zip(mass,theta)]
    regret=[F() for _ in range(64)];query_records=[];all_alternatives=0;stable_queries=0;retained_alternatives=0
    for mode,S in enumerate(selectors):
        for T in range(32):
            coef=coefs[mode*32+T]
            if not coef:continue
            ref=ANCHOR_SELECTORS[mode][T]
            checks.require("anchor_selector_in_complete_menu",0<=ref<len(S))
            ds[T]=[x-coef*t*s for x,t,s in zip(ds[T],theta,S[ref])]
            branch_max=[F() for _ in range(64)];kept=0
            for k,sel in enumerate(S):
                if k==ref:continue
                all_alternatives+=1
                difference=factory.polynomial(T,[t*(s-r) for t,s,r in zip(theta,sel,S[ref])])
                global_num,branch_num=upper_numerators(difference)
                if global_num<=0:continue
                retained_alternatives+=1;kept+=1
                for r,num in enumerate(branch_num):branch_max[r]=max(branch_max[r],F(num,2*difference[3]))
            stable_queries+=int(kept==0)
            for r,value in enumerate(branch_max):regret[r]+=coef*value
            query_records.append(dict(mode=mode,support=T,reference_selector=ref,selector_count=len(S),retained_alternatives=kept,coefficient=coef))
    const=F();unary=[[F()]*8 for _ in range(10)];pairs={}
    for T,d in enumerate(ds):
        pc,pu,pv=factory.coefficients(T,d);const+=pc
        for e in range(10):unary[e]=[x+y for x,y in zip(unary[e],pu[e])]
        for ef,row in pv.items():pairs[ef]=[x+y for x,y in zip(pairs.get(ef,[F()]*8),row)]
    reference_polynomial=integer_polynomial(const,unary,pairs)
    ref_gate=(1-c)*sum(m*t*h for m,t,h in zip(mass,theta,ref_H[0]))
    for record in query_records:
        mode,T,ref=record['mode'],record['support'],record['reference_selector']
        ref_gate-=record['coefficient']*sum(s*t*h for s,t,h in zip(selectors[mode][ref],theta,ref_H[T]))
    checks.require('reference_polynomial_matches_chosen_selector_gate',evaluate(reference_polynomial,REFERENCE)==ref_gate)
    branches=[]
    for r in range(64):
        lb=lower_one_sweep(restrict(reference_polynomial,r),checks)
        gate=lb-regret[r]
        checks.require('every_complete_branch_gate_above_one_over2000',gate>F(1,2000))
        branches.append(dict(fixed_first_edge_role=r,polynomial_lower=lb,selector_regret_upper=regret[r],gate_lower=gate,Haar_lower=alpha*gate))
    checks.require('64_disjoint_exhaustive_first_edge_branches',len(branches)==64 and [x['fixed_first_edge_role'] for x in branches]==list(range(64)))
    checks.require('uniform_gate_implies_Haar',alpha*F(1,2000)>F(1,104000))
    minbranch=min(branches,key=lambda x:x['gate_lower'])
    out=dict(schema='all-pair-roles-common-theta-v1',source=source,
             scope=dict(pair_labels=120,role_blocks=30,padded_profiles_per_block=64,complete_padded_layouts=64**30,aligned_layouts=64**10,actual_central_profiles_per_present_block=225,aligned_extension='Fixed common theta; separate concavity and three-type convex mixtures per edge',fixed='Report606 pure3/pure5 source; central15, existing stars and ten9q/25q roles',excluded='Extra ten squares,160 labels,exterior branches,arbitrary pure/star phases,unrestricted odd covering',lean_verified=False),
             theta_denominator=THETA_DENOMINATOR,theta_numerators=THETA_NUMERATORS,reference_layout=REFERENCE,anchor_selectors=ANCHOR_SELECTORS,
             constants=dict(continuation_c=c,Haar_factor=alpha,uniform_gate=F(1,2000),uniform_Haar=F(1,104000)),
             universal_strict_region=region,selector_counts=[len(S) for S in selectors],query_records=query_records,
             query_summary=dict(active=len(query_records),stable=stable_queries,alternatives=all_alternatives,retained=retained_alternatives),
             branches=branches,minimum_branch=minbranch,checks=checks.values,predicate_evaluations=checks.evaluations,
             producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(out),indent=2)+'\n')
    print('PASS',len(checks.values),'predicates',checks.evaluations,'evaluations; min role',minbranch['fixed_first_edge_role'],'gate',str(minbranch['gate_lower']),'decimal',float(minbranch['gate_lower']),flush=True)
if __name__=='__main__':main()
