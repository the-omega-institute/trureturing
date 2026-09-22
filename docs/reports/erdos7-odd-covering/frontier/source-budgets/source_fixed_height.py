#!/usr/bin/env python3
"""Fixed-source Haar lifts: independent finite row sums and exact limiting value."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from functools import lru_cache
import importlib.util
import argparse
import hashlib
import json
CERTIFICATE = 'certificates/source_norms/source-budgets/source_fixed_height.json'
SOURCES = ('certificate_io.py', 'frontier/source-budgets/source_full_square.py', 'frontier/source-budgets/source_plain_schur.py', 'profile-notes/321-384/339-irredundant-source-seven-labels-bound-the-actual-surplus.md', 'profile-notes/321-384/339b-the-actual-near-j-source-and-the-unit-refund.md', 'profile-notes/321-384/339d-the-complete-plain-source-square-at-every-height.md', 'profile-notes/321-384/339f-fixed-plain-source-at-arbitrary-test-heights.md')
def require(ok,msg):
    if not ok:raise ValueError(msg)
def load(name,path):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); s.loader.exec_module(m);return m

def hp(p,H,k):return F(k+1)+sum(F(1,p**j) for j in range(1,H-k+1))
def sum_geom(p,start,end):return sum(F(1,p**j) for j in range(start,end+1))

def baseline_correction(N,heights,i,schur):
    A,B,E=heights;a,b,e=i;t,q,u=schur.params(N)
    r5=sum_geom(5,1,B)-q;r7=sum_geom(7,1,E)-(1-u)
    require(r5>=0 and r7>=0,'Nonnegative extra test tails, fixed source')
    h3,h5,h7=hp(3,A,a),hp(5,B,b),hp(7,E,e)
    if a>=2:
        gamma=(F(5,7) if a==2 else F(6,7)) if e==0 else F(1)
        baseline=((1-q)*h3-gamma if b==0 else h5*(h3-gamma))*(1 if e==0 else h7)
        if b==e==0:correction=r5*(h3-gamma)+r7*((1-q)*h3-1)+r5*r7*(h3-1)
        elif e==0:correction=h5*(h3-1)*r7
        elif b==0:correction=h7*(h3-1)*r5
        else:correction=F(0)
    else:
        T3=sum_geom(3,2,A);U=F(2,9)-t;R=(3-4*q)/9-t*q;R0=F(11,63)-6*t/7
        baseline=3*(2*(R if b==0 else F(1,3))-(R0 if e==0 else U)+T3*((1-q) if b==0 else 1))*(1 if b==0 else h5)*(1 if e==0 else h7)
        if b==e==0:correction=3*(r5*(F(2,3)+T3-R0)+r7*(2*R+T3*(1-q)-U)+r5*r7*(F(2,3)+T3-U))
        elif e==0:correction=3*h5*r7*(F(2,3)+T3-U)
        elif b==0:correction=3*h7*r5*(F(2,3)+T3-U)
        else:correction=F(0)
    require(correction>=0 and baseline>=schur.hlo(a,b,e)>0,'Nonnegative correction and retained strict lower H')
    return baseline,correction


def calculate(base):
    source_dir=base/'frontier/source-budgets'
    api=load('fixed_source_api',source_dir/'source_full_square.py')
    schur=load('prior_schur_formulas',source_dir/'source_plain_schur.py')
    rows=[]
    for N,heights in ((12,(12,13,14)),(12,(14,12,13)),(13,(15,14,13))):
        source=api.CompressedSource(N,False);norm=source.haar_normalization
        A,B,E=heights
        @lru_cache(None)
        def raw(a,r,b,e):
            # Haar lift only: no new originals. Project the cylinder to source period.
            aa,bb,ee=min(a,N),min(b,N),min(e,N)
            excess=3**(a-aa)*5**(b-bb)*7**(e-ee)
            return source.mass(aa,r%3**aa,bb,ee)*norm/excess
        def centered(a,b,e):return raw(a,4%3**a,b,e)
        def cap0(a,b,e):return raw(a,0 if a==1 else 3 if a==2 else 18,b,e)
        labels=tuple(product(range(A+1),range(B+1),range(E+1)))
        all_moments=0
        for a,b,e in labels:
            if a==0:continue
            for kind,actual in (('p',centered(a,b,e)),('u',cap0(a,b,e))):
                require(actual==schur.moment(a,b,e,*schur.params(N),kind),'Lifted actual cylinder equals fixed-parameter kernel')
                all_moments+=1
        vals_a=sorted(set([1,2,3,N,A]+([N+1] if N<A else [])))
        selected=tuple(product(vals_a,sorted(set((0,1,B))),sorted(set((0,1,E)))))
        checked=[]
        for i in selected:
            a,b,e=i
            directly=sum(centered(max(a,aa),max(b,bb),max(e,ee)) for aa,bb,ee in labels)
            directly-=sum(cap0(a,max(b,bb),max(e,ee)) for bb,ee in product(range(B+1),range(E+1)))
            scaled=directly*3**a*5**b*7**e
            baseline,correction=baseline_correction(N,heights,i,schur)
            require(scaled==baseline+correction,'Complete unequal-height H identity '+str((N,heights,i)))
            require(schur.G(a,b,e,*schur.params(N))<=F(49,25)*schur.c(a,b,e)*baseline,'Inherited infinite row bound at this fixed-source point')
            checked.append(dict(vertex=list(i),actual_H_over_d=str(scaled),baseline=str(baseline),correction=str(correction)))
        value=sum((2*a+1)*(2*b+1)*(2*e+1)*centered(a,b,e) for a,b,e in labels)
        Js=tuple(sum(F(2*k+1,p**k) for k in range(H+1)) for p,H in zip((3,5,7),heights))
        closed=schur.value(*schur.params(N),*Js)
        require(value/norm==closed,'Rectangular full centered-pair histogram matches closed expression')
        rows.append(dict(source_height=N,test_heights=list(heights),originals=N*N+5*N,complete_labels=len(labels),all_lifted_moment_checks=all_moments,direct_complete_rows=len(selected),raw_value=str(value),normalized_value=str(closed),normalized_decimal=float(closed),rows=checked))

    source=api.CompressedSource(12,False)
    inf=schur.value(*schur.params(12),*(F(p*(p+1),(p-1)**2) for p in (3,5,7)))
    inf_raw=inf*source.haar_normalization
    require(inf==F(195513306639135135978326165,7696556594173900372773312),'Fixed-source normalized infinite supremum')
    require(inf_raw==F(39102661327827027195665233,8620110364906219921875000),'Fixed-source raw infinite supremum')
    require(inf>source.centered_square(),'Fixed-source test extension strictly changes square')
    require(inf!=F(1829,72),'Fixed source and source-growing limits differ')
    result=dict(cases=rows,fixed12_supremum_raw=str(inf_raw),fixed12_supremum_normalized=str(inf),fixed12_supremum_decimal=float(inf),source_growing_limit='1829/72',scope='Only fixed plain F_N, N>=12, Haar-lifted to complete test rectangles A,B,E>=N. Infinite-index comparison uses the existing ordinary source-box proof.')
    result['schema'] = 'source-fixed-height-v1'
    result['source_sha256'] = {p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    io = load('fixed_height_certificate_io',args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact fixed-source height certificate replay')
    print(json.dumps({**result,'cases':[{k:v for k,v in r.items() if k!='rows'} for r in result['cases']]},indent=2))


if __name__ == '__main__':
    main()
