#!/usr/bin/env python3
"""Finite, exact diagnostics for the appended fusion-tree theory.

Coefficient ring Q[s]/(s^4+s^2-1), evaluated at s=sqrt(phi^-1).
The program proves no infinite-net, category-coherence, DHR or Lean claim.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict, Counter
import json

Z = (Q(0),)*4
ONE = (Q(1),Q(0),Q(0),Q(0))
S = (Q(0),Q(1),Q(0),Q(0))
R = (Q(0),Q(0),Q(1),Q(0))

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    v=[Q(0)]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b): v[i+j]+=x*y
    for i in range(6,3,-1):
        v[i-4]+=v[i]; v[i-2]-=v[i]
    return tuple(v[:4])
def scale(a,q): return tuple(x*Q(q) for x in a)
def summ(xs):
    v=Z
    for x in xs: v=add(v,x)
    return v

def fuse(a,b):
    if a==0: return (b,)
    if b==0: return (a,)
    return (0,1)

def fentry(a,b,c,z,e,h):
    if e not in fuse(a,b) or z not in fuse(e,c): return Z
    if h not in fuse(b,c) or z not in fuse(a,h): return Z
    if (a,b,c,z)==(1,1,1,1):
        return ((R,S),(S,neg(R)))[e][h]
    return ONE

def paths(n,c=None):
    out=[(0,)]
    for _ in range(n):
        out=[p+(t,) for p in out for t in fuse(p[-1],1)]
    return [p for p in out if c is None or p[-1]==c]

# Sparse matrices keyed by row,column. Empty dict is an exact zero matrix.
def eye(n): return {(i,i):ONE for i in range(n)}
def madd(a,b):
    out=dict(a)
    for ij,v in b.items():
        out[ij]=add(out.get(ij,Z),v)
        if out[ij]==Z: del out[ij]
    return out

def mscale(a,s): return {ij:mul(v,s) for ij,v in a.items() if mul(v,s)!=Z}
def mmul(a,b):
    rows=defaultdict(list)
    for (j,k),v in b.items(): rows[j].append((k,v))
    out={}
    for (i,j),v in a.items():
        for k,w in rows[j]:
            ij=(i,k); out[ij]=add(out.get(ij,Z),mul(v,w))
    return {ij:v for ij,v in out.items() if v!=Z}

def trans(a): return {(j,i):v for (i,j),v in a.items()}
def mentry(a,i,j): return a.get((i,j),Z)

def projector(n,c,i):
    ps=paths(n,c); ids={p:j for j,p in enumerate(ps)}; out={}
    for j,p in enumerate(ps):
        a,b,d=p[i-1:i+2]
        for bp in (0,1):
            pp=p[:i]+(bp,)+p[i+1:]
            if pp not in ids: continue
            v=mul(fentry(a,1,1,d,b,0), fentry(a,1,1,d,bp,0))
            if v!=Z: out[(ids[pp],j)]=v
    return out

def require(cond, tag, data=None):
    if not cond: raise AssertionError((tag,data))


def run():
    counts=Counter(); pentagon_shape=Counter(); nontrivial={}
    # All 32 boundary-type assignments, all admissible source/target states.
    for a,b,c,d,z in product((0,1),repeat=5):
        source=[(e,f) for e in fuse(a,b) for f in fuse(e,c) if z in fuse(f,d)]
        target=[(h,g) for h in fuse(c,d) for g in fuse(b,h) if z in fuse(a,g)]
        require(len(source)==len(target),'pentagon dimensions',(a,b,c,d,z))
        pentagon_shape[str(len(source))]+=1; mat=[]
        for e,f in source:
            row=[]
            for h,g in target:
                lhs=summ(mul(mul(fentry(a,b,c,f,e,j),fentry(a,j,d,z,f,g)),
                             fentry(b,c,d,g,j,h)) for j in (0,1))
                rhs=mul(fentry(e,c,d,z,f,h),fentry(a,b,h,z,e,g))
                require(lhs==rhs,'pentagon',(a,b,c,d,z,e,f,h,g))
                counts['pentagon_entries']+=1
                row.append([str(x) for x in rhs])
            mat.append(row)
        counts['pentagon_boundary_cases']+=1
        if (a,b,c,d)==(1,1,1,1):
            nontrivial[str(z)]={'source':source,'target':target,'matrix':mat}
    for a,b,c,z in product((0,1),repeat=4):
        es=[e for e in fuse(a,b) if z in fuse(e,c)]
        hs=[h for h in fuse(b,c) if z in fuse(a,h)]
        for e,e2 in product(es,repeat=2):
            val=summ(mul(fentry(a,b,c,z,e,h),fentry(a,b,c,z,e2,h)) for h in hs)
            require(val==(ONE if e==e2 else Z),'F unitarity',(a,b,c,z,e,e2))
            counts['F_unitarity_entries']+=1
    # Path counts and actual matrix-unit right extension.
    fib=[0,1]
    for _ in range(45): fib.append(fib[-1]+fib[-2])
    for n in range(1,16):
        for c in (0,1):
            require(len(paths(n,c))==fib[n-1+c],'paths',(n,c)); counts['path_counts']+=1
        require(sum(len(paths(n,c))**2 for c in (0,1))==fib[2*n-1],'algebra dim',n)
        counts['algebra_dimensions']+=1
    # Exact Temperley-Lieb and distant locality on both actual total-charge sectors.
    max_n=9
    for n in range(2,max_n+1):
        for c in (0,1):
            ps=paths(n,c); projs={i:projector(n,c,i) for i in range(1,n)}
            for i,p in projs.items():
                require(p==trans(p),'self adjoint',(n,c,i))
                require(mmul(p,p)==p,'projector',(n,c,i))
                counts['projection_relations']+=1
            for i,p in projs.items():
                for j,q in projs.items():
                    if abs(i-j)==1:
                        require(mmul(mmul(p,q),p)==mscale(p,mul(R,R)), 'TL',(n,c,i,j))
                        counts['adjacent_TL_relations']+=1
                    if j>i+1:
                        require(mmul(p,q)==mmul(q,p),'distant commutation',(n,c,i,j))
                        counts['distant_commutations']+=1
            if n<max_n:
                for i,p in projs.items():
                    for d in fuse(c,1):
                        target=paths(n+1,d); tids={v:j for j,v in enumerate(target)}
                        q=projector(n+1,d,i)
                        for row,pr in enumerate(ps):
                            for col,pc in enumerate(ps):
                                require(mentry(p,row,col)==mentry(q,tids[pr+(d,)],tids[pc+(d,)]),
                                        'right inclusion coefficient',(n,c,d,i,row,col))
                                counts['right_extension_coefficients']+=1
    # Small full matrix-unit multiplication checks of the embedding, including off-block zero.
    for n in range(1,5):
        src=[(c,p,q) for c in (0,1) for p in paths(n,c) for q in paths(n,c)]
        def ext(unit):
            c,p,q=unit
            return {(d,p+(d,),q+(d,)):1 for d in fuse(c,1)}
        def unitprod(u,v):
            c,p,q=u;d,r,s=v
            return (c,p,s) if c==d and q==r else None
        for u in src:
            for v in src:
                expected={} if unitprod(u,v) is None else ext(unitprod(u,v))
                actual=defaultdict(int)
                for eu in ext(u):
                    for ev in ext(v):
                        evv=unitprod(eu,ev)
                        if evv is not None: actual[evv]+=1
                require(dict(actual)==expected,'matrix-unit embedding',(n,u,v))
                counts['matrix_unit_products']+=1
    # Single-sector exact witnesses, F^2=I versus classical composition.
    F={(0,0):R,(0,1):S,(1,0):S,(1,1):neg(R)}
    P={(0,0):ONE}; Qp=mmul(mmul(F,P),F)
    require(mmul(F,F)==eye(2),'F involution'); counts['two_channel_identities']+=1
    for a in (mmul(mmul(P,Qp),P),):
        require(a==mscale(P,mul(R,R)),'PQP'); counts['two_channel_identities']+=1
    comm=madd(mmul(P,Qp),mscale(mmul(Qp,P),neg(ONE)))
    require(mmul(trans(comm),comm)==mscale(eye(2),mul(mul(R,R),R)),'commutator norm square')
    counts['two_channel_identities']+=1
    shadow={ij:mul(v,v) for ij,v in F.items()}
    require(mmul(shadow,shadow)!=eye(2),'classical loss of inverse')
    require(mentry(mmul(shadow,shadow),0,1)==scale(mul(mul(R,R),R),2),'classical false transition')
    counts['two_channel_identities']+=2
    # A genuine negative control: replace only the nontrivial F with diag(1,-1).
    def badf(a,b,c,z,e,h):
        v=fentry(a,b,c,z,e,h)
        if (a,b,c,z)==(1,1,1,1):
            return ONE if e==h==0 else neg(ONE) if e==h==1 else Z
        return v
    failed=[]
    a=b=c=d=z=1
    source=[(e,f) for e in fuse(a,b) for f in fuse(e,c) if z in fuse(f,d)]
    target=[(h,g) for h in fuse(c,d) for g in fuse(b,h) if z in fuse(a,g)]
    for e,f in source:
        for h,g in target:
            lhs=summ(mul(mul(badf(a,b,c,f,e,j),badf(a,j,d,z,f,g)),badf(b,c,d,g,j,h)) for j in (0,1))
            rhs=mul(badf(e,c,d,z,f,h),badf(a,b,h,z,e,g))
            if lhs!=rhs: failed.append([e,f,h,g])
    require(bool(failed),'bad F must fail pentagon'); counts['deliberate_negative_controls']+=1
    # Complex 2 by 2 matrices over the same exact coefficient ring.
    def cc(x,y=Z): return (x,y)
    def ca(x,y): return (add(x[0],y[0]),add(x[1],y[1]))
    def cm(x,y): return (sub(mul(x[0],y[0]),mul(x[1],y[1])),add(mul(x[0],y[1]),mul(x[1],y[0])))
    def cj(x): return (x[0],neg(x[1]))
    cz=cc(Z); co=cc(ONE)
    def cs(xs):
        out=cz
        for x in xs: out=ca(out,x)
        return out
    def mat(r): return [[cc(mentry(r,i,j)) for j in range(2)] for i in range(2)]
    def prod2(a,b): return [[cs(cm(a[i][k],b[k][j]) for k in range(2)) for j in range(2)] for i in range(2)]
    def star(a): return [[cj(a[j][i]) for j in range(2)] for i in range(2)]
    def expect(a,rho): return cs(prod2(a,rho)[i][i] for i in range(2))
    I2=mat(eye(2)); Pr=mat(P); Qr=mat(Qp); bval=mul(R,S); hval=sub(mul(R,R),R)
    def pulse(proj,z):
        factor=ca(z,cc(neg(ONE)))
        return [[ca(I2[i][j],cm(factor,proj[i][j])) for j in range(2)] for i in range(2)]
    phase_pairs=[(Q(1),Q(0)),(Q(-1),Q(0)),(Q(0),Q(1)),(Q(0),Q(-1)),(Q(3,5),Q(4,5)),(Q(3,5),Q(-4,5))]
    phases=[cc(scale(ONE,x),scale(ONE,y)) for x,y in phase_pairs]
    for proj in (Pr,Qr):
        for z in phases:
            U=pulse(proj,z)
            require(prod2(U,star(U))==I2,'pulse unitarity')
            counts['pulse_unitarity']+=1
            for w in phases:
                require(prod2(U,pulse(proj,w))==pulse(proj,cm(z,w)),'pulse composition')
                counts['pulse_composition']+=1
    for z,(re,im) in zip(phases,phase_pairs):
        U=pulse(Qr,z); v=U[1][0]
        require(cm(v,cj(v))==cc(scale(mul(mul(R,R),R),2*(1-re))),'transition probability')
        counts['pulse_transfer']+=1
    V=pulse(Pr,cc(Z,ONE))
    for pval in (Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)):
        for xval,yval in product((Q(-1,4),Q(0),Q(1,4)),repeat=2):
            if xval*xval+yval*yval>pval*(1-pval): continue
            rv,xv,yv=[scale(ONE,v) for v in (pval,xval,yval)]
            rho=[[cc(rv),cc(xv,yv)],[cc(xv,neg(yv)),cc(sub(ONE,rv))]]
            m0=expect(Pr,rho);m1=expect(Qr,rho);m2=expect(Qr,prod2(prod2(V,rho),star(V)))
            require(m0==cc(rv),'tomography p')
            baseline=add(R,mul(hval,rv))
            require(m1==cc(add(baseline,scale(mul(bval,xv),2))),'tomography real')
            require(m2==cc(sub(baseline,scale(mul(bval,yv),2))),'tomography imaginary')
            counts['tomography_states']+=1
    invs=add(S,mul(S,R)); invb=mul(mul(invs,invs),invs)
    require(mul(bval,invb)==ONE,'exact inverse coefficient')
    dx=scale(mul(sub(ONE,hval),invb),Q(1,2));dy=neg(dx)
    require(add(ONE,add(mul(dx,dx),mul(dy,dy)))==add(scale(ONE,3),scale(R,2)), 'sharp tomography noise coefficient')
    counts['tomography_sharp_bound']=1
    # For P-only observation, i[Q,P] and a further commutator with P supply both coherences.
    def minus2(a,b): return [[ca(a[i][j],cc(neg(b[i][j][0]),neg(b[i][j][1]))) for j in range(2)] for i in range(2)]
    def i_comm(a,b):
        v=minus2(prod2(a,b),prod2(b,a))
        return [[cm(cc(Z,ONE),v[i][j]) for j in range(2)] for i in range(2)]
    C=i_comm(Qr,Pr);D=i_comm(Pr,C)
    require(C[0][1]==cc(Z,neg(bval)) and D[0][1]==cc(bval), 'observable coherence directions')
    counts['observable_closure_witness']=1
    return {'status':'passed','coefficient_ring':'Q[s]/(s^4+s^2-1), s=sqrt(phi^-1)',
            'case_counts':dict(counts),'pentagon_dimension_histogram':dict(pentagon_shape),
            'nontrivial_pentagons':nontrivial,'wrong_F_failed_entries':failed,'largest_chain_n':max_n,
            'scope':'Finite exact arithmetic/matrix diagnostics. No Lean, infinite-net, DHR or full-classification validation.'}

if __name__=='__main__': print(json.dumps(run(),ensure_ascii=False,indent=2))
