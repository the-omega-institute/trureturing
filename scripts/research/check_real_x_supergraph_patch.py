#!/usr/bin/env python3
"""Uniform two-parameter interval certificate for a one-sided orthogonality graph.

Reuses check_strict_x_counterexample.py for rational interval arithmetic.
All acceptance arithmetic is Fraction/integer. A graph edge is allowed, never
asserted from a small residual. The root collection is NOT globally exhaustive.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import argparse,hashlib,itertools,json
import check_strict_x_counterexample as base
I,C=base.I,base.C
if not __debug__:raise RuntimeError('Assertions must be enabled')

def rnd(x:I,bits=90):
    d=1<<bits
    return I(F(x.lo.numerator*d//x.lo.denominator,d),
             F(-((-x.hi.numerator*d)//x.hi.denominator),d))

def cr(z):return C(rnd(z.re),rnd(z.im))
def mid(x):return (x.lo+x.hi)/2

def inverse(A):
    n=len(A);M=[list(row)+[F(int(i==j)) for j in range(n)] for i,row in enumerate(A)]
    for k in range(n):
        pivot=next((i for i in range(k,n) if M[i][k]),None)
        assert pivot is not None,'singular proposed Jacobian midpoint'
        M[k],M[pivot]=M[pivot],M[k];t=M[k][k];M[k]=[x/t for x in M[k]]
        for i in range(n):
            if i!=k:
                t=M[i][k];M[i]=[x-t*y for x,y in zip(M[i],M[k])]
    return [row[n:] for row in M]

def midpoint_preconditioner(J):
    scale=1<<42
    A=[[F(round(mid(x)*scale),scale) for x in row] for row in J]
    Inv=inverse(A)
    return [[F(round(x*scale),scale) for x in row] for row in Inv]

def cayley_identity():
    # Exact polynomial arithmetic over Q(i), with exponent order (a,b,t).
    Q=base.E.rat; ii=base.E((F(0),F(1),F(0),F(0)))
    def add(A,B):
        R=dict(A)
        for e,c in B.items():R[e]=R.get(e,Q(0))+c
        return {e:c for e,c in R.items() if c!=Q(0)}
    def scale(A,c):return {e:x*c for e,x in A.items()}
    def mul(A,B):
        R={}
        for e,x in A.items():
            for f,y in B.items():
                k=tuple(a+b for a,b in zip(e,f));R[k]=R.get(k,Q(0))+x*y
        return {e:c for e,c in R.items() if c!=Q(0)}
    one={(0,0,0):Q(1)};a={(1,0,0):Q(1)};b={(0,1,0):Q(1)};t={(0,0,1):Q(1)}
    n=add(one,scale(t,ii));d=add(one,scale(t,-ii))
    al=add(a,scale(b,ii));ac=add(a,scale(b,-ii))
    left=add(add(mul(mul(n,n),n),scale(mul(mul(al,n),mul(n,d)),Q(-1))),
             add(mul(mul(ac,n),mul(d,d)),scale(mul(mul(d,d),d),Q(-1))))
    p=add(add(mul(add(one,a),mul(mul(t,t),t)),mul(b,mul(t,t))),
          add(mul(add(a,scale(one,Q(-3))),t),b))
    assert add(left,scale(p,ii*2))=={},'Cayley coefficient identity failed'

def pvalue(a,b,t):return (1+a)*t*t*t+b*t*t+(a-3)*t+b

def phase_roots(a,b,sign,delta):
    aa=a*sign;bb=b*sign
    c=I.point(2) if sign==1 else base.sqrtI(21)/3
    z=I.point(0);h=4*delta
    candidates=[I(-c.hi-h,-c.lo+h),I(c.lo-h,c.hi+h),I(-h,h)]
    for X in candidates:
        left=pvalue(aa,bb,I.point(X.lo));right=pvalue(aa,bb,I.point(X.hi))
        assert (left.hi<0<right.lo) or (right.hi<0<left.lo),'cubic sign isolation failed'
        der=3*(1+aa)*X.sq()+2*bb*X+aa-3
        assert der.lo>0 or der.hi<0,'cubic derivative includes zero'
    for X,Y in itertools.combinations(candidates,2):assert X.hi<Y.lo or Y.hi<X.lo
    # Three distinct real roots of a cubic exhaust it. Cayley maps them to
    # the roots of z^3-alpha*z^2+conj(alpha)*z-1 (or alpha replaced by -alpha).
    return [cr((1+C.point(0,1)*x)/(1-C.point(0,1)*x)) for x in candidates]

def parameter_matrix(center,delta):
    assert center==[F(-1,5),F(0)] and 0<delta<F(1,100)
    a=I(center[0]-delta,center[0]+delta);b=I(-delta,delta)
    r=phase_roots(a,b,1,delta);s=phase_roots(a,b,-1,delta)
    A=base.circ(cr(r[0]*r[1]),r[1],C.point(1))
    B=base.circ(cr(s[0]*s[1]),s[1],C.point(1))
    H=[A[i]+B[i] for i in range(3)]+[base.adj(B)[i]+[-z for z in row] for i,row in enumerate(base.adj(A))]
    return [[cr(z) for z in H[i]] for i in [2,0,1,4,5,3]]

def squared_minor_separation(H):
    witnesses=[]
    for side,M in [('rows',H),('columns',base.mt(H))]:
        for i,j in itertools.combinations(range(6),2):
            best=None
            for p,q in itertools.combinations(range(6),2):
                a=M[i][p]*M[i][p]*M[j][q]*M[j][q]
                b=M[i][q]*M[i][q]*M[j][p]*M[j][p]
                lo=(a-b).normsq().lo
                if best is None or lo>best[0]:best=(lo,p,q)
            assert best[0]>0,'squared-minor Fourier separation failed'
            witnesses.append({'side':side,'pair':[i,j],'witness':[best[1],best[2]],'lower':str(best[0])})
    return witnesses

def root_box(charts,nums,den,radius,H):
    assert len(charts)==6 and charts[0]==0 and all(type(q)is int and 0<=q<4 for q in charts)
    assert len(nums)==5 and all(type(x)is int for x in nums)
    center=[F(x,den) for x in nums];X=[I(t-radius,t+radius) for t in center]
    f0,J0,_=base.equations_and_jacobian([I.point(x) for x in center],charts,H)
    _,J,_=base.equations_and_jacobian(X,charts,H)
    P=midpoint_preconditioner(J0)
    err=[[I.point(int(i==j))-sum((P[i][k]*J[k][j] for k in range(5)),I.point(0)) for j in range(5)] for i in range(5)]
    contraction=max(sum(e.abs_upper() for e in row) for row in err)
    assert contraction<F(1,4), 'contraction exceeds 1/4'
    D=[-sum((P[i][k]*f0[k] for k in range(5)),I.point(0))+
       sum((err[i][j]*I(-radius,radius) for j in range(5)),I.point(0)) for i in range(5)]
    assert all(d.abs_upper()<radius for d in D),'uniform Newton image is not internal'
    Y=[rnd(t+d) for t,d in zip(center,D)]
    assert all(X[j].lo<Y[j].lo<=Y[j].hi<X[j].hi for j in range(5))
    # ||I-P J||<1 implies P is nonsingular; hence the unique fixed point
    # of x -> x-P f_theta(x) is a root, for EACH exact theta in the patch.
    ray=[cr(z) for z in base.phase_map(Y,charts)]
    return {'ray':ray,'box':X,'chart':charts,'contraction':contraction,
            'displacement':max(x.abs_upper() for x in D)}

def shift(z):return [z[j] for j in [1,2,0,4,5,3]]

def fixed_shift(root):
    w=shift(root['ray']);assert w[0].normsq().lo>0
    w=[cr(z/w[0]) for z in w]
    for j in range(1,6):
        z=cr(w[j]*base.UNITS[(-root['chart'][j])%4])
        if (z+1).normsq().lo<=0:return False
        t=cr(C.point(0,-1)*(z-1)/(z+1));X=root['box'][j-1]
        if not X.lo<t.re.lo<=t.re.hi<X.hi:return False
    return True

def check(path):
    data=json.loads(Path(path).read_text());assert data['schema']=='x-uniform-supergraph-patch-v1'
    cayley_identity()
    delta=F(data['parameter_radius']);radius=F(data['root_radius']);den=data['center_denominator']
    assert type(den)is int and den>0 and radius>0
    H=parameter_matrix([F(x) for x in data['parameter_center']],delta)
    seams=squared_minor_separation(H)
    assert len(data['center_numerators'])==len(data['chart_quarter_turns'])==60
    roots=[root_box(q,n,den,radius,H) for q,n in zip(data['chart_quarter_turns'],data['center_numerators'])]
    edges={tuple(x) for x in data['allowed_edges']}
    assert len(edges)==114 and all(0<=i<j<60 for i,j in edges)
    can=set(data['canonical_vertices']);colors=data['noncanonical_colors']
    assert len(can)==6 and len(colors)==60
    assert all(colors[i] in (0,1) for i in range(60) if i not in can)
    assert all(((i in can and j in can) or (i not in can and j not in can and colors[i]!=colors[j])) for i,j in edges)
    assert all((i,j) in edges for i,j in itertools.combinations(sorted(can),2))
    assert all(fixed_shift(roots[i]) for i in can),'canonical continuation not certified mode-local'
    lowest=None;maxdistinct=F(0);nonedges=0
    for i,j in itertools.combinations(range(60),2):
        ip=sum((a.conj()*b for a,b in zip(roots[i]['ray'],roots[j]['ray'])),C.point())/6
        n=ip.normsq();assert n.hi<1,'projective distinctness failed'
        maxdistinct=max(maxdistinct,n.hi)
        if (i,j) not in edges:
            assert n.lo>F(1,10**8),'forbidden pair lacks uniform positive margin'
            lowest=n.lo if lowest is None else min(lowest,n.lo);nonedges+=1
    assert nonedges==1656
    return {'status':'PASS','arithmetic':'Fraction-only interval and exact rational preconditioner computation',
      'parameter_center':data['parameter_center'],'parameter_radius':str(delta),'root_radius':str(radius),
      'parameter_dimension':2,'continuing_rays':60,'uniformly_certified_nonedges':nonedges,
      'allowed_supergraph_edges':114,'canonical_vertices':sorted(can),'canonical_rays_are_shift_eigenvectors':True,
      'noncanonical_supergraph_is_bipartite':True,'known_root_completion_affinity':'2',
      'contraction_bound':'1/4','nonedge_normsq_strict_bound':'1/100000000',
      'squared_minor_separation_witnesses':30,'cayley_polynomial_identity':'exact coefficients checked',
      'six_clique_containment':'Every 6-clique among the 60 continuing rays is the distinguished canonical set.',
      'important_logic':'Allowed edges may disappear. No persistence of zero inner products is asserted.',
      'global_root_coverage':False,'all_completion_lower_bound':False,'lean_kernel_verified':False,
      'interval_kernel_sha256':hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
      'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'certificate_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest()}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--report');args=ap.parse_args()
    result=check(args.certificate);s=json.dumps(result,indent=2)+'\n'
    if args.report:Path(args.report).write_text(s)
    print(s)
