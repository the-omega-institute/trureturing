#!/usr/bin/env python3
"""Exact rational interval verification of an orthogonality-bridge counterexample.

No floating-point operation or numerical package is used in the validation path.
The numerical discovery program is deliberately separate. Existence uses the
Banach/Krawczyk theorem for the explicitly displayed five-variable rational map.
This checker is not a Lean kernel proof of that analytic theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import itertools, json

if not __debug__:
    raise RuntimeError("Run this checker without Python -O: assertions are mandatory.")

@dataclass(frozen=True)
class I:
    lo: F
    hi: F
    def __post_init__(self):
        if self.lo > self.hi: raise ValueError('empty interval')
    @staticmethod
    def point(v):
        v=F(v);return I(v,v)
    def __add__(self,o):
        o=ival(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-ival(o)
    def __rsub__(self,o):return ival(o)+-self
    def __mul__(self,o):
        o=ival(o);p=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return I(min(p),max(p))
    __rmul__=__mul__
    def reciprocal(self):
        if self.lo<=0<=self.hi:raise ValueError('division interval contains zero')
        return I(1/self.hi,1/self.lo)
    def __truediv__(self,o):return self*ival(o).reciprocal()
    def __rtruediv__(self,o):return ival(o)*self.reciprocal()
    def sq(self):
        return I(F(0) if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
    def abs_upper(self):return max(abs(self.lo),abs(self.hi))

def ival(v):return v if isinstance(v,I) else I.point(v)

@dataclass(frozen=True)
class C:
    re:I
    im:I
    @staticmethod
    def point(re=0,im=0):return C(ival(re),ival(im))
    def __add__(self,o):
        o=cval(o);return C(self.re+o.re,self.im+o.im)
    __radd__=__add__
    def __neg__(self):return C(-self.re,-self.im)
    def __sub__(self,o):return self+-cval(o)
    def __rsub__(self,o):return cval(o)+-self
    def __mul__(self,o):
        o=cval(o);return C(self.re*o.re-self.im*o.im,self.re*o.im+self.im*o.re)
    __rmul__=__mul__
    def conj(self):return C(self.re,-self.im)
    def normsq(self):return self.re.sq()+self.im.sq()
    def reciprocal(self):
        den=self.normsq()
        return C(self.re/den,-self.im/den)
    def __truediv__(self,o):return self*cval(o).reciprocal()
    def __rtruediv__(self,o):return cval(o)*self.reciprocal()

def cval(v):return v if isinstance(v,C) else C.point(v)

# Exact field Q(i,sqrt(21)), basis 1,i,sqrt(21),i*sqrt(21).
@dataclass(frozen=True)
class E:
    a:tuple[F,F,F,F]
    @staticmethod
    def rat(v):return E((F(v),F(0),F(0),F(0)))
    def __add__(self,o):
        o=evalq(o);return E(tuple(x+y for x,y in zip(self.a,o.a)))
    __radd__=__add__
    def __neg__(self):return E(tuple(-x for x in self.a))
    def __sub__(self,o):return self+-evalq(o)
    def __rsub__(self,o):return evalq(o)+-self
    def __mul__(self,o):
        o=evalq(o);r=[F(0)]*4
        for j,k in itertools.product(range(4),repeat=2):
            ip=(j%2)+(k%2);sp=(j//2)+(k//2)
            r[(ip%2)+2*(sp%2)]+=self.a[j]*o.a[k]*((-1)**(ip//2))*(21**(sp//2))
        return E(tuple(r))
    __rmul__=__mul__
    def __truediv__(self,q):return E(tuple(x/F(q) for x in self.a))
    def conj(self):return E((self.a[0],-self.a[1],self.a[2],-self.a[3]))
    def power(self,n):
        r=E.rat(1)
        for _ in range(n):r=r*self
        return r

def evalq(x):return x if isinstance(x,E) else E.rat(x)

def mm(A,B):return [[sum((A[i][k]*B[k][j] for k in range(len(B))),0) for j in range(len(B[0]))] for i in range(len(A))]
def mt(A):return [list(x) for x in zip(*A)]
def adj(A):return [[A[j][i].conj() for j in range(len(A))] for i in range(len(A[0]))]
def circ(a,b,c):return [[a,b,c],[c,a,b],[b,c,a]]
def hadamard(b,e):
    one=b*0+1
    A=circ(one,b,one);B=circ(one,e,one)
    return [A[i]+B[i] for i in range(3)]+[adj(B)[i]+[-x for x in row] for i,row in enumerate(adj(A))]

def is_monomial(A):
    z=E.rat(0);one=E.rat(1)
    return (all(sum(x!=z for x in row)==1 for row in A) and
            all(sum(x!=z for x in col)==1 for col in mt(A)) and
            all(x==z or x*x.conj()==one for row in A for x in row))

def symbolic_audit():
    bi=E((F(-3,5),F(4,5),F(0),F(0)))
    ei=E((F(-2,5),F(0),F(0),F(1,5)))
    H=hadamard(bi,ei);zero=E.rat(0);one=E.rat(1)
    assert all(x*x.conj()==one for row in H for x in row)
    I6=[[E.rat(int(i==j)) for j in range(6)] for i in range(6)]
    assert mm(H,adj(H))==[[x*6 for x in row] for row in I6]
    assert mm(adj(H),H)==[[x*6 for x in row] for row in I6]
    pi=[5,3,4,1,2,0]
    M=[[E.rat((1 if i<3 else -1)*int(j==pi[i])) for j in range(6)] for i in range(6)]
    assert mt(M)==[[-x for x in row] for row in M]
    assert mm(M,adj(M))==I6
    N=[[E.rat((-1 if i<3 else 1)*int(j==(i+3)%6)) for j in range(6)] for i in range(6)]
    assert is_monomial(N)
    assert mm(adj(H),M)==mm(N,mt(H))
    # Dephase using only unit phases, then apply the published row/column
    # -1-pattern criterion (Matszangosz-Szollosi 2024, Corollary 23).
    Hd=[[H[i][j]*H[i][0].conj()*H[0][j].conj()*H[0][0] for j in range(6)] for i in range(6)]
    assert all(x==one for x in Hd[0]) and all(row[0]==one for row in Hd)
    minus_row=[sum(x==-one for x in row) for row in Hd]
    minus_col=[sum(x==-one for x in col) for col in mt(Hd)]
    assert minus_row==[0,0,0,1,1,2] and minus_col==[0,0,0,2,1,1]
    assert max(minus_row)<3 and max(minus_col)<3
    # Exact Haagerup four-entry invariant includes conjugate(b), not a sixth root.
    assert bi.conj().power(6)!=one
    alpha=F(-1,5)
    disc=lambda t:t**4+18*t*t-8*t**3-27
    assert disc(alpha)==F(-16384,625)
    assert disc(-alpha)==F(-16464,625)
    # Pass to the row-permuted, symmetric-block representative H0.
    lp=[2,0,1,4,5,3]
    H0=[H[i] for i in lp]
    J=[[E.rat((-1 if i<3 else 1)*int(j==(i+3)%6)) for j in range(6)] for i in range(6)]
    assert mm(adj(H0),J)==[[-x for x in row] for row in mm(J,mt(H0))]
    for p in itertools.permutations(range(3)):
        gp=list(p)+[j+3 for j in p]
        G=[[E.rat(int(j==gp[i])) for j in range(6)] for i in range(6)]
        assert mm(G,H0)==mm(H0,G)
    return {'entrywise_unit':True,'both_Hadamard_Grams':True,'skew_monomial_M':True,
            'H_adjoint_M_eq_N_H_transpose':True,'Haagerup_value_not_sixth_root':True,
            'dephased_minus_one_counts_rows':minus_row,
            'dephased_minus_one_counts_columns':minus_col,
            'strict_X_external_input':'Matszangosz and Szollosi 2024, Corollary 23: the absence of three -1 entries in any normalized row or column excludes both Fourier families. This literature theorem is not reproved by this checker.',
            'symmetric_block_full_S3_symmetry':True, 'symmetric_block_extra_skew_antiunitary':True,
            'cubic_discriminants':[str(disc(alpha)),str(disc(-alpha))]}

def sqrtI(n,digits=45):
    den=10**digits;p=isqrt(n*den*den)
    assert p*p<=n*den*den<(p+1)*(p+1)
    return I(F(p,den),F(p+1,den))

UNITS=[C.point(1),C.point(0,1),C.point(-1),C.point(0,-1)]

def phase_map(t,charts):
    ii=C.point(0,1)
    return [C.point(1)]+[UNITS[charts[j+1]]*(1+ii*t[j])/(1-ii*t[j]) for j in range(5)]

def equations_and_jacobian(t,charts,H):
    u=phase_map(t,charts);HA=adj(H)
    y=[sum((h*v for h,v in zip(row,u)),C.point()) for row in HA]
    du=[];ii=C.point(0,1)
    for j in range(5):
        den=1-ii*t[j]
        du.append(UNITS[charts[j+1]]*C.point(0,2)/(den*den))
    J=[]
    for i in range(5):
        row=[]
        for j in range(5):
            dy=HA[i][j+1]*du[j]
            row.append(2*(y[i].re*dy.re+y[i].im*dy.im))
        J.append(row)
    return [yy.normsq()-6 for yy in y[:5]],J,u

def determinant(A):
    s=A[0][0]*0
    for p in itertools.permutations(range(len(A))):
        inv=sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
        t=(-1)**inv
        for i,j in enumerate(p):t=t*A[i][j]
        s=s+t
    return s

def pair_evidence(t,charts):
    u=phase_map(t,charts)
    perm=[5,3,4,1,2,0]
    w=[(1 if i<3 else -1)*u[perm[i]].conj() for i in range(6)]
    shift=lambda z,m:[z[3*(j//3)+(j+m)%3] for j in range(6)]
    inner=lambda a,b:sum((x.conj()*y for x,y in zip(a,b)),C.point())/6
    c1=inner(u,shift(w,1));c2=inner(u,shift(w,2))
    energy=c1.normsq()+c2.normsq()
    om=C(I.point(F(-1,2)),sqrtI(3)/2)
    powers=[C.point(1),om,om*om]
    def features(z):
        # Raw inverse DFT modes. Actual unit-vector modes divide by sqrt(18).
        raw=[[sum((powers[(-j*k)%3]*z[3*a+j] for j in range(3)),C.point()) for k in range(3)] for a in range(2)]
        weights=[(raw[0][k].normsq()+raw[1][k].normsq())/18 for k in range(3)]
        G=[[raw[a][k].conj()*raw[a][(k+1)%3]/18 for k in range(3)] for a in range(2)]+[[C.point(1)]*3]
        det=determinant(G)
        return weights,det.normsq()
    pu,dv=features(u);pw,dw=features(w)
    assert energy.lo>F(7,10)
    assert dv.lo>F(1,200) and dw.lo>F(1,200)
    assert all(p.lo>F(1,5) for p in pu+pw)
    return {'shifted_energy_strictly_greater_than':'7/10',
            'both_phase_determinant_normsq_strictly_greater_than':'1/200',
            'all_six_mode_weights_strictly_greater_than':'1/5',
            'global_inner_product_zero_reason':'M^T=-M, hence conjugate(u)^T*M*conjugate(u)=0 exactly',
            'actual_lower_bounds_decimal_for_display_only':{
                'shifted_energy':str(F(energy.lo.numerator*10**10//energy.lo.denominator,10**10)),
                'phase_det_v_sq':str(F(dv.lo.numerator*10**10//dv.lo.denominator,10**10)),
                'phase_det_w_sq':str(F(dw.lo.numerator*10**10//dw.lo.denominator,10**10))}}

def induced_orbit_graph(t,charts):
    # H0=L H with this row permutation; its blocks are scalar*I+J_3.
    u=phase_map(t,charts);u0=[u[j] for j in [2,0,1,4,5,3]]
    ps=list(itertools.permutations(range(3)))
    vecs=[];gs=[]
    for p in ps:
        gp=list(p)+[j+3 for j in p]
        vecs.append([u0[j] for j in gp])
        gs.append([[F(int(j==gp[i])) for j in range(6)] for i in range(6)])
    vecs += [[-z.conj() for z in v[3:]]+[z.conj() for z in v[:3]] for v in vecs[:]]
    J=[[F((-1 if i<3 else 1)*int(j==(i+3)%6)) for j in range(6)] for i in range(6)]
    edges=[];degrees=[0]*12
    for i,j in itertools.combinations(range(12),2):
        exact_zero=False
        if i<6<=j:
            K=mm(mm(mt(gs[i]),J),gs[j-6])
            exact_zero=mt(K)==[[-x for x in row] for row in K]
        if exact_zero:
            edges.append([i,j]);degrees[i]+=1;degrees[j]+=1
        else:
            g=sum((a.conj()*b for a,b in zip(vecs[i],vecs[j])),C.point())/6
            assert g.normsq().lo>F(1,1000)
            assert g.normsq().hi<F(1,2)
    assert len(edges)==24 and degrees==[4]*12
    assert all(i<6<=j for i,j in edges)
    return {'vertices':12,'edges':24,'degrees':degrees,'bipartition':[list(range(6)),list(range(6,12))],
            'exact_edge_list':edges,'nonedge_inner_normsq_strict_lower_bound':'1/1000',
            'all_distinct_ray_pairs_inner_normsq_strict_upper_bound':'1/2',
            'clique_number':2,
            'scope':'Exact induced graph on this symmetry orbit, not an assertion that it is a full connected component of all common-unbiased rays.'}

def check(path:Path):
    cert=json.loads(path.read_text())
    assert cert['parameters']=={'b':'(-3+4*i)/5','e':'(-2+i*sqrt(21))/5','positive_sqrt21':True}
    charts=cert['chart_quarter_turns']
    assert len(charts)==6 and charts[0]==0 and all(type(c) is int and 0<=c<4 for c in charts)
    center=[F(v) for v in cert['center']];rad=F(cert['radius'])
    assert len(center)==5 and rad>0
    Cmat=[[F(v) for v in row] for row in cert['preconditioner']]
    assert len(Cmat)==5 and all(len(row)==5 for row in Cmat)
    assert determinant(Cmat)!=0
    H=hadamard(C.point(F(-3,5),F(4,5)),C(I.point(F(-2,5)),sqrtI(21)/5))
    box=[I(x-rad,x+rad) for x in center];point=[I.point(x) for x in center]
    f0,_,_=equations_and_jacobian(point,charts,H)
    _,J,_=equations_and_jacobian(box,charts,H)
    E=[[I.point(int(i==j))-sum((Cmat[i][k]*J[k][j] for k in range(5)),I.point(0)) for j in range(5)] for i in range(5)]
    contraction=max(sum(e.abs_upper() for e in row) for row in E)
    delta=[]
    for i in range(5):
        z=-sum((Cmat[i][k]*f0[k] for k in range(5)),I.point(0))
        z+=sum((E[i][j]*I(-rad,rad) for j in range(5)),I.point(0))
        delta.append(z)
    assert contraction<F(1,1000)
    assert all(-rad<z.lo and z.hi<rad for z in delta)
    assert all(z.abs_upper()<rad/F(1000) for z in delta)
    # G(x)=x-CF(x) maps the box into its strict interior and is contractive.
    # C is invertible, so its unique fixed point is a zero of all five equations.
    # The exact row Gram implies the omitted sixth equation at that root.
    result={'status':'PASS','arithmetic':'fractions.Fraction rational interval operations only',
            'symbolic':symbolic_audit(),
            'root_existence':{'theorem':'Banach fixed point / Krawczyk inclusion',
                'dimension':5,'box_radius':str(rad),'preconditioner_determinant_nonzero':True,
                'contraction_inf_norm_less_than':'1/1000',
                'Krawczyk_displacement_less_than_radius_over':'1000',
                'conclusion':'one and only one real root in the stated rational chart box'},
            'pair':pair_evidence(box,charts),
            'certified_induced_orbit_graph':induced_orbit_graph(box,charts),
            'scope':'Counterexample at one exact 2-circulant point; no exhaustive root count or four-MUB conclusion.',
            'formal_status':'Exact independently rerunnable certificate; not yet a Lean kernel proof of the analytic enclosure.'}
    return result

if __name__=='__main__':
    import sys
    cert=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[2]/'docs/develop/certificates/strict_x_counterexample_certificate.json'
    result=check(cert)
    out=cert.with_name('strict_x_counterexample_verification.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
