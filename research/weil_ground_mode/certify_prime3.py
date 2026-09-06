"""Reproducible directed-interval certificate for the c=3 Weil window.

No zeta-zero positions enter. mpmath.iv supplies constants and the small
finite matrix. Array intervals use correctly rounded IEEE binary64 basic
operations with one outward nextafter. The large Gram sum uses exact int64
products after an explicitly bounded dyadic quantization, not floating BLAS.
Analytic formulas and all remainder budgets are documented in the theory
appendix. This is an independently executable certificate, not a Lean run.
"""
from __future__ import annotations
import hashlib, json, math, pathlib, platform, time
from fractions import Fraction
import numpy as np
from mpmath import mp, iv
from sympy import bernoulli
import mpmath, sympy

if not __debug__:
    raise RuntimeError("Verification requires assertions; do not run Python with -O.")

iv.dps=45
mp.dps=60
N=64
M=32768
BITS=40
# Fixed even dyadic candidate, generated once and independently verified below.
CANDIDATE = (
    1884327, 1949881, 2454431, 1955838, 2267166, 2628844, 2019817, 2725995,
    2666928, 2258922, 3191558, 2627834, 2740665, 3535958, 2652877, 3431115,
    3691004, 2914967, 4199523, 3702151, 3543262, 4868979, 3743722, 4552854,
    5304731, 4078317, 5814371, 5510634, 4965730, 7089643, 5694160, 6550526,
    8139061, 6265021, 8774613, 8880841, 7751943, 11365368, 9561858, 10650784,
    13940578, 10893066, 15245277, 16256238, 14112283, 21456639, 18619811, 20944288,
    28759160, 22515646, 33301119, 36045767, 31375026, 51306542, 40139614, 48028821,
    55055748, 16558565, -14587791, -293594608, -638883816, -8057897274, -64380122561, 494208169232,
    -843813904619, 494208169232, -64380122561, -8057897274, -638883816, -293594608, -14587791, 16558565,
    55055748, 48028821, 40139614, 51306542, 31375026, 36045767, 33301119, 22515646,
    28759160, 20944288, 18619811, 21456639, 14112283, 16256238, 15245277, 10893066,
    13940578, 10650784, 9561858, 11365368, 7751943, 8880841, 8774613, 6265021,
    8139061, 6550526, 5694160, 7089643, 4965730, 5510634, 5814371, 4078317,
    5304731, 4552854, 3743722, 4868979, 3543262, 3702151, 4199523, 2914967,
    3691004, 3431115, 2652877, 3535958, 2740665, 2627834, 3191558, 2258922,
    2666928, 2725995, 2019817, 2628844, 2267166, 1955838, 2454431, 1949881,
    1884327,
)
ROOT=pathlib.Path(__file__).resolve().parent

def down(x): return np.nextafter(np.asarray(x,dtype=float),-np.inf)
def up(x): return np.nextafter(np.asarray(x,dtype=float),np.inf)

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I): self.lo,self.hi=a.lo,a.hi
        else:
            self.lo=np.asarray(a,dtype=float)
            self.hi=np.asarray(a if b is None else b,dtype=float)
    def __add__(self,y):
        y=I(y); return I(down(self.lo+y.lo),up(self.hi+y.hi))
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,y):return self+-I(y)
    def __rsub__(self,y):return I(y)+-self
    def __mul__(self,y):
        y=I(y)
        aa=[self.lo*y.lo,self.lo*y.hi,self.hi*y.lo,self.hi*y.hi]
        return I(down(np.minimum.reduce(aa)),up(np.maximum.reduce(aa)))
    __rmul__=__mul__
    def inv(self):
        assert np.all((self.lo>0)|(self.hi<0))
        return I(down(1/self.hi),up(1/self.lo))
    def __truediv__(self,y):return self*I(y).inv()
    def __rtruediv__(self,y):return I(y)*self.inv()
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        r=I(1);a=self
        while n:
            if n%2:r=r*a
            a=a*a;n//=2
        return r
    def mid(self):return (self.lo+self.hi)/2
    def widen(self,e):return I(down(self.lo-e),up(self.hi+e))


def outer_iv(x):
    return I(down(float(x.a)),up(float(x.b)))
PI=outer_iv(iv.pi)
LOG2=outer_iv(iv.ln(2))
LOG3=outer_iv(iv.ln(3))
SQRT2=outer_iv(iv.sqrt(2))
SQRT3=outer_iv(iv.sqrt(3))
B20=Fraction(bernoulli(20))

def atan_positive(x):
    """Bound arctan on positive intervals by reduction and a Taylor remainder."""
    assert np.all(x.lo>=0)
    invmask=x.mid()>1
    # Both branches are evaluated only on nonzero x; all calls here have x>0.
    xi=x.inv()
    y=I(np.where(invmask,xi.lo,x.lo),np.where(invmask,xi.hi,x.hi))
    shift=y.mid()>.5
    yy=(y-1)/(y+1)
    y=I(np.where(shift,yy.lo,y.lo),np.where(shift,yy.hi,y.hi))
    bound=np.maximum(abs(y.lo),abs(y.hi))
    assert np.all(bound<.501)
    val=I(0);power=y; y2=y*y
    for j in range(36):
        val=val+((-1)**j)*power/(2*j+1)
        power=power*y2
    # Integral geometric remainder: <= |y|^73/73, enlarged uniformly.
    assert Fraction(501,1000)**73/73 < Fraction.from_float(1e-23)
    val=val.widen(1e-23)
    shifted=PI/4+val
    val=I(np.where(shift,shifted.lo,val.lo),np.where(shift,shifted.hi,val.hi))
    inverse=PI/2-val
    return I(np.where(invmask,inverse.lo,val.lo),np.where(invmask,inverse.hi,val.hi))

def sin_interval(x):
    quot=np.floor(x.mid()/(2*np.pi)+.5)
    # quot is an exact integer. Correctness does not require exact range selection.
    r=x-2*PI*I(quot)
    assert np.max(np.maximum(abs(r.lo),abs(r.hi)))<3.15
    r2=r*r;term=r;result=I(0)
    for j in range(25):
        result=result+term
        term=-term*r2/((2*j+2)*(2*j+3))
    # Lagrange sine remainder after degree 49, certified with exact fractions.
    assert Fraction(63,20)**50/math.factorial(50)<Fraction.from_float(1e-38)
    return result.widen(1e-38)

def cmul(z,w):
    return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def cinv(r,w):
    d=r*r+w*w
    return (r/d,-w/d)

def psi_im_array(w):
    """Imaginary digamma on 1/4+iw. EM remainder is bounded using Re(z+16)."""
    r=I(65)/4
    zi=cinv(r,w)
    result=atan_positive(w/r)-zi[1]/2
    z2=cmul(zi,zi);power=z2
    for j in range(1,11):
        b=Fraction(bernoulli(2*j))
        coeff=I(b.numerator)/b.denominator/(2*j)
        result=result-coeff*power[1]
        power=cmul(power,z2)
    for j in range(16):result=result-cinv(I(4*j+1)/4,w)[1]
    # |R_psi| <= |B20|/(20*(65/4)^20) < 2e-23.
    assert abs(B20)/(20*Fraction(65,4)**20)<Fraction.from_float(2e-23)
    return result.widen(2e-23)

def symbol_array(ns):
    ns=np.asarray(ns,dtype=np.int64)
    assert np.all(ns>0)
    omega=2*PI*I(ns)/LOG3
    gam=psi_im_array(omega/2)/2
    decay=1/SQRT3
    correction=I(0)
    for j in range(32):
        b=I(4*j+1)/2
        correction=correction+omega*decay/(b*b+omega*omega)
        decay=decay/9
    # sum omitted <= (1/sqrt3)*9^-32/(1-1/9) < 1e-30.
    assert bool((iv.mpf(1)/iv.sqrt(3))*iv.mpf(9)**-32/(1-iv.mpf(1)/9)<iv.mpf(1)/10**30)
    gam=gam-correction
    gam=gam.widen(1e-30)
    ch=(SQRT3+1/SQRT3)/2
    pole=-2*omega*(ch-1)/(I(1)/4+omega*omega)
    prime=-(LOG2/SQRT2)*sin_interval(omega*LOG2)
    return pole-gam+prime


def psi_iv(z,tri=False):
    Z=z+16;iz=1/Z
    if not tri:
        ans=iv.log(Z)-iz/2
        for j in range(1,11):
            b=Fraction(bernoulli(2*j))
            ans-=iv.mpf(b.numerator)/b.denominator/(2*j)*iz**(2*j)
        for j in range(16):ans-=1/(z+j)
        R=iv.mpf(abs(B20.numerator))/B20.denominator/(20*iv.mpf(65/4)**20)
    else:
        ans=iz+iz**2/2
        for j in range(1,11):
            b=Fraction(bernoulli(2*j))
            ans+=iv.mpf(b.numerator)/b.denominator*iz**(2*j+1)
        for j in range(16):ans+=1/(z+j)**2
        R=iv.mpf(abs(B20.numerator))/B20.denominator/iv.mpf(65/4)**21
    return ans+iv.mpc(iv.mpf([-1,1])*R,iv.mpf([-1,1])*R)

def diagonal_iv(n):
    L=iv.ln(3);w=2*iv.pi*n/L;z=iv.mpc(iv.mpf(1)/4,w/2)
    gamma=psi_iv(z).real-iv.ln(iv.pi)+psi_iv(z,True).real/(2*L)
    correction=iv.mpf(0)
    for j in range(32):
        b=iv.mpf(4*j+1)/2
        correction+=iv.mpf(3)**(-b)*(1/iv.mpc(b,-w)**2).real
    gamma-=2/L*correction
    # Omitted correction: <= 2/L * 3^(-129/2)/( (129/2)^2*(1-1/9)).
    remainder=2/L*iv.mpf(3)**(-iv.mpf(129)/2)/( (iv.mpf(129)/2)**2*(1-iv.mpf(1)/9))
    gamma+=iv.mpf([-1,1])*remainder
    ch=(iv.sqrt(3)+1/iv.sqrt(3))/2
    pole=4*(ch-1)/L*(1/iv.mpc(iv.mpf(1)/2,w)**2).real
    prime=-2*iv.ln(2)/iv.sqrt(2)*(1-iv.ln(2)/L)*iv.cos(w*iv.ln(2))
    return gamma+pole+prime

def exact_gram(X):
    """Integer dot products; overflow ruled out for each signed accumulator."""
    radix=2**20
    H=X//radix;T=X-H*radix
    rows=X.shape[0]
    for U,V in [(H,H),(H,T),(T,T)]:
        assert 2*rows*int(np.max(abs(U)))*int(np.max(abs(V)))<2**63
    # Blocks keep each integer dot product local to cache. The global bounds
    # above also bound every partial sum, so chunking cannot overflow.
    cols=X.shape[1]
    HH=np.zeros((cols,cols),dtype=np.int64)
    HT=np.zeros_like(HH);TT=np.zeros_like(HH)
    for first in range(0,rows,2048):
        h=np.asfortranarray(H[first:first+2048])
        t=np.asfortranarray(T[first:first+2048])
        HH+=h.T@h;HT+=h.T@t;TT+=t.T@t
    return HH.astype(object)*radix**2+(HT+HT.T).astype(object)*radix+TT.astype(object)

def iv_from_float(x):
    p,q=float(x).as_integer_ratio();return iv.mpf(p)/q

def interval_ldl(A,name):
    d=len(A);lower=[[iv.mpf(0) for _ in range(d)] for _ in range(d)]
    piv=[]
    for j in range(d):
        lower[j][j]=iv.mpf(1)
        dj=A[j][j]-sum((lower[j][k]**2*piv[k] for k in range(j)),iv.mpf(0))
        if not bool(dj>0):
            raise ArithmeticError(f'{name}: nonpositive/uncertain pivot {j}: {dj}')
        piv.append(dj)
        for i in range(j+1,d):
            lower[i][j]=(A[i][j]-sum((lower[i][k]*lower[j][k]*piv[k] for k in range(j)),iv.mpf(0)))/dj
    low=min(float(p.a) for p in piv)
    print(name,'dimension',d,'minimum pivot lower',low,flush=True)
    return low

def run():
    start=time.time()
    sigpos=symbol_array(np.arange(1,M+1))
    slo=np.r_[-sigpos.hi[:N][::-1],0,sigpos.lo[:N]]
    shi=np.r_[-sigpos.lo[:N][::-1],0,sigpos.hi[:N]]
    ns=np.arange(-N,N+1)
    ms=np.r_[np.arange(-M,-N),np.arange(N+1,M+1)]
    tlo=np.r_[-sigpos.hi[N:][::-1],sigpos.lo[N:]]
    thi=np.r_[-sigpos.lo[N:][::-1],sigpos.hi[N:]]
    C=(I(slo[None,:],shi[None,:])-I(tlo[:,None],thi[:,None]))/(PI*I(ms[:,None]-ns[None,:]))
    X=np.rint(C.mid()*2**BITS).astype(np.int64)
    assert np.all(np.isfinite(C.lo)) and np.all(np.isfinite(C.hi))
    assert int(np.max(abs(X))) < 2**53
    exactx=np.ldexp(X.astype(float),-BITS)
    err=np.max(np.maximum(up(C.hi-exactx),up(exactx-C.lo)))
    # dyadic upper error, checked against the entire directed interval array
    errq=Fraction(1,2**38)
    assert err<float(errq),(err,errq)
    print('symbol intervals and quantization',time.time()-start,'error <=',str(errq),flush=True)
    G=exact_gram(X)
    assert np.array_equal(G,G[::-1,::-1]), 'quantized Gram must preserve reflection'
    trace=sum(int(G[i,i]) for i in range(len(ns)))
    assert trace<Fraction(16)*2**(2*BITS) # ||Cq||_F <4
    e2=len(ms)*len(ns)*errq**2
    # 2*||Cq||*||error||+||error||^2 <= eta by squared rational comparison
    eta=Fraction(1,10**7)
    assert eta>e2 and 64*e2<(eta-e2)**2
    print('exact Gram',time.time()-start,'trace',float(Fraction(trace,2**80)),flush=True)
    # Full arithmetic high-mode lower bound beta>=1 from a positive digamma increment.
    a=iv.ln(3)/2;eps=4/(3*iv.pi**2);R=iv.pi*N/(4*a)
    g0=-iv.euler-iv.pi/2-3*iv.ln(2)-iv.ln(iv.pi)
    t=R/2
    incr=sum((t**2/((iv.mpf(j)+iv.mpf(1)/4)*((iv.mpf(j)+iv.mpf(1)/4)**2+t**2)) for j in range(512)),iv.mpf(0))
    gamlo=g0+incr
    D=2*((iv.sqrt(3)-1/iv.sqrt(3))/2-a)
    beta=(1-eps)*gamlo+eps*g0-iv.ln(2)/iv.sqrt(2)-D
    assert bool(beta>1),beta
    B=iv.mpf(3)
    assert bool(2*((iv.sqrt(3)+1/iv.sqrt(3))/2)+iv.ln(2)/iv.sqrt(2)<B)
    # The fourth-power tail was bounded by M^-2 times the reciprocal-square tail.
    erem=16*B**2*N**2*(2*N+1)/(iv.pi**2*(1-iv.mpf(N)/M)**2*M**3)
    epsq=Fraction(1,4*10**6)
    assert bool(erem<iv.mpf(epsq.numerator)/epsq.denominator),erem
    print('beta lower',beta,'remainder upper',erem,flush=True)
    ss=[iv.mpf([float(slo[i]),float(shi[i])]) for i in range(len(ns))]
    AA=[[iv.mpf(0) for _ in ns] for _ in ns]
    for i,ni in enumerate(ns):
        AA[i][i]=diagonal_iv(int(ni))
        for j in range(i):
            val=(ss[i]-ss[j])/(iv.pi*int(ns[j]-ni))
            AA[i][j]=val;AA[j][i]=val
    vi=np.array(CANDIDATE,dtype=np.int64)
    assert len(vi)==2*N+1
    assert np.array_equal(vi,vi[::-1])
    vv=[iv.mpf(int(x))/2**40 for x in vi]
    norm=sum((x*x for x in vv),iv.mpf(0))
    ray=sum((vv[i]*AA[i][j]*vv[j] for i in range(len(ns)) for j in range(len(ns))),iv.mpf(0))/norm
    assert bool(ray<iv.mpf(1)/10**7),ray
    tau=iv.mpf(1)/10**6
    alpha=8/(iv.pi**2*M)
    # H = A - tau I - upper_bound(C* C)/(1-tau) + |v><v|.
    H=[[iv.mpf(0) for _ in ns] for _ in ns]
    for i in range(len(ns)):
        for j in range(i+1):
            qgram=iv.mpf(int(G[i,j]))/2**80
            tail=alpha*(ss[i]*ss[j]+9)
            if i==j:tail+=iv.mpf(eta.numerator)/eta.denominator+iv.mpf(epsq.numerator)/epsq.denominator
            val=AA[i][j]-(qgram+tail)/(1-tau)+vv[i]*vv[j]
            if i==j:val-=tau
            H[i][j]=val;H[j][i]=val
    # Algebraic parity invariance is exact for the mathematical operator and tail majorant.
    # Congruences use e_0 and e_j +/- e_-j, with no irrational basis normalization.
    def bilinear(x,y):
        return sum((sx*sy*H[i][j] for i,sx in x for j,sy in y),iv.mpf(0))
    even=[[(N,1)]]+[[(N+j,1),(N-j,1)] for j in range(1,N+1)]
    odd=[[(N+j,1),(N-j,-1)] for j in range(1,N+1)]
    E=[[bilinear(x,y) for y in even] for x in even]
    O=[[bilinear(x,y) for y in odd] for x in odd]
    pe=interval_ldl(E,'even');po=interval_ldl(O,'odd')
    report={
      'scale':'a=log(3)/2','N':N,'M':M,'beta_lower_certified':'1',
      'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
      'exact_gram_sha256':hashlib.sha256(json.dumps([[str(int(x)) for x in row] for row in G],separators=(',',':')).encode()).hexdigest(),
      'python':platform.python_version(), 'numpy':np.__version__,
      'mpmath':mpmath.__version__, 'sympy':sympy.__version__,
      'beta_interval_display':str(beta),
      'tau':'1/1000000','candidate_rayleigh_interval':str(ray),
      'candidate_even_dyadic_numerators':[str(int(x)) for x in vi],
      'candidate_denominator':str(2**40),'candidate_norm_sq_interval':str(norm),
      'gram_quantization_error_per_entry':str(errq),
      'gram_error_operator_upper':str(eta),
      'coupling_scalar_tail_upper':str(epsq),
      'even_min_pivot_lower_display':pe,'odd_min_pivot_lower_display':po,
      'elapsed_seconds':time.time()-start,
      'status':'directed interval inequalities passed; not a Lean elaboration',
      'claimed_scope':'fixed-window full-form codimension-one bound using the stated paper Fourier/domain identifications',
    }
    (ROOT/'prime3_certificate.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if 'numerators' not in k},indent=2),flush=True)

if __name__=='__main__':run()
