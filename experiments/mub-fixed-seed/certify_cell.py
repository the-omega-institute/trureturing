"""Exact rational outward certificate for one fixed source-model N=16 cell.
Requires Python 3 and SymPy. No floating-point arithmetic participates in acceptance.
"""
from fractions import Fraction as F
from math import isqrt
import sympy as sp
import json
from pathlib import Path
import argparse
class I:
 def __init__(self,a,b=None): self.a=F(a);self.b=F(a if b is None else b);assert self.a<=self.b
 def __add__(self,o):
  if not isinstance(o,I):o=I(o)
  return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+-o if isinstance(o,I) else self+I(-o)
 def __rsub__(self,o):return I(o)+-self
 def __mul__(self,o):
  if not isinstance(o,I):o=I(o)
  a=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b];return I(min(a),max(a))
 __rmul__=__mul__
 def __truediv__(self,o):
  if not isinstance(o,I):o=I(o)
  assert o.a>0;return self*I(1/o.b,1/o.a)
 def __rtruediv__(self,o):return I(o)/self
 def sq(self):
  return I(0,max(self.a*self.a,self.b*self.b)) if self.a<=0<=self.b else I(min(self.a*self.a,self.b*self.b),max(self.a*self.a,self.b*self.b))
 def sqrt(self):
  assert self.a>=0;scale=10**45
  lo=isqrt((self.a.numerator*scale*scale)//self.a.denominator)
  hi=isqrt((self.b.numerator*scale*scale)//self.b.denominator)+1
  return I(F(lo,scale),F(hi,scale))
 def decimals(self,places=12):
  scale=10**places
  lo=self.a.numerator*scale//self.a.denominator
  hi=-((-self.b.numerator*scale)//self.b.denominator)
  def fmt(n):return ('-' if n<0 else '')+str(abs(n)//scale)+'.'+str(abs(n)%scale).zfill(places)
  return [fmt(lo),fmt(hi)]

def z(r=0,i=0):return (r if isinstance(r,I) else I(r),i if isinstance(i,I) else I(i))
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def neg(x):return (-x[0],-x[1])
def conj(x):return (x[0],-x[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scale(x,a):return (x[0]*a,x[1]*a)
def power(x,n):
 q=z(1)
 while n:
  if n%2:q=mul(q,x)
  x=mul(x,x);n//=2
 return q
def adj(A):return [[conj(A[j][i]) for j in range(len(A))] for i in range(len(A[0]))]
def mm(A,B):
 return [[sumz([mul(A[i][k],B[k][j]) for k in range(len(B))]) for j in range(len(B[0]))] for i in range(len(A))]
def sumz(xs):
 s=z()
 for x in xs:s=add(s,x)
 return s

i=sp.I;r=sp.sqrt(7)
H=sp.Matrix([[1,1,1,1,1,1],[1,i,-1,i,-i,-i],[1,-1,i,-i,-i,i],[1,-i,i,-1,i,-i],[1,-i,-i,i,-1,i],[1,i,-i,-i,i,-1]])
assert H*H.conjugate().T==6*sp.eye(6)
E=H[:2,:2];B=H[:2,2:];C=H[2:,:2]
Nb=sp.Matrix([[0,-2*(1+i)],[0,2*i],[r,1],[-r,1]])
Nc=sp.Matrix([[0,-2*(1-i)],[r,1],[-r,1],[0,-2*i]])
assert sp.simplify(Nb.conjugate().T*Nb)==14*sp.eye(2)
assert sp.simplify(Nc.conjugate().T*Nc)==14*sp.eye(2)
assert B*Nb==sp.zeros(2) and C.conjugate().T*Nc==sp.zeros(2)
Dspan=-C*E.conjugate().T*(B*B.conjugate().T).inv()*B
assert all(sp.re(a).is_Rational and sp.im(a).is_Rational for a in Dspan)
def exactq(q):return F(int(q.p),int(q.q))
DspanI=[[z(exactq(sp.re(Dspan[j,k])),exactq(sp.im(Dspan[j,k]))) for k in range(4)] for j in range(4)]
s2=I(2).sqrt();s6=I(6).sqrt();s7=I(7).sqrt()
nb=[[z(),z(-2,-2)],[z(),z(0,2)],[z(s7),z(1)],[z(-s7),z(1)]]
nc=[[z(),z(-2,2)],[z(s7),z(1)],[z(-s7),z(1)],[z(),z(0,-2)]]
# omega=exp(i*pi/16) by the positive half-angle identities.
omega=z((2+(2+s2).sqrt()).sqrt()/2,(2-(2+s2).sqrt()).sqrt()/2)
index=[1,2,12,3];ph=[power(omega,2*k+1) for k in index]
alpha,T,beta,gamma=ph
U=[[mul(alpha,scale(beta,T[0])),mul(alpha,scale(gamma,T[1]))],
   [neg(mul(alpha,scale(conj(gamma),T[1]))),mul(alpha,scale(conj(beta),T[0]))]]
DK=mm(mm(nc,U),adj(nb));D=[[add(DspanI[j][k],scale(DK[j][k],s6/14)) for k in range(4)] for j in range(4)]
Fdef=I(0)
for row in D:
 for a,b in row:Fdef+=((a.sq()+b.sq()).sqrt()-1).sq()

def atan(q,n):
 s=sum((F((-1)**k)*q**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
 t=F((-1)**n)*q**(2*n+1)/F(2*n+1)
 return I(min(s,s+t),max(s,s+t))
pi=16*atan(F(1,5),100)-4*atan(F(1,239),30)
R=2*pi*F('0.0320001');h=pi/16;m2=4-s2
assert ((2+s2).sqrt()+R).a>2
A=1+2/m2;Dk=24/(16-s2.sq());Boff=s6/m2
lam=(A+Dk+((A-Dk).sq()+4*Boff.sq()).sqrt())/2
qnew=R.sq()*lam;qold=R.sq()*(1+10/m2)
def p(q):return q/(s6+(6-q).sqrt())
def zsq(q):return (R*(s6+2)).sq()/m2+(6*h+p(q)).sq()
zn=zsq(qnew);zo=zsq(qold)
assert zn.b<Fdef.a,'New norm test must strictly exclude'
assert Fdef.b<zo.a,'Old norm test must be strictly inconclusive'
assert (Fdef-zn).a>F('0.02278')
assert (zo-Fdef).a>F('0.02121')
assert Fdef.a>F('1.77328') and Fdef.b<F('1.77330')
out={'cell_index_alpha_t_beta_gamma':index,'N':16,'seed_radius_cycles':'0.0320001','defect':Fdef.decimals(),'z_new_squared':zn.decimals(),'z_source_squared':zo.decimals(),'new_exclusion_margin':(Fdef-zn).decimals(),'old_inconclusive_margin':(zo-Fdef).decimals(),'acceptance':'Exact Fraction inequalities; printed endpoints outward rounded by integer division','scope':'Prescribed exact seed/frames/cell only; no archive/pipeline execution, no full coverage, no Lean'}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,help='Optional JSON result destination; otherwise print only')
args=parser.parse_args()
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
