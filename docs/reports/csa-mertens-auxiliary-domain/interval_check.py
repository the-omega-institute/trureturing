from fractions import Fraction as Q
from decimal import Decimal, localcontext
import json
P=10**42
class I:
 def __init__(self,a,b=None):
  self.l=Q(a); self.h=self.l if b is None else Q(b)
 def __add__(self,o):
  o=iv(o);return I(self.l+o.l,self.h+o.h)
 __radd__=__add__
 def __neg__(self):return I(-self.h,-self.l)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  o=iv(o);v=[self.l*o.l,self.l*o.h,self.h*o.l,self.h*o.h];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert o.l>0;return self*I(1/o.h,1/o.l)
 def __rtruediv__(self,o):return iv(o)/self
 def pow(self,p):
  p=Q(p);assert self.l>0
  if p<0:return I(1)/self.pow(-p)
  if p==0:return I(1)
  return I(rootbound(self.l,p,False),rootbound(self.h,p,True))
 def bounds(self,d=12):
  k=10**d;l=self.l*k;h=self.h*k
  return [fmt(l.numerator//l.denominator,d),fmt(-((-h.numerator)//h.denominator),d)]
def fmt(n,d):
 s=str(n).zfill(d+1);return s[:-d]+'.'+s[-d:] if d else s

def iv(o):return o if isinstance(o,I) else I(o)
def rootbound(x,p,up):
 n,m=p.numerator,p.denominator;target=x**n
 # The floating decimal below only seeds the integer search; all decisions are exact.
 with localcontext() as ctx:
  ctx.prec=60
  v=(Decimal(x.numerator)/Decimal(x.denominator))**(Decimal(n)/Decimal(m))
  k=int(v*P)
 while Q(k,P)**m>target:k-=1
 while Q(k+1,P)**m<=target:k+=1
 return Q(k+int(up),P)
def atan_bounds(x,n):
 terms=[(-1)**k*x**(2*k+1)/Q(2*k+1) for k in range(n)]
 s=sum(terms,Q(0));other=s+(-1)**n*x**(2*n+1)/Q(2*n+1)
 return I(min(s,other),max(s,other))
pi=16*atan_bounds(Q(1,5),25)-4*atan_bounds(Q(1,239),25)
assert Q('3.141592653589793238462643383279')<pi.l<pi.h<Q('3.141592653589793238462643383280')
# Lower log bound by the positive atanh series, 40 terms.
def loglower(x):
 z=(x-1)/(x+1);return 2*sum((z**(2*k+1)/Q(2*k+1) for k in range(40)),Q(0))
def expsum(x,n):
 t=Q(1);s=t
 for k in range(1,n+1):t=t*x/k;s+=t
 return s
rows=[('0','1/4345',1,'.00776291','.002969'),('1/2','.002969',2,'8.072','.10917'),('1','.10917',2,'8.072','1.3640'),('4/3','1.3640',2,'8.072','7.8538'),('14/9','7.8538',3,'10644','173.9913'),('23/12','173.9913',3,'10644','1893.436')]
EU=['.002947734','.10905180','1.36282534','7.84848144','173.926792','1892.835887']
FU=['.002947734','.10955529','1.37452789','7.90836318','176.998977','1921.773359']
KU=['.0029685','.109152','1.36373','7.85241','173.9721','1893.236']
PL=['1.69','5.53','3.27','1.19','7.29','4.43']
result=[]
for j,(aa,AA,b,BB,cc) in enumerate(rows):
 a,A,B,c=map(Q,[aa,AA,BB,cc]);r=(a+1)/(b+1);d=1-r;g=b*r
 D=(3*B*b/(pi*pi*A)).pow(Q(1,b+1));T=I(c/A).pow(1/(g-a));S=Q(9,10)*T
 qS=D/S.pow(d);ell=D*S.pow(r);m=S-ell
 Pcheck=S.pow(d)*A*D.pow(b)*loglower(D.l)/(Q('0.8')*B)
 side=ell.pow(b)/(Q('.034')*B)
 def f(q):return 2*A*D/(1-q).pow(a)+2*A*D/b*(1-q)
 def bound(t):
  f0=2*A*D*(1+Q(1,b));ft=f(D/t.pow(d));return I(max(f0.l,ft.l),max(f0.h,ft.h))
 E,F=bound(T),bound(S)
 assert E.h<Q(EU[j]) and F.h<Q(FU[j])
 assert Pcheck.l>Q(PL[j])>1
 assert qS.h<Q('.34') and ell.l>39 and m.l>110
 assert (m.pow(a)/A).l>4000
 assert side.h<11000000
 assert expsum(S.l,4)>11000000
 assert S.l>149 and T.l>10*g
 eupper=Q('0.00000006') if j==0 else Q('1e-58')
 assert expsum(Q(T.bounds()[0])/10,250)>1/eupper
 K=I(EU[j])+(Q(1,4345)+I(FU[j])/S.pow(g))*T.pow(g)*eupper+I(FU[j])*T.pow(g)/S.pow(g+1)*eupper+I(FU[j])/(I('.9').pow(g+1)*T)
 assert K.h<Q(KU[j])<c
 result.append(dict(iteration=j+1,alpha=str(a),A=str(A),beta=b,B=str(B),gamma=str(g),c=str(c),D=D.bounds(),T=T.bounds(),S=S.bounds(),E=E.bounds(),F=F.bounds(),K_upper=KU[j],P_lower=PL[j],log_y=ell.bounds(6),log_x_over_y=m.bounds(6)))
# Interpolation and small real interval.
Tstar=I(Q('1893.436')/Q('173.9913')).pow(Q(48,13))
J=Q('173.9913')*Tstar.pow(Q(1,12))
assert Q('362.6763')<J.l<J.h<Q('362.6764')<Q('362.7')
assert Q(8,3)**16>2160535
out=dict(pi=pi.bounds(30),rows=result,interpolation_t=Tstar.bounds(),interpolation_coefficient=J.bounds(),assertions='All exact rational assertions passed; Decimal only proposes brackets, which are checked by integer powers.')
print(json.dumps(out,indent=2))
open('interval_certificate.json','w').write(json.dumps(out,indent=2)+'\n')
