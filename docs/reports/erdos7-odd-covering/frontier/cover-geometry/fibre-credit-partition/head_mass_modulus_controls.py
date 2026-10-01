"""Small exact controls for the HM7 head-mass continuity modulus.
No covering search or uniform positivity claim.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',required=True)
args=parser.parse_args()
checks=0
def need(ok,message):
 global checks
 checks+=1
 if not ok:raise ValueError(message)
def cap(p,l):return F(p-1,p-2)/p**l
def B(p,l):return cap(p,l)*F(p,p-1)
def phi(p,l,delta):
 if delta==0:return F(0),0
 k=0;v=cap(p,l)
 while v>delta:k+=1;v/=p
 return k*delta+v*F(p,p-1),k
phi_controls=[]
for p,l in product((5,7),(1,2)):
 for delta in (F(0),cap(p,l),cap(p,l)/p**2,F(1,1000),F(1,1000000)):
  value,k=phi(p,l,delta)
  need(0<=value<=B(p,l),'Finite geometric cap bound')
  if delta:
   need(cap(p,l+k)<=delta and (k==0 or cap(p,l+k-1)>delta),'Minimal exact threshold')
   N=l+k+4
   direct=sum((min(cap(p,e),delta) for e in range(l,N)),F(0))+B(p,N)
   need(value==direct,'Independent prefix plus already-small geometric tail')
   need(value<=delta*(k+F(p,p-1)),'Exact logarithm-free modulus bound')
  else:need(value==0,'Zero endpoint')
  phi_controls.append({'p':p,'lower_depth':l,'delta':str(delta),'threshold_shift':k,'phi':str(value)})
# Nonlinear two-head maximum and exact tail summation, not just the scalar formula.
w={1:{5:[F(0),F(1,5),F(4,15),F(1,5),F(0)],7:[F(6,35)]*5+[F(1,7),F(0)]},
   2:{5:[F(4,15)]*3+[F(1,5),F(0)],7:[F(0),F(1,7)]+[F(6,35)]*3+[F(1,7),F(0)]}}
T={r:[[F((r+i+2*j)%7+1,8) for j in range(7)] for i in range(5)] for r in (1,2)}
def fee(weights,kernels):
 labels={}
 for p in (5,7):
  positive=[x for r in (1,2) for x in weights[r][p] if x>0]
  N=1
  while cap(p,N)>min(positive):N+=1
  labels[p]=[(e,F(1)) for e in range(1,N)]+[(N,F(p,p-1))]
 total=F(0)
 for (e5,m5),(e7,m7) in product(labels[5],labels[7]):
  values={r:[[F(1,2)*kernels[r][i][j]*min(cap(5,e5),weights[r][5][i])*min(cap(7,e7),weights[r][7][j]) for j in range(7)] for i in range(5)] for r in (1,2)}
  free=max(values[1][i][j]+values[2][i][j] for i in range(5) for j in range(7))
  selected=max(values[r][i][j] for r in (1,2) for i in range(5) for j in range(7))
  total+=m5*m7*(free+selected)
 return total
old=fee(w,T);max_controls=[]
for delta in (F(1,1000),F(1,1000000)):
 ww={r:{p:row.copy() for p,row in heads.items()} for r,heads in w.items()}
 for r in (1,2):
  ww[r][5][3]-=delta;ww[r][5][4]+=delta
  ww[r][7][5]-=delta;ww[r][7][6]+=delta
 changed=fee(ww,T)
 bound=F(3,2)*(phi(5,1,delta)[0]*B(7,1)+phi(7,1,delta)[0]*B(5,1))
 need(abs(changed-old)<=bound,'Two-head sum of per-depth maxima satisfies the product modulus')
 TT={r:[[x+delta for x in row] for row in rows] for r,rows in T.items()}
 changed_T=fee(ww,TT);extra=F(3,2)*delta*B(5,1)*B(7,1)
 need(abs(changed_T-changed)<=extra,'Separate uniform T perturbation term')
 need(abs(changed_T-old)<=bound+extra,'Combined row and T perturbation')
 max_controls.append({'delta':str(delta),'old_fee':str(old),'new_fee':str(changed),'row_modulus':str(bound),'new_fee_with_T_change':str(changed_T),'T_modulus':str(extra)})
# The zero-mask has a genuine jump, even when all kernels are positive.
zero_controls=[]
for delta in (F(1,1000),F(1,1000000)):
 before=[F(0),F(1,5),F(4,15),F(1,5),F(0)]
 after=[F(0),F(1,5),F(4,15),F(1,5)-delta,delta]
 tt=[F(1,2)]*4+[F(1)]
 z0=B(5,1)*max(tt[i] if before[i]>0 else F(0) for i in range(5))
 z1=B(5,1)*max(tt[i] if after[i]>0 else F(0) for i in range(5))
 need(sum(before)==sum(after)==F(2,3) and all(0<=x<=F(4,15) for x in after),'Zero-row opening preserves total and head cap')
 need(z1-z0==F(1,6),'Zero-mask jump does not shrink with delta')
 zero_controls.append({'delta':str(delta),'zero_mask_jump':str(z1-z0)})
P=(11,13,17,19,23,29,31,37,41)
C=F(1)
for q in P:C*=1+F(1,q-2)
C1=sum((F(1,q-2) for q in P),F(0));C2=C-1-C1
b5,b7=B(5,1),B(7,1);d5,d7=B(5,2),B(7,2)
S=C2*(1+b5+b7)+C1*(d5+d7)+C*b5*b7
moduli=[]
for delta in (F(1,1000),F(1,10000),F(1,1000000)):
 f51=phi(5,1,delta)[0];f71=phi(7,1,delta)[0]
 omega=F(3,2)*(C1*(phi(5,2,delta)[0]+phi(7,2,delta)[0])+C2*(f51+f71)+C*(b7*f51+b5*f71))
 outside=F(3,2)*delta*(12*C2+C1*(7*d5+5*d7)+C2*(7*b5+5*b7))
 moduli.append({'delta':str(delta),'fixed_T_fee_modulus':str(omega),'fixed_T_fee_modulus_decimal':float(omega),'additional_unsupported_head_integral_modulus':str(outside),'all_head_fee_modulus_decimal':float(omega+outside),'uniform_T_epsilon_coefficient':str(F(3,2)*S)})
# Raw factors have no division by g and keep valid bounds at zero carriers.
raw_cases=[(F(0),F(0),F(0),F(0)),(F(1,1000),F(1,3000),F(1,2000),F(0)),
 (F(1,4),F(1,5),F(1,5),F(3,20)),(F(1,4),F(1,5),F(1,5),F(1,5))]
raw_controls=[]
for gg,xx,yy,zz in raw_cases:
 need(0<=xx<=gg<=1 and 0<=yy<=gg and 0<=zz<=min(xx,yy) and xx+yy-zz<=gg,'Valid raw actual subset masses')
 lower=max(F(0),gg-xx-yy);actual=gg-xx-yy+zz;upper=gg-max(xx,yy)
 need(0<=lower<=actual<=upper<=1,'Raw lower and upper survivors including g=0')
 raw_controls.append({'g':str(gg),'X':str(xx),'Y':str(yy),'intersection':str(zz),'lower':str(lower),'actual':str(actual),'upper':str(upper)})
for left,right in zip(raw_cases,raw_cases[1:]):
 g0,x0,y0,_=left;g1,x1,y1,_=right
 need(abs((g0-max(x0,y0))-(g1-max(x1,y1)))<=abs(g0-g1)+max(abs(x0-x1),abs(y0-y1)),'Raw upper factor perturbation')
 need(abs(max(F(0),g0-x0-y0)-max(F(0),g1-x1-y1))<=abs(g0-g1)+abs(x0-x1)+abs(y0-y1),'Raw lower factor perturbation')
out={'contract':'Exact arithmetic controls of scalar geometric moduli, two-head per-depth maximum bounds, a positive-kernel zero-mask discontinuity and finite-support coefficients. No covering search, uniform positivity or Lean verification.',
'checks':checks,'phi_controls':phi_controls,'two_head_controls':max_controls,'zero_mask_controls':zero_controls,'finite_support_moduli':moduli,'raw_controls':raw_controls}
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'finite_support_moduli':moduli,'raw_controls':raw_controls},sort_keys=True))
