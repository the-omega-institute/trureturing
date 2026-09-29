#!/usr/bin/env python3
"""Exact continuous threshold optimization for the single clipped-law certificate.
No finite grid is substituted for a continuous optimum.
"""
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from pathlib import Path
import json

ROWS=((11,2,F(5,3)),(13,2,F(3,2)),(17,4,F(2)),(19,4,F(9,5)))
B=F(432040125182653876501,86355045355449035400)
T=F(566,49);theta=F(1,27);LIMIT=28
checks=[]
def need(name,p):
 if not p:raise ValueError(name)
 checks.append(name)
def coordinate(p,m,c):
 return (m,m+c/(p-1),{n:(m-c/p if n==1 else c*F(p-1,p**n)) for n in range(1,LIMIT+1)})
def mul(a,b):
 z={}
 for i,u in a[2].items():
  for j,v in b[2].items():
   if i*j<=LIMIT:z[i*j]=z.get(i*j,F(0))+u*v
 return a[0]*b[0],a[1]*b[1],z
def hinge(law,r):return law[1]-r*law[0]+sum((r-i)*w for i,w in law[2].items() if i<r)
unit=(F(1),F(1),{1:F(1)})
suffix=[]
for j in range(5):
 a=unit
 for p,t,c in ROWS[j:]:a=mul(a,coordinate(p,F(1),c))
 suffix.append(a)
cs=[]
for x,y in product((F(1,2),F(1)),(F(2,3),F(1))):
 a=mul(coordinate(5,x,F(1)),coordinate(7,y,F(1)));alpha=x*y-F(1,12);charges=[]
 for p,t,c in ROWS:
  charge=2*c/(p-1)*hinge(a,F(t));charges.append(charge);alpha-=charge;a=mul(a,coordinate(p,F(1),c))
 need('positive alpha '+str(x)+' '+str(y),alpha>0)
 values=[]
 for t in range(28):
  z=[hinge(s,F(t+1)) for s in suffix]
  values.append((hinge(a,F(t+1))-z[0]/12-sum(zz*dd for zz,dd in zip(z[1:],charges)))/alpha)
 cs.append({'x':x,'y':y,'alpha':alpha,'charges':charges,'K_integer':values})

# On each integer interval every corner is affine. All pairwise crossings
# are rational; a complete breakpoint list suffices even if some crossings
# are not on the upper envelope.
knots={F(i) for i in range(28)}
crossings=[]
for n in range(27):
 for i,j in combinations(range(4),2):
  a=cs[i]['K_integer'][n]-cs[j]['K_integer'][n]
  b=(cs[i]['K_integer'][n+1]-cs[i]['K_integer'][n])-(cs[j]['K_integer'][n+1]-cs[j]['K_integer'][n])
  if b:
   s=-a/b
   if 0<s<1:
    knots.add(F(n)+s);crossings.append({'t':F(n)+s,'pair':[i,j]})
knots=sorted(knots)
def value(t,i):
 n=min(t.numerator//t.denominator,26);s=t-n
 return (1-s)*cs[i]['K_integer'][n]+s*cs[i]['K_integer'][n+1]
def K(t):return max(value(t,i) for i in range(4))
def affine_suffix(t,j):
 n=min(t.numerator//t.denominator,26);s=t-n
 return (1-s)*hinge(suffix[j],F(n+1))+s*hinge(suffix[j],F(n+2))
records=[]
for t in knots:
 k=K(t);kap=1-theta*t;den=kap-theta*k;num=kap*B+1+B
 need('all debit coefficients admissible at '+str(t),k>=max(affine_suffix(t,j) for j in range(5)))
 records.append({'t':t,'kappa':kap,'K':k,'active_corners':[i for i in range(4) if value(t,i)==k],
                 'denominator':den,'R':num/den if den>0 and kap>0 else None,
                 'gate':T*den-num})
valid=[r for r in records if r['R'] is not None]
best=min(valid,key=lambda r:r['R']);bestgate=max(records,key=lambda r:r['gate'])
need('corner zero dominates all corners at every integer endpoint',all(cs[0]['K_integer'][n]>=cs[i]['K_integer'][n] for n in range(28) for i in range(1,4)))
need('exact certificate minimum remains above gate',best['R']>T)
need('maximum affine gate remains negative',bestgate['gate']<0)
need('recover574 threshold3 hinge',K(F(3))==F(12019840537595758779003,5715264751774801992890))
result={'scope':'Exact entire t in [0,27) for unmodified PA source, full suffix deletion credits, four-corner K envelope and one scalar clipping threshold. Certificate failure only.',
 'B':B,'theta':theta,'target':T,'corners':cs,'crossings':crossings,'breakpoints':records,'best':best,'best_gate':bestgate,
 'check_count':len(checks),'checks':checks}
with Path(__file__).with_suffix('.json').open('w') as f:json.dump(result,f,default=str,indent=2);f.write('\n')
print(json.dumps({'checks':len(checks),'crossings':len(crossings),'best_t':str(best['t']),'best_kappa':str(best['kappa']),'best_R':str(best['R']),'best_R_decimal':float(best['R']),'best_gate_t':str(bestgate['t']),'max_gate':str(bestgate['gate'])}))
