#!/usr/bin/env python3
"""Exact two-root convex clipping certificate and global supporting dual."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from math import prod
import argparse
import hashlib
import json

ap=argparse.ArgumentParser()
ap.add_argument('--hinge-input',default=str(Path(__file__).with_name('height_three_clipping_envelope.json')))
ap.add_argument('--output',default=str(Path(__file__).with_suffix('.json')))
args=ap.parse_args()
checks=[]
def need(name,p):
    if not p: raise ValueError(name)
    checks.append(name)

source_bytes=Path(args.hinge_input).read_bytes()
source=json.loads(source_bytes)
B=F(source['B'])
target=F(566,49)
corners=[[F(v) for v in c['K_integer'][:8]] for c in source['corners']]
need('same actual PA query supplier',B==F(432040125182653876501,86355045355449035400))
need('complete four low-threshold corner profiles',len(corners)==4 and all(len(c)==8 for c in corners))
need('corner zero dominates every integer endpoint',all(corners[0][n]>=corners[i][n] for n in range(8) for i in range(1,4)))
K=corners[0]
K3=K[3]
r=(24+48*B)/(24-K3)
q=2-(1+3*B)/r
y=3+K3/q
alpha=(1+(1+B)/(r*q))/2
need('exact candidate r',r==F(7548357118614250413488684,625732567524997445251785))
need('dual is a two-point probability',0<q<1)
need('dual atom lies below both root scales',6<y<7<12)
need('dual convex weights',0<alpha<1)
need('dual also respects the complete first moment',q*y<B)

def low_K(t):
    if t==7:return K[7]
    n=t.numerator//t.denominator
    return (n+1-t)*K[n]+(t-n)*K[n+1]

support_rows=[]
for t in sorted({F(n) for n in range(8)}|{y}):
    k=low_K(t)
    lower=q*max(F(0),y-t)
    need('supporting scalar hinge at '+str(t),k>=lower)
    support_rows.append({'t':t,'K':k,'dual_hinge':lower,'gap':k-lower})
need('contact at threshold three',K3==q*(y-3))
need('positive entire low-threshold profile',all(k>=0 for k in K))
need('dual first cancellation',r*q==2*r-1-3*B)
need('dual second cancellation',r*q*(15-y)==12*(1+B))
need('dual weight cancellation',(2*alpha-1)*r*q==1+B)
constant=B-r+(1+B)+r*q*(1-alpha)
w_coefficient=-(1+B)+r*q*(2*alpha-1)
x_coefficient=9*(1+B)-r*q*(alpha*(12-y)+(1-alpha)*(18-y))
need('global certificate dual has zero constant and coefficients',constant==w_coefficient==x_coefficient==0)

def hinge_terms(la,ta,lb,tb):
    if ta>tb:la,ta,lb,tb=lb,tb,la,ta
    if la>=lb:return [(la,ta)]
    cross=(lb*tb-la*ta)/(lb-la)
    return [(la,ta),(lb-la,cross)]

# Setting the unneeded high-threshold costs to zero is optimistic. Every
# nonnegative valid extension costs at least this relaxation. This is used
# only to diagnose the LOWER dual, never to claim an actual upper bound.
def optimistic_K(t):
    return low_K(t) if t<=7 else F(0)

control_count=0
for w,ta,tb in product((F(0),F(1,8),F(3,8),F(1,2),F(5,8),F(7,8),F(1)),
                       map(F,(0,1,3,6,9,11)),map(F,(0,1,3,7,12,17))):
    la=w/(12-ta);lb=(1-w)/(18-tb)
    terms=hinge_terms(la,ta,lb,tb)
    knots={F(0),ta,tb,y,*[t for _,t in terms]}
    probes=knots|{t+1 for t in knots}
    if not all(sum(c*max(F(0),z-t) for c,t in terms)==max(la*max(F(0),z-ta),lb*max(F(0),z-tb)) for z in probes):
        raise ValueError(('hinge decomposition',w,ta,tb))
    cost=sum(c*optimistic_K(t) for c,t in terms)
    x=max(la,lb)
    N=B+(1+B)*(max(w,1-w)+9*x)
    if cost<q*max(la*max(F(0),y-ta),lb*max(F(0),y-tb)) or N-r*(1-cost)<0:
        raise ValueError(('global dual control',w,ta,tb))
    control_count+=1
need('all rational hinge and global-dual controls',control_count==252)

w=F(3,8);ta=tb=F(3);la=w/(12-ta);lb=(1-w)/(18-tb)
N=B+(1+B)*(max(w,1-w)+9*max(la,lb))
cost=la*K3
need('candidate equal slopes and legal clips',la==lb==F(1,24) and 1-ta/12==F(3,4) and 1-tb/18==F(5,6))
need('candidate positive mass certificate',0<1-cost)
need('candidate attains dual globally',N/(1-cost)==r)
need('full two-root envelope misses continuation gate',r>target)

# Actual fixed original family and all32 Q-activation atoms.
primes=(5,7,11,13,17)
ternary=(0,6,9,15,18)
originals=[{'m':3,'a':1},{'m':9,'a':3}]
for p,a in zip(primes,ternary):
    full_a=a+81*((-a*pow(81,-1,p))%p)
    originals.append({'m':81*p,'a':full_a})
need('actual original labels are distinct',len({c['m'] for c in originals})==7)
need('actual full CRT phases retained',all(c['a']%81==a and c['a']%p==0 for c,p,a in zip(originals[2:],primes,ternary)))
A=[t for t in range(81) if t%3==0 and t%9!=3]
Broot=[t for t in range(81) if t%3==2]
need('actual root fibre sizes',len(A)==18 and len(Broot)==27 and len(set(ternary))==5 and all(t in A for t in ternary))
raw_mass=F(0);hinge_mass=F(0);nu_mass=F(0)
for bits in product((0,1),repeat=5):
    prob=prod(F(1,p) if b else F(p-1,p) for p,b in zip(primes,bits))
    forbidden={a for a,b in zip(ternary,bits) if b}
    ca=F(sum(t not in forbidden for t in A),len(A))
    cb=F(sum(t not in forbidden for t in Broot),len(Broot))
    n=sum(bits)
    if ca!=1-F(n,18) or cb!=1:
        raise ValueError(('actual fibre',bits))
    beta=w*min(F(1),ca/F(3,4))+(1-w)*min(F(1),cb/F(5,6))
    raw_mass+=prob*beta
    hinge_mass+=prob*F(1,24)*max(F(0),F(2*n,3)-3)
    nu_mass+=prob
need('actual Q atoms form one probability',nu_mass==1)
need('nonzero actual clipping loss attains its scalar majorant',1-raw_mass==hinge_mass==F(1,6126120))
all_active_ca=F(sum(t not in set(ternary) for t in A),len(A))
eta_root_A=w*all_active_ca/max(all_active_ca,F(3,4))
eta_root_B=1-w
conditional_root_A=eta_root_A/(eta_root_A+eta_root_B)
fixed_u_root_A=w*all_active_ca/(w*all_active_ca+1-w)
need('root-dependent normalization differs from fixed-u normalization',
     conditional_root_A==F(26,71) and fixed_u_root_A==F(13,43)
     and conditional_root_A!=fixed_u_root_A)

result={'scope':'Exact global certificate dual for the full max-two-hinge envelope; not an actual-query lower bound or source-realizability claim.',
 'hinge_input_sha256':hashlib.sha256(source_bytes).hexdigest(),'B':B,'K3':K3,'target':target,
 'optimum':r,'gap':r-target,'q':q,'y':y,'alpha':alpha,'dual_mean':q*y,
 'supporting_hinge':support_rows,'rational_parameter_controls':control_count,
 'actual_originals':originals,'actual_raw_mass':raw_mass,'actual_loss':hinge_mass,
 'actual_all_active_root_conditional':conditional_root_A,
 'actual_fixed_u_all_active_root_conditional':fixed_u_root_A,
 'check_count':len(checks),'checks':checks}
Path(args.output).write_text(json.dumps(result,default=str,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'parameter_controls':control_count,'optimum':str(r),
                  'optimum_decimal':float(r),'gap':str(r-target),'actual_loss':str(hinge_mass)}))
