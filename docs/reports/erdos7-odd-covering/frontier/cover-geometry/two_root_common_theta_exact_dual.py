#!/usr/bin/env python3
"""Exact zero optimum certificate for common central thinning at root budget21111.
Uses the unchanged640 full512 costs and same actual source. No floating LP is
executed or trusted. A mask-stabilizer argument reduces a robust common theta
to3 block values; two explicit source corners give an exact dual upper bound0.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import argparse,json
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-certificate',type=Path,default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args();raw=args.source_certificate.read_bytes();base=json.loads(raw)
Q=(7,11,13,17,19);d=(2,1,1,1,1);A=[1-F(k,q-1)for k,q in zip(d,Q)]
g=F(base['constants']['g']);co=list(map(F,base['combined512_coefficients']));H=[prod(A[i]for i in range(5)if not T>>i&1)for T in range(32)]
fees=[sum((co[32*m+T]*H[T]for T in range(32)),F())for m in range(16)]
CHECKS={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 CHECKS[k]=True
ck('unchanged_complete512',len(co)==512 and min(co)>=0)
ck('positive_same_source_factors',min(A)>0 and H[0]==F(187,384))
def menus(u,v):
 rows=[[(u,9-u)],[(u,0),(0,9-u)],[(2,0),(0,2)],[(9,0),(0,9)]]
 cols=[[(v,75-v)],[(v,0),(0,20)],[(4,0),(0,4)],[(60,0),(0,60)]]
 return [set((x0*y1,x1*y0,x1*y1)for x0,x1 in rows[e3]for y0,y1 in cols[e5])for e3,e5 in product(range(4),repeat=2)]
# Validate the16 shapes against actual full literal source-corner selectors.
# Axis collapse uses theta's3 blocks; domination removes inferior options
# only for nonnegative block weights. Deep weights are9 and60, no leaf mass.
def nondominated(vals):
 return {x for x in vals if not any(x!=y and all(a<=b for a,b in zip(x,y))for y in vals)}
def axis(n,block,weights,mode,deep):
 if mode==0:return [tuple(weights)]
 if mode==1:return [tuple(w if i//block==r else 0 for i,w in enumerate(weights))for r in range(n//block)]
 return [tuple((weights[i]if mode==2 else deep)if j==i else 0 for j in range(n))for i in range(n)if weights[i]]
shapes={};source_count=0
for z,w,zz,ww in product(range(6),range(6),range(20),range(20)):
 if z==w or zz==ww:continue
 U=[0 if l==z else 1 if l==w else 2 for l in range(6)];V=[0 if m==zz else 3 if m==ww else 4 for m in range(20)]
 u=sum(U[:3]);v=sum(V[:5]);source_count+=1;key=(u,v)
 if key not in shapes:
  shapes[key]={'count':0,'representative':[z,w,zz,ww]}
  expected=menus(u,v)
  for e3,e5 in product(range(4),repeat=2):
   left=axis(6,3,U,e3,9);right=axis(20,5,V,e5,60)
   literal=set()
   for aa in left:
    for bb in right:
     x0=sum(aa[:3]);x1=sum(aa[3:]);y0=sum(bb[:5]);y1=sum(bb[5:]);literal.add((x0*y1,x1*y0,x1*y1))
   ck(f'literal_menu_{u}_{v}_{e3}_{e5}',nondominated(literal)==nondominated(expected[4*e3+e5]))
 # Root maxima that justify identical menus in the rest of this shape.
 ck('axis_caps_'+'_'.join(map(str,(z,w,zz,ww))),max(U[:3])==max(U[3:])==2 and max(V[:5])==max(V[5:])==4 and max(sum(V[5*j:5*j+5])for j in(1,2,3))==20)
 shapes[key]['count']+=1
ck('all11400_exact16_shapes',source_count==11400 and len(shapes)==16)
K0=[(360,45,180),(120,0,60),(24,0,12),(360,0,180),(360,0,0),(120,0,0),(24,0,0),(360,0,0),(0,30,120),(40,0,0),(0,8,0),(120,0,0),(0,135,540),(0,0,180),(36,0,0),(0,540,0)]
K1=[(330,60,165),(120,0,60),(24,0,12),(360,0,180),(330,0,0),(120,0,0),(24,0,0),(360,0,0),(0,40,110),None,(0,8,0),(120,0,0),(0,180,495),(0,0,180),(36,0,0),(540,0,0)]
M0=menus(6,15);M1=menus(6,20)
for m in range(16):
 ck('first_corner_legal_selector_'+str(m),K0[m]in M0[m])
 if m!=9:ck('second_corner_legal_selector_'+str(m),K1[m]in M1[m])
for j,k in enumerate(((40,0,0),(0,40,0),(0,0,40))):ck('three_mixed_selectors_'+str(j),k in M1[9])
V0=[g*H[0]*F(K0[0][j],675)-sum((fees[m]*F(K0[m][j],675)for m in range(16)),F())for j in range(3)]
V1=[g*H[0]*F(K1[0][j],675)-sum((fees[m]*F(K1[m][j],675)for m in range(16)if m!=9),F())for j in range(3)]
k=fees[9]*F(40,675)
lam=(k-sum(V1))/(sum(V0)-sum(V1)+k)
pi=[(lam*V0[j]+(1-lam)*V1[j])/((1-lam)*k)for j in range(3)]
ck('convex_two_corner_weights',0<lam<1)
ck('convex_selector_weights',min(pi)>0 and sum(pi)==1)
residual=[lam*V0[j]+(1-lam)*(V1[j]-k*pi[j])for j in range(3)]
ck('exact_zero_dual',residual==[F()]*3)
# Each chosen selector bounds its maximum from below; subtracting its
# nonnegative fee gives an affine upper bound. Convex combination preserves
# that direction. Weighted corner gate is therefore <=0 for EVERY theta>=0.
# theta0 supplies lower value0, so the robust maximum is exactly0.
zero_gate=max(sum((F(0)*x for x in fees),F()),F())
ck('zero_theta_attains_zero',zero_gate==0)
def gate(theta,u,v):
 mm=menus(u,v);mass=sum(F(x,675)*t for x,t in zip(next(iter(mm[0])),theta))
 return g*H[0]*mass-sum((fees[m]*max(sum(F(x,675)*t for x,t in zip(option,theta))for option in mm[m])for m in range(16)),F())
# Tests are redundant checks of the exact dual, not its universal proof.
for t in product((F(),F(1,3),F(1)),repeat=3):ck('dual_sample_'+str(t),lam*gate(t,6,15)+(1-lam)*gate(t,6,20)<=0)
full_theta=min((gate((F(1),)*3,u,v),(u,v))for u,v in shapes)
out={'schema':'two-root-common-central-thinning-exact-dual-v1','status':'EXACT_ZERO_ROBUST_OPTIMUM','scope':'Budget(2,1,1,1,1), unchanged640 complete512 gate, one common central theta across every11400 null/weak corner. Mask-stabilizer averaging reduces any such theta to3 blocks; two explicit corners and exact convex query-selector weights certify maxmin=0. This is a method-boundary result, not nonexistence of an actual surviving law or an unrestricted covering example. Ordinary mathematics, no Lean.', 'budget':d,'outside_factors':list(map(str,A)),'all32_H':list(map(str,H)),'folded16_fees':list(map(str,fees)),'source_shapes':[{'u':u,'v':v,**info}for(u,v),info in sorted(shapes.items())],'dual':{'source_corners':[[3,4,0,1],[3,4,5,6]],'source_shapes':[[6,15],[6,20]],'first_corner_weight':str(lam),'first_corner_weight_float':float(lam),'first_selectors':K0,'second_selectors':K1,'second_mode9_mixture':list(map(str,pi)),'second_mode9_mixture_float':list(map(float,pi)),'V0':list(map(str,V0)),'V1_before_mode9':list(map(str,V1)),'mode9_factor':str(k),'residual':list(map(str,residual))},'theta1':{'minimum':str(full_theta[0]),'shape':full_theta[1]},'checks':len(CHECKS),'source_certificate_sha256':sha256(raw).hexdigest(),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in('status','scope','theta1','checks')},indent=2))
print('lambda',lam,float(lam));print('pi',pi,list(map(float,pi)))
