#!/usr/bin/env python3
"""Weak-priority corner selections: one actual source and a positive complete gate.
The complete gate lower bound reuses643's full512 certificate via monotonicity;
this does not re-enumerate its corners. A literal higher-pure source checks all
central prefixes through resolving heights3 and all32 outside response fields.
All-height scope belongs to the ordinary same-source density proof.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
from collections import Counter
import argparse,json
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-certificate',type=Path,default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
ap.add_argument('--conditional-certificate',type=Path,default=Path(__file__).with_name('conditional_second7_root_certificate.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=ap.parse_args();raw=a.source_certificate.read_bytes();base=json.loads(raw);cr=a.conditional_certificate.read_bytes();cond=json.loads(cr)
checks=Counter()
def ck(k,b):
 if not b:raise ArithmeticError(k)
 checks[k]+=1
co=list(map(F,base['combined512_coefficients']));g=F(base['constants']['g']);h=list(map(F,base['all32_outside_responses']));eps=F(1,1000)
ck('full512_nonnegative',len(co)==512 and min(co)>=0)
ck('conditional_source_pin',cond['source_certificate_sha256']==sha256(raw).hexdigest())
positive=[r for r in cond['mask_records']if F(r['minimum'])>0];gamma=min(F(r['minimum'])for r in positive)
ck('inherited_complete_positive_class',len(positive)==23 and gamma==F(cond['minimum_positive_gate']))
ck('actual_outside_mass_envelope',h[0]==F(935,1536))
delta=gamma-g*eps*h[0]
ck('uniform_positive_complete_gate',delta==F(11487698589965543917,119465707774887936000000)and delta>F(1,11000))
# Physical actual624 sources, constant on each surviving leaf.
s3={x:F(2,27)if x%9 in(3,1,4,7)else F(5,81)for x in range(27)if x%3!=2 and x%9!=0 and x!=3}
s5={y:F(19,1875)if y%25==2 else F(4,375)for y in range(125)if y%5!=4 and y%25!=0 and y!=1}
leaf3=lambda l:l//3+3*(l%3)
leaf5=lambda m:m//5+5*(m%5)
inv3={leaf3(l):l for l in range(6)};inv5={leaf5(m):m for m in range(20)}
live3=tuple(range(1,6));live5=tuple(range(1,20));S={1,3}
w={l:sum((p for x,p in s3.items()if x%9==leaf3(l)),F())for l in live3}
v={m:sum((p for y,p in s5.items()if y%25==leaf5(m)),F())for m in live5}
C3={l:F(2)*F(sum(x%9==leaf3(l)for x in s3),27)for l in live3}
C5={m:F(4,3)*F(sum(y%25==leaf5(m)for y in s5),125)for m in live5}
alpha={l:9*(F(2,9)-w[l])for l in live3};beta={m:75*(F(4,75)-v[m])for m in live5}
ck('actual_probabilities',sum(s3.values())==sum(s5.values())==1)
ck('actual_density_caps',max(s3.values())<=F(2,27)and max(s5.values())<=F(4,375))
ck('product_mixing',sum(alpha.values())==sum(beta.values())==1 and min(alpha.values())>=0 and min(beta.values())>=0)
ck('actual_capacity_deficiency_correlation',all(alpha[l]>=9*(F(2,9)-C3[l])for l in live3)and all(beta[m]>=75*(F(4,75)-C5[m])for m in live5))
corner3=lambda i,l:F(1,9)if i==l else F(2,9)
corner5=lambda j,m:F(3,75)if j==m else F(4,75)
def theta(i,j,l,m):
 return F()if l<3 and m<5 else 1-eps*(i!=l and j!=m)
fields={}
for l,m in product(live3,live5):
 lam=a3=a5=a35=F()
 for i,j in product(live3,live5):
  th=theta(i,j,l,m)
  ck('weak_priority',theta(l,j,l,m)>=th and theta(i,m,l,m)>=th)
  mass=alpha[i]*beta[j]*th;wi=corner3(i,l);vj=corner5(j,m)
  lam+=mass*wi*vj;a3+=mass*vj;a5+=mass*wi;a35+=mass
 ck('actual_submeasure',0<=lam<=w[l]*v[m])
 ck('old_query_fields_without_clipping',lam<=w[l]*a3 and lam<=v[m]*a5 and lam<=w[l]*v[m]*a35)
 ck('capacity_clip_exactly_zero_loss',min(lam,C3[l]*a3,C5[m]*a5,C3[l]*C5[m]*a35)==lam)
 fields[l,m]=(lam,a3,a5,a35)
ck('nonconstant_corner_selection',theta(1,5,1,5)==1 and theta(2,10,1,5)==1-eps)
mu={(x,y):fields[inv3[x%9],inv5[y%25]][0]/(w[inv3[x%9]]*v[inv5[y%25]])*p*q for x,p in s3.items()for y,q in s5.items()}
ck('actual_source_domination',all(p<=s3[x]*s5[y]for(x,y),p in mu.items()))
# An actual conditional outside root restriction: roots0 pure-null, root1
# removed everywhere, root2 additionally removed at7 on the two leaves S.
Q=(7,11,13,17,19)
A={}
for l in live3:
 for q in Q:
  excluded={1,2}if q==7 and l in S else{1}
  law={r:F(1,q-1)for r in range(1,q)if r not in excluded}
  A[l,q]=sum(law.values())
  ck('one_actual_outside_restriction',A[l,q]==1-F(len(excluded),q-1)and all(p==F(1,q-1)for p in law.values()))
H={(T,l):prod(A[l,q]for j,q in enumerate(Q)if not T>>j&1)for T in range(32)for l in live3}
for T,l in product(range(32),live3):
 ck('same32_conditional_response_fields',H[T,l]==h[T]*(1-F(l in S,5)if not T&1 else 1))
# Compare actual central-prefix mass multiplied by the common outside envelope
# to the corner-averaged envelope. At queried outside coordinates the actual
# root restriction is dominated by its unconditioned root-balanced source.
queries=0
for T in range(32):
 for e,f in product(range(4),repeat=2):
  n3,n5=3**e,5**f;actual={};bound={}
  for(x,y),p in mu.items():
   key=x%n3,y%n5;actual[key]=actual.get(key,F())+p*H[T,inv3[x%9]]
  for(l,m),(lam,a3,a5,a35)in fields.items():
   val=lam if e<=2 and f<=2 else F(2,n3)*a3 if f<=2 else F(4,3*n5)*a5 if e<=2 else F(8,3*n3*n5)*a35
   val*=H[T,l]
   aa=[leaf3(l)%n3]if e<=2 else range(leaf3(l),n3,9)
   bb=[leaf5(m)%n5]if f<=2 else range(leaf5(m),n5,25)
   for x,y in product(aa,bb):bound[x,y]=bound.get((x,y),F())+val
  for x,y in product(range(n3),range(n5)):
   ck('all32_times6240_prefix_bounds',actual.get((x,y),F())<=bound.get((x,y),F()));queries+=1
ck('query_inventory',queries==32*6240)
out={'schema':'weak-priority-actual-mixing-v1','status':'PASS','scope':__doc__,'epsilon':str(eps),'inherited_positive_mask_count':len(positive),'inherited_minimum_gate':str(gamma),'outside_mass_envelope':str(h[0]),'uniform_complete_gate':str(delta),'head_haar_lower_bound':str(F(base['constants']['alpha'])*delta),'actual_example':{'pure3_originals':[[3,2],[9,0],[27,3]],'pure5_originals':[[5,4],[25,0],[125,1]],'ternary_null_index':0,'quinary_null_index':0,'conditional_second7_leaves':sorted(S),'alpha':{str(k):str(x)for k,x in alpha.items()},'beta':{str(k):str(x)for k,x in beta.items()},'central_mass':str(sum(mu.values())),'outside_integrated_mass':str(sum((p*H[0,inv3[x%9]]for(x,y),p in mu.items()),F()))},'checks':dict(checks),'check_count':sum(checks.values()),'source_certificate_sha256':sha256(raw).hexdigest(),'conditional_certificate_sha256':sha256(cr).hexdigest(),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False}
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in('status','uniform_complete_gate','head_haar_lower_bound','check_count')},indent=2))
