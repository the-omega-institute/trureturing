#!/usr/bin/env python3
"""Actual finite pure families: naive corner mixture fails deep caps; capacity repair works.
All queries through resolving heights3 are exact. The ordinary density proof
supplies arbitrary-depth scope; finite checks do not prove that scope by scan.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from hashlib import sha256
import json
CHECKS={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 CHECKS[k]=True
# Actual ternary pure family:2mod3,0mod9,3mod27.
# Leaf3 has two surviving children; leaf6 is thinned uniformly.
s3={x:F(2,27)if x%9 in(3,1,4,7)else F(5,81)for x in range(27)if x%3!=2 and x%9!=0 and x!=3}
ck('rho3_probability',sum(s3.values())==1)
ck('rho3_density',max(s3.values())<=F(2,27))
ck('rho3_constant_actual_leaves',all(len({w for x,w in s3.items()if x%9==l})==1 for l in(3,6,1,4,7)))
w0={l:F(1,9)if l==6 else F(2,9)for l in(3,6,1,4,7)}
w1={l:F(1,9)if l==3 else F(2,9)for l in(3,6,1,4,7)}
alpha=(F(1,3),F(2,3))
w={l:sum((p for x,p in s3.items()if x%9==l),F())for l in w0}
ck('actual3_corner_leaf_decomposition',all(w[l]==alpha[0]*w0[l]+alpha[1]*w1[l]for l in w))
lam=alpha[0]*w0[3];average_theta=alpha[0];effective_theta=lam/w[3]
naive_child=effective_theta*s3[12];averaged_bound=average_theta*F(2,27)
C3=F(2)*F(2,27);repaired=min(lam,C3*average_theta);deficit=lam-repaired
ck('naive3_deep_failure',effective_theta==F(1,2)and naive_child==F(1,27)>averaged_bound==F(2,81))
ck('corner3_not_actual_capacity',w0[3]>C3)
ck('capacity3_repair',repaired==F(4,81)and deficit==F(2,81)and repaired/w[3]*s3[12]==averaged_bound)
# Actual quinary pure family:4mod5,0mod25,1mod125.
# Targetleaf1 saturates its actual capacity; leaf2 is constantly thinned.
s5={y:F(19,1875)if y%25==2 else F(4,375)for y in range(125)if y%5!=4 and y%25!=0 and y!=1}
ck('rho5_probability',sum(s5.values())==1)
ck('rho5_density',max(s5.values())<=F(4,375))
leaves5=sorted({y%25 for y in s5})
ck('rho5_constant_actual_leaves',all(len({p for y,p in s5.items()if y%25==m})==1 for m in leaves5))
v0={m:F(3,75)if m==2 else F(4,75)for m in leaves5};v1={m:F(3,75)if m==1 else F(4,75)for m in leaves5};beta=(F(1,5),F(4,5))
v={m:sum((p for y,p in s5.items()if y%25==m),F())for m in leaves5}
ck('actual5_corner_leaf_decomposition',all(v[m]==beta[0]*v0[m]+beta[1]*v1[m]for m in v))
C5=F(4,3)*F(4,125);gamma=alpha[0]*beta[0]
# Only theta^(0,0) retains the targetcell(3,1); all other fields vanish.
joint_lam=gamma*w0[3]*v0[1];a3=gamma*v0[1];a5=gamma*w0[3];a35=gamma
limits=(joint_lam,C3*a3,C5*a5,C3*C5*a35);joint_star=min(limits)
mu={(x,y):joint_star/(w[3]*v[1])*p*q for x,p in s3.items()for y,q in s5.items()if x%9==3 and y%25==1}
ck('joint_actual_source_domination',all(p<=s3[x]*s5[y]for(x,y),p in mu.items()))
ck('joint_source_support',len(mu)==8 and sum(mu.values())==joint_star)
ck('joint_repair_values',joint_lam==F(8,10125)and joint_star==F(64,151875)and joint_lam-joint_star==F(56,151875))
naive_atom=joint_lam/(w[3]*v[1])*s3[12]*s5[26]
deep_bound=gamma*F(2,27)*F(4,375)
ck('joint_naive_double_deep_failure',naive_atom==F(1,10125)>deep_bound==F(8,151875))
ck('joint_repair_double_deep_exact',mu[12,26]==deep_bound)
# Verify every actual prefix pair through the resolving depths, not only
# the16 modal maxima. At deeper levels the same constant densities apply.
query_count=0
for e,f in product(range(4),repeat=2):
 n3=3**e;n5=5**f;mass={}
 for(x,y),p in mu.items():mass[x%n3,y%n5]=mass.get((x%n3,y%n5),F())+p
 for a,b in product(range(n3),range(n5)):
  # A query can meet the targetleaf iff their shared prefix agrees.
  meet3=a%(3**min(e,2))==3%(3**min(e,2));meet5=b%(5**min(f,2))==1%(5**min(f,2))
  cap3=w0[3]if e<=2 else F(2,3**e)
  cap5=v0[1]if f<=2 else F(4,3*5**f)
  bound=gamma*cap3*cap5 if meet3 and meet5 else F()
  ck(f'all_prefix_{e}_{a}_{f}_{b}',mass.get((a,b),F())<=bound);query_count+=1
ck('all6240_prefix_pairs',query_count==6240)
# A released mass debit is paid by g times mass in the unit-inclusive gate.
g=F(200163067,201247200);outside_h0=F(187,384)
penalty=g*outside_h0*(joint_lam-joint_star)
out={'schema':'actual-corner-capacity-repair-examples-v1','status':'PASS','scope':'Actual624-style constant-density pure-survivor sources at3 and5; numerical leaf-corner mixtures do not have automatic deep-cap transport. Capped repaired submeasure is checked against every6240 prefix pair through resolving heights3. Ordinary density proof handles allhigher queries; no positive universal gate or Lean claim.','ternary':{'pure_originals':[[3,2],[9,0],[27,3]],'weights':list(map(str,alpha)),'actual_rho':{str(x):str(p)for x,p in s3.items()},'lambda':str(lam),'theta_effective':str(effective_theta),'naive_child':str(naive_child),'averaged_deep_bound':str(averaged_bound),'actual_capacity':str(C3),'repaired_mass':str(repaired),'mass_deficit':str(deficit)},'quinary':{'pure_originals':[[5,4],[25,0],[125,1]],'weights':list(map(str,beta)),'actual_rho':{str(y):str(p)for y,p in s5.items()},'actual_capacity':str(C5)},'joint':{'corner_weight':str(gamma),'lambda':str(joint_lam),'limits':list(map(str,limits)),'lambda_repaired':str(joint_star),'mass_deficit':str(joint_lam-joint_star),'naive_deep_atom':str(naive_atom),'averaged_deep_bound':str(deep_bound),'complete_gate_mass_penalty':str(penalty)},'checks':len(CHECKS),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in('status','scope','joint','checks')},indent=2))
