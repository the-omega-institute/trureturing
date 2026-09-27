#!/usr/bin/env python3
"""Fixed109 source with joint q7/q11 root and child retention.
Exact standard-library replay of the fixed dual, without an optimizer. No phase optimization.
"""
from pathlib import Path
from argparse import ArgumentParser
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
p=ArgumentParser(description=__doc__)
p.add_argument('--fixture',type=Path,default=HERE/'clustered_global_phase_fixture.json')
p.add_argument('--higher',type=Path,default=HERE/'clustered_higher_pure_capacity_obstruction.json')
p.add_argument('--source640',type=Path,default=HERE/'remaining33_global_root_exclusion_certificate.json')
p.add_argument('--output',type=Path,default=HERE/'clustered_q7_q11_retention_obstruction_verification.json')
p.add_argument('--candidate',type=Path,default=HERE/'clustered_q7_q11_retention_obstruction.json')
a=p.parse_args();checks={}
def ck(k,ok):
 checks[k]=checks.get(k,0)+1
 if not ok:raise RuntimeError(k)
Q=(7,11,13,17,19);fix=json.loads(a.fixture.read_text());higher=json.loads(a.higher.read_text());originals=fix['actual_originals'];local=[[] for q in Q]
ck('same_base_fixture',sha256(a.fixture.read_bytes()).hexdigest()==higher['input_sha256'][a.fixture.name])
ck('actual_n4_extension',higher['first_tested_success']['n']==4)
added=higher['first_tested_success']['added_higher_pure_originals'];ck('109_distinct_originals',len({o['modulus'] for o in originals+added})==109)
for o in originals:
 c=o['modulus'];b=o['residue'];qs=[]
 for i,q in enumerate(Q):
  if c%q==0:
   power=1
   while c%q==0:c//=q;power*=q
   qs.append((i,power))
 if len(qs)==1 and c>1:
  i,d=qs[0];local[i].append((c,b%c,d,b%d))
 if len(qs)==2:ck('same_pair_root1',all(b%Q[i]==1 for i,d in qs))
for i,j in combinations(range(5),2):ck('root_pair_present',any(o['modulus']==Q[i]*Q[j] and o['residue']==1 for o in originals))
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5);cells=tuple((l,m) for l,m in product(I,J) if not(l<3 and m<5))
w=[F(0) if l==3 else F(1,9) if l==4 else F(2,9) for l in range(6)];v=[F(0) if m==5 else F(3,75) if m==10 else F(4,75) for m in range(20)]
gamma3=F(81,82);gamma5=F(1875,1876)
counts={};A={};B={};category_counts={}
for l,m in cells:
 c=next(x for x in range(l//3+3*(l%3),225,9) if x%25==m//5+5*(m%5))
 rows=[]
 for i,q in enumerate(Q):
  atoms=[z for z in range(q*q) if z%q and all(c%cm!=cr or z%qm!=qr for cm,cr,qm,qr in local[i])]
  rows.append(atoms)
  if i>=2:ck('other_queried_root9_free',all(9+q*k in atoms for k in range(q)))
 counts[l,m]=rows;A[l,m]=[F(sum(z%q==1 for z in rows[i]),q*(q-1)) for i,q in enumerate(Q)];B[l,m]=[F(sum(z%q!=1 for z in rows[i]),q*(q-1)) for i,q in enumerate(Q)]
 cats7=[sum(z==1 for z in rows[0]),sum(z%7==1 and z!=1 for z in rows[0])]+[sum(z%7==r for z in rows[0]) for r in range(2,7)]
 cats11=[sum(z==1 for z in rows[1]),sum(z%11==1 and z!=1 for z in rows[1])]+[sum(z%11==r for z in rows[1]) for r in range(2,9)]+[sum(z%11 in (9,10) for z in rows[1])]
 ck('seven_category_partition',sum(cats7)==len(rows[0]) and cats7[0] in (0,1) and cats7[1] in (0,6) and all(x in (0,7) for x in cats7[2:]))
 ck('eleven_category_partition',sum(cats11)==len(rows[1]) and cats11[0] in (0,1) and cats11[1] in (0,10) and all(x in (0,11) for x in cats11[2:9]) and cats11[9]==22)
 category_counts[l,m]=(cats7,cats11)
variables=[(l,m,k,h) for l,m in cells for k in range(7) for h in range(10) if category_counts[l,m][0][k] and category_counts[l,m][1][h] and not(k<2 and h<2)]
index={x:i for i,x in enumerate(variables)}
# First-root/deep normalization is separate from unqueried class mass.
def factor(q,cats,k,choice):
 count=cats[k]
 if not count:return F(0)
 if choice==-1:return F(count,q*(q-1))
 if choice==0:return F(count,q) if k<2 else F(0)
 if q==7:
  if 1<=choice<=5:return F(int(k==choice+1))
  return F(5,6) if k==choice-6 else F(0)
 if 1<=choice<=7:return F(int(k==choice+1))
 if choice==8:return F(int(k==9)) # One root9 query, not the two-root class mass.
 return F(9,10) if k==0 else F(0)
def querychoices(T):return product(range(8) if T&1 else (-1,),range(10) if T&2 else (-1,))
patterns={};outside={}
for l,m in cells:
 cats7,cats11=category_counts[l,m]
 for c7,c11 in product(range(-1,8),range(-1,10)):
  row=[]
  for k in range(7):
   for h in range(10):
    if (l,m,k,h) not in index:continue
    z=factor(7,cats7,k,c7)*factor(11,cats11,h,c11)
    if z:row.append((index[l,m,k,h],z,int(k<2 or h<2)))
  patterns[l,m,c7,c11]=row
 for T in range(0,32,4):
  U=[i for i in range(2,5) if not(T>>i&1)];zero=prod(B[l,m][i] for i in U)
  one=zero+sum((A[l,m][j]*prod(B[l,m][i] for i in U if i!=j) for j in U),F(0))
  ck('other_factor_positive',0<zero<=one<=1)
  outside[l,m,T]=(one,zero)
base_raw=a.source640.read_bytes();ck('source640_pin',sha256(base_raw).hexdigest()=='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4')
C=list(map(F,json.loads(base_raw)['combined512_coefficients']));g=F(200163067,201247200)
# Full events9q², not the guarded residual mode9.
for i,q in enumerate(Q):
 if i:C[256+(1<<i)]+=g*F(1,q*(q-2))
ck('complete_full_fees',len(C)==512 and min(C)>=0)
def axis(weights,level,block,deep,weak,gamma):
 live=[i for i,t in enumerate(weights) if t]
 if level==0:return [(0,weights)]
 if level==1:return [(r,[a0 if i//block==r else F(0) for i,a0 in enumerate(weights)]) for r in range(len(weights)//block)]
 if level==2:return [(t,[a0 if i==t else F(0) for i,a0 in enumerate(weights)]) for t in live]
 return [(t,[deep*(gamma if t==weak else 1) if i==t else F(0) for i in range(len(weights))]) for t in live]
selectors=[];bymode=[]
for mode in range(16):
 ex,ey=divmod(mode,4);ids=[]
 for (left,x),(right,y) in product(axis(w,ex,3,F(1),4,gamma3),axis(v,ey,5,F(4,5),10,gamma5)):
  ids.append(len(selectors));selectors.append((mode,left,right,[(l,m,x[l]*y[m]) for l,m in cells if x[l]*y[m]]))
 bymode.append(ids)
ck('complete_literal_selectors',len(selectors)==559)
source=[F(0)]*len(variables)
for l,m in cells:
 for col,normal,hasone in patterns[l,m,-1,-1]:source[col]+=g*w[l]*v[m]*normal*outside[l,m,0][hasone]
ck('exact_actual_source_mass_before_retention',sum(source,F(0))/g==F(305684996597,646498195200))
candidate_raw=a.candidate.read_bytes();candidate=json.loads(candidate_raw)
ck('candidate_schema',candidate['schema']=='clustered-q7-q11-retention-obstruction-v1')
for pp in (a.fixture,a.higher,a.source640):ck('candidate_input_pin',sha256(pp.read_bytes()).hexdigest()==candidate['source_sha256'][pp.name])
ck('literal_central_capacity_parameters',candidate['central_nulls']==[3,5] and candidate['central_weak_leaves']==[4,10] and candidate['higher_pure_depth']==4 and F(candidate['gamma3'])==gamma3 and F(candidate['gamma5'])==gamma5)
ck('literal_eight_new_pure_originals',{(x['modulus'],x['residue']) for x in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)})
ck('higher_pure_capacity_identity',F(higher['first_tested_success']['gamma3'])==gamma3 and F(higher['first_tested_success']['gamma5'])==gamma5)
actual_capacities=[];actual_densities=[]
for prime,weak,weight,reference,expected in ((3,4,F(1,9),F(2),F(41,729)),(5,2,F(1,25),F(4,3),F(469,15625))):
 pure=[(o['modulus'],o['residue']) for o in added if o['modulus']%prime==0]
 depth=max(m for m,r in pure)
 count=sum(all(x%m!=r for m,r in pure) for x in range(weak,depth,prime*prime))
 capacity=F(count,depth);density=weight/capacity
 ck('actual_weak_capacity',capacity==expected)
 ck('actual_weak_density_ratio',density/reference==(gamma3 if prime==3 else gamma5))
 actual_capacities.append(capacity);actual_densities.append(density)
domination_factor=F(1)/(gamma3*gamma5)
ck('joint_central_domination_factor',domination_factor==F(153832,151875))
ck('deep_other11_dominated_by_firstroot',F(10,11)>F(9,10))
for l,m in cells:
 cat7,cat11=category_counts[l,m]
 ck('free11_actual_unqueried_mass',factor(11,cat11,9,-1)==F(1,5))
 ck('free11_actual_fixedroot_query',factor(11,cat11,9,8)==1)
D=candidate['dual_denominator'];ck('positive_dual_denominator',isinstance(D,int) and D>0)
residual=source[:];loads=[F(0)]*512;seen=set();selector_map={(mode,left,right):row for mode,left,right,row in selectors}
# Separate exact test of whether these SAME multipliers lift to all outside fields.
root2_mass=prod(F(1,q-1) for q in Q);lift_source=g*w[4]*v[10]*root2_mass;lift_debit=F(0)
for i,q in enumerate(Q):ck('root2_joint_lift_field_actual',all(2+q*k in counts[4,10][i] for k in range(q)))
for mode,T,c7,c11,left,right,N in candidate['dual_rows']:
 ck('literal_dual_selector',(mode,left,right) in selector_map and 0<=T<32 and c7 in (range(8) if T&1 else (-1,)) and c11 in (range(10) if T&2 else (-1,)))
 ck('nonnegative_dual_numerator',isinstance(N,int) and N>0)
 address=(mode,T,c7,c11,left,right);ck('unique_dual_address',address not in seen);seen.add(address)
 lam=F(N,D);loads[32*mode+T]+=lam;selector=selector_map[mode,left,right]
 for l,m,co in selector:
  out=outside[l,m,T&28]
  for col,normal,hasone in patterns[l,m,c7,c11]:residual[col]-=lam*co*normal*out[hasone]
  if (l,m)==(4,10) and not(T&28):
   f7=F(int(c7==1)) if T&1 else F(1,6);f11=F(int(c11==1)) if T&2 else F(1,10)
   lift_debit+=lam*co*f7*f11*prod(F(1,q-1) for q in Q[2:])
for j in range(512):ck('every_exact_fee_budget',loads[j]<=C[j])
upper=sum((max(F(0),x) for x in residual),F(0));ex=candidate['expected']
ck('exact_universal_upper',upper==F(ex['universal_upper']))
ck('target_not_paid',upper<F(ex['upper_ceiling'])<F(ex['target']))
lifted_upper=domination_factor*upper
ck('joint_density_lift_exact',lifted_upper==F(1507661452610803341661,8576320051036237500000000000000))
ck('joint_density_lift_below_target',lifted_upper<F(ex['target']))
ck('literal_field_dimensions',len(variables)==ex['active_field_columns']==3484 and len(candidate['dual_rows'])==ex['dual_nonzero_count']==2568)
lift_residual=lift_source-lift_debit
ck('frozen_dual_fails_pointwise_lifting',lift_residual==F(737374609602494947,48120620486400000000000000) and lift_residual>upper)
result=dict(schema='clustered-q7-q11-retention-obstruction-verification-v1',status='PASS',optimizer_used=False,new_lean_verification=False,candidate_sha256=sha256(candidate_raw).hexdigest(),verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),source_sha256={pp.name:sha256(pp.read_bytes()).hexdigest() for pp in (a.fixture,a.higher,a.source640)},active_field_columns=len(variables),dual_nonzero_count=len(candidate['dual_rows']),source_mass=str(sum(source,F(0))/g),universal_upper=str(upper),target=ex['target'],Dscaled_upper=str(upper*F(429470970629,743970230784)),frozen_dual_lifting_failure=dict(cell=[4,10],outside_roots=[2]*5,source=str(lift_source),dual_debit=str(lift_debit),positive_residual=str(lift_residual),scope='Failure of these fixed query roots/multipliers outside the7/11-only field class; not a positive full query gate.'),checks=checks,check_count=sum(checks.values()),scope=candidate['scope'])
result['central_density_lift']=dict(actual_weak_capacities=list(map(str,actual_capacities)),actual_weak_densities=list(map(str,actual_densities)),joint_density_cap='8/3',domination_factor=str(domination_factor),lifted_upper=str(lifted_upper),scope='Arithmetic for the measurable coarsening and joint density domination theorem proved in Report682; fixed outside conditional law and query interface.')
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='PASS',checks=result['check_count'],upper=str(upper),lifted_upper=str(lifted_upper),lift_residual=str(lift_residual))))
