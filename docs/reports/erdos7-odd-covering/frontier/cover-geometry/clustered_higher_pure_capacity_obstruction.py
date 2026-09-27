#!/usr/bin/env python3
"""Reuse the fixed 680 dual on actual finite higher-pure leaf deletions.
No optimizer and no changed original mixed phases. All exact arithmetic uses the standard library.
"""
from pathlib import Path
from argparse import ArgumentParser
from fractions import Fraction as F
from itertools import combinations
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
p=ArgumentParser(description=__doc__)
p.add_argument('--fixture',type=Path,default=HERE/'clustered_global_phase_fixture.json')
p.add_argument('--source',type=Path,default=HERE/'clustered_exact_actual_source.json')
p.add_argument('--witness',type=Path,default=HERE/'clustered_actual_boundary_gate_witness.json')
p.add_argument('--source640',type=Path,default=HERE/'remaining33_global_root_exclusion_certificate.json')
p.add_argument('--output',type=Path,default=HERE/'clustered_higher_pure_capacity_obstruction.json')
a=p.parse_args();checks={}
def ck(k,ok):
 checks[k]=checks.get(k,0)+1
 if not ok:raise RuntimeError(k)
fixture=json.loads(a.fixture.read_text());src=json.loads(a.source.read_text());wit=json.loads(a.witness.read_text());base=json.loads(a.source640.read_text())
for path in (a.fixture,a.source,a.source640):ck('inherited680_input_pin',sha256(path.read_bytes()).hexdigest()==wit['source_sha256'][path.name])
ck('literal680_source',src['schema']=='clustered91-exact-actual-root-square-survivor-v1' and wit['schema']=='clustered-same-law-boundary-gate-witness-v1' and wit['corner']==[4,10])
originals=fixture['actual_originals'];ck('base101_distinct_actual_originals',len(originals)==len({o['modulus'] for o in originals})==101)
for original in originals:
 central_mod=original['modulus']
 for q in (7,11,13,17,19):
  while central_mod%q==0:central_mod//=q
 ck('all_base_central_predicates_resolve_at225',225%central_mod==0)
Q=(7,11,13,17,19);cells=tuple(map(tuple,wit['coordinates']));tables={tuple(row['cell']):[[F(s) for s in v] for v in row['H_by_support_and_root7']] for row in src['cells']}
ck('fixed_eighty_cells',len(cells)==80 and set(cells)==set(tables))
w=[F(0) if l==3 else F(1,9) if l==4 else F(2,9) for l in range(6)]
v=[F(0) if m==5 else F(3,75) if m==10 else F(4,75) for m in range(20)]
source_mass=sum((w[l]*v[m]*tables[l,m][0][0] for l,m in cells),F(0));ck('coarse_source_mass',source_mass==F(305684996597,646498195200))
C=list(map(F,base['combined512_coefficients']));g=F(200163067,201247200)
for i,q in enumerate(Q):
 if i:C[288+(1<<i)]+=g*F(1,q*(q-2))
ck('same_complete_fees',len(C)==512 and min(C)>=0)
for col in range(4):
 for m in range(20):ck('full_mode8_dominates_guarded_mode9',0<=v[m]*int(m//5==col)<=v[m])
D=wit['dual_denominator'];ck('same_fixed_dual_denominator',D==2**32)
# Parse the inherited literal mixtures once; each is a valid nonnegative combination of original screens.
terms=[]
for j in range(512):
 es=wit['generic_dual'].get(str(j),[]);ck('same_dual_budget',sum(e['numerator'] for e in es)<=D)
 mode,T=divmod(j,32);ex,ey=divmod(mode,4)
 for e in es:
  n=e['numerator'];r=e['root7'];left=e['left'];right=e['right']
  ck('legal_inherited_dual_address',isinstance(n,int) and n>=0 and r in (5,6) and left in ((0,) if ex==0 else range(2) if ex==1 else (0,1,2,4,5)) and right in ((0,) if ey==0 else range(4) if ey==1 else tuple(m for m in range(20) if m!=5)))
  terms.append((C[j]*F(n,D),T,r,ex,ey,left,right))
# Residuals are p - debit00 - gamma3*debit10 - gamma5*debit01 - gamma3*gamma5*debit11.
debits={c:[F(0)]*4 for c in cells};pvals={c:g*w[c[0]]*v[c[1]]*tables[c][0][0] for c in cells}
def generic_axis(weights,level,chosen,index,block,deep):
 if level==0:return weights[index]
 if level==1:return weights[index] if index//block==chosen else F(0)
 if level==2:return weights[index] if index==chosen else F(0)
 return deep if index==chosen else F(0)
for lam,T,r,ex,ey,left,right in terms:
 for l,m in cells:
  x=generic_axis(w,ex,left,l,3,F(1));y=generic_axis(v,ey,right,m,5,F(4,5))
  ri=r-1 if T&1 else 0;h=tables[l,m][T][ri]
  k=int(ex==3 and l==4)+2*int(ey==3 and m==10)
  debits[l,m][k]+=lam*x*y*h
for vals in debits.values():
 for value in vals:ck('nonnegative_debit_coefficient',value>=0)
def upper(gamma3,gamma5):
 residual=[]
 for c in cells:
  z=debits[c];residual.append(pvals[c]-z[0]-gamma3*z[1]-gamma5*z[2]-gamma3*gamma5*z[3])
 return sum((max(F(0),r) for r in residual),F(0)),residual
lim,_=upper(F(1),F(1));ck('inherited_generic_upper',lim==F(wit['expected']['generic_upper']))
rows=[];previous=None;chosen=None
for n in range(13):
 added=[];capacities=[]
 for prime,leaf,weight,density in ((3,4,F(1,9),F(2)),(5,2,F(1,25),F(4,3))):
  laws=[]
  for j in range(1,n+1):
   modulus=prime**(j+2);residue=leaf+prime*prime*sum(prime**k for k in range(j-1))
   ck('higher_pure_actual_original',0<=residue<modulus and modulus>1 and modulus%2==1 and residue%(prime*prime)==leaf)
   laws.append((modulus,residue));added.append(dict(modulus=modulus,residue=residue,prime=prime,height=j+2,word='1'*(j-1)+'0'))
  for (m1,b1),(m2,b2) in combinations(laws,2):ck('same_prime_deleted_cylinders_disjoint',b2%m1!=b1)
  t=F(1,prime*prime)-sum((F(1,m) for m,b in laws),F(0))
  formula=(F(prime-2)+F(1,prime**n))/F(prime*prime*(prime-1));ck('exact_remaining_leaf_capacity',t==formula)
  gamma=weight/(density*t);expected=F((prime-2)*prime**n,(prime-2)*prime**n+1)
  ck('exact_weak_density_factor',gamma==expected and 0<gamma<=1)
  # One fixed first higher digit 2 survives every deletion; every subsequent digit is zero.
  ray=leaf+2*prime*prime
  for m,b in laws:ck('intact_child2_disjoint_from_all_deleted_words',ray%min(prime**3,m)!=b%min(prime**3,m))
  for e in range(3,n+7):
   query_mod=prime**e;query_res=ray
   ck('one_global_nested_query_ray',0<=query_res<query_mod and query_res%(prime*prime)==leaf)
   for m,b in laws:ck('actual_query_ray_survives',query_res%min(query_mod,m)!=b%min(query_mod,m))
   query_mass=weight*F(1,query_mod)/t
   ck('deep_density_attained_on_intact_ray',query_mass/(density*F(1,query_mod))==gamma)
  capacities.append(dict(prime=prime,weak_leaf_residue=leaf,weight=str(weight),haar_capacity=str(t),reference_density=str(density),gamma=str(gamma),nested_query_residue=ray))
 allmods=[o['modulus'] for o in originals]+[o['modulus'] for o in added]
 ck('actual_union_distinct_odd_originals',len(allmods)==len(set(allmods))==101+2*n)
 # One actual finite integer also realizes the intact weak-leaf ray while avoiding every explicit original.
 crt_value=0;crt_modulus=1
 for modulus,residue in [(3**max(n+2,3),22),(5**max(n+2,3),52)]+[(q*q,2) for q in Q]:
  crt_value+=crt_modulus*((residue-crt_value)*pow(crt_modulus,-1,modulus)%modulus);crt_modulus*=modulus;crt_value%=crt_modulus
 for original in originals+added:ck('actual_joint_crt_realization',crt_value%original['modulus']!=original['residue'])
 gamma3=F(3**n,3**n+1);gamma5=F(3*5**n,3*5**n+1);un,res=upper(gamma3,gamma5)
 ck('upper_limit_lower_bound',lim<=un)
 if previous is not None:ck('upper_monotone_with_actual_deletion_depth',un<=previous)
 previous=un
 row=dict(n=n,original_count=101+2*n,actual_avoiding_integer=crt_value,actual_crt_modulus=crt_modulus,gamma3=str(gamma3),gamma5=str(gamma5),upper=str(un),upper_decimal=float(un),below_target=un<F(193,100000),capacities=capacities,added_higher_pure_originals=added)
 rows.append(row)
 if row['below_target']:
  chosen=row;chosen_residual=res;break
ck('finite_obstruction_found',chosen is not None)
# At n=0 this is precisely the original actual-cap interface, whose positive witness remains below the dual upper.
ck('n0_supports_original_positive_gate',F(rows[0]['upper'])>=F(wit['expected']['actual_positive_gate']))
result=dict(schema='clustered-higher-pure-capacity-obstruction-v1',status='PASS',new_lean_verification=False,optimizer_used=False,input_sha256={pp.name:sha256(pp.read_bytes()).hexdigest() for pp in (a.fixture,a.source,a.witness,a.source640)},verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),source_mass=str(source_mass),original_mixed_phases_unchanged=True,common_dual_term_count=len(terms),target='193/100000',generic_limit_upper=str(lim),depth_results=rows,first_tested_success=chosen,full_inventory_case='The stronger fee case replacing four guarded mode9 extras by full mode8 extras has a no-larger gate for every field, so the same upper applies. Coefficients are not claimed entrywise ordered.',finite_central_field_extension='For the same all-height normalized deep-sup interface, averaging any finite-cylinder central-only field on coarse survivor leaf pairs preserves mass and shallow responses and decreases every deep screen. The ordinary finite partition proof therefore extends this upper beyond coarse cell fields. No outside-dependent field or changed conditional source is covered.',chosen_residuals=[dict(cell=list(c),value=str(r)) for c,r in zip(cells,chosen_residual)],checks=checks,check_count=sum(checks.values()),scope='One nested family extending the fixed101-original fixture by actual higher pure moduli3^3..3^(n+2) and5^3..5^(n+2), with fixed coarse leaf weights and uniform conditional laws on actual survivors. One fixed generic680 dual bounds all fields for each resulting actual deep-cap response interface. No arbitrary-phase, all-source, all95, continuation, cap-attainment across all charged originals, or covering conclusion.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=result['check_count'],n=chosen['n'],upper=chosen['upper'],decimal=chosen['upper_decimal'],gamma3=chosen['gamma3'],gamma5=chosen['gamma5'],original_count=chosen['original_count'],depths=[dict(n=r['n'],upper=r['upper_decimal']) for r in rows])),flush=True)
