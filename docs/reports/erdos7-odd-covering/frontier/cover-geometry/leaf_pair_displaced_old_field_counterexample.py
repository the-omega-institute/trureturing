#!/usr/bin/env python3
"""Independent failure audit: old661 fields with all ten9qs at centralleaf4.
Reads only canonical640 coefficients; all new layout and actual-source data are reconstructed independently.
Does not read the same-round priority95 producer, its data, or its algorithms.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,product
from math import prod,lcm
from hashlib import sha256
from argparse import ArgumentParser
import json
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
ROOT=args.directory
raw=(ROOT/'remaining33_global_root_exclusion_certificate.json').read_bytes()
base=json.loads(raw)
checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c:raise RuntimeError(k)
ck('canonical640_pin',sha256(raw).hexdigest()=='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4')
Q=(7,11,13,17,19); edges=list(combinations(range(5),2))
r=[F(1,q-1) for q in Q]; a=[F(1,q*(q-2)) for q in Q]
z=[F(5,6)]+[F(q-2,q-1)-2*a[k] for k,q in enumerate(Q) if k]
g=F(200163067,201247200)
C=[F(x) for x in base['combined512_coefficients']]
for k in range(1,5):C[9*32+(1<<k)]+=g*a[k]
ck('complete512_nonnegative',len(C)==512 and min(C)>=0)
I=[0,1,2,4,5];J=[m for m in range(20) if m!=5]
# Six central profiles suffice algebraically; literal cells are retained below.
profiles={}
for l in I:
 for m in J:
  if l<3 and m<5:continue
  n=int(l//3==1)+int(m//5==2)+int(l==5)
  key=(n,int(l==4))
  zz=list(z);zz[0]-=F(n,35)
  beta=[a[i]*r[j]+r[i]*a[j]+r[i]*r[j]*int(l==4) for i,j in edges]
  profiles[key]=(zz,beta)
# Explicit induced polynomials for every subset of the dependency graph's10edges.
# Independent sets are zero, one or two disjoint edges.
strict={}; Hprofiles={}
for key,(zz,beta) in profiles.items():
 p=[b/(zz[i]*zz[j]) for b,(i,j) in zip(beta,edges)]
 vals=[]
 for mask in range(1024):
  chosen=[e for e in range(10) if mask>>e&1]
  val=1-sum((p[e] for e in chosen),F(0))
  val+=sum((p[e]*p[f] for e,f in combinations(chosen,2) if set(edges[e]).isdisjoint(edges[f])),F(0))
  ck('all_induced_shearer_polynomials_positive',val>0)
  vals.append(val)
 strict[str(key)]=str(min(vals))
 table=[]
 for support in range(32):
  U=set(i for i in range(5) if not(support>>i&1))
  val=prod(zz[i] for i in U)
  es=[e for e,ends in enumerate(edges) if set(ends)<=U]
  val-=sum((beta[e]*prod(zz[i] for i in U-set(edges[e])) for e in es),F(0))
  val+=sum((beta[e]*beta[f]*prod(zz[i] for i in U-set(edges[e])-set(edges[f])) for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])),F(0))
  ck('positive_response_below_unary_product',0<val<=prod(zz[i] for i in U))
  table.append(val)
 Hprofiles[key]=table
hden=lcm(*(x.denominator for hh in Hprofiles.values() for x in hh))
cden=lcm(g.denominator,*(x.denominator for x in C)); cnum=[int(x*cden) for x in C];gnum=int(g*cden)
THETA_DEN=180

def tnum(weak,l,m):
 if l==3 or m==5 or (l<3 and m<5):return 0
 if l==5:return 180
 if m//5==2:return 171 if l==weak else 165
 return 165 if l==weak else 160

for l in range(6):
 for m in range(20):
  for i,j in product(I,J):
   t=tnum(i,l,m)
   ck('theta_between_zero_and_one',0<=t<=180)
   if l in I:ck('ternary_weak_marker_priority',tnum(l,l,m)>=t)
   if m in J:ck('quinary_weak_marker_priority',tnum(i,l,m)==t)

H={}
for support in range(32):
 arr=[[0]*20 for _ in range(6)]
 for l,m in product(I,J):
  if l<3 and m<5:continue
  key=(int(l//3==1)+int(m//5==2)+int(l==5),int(l==4))
  arr[l][m]=int(Hprofiles[key][support]*hden)
 H[support]=arr
# Every selector is evaluated as an integer; no float comparison enters.
def maxima(mat,w,v):
 out=[]
 xgroups=[[w],[[w[l] if l//3==row else 0 for l in range(6)] for row in range(2)],[[w[l] if l==i else 0 for l in range(6)] for i in I],[[9 if l==i else 0 for l in range(6)] for i in I]]
 for family in xgroups:
  best=[0,0,0,0]
  for x in family:
   col=[sum(x[l]*mat[l][m] for l in I) for m in J]
   weighted=[col[k]*v[m] for k,m in enumerate(J)]
   local=[sum(weighted),max(sum(weighted[k] for k,m in enumerate(J) if m//5==root) for root in range(4)),max(weighted),60*max(col)]
   best=[max(a,b) for a,b in zip(best,local)]
  out.extend(best)
 return out

gates=[]; cornerfees={}
for i,j in product(I,J):
 w=[0 if l==3 else 1 if l==i else 2 for l in range(6)]
 v=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
 fields={};fees=0;mass=None
 for support in range(32):
  mat=[[H[support][l][m]*tnum(i,l,m) for m in range(20)] for l in range(6)]
  screen=maxima(mat,w,v)
  if support==0:mass=screen[0]
  for mode in range(16):
   fees+=cnum[32*mode+support]*screen[mode]
   ck('complete512_screens_nonnegative',screen[mode]>=0)
 numerator=gnum*mass-fees
 value=F(numerator,cden*9*75*THETA_DEN*hden)

 gates.append(dict(weak3=i,weak5=j,gate=str(value),decimal=float(value)))
 cornerfees[str((i,j))]=dict(mass_numerator=mass,fees_numerator=fees)
minimum=min(F(row['gate']) for row in gates)
mins=[(row['weak3'],row['weak5']) for row in gates if F(row['gate'])==minimum]
ck('all_ninety_five_corners',len(gates)==95)
witness=next(F(row['gate']) for row in gates if (row['weak3'],row['weak5'])==(5,6))
ck('claimed_negative_corner',witness==F(-1564824019544284842082124059,541767427502494798725120000000)<0)
policies=[]
# One finite globally phased family realizing the layout. Every original is kept.
HEAD=(3,5)+Q+(23,29,31)
fixture={}
def put(label,components):
 modulus=prod(d for a,d in components)
 residue=sum(a*(modulus//d)*pow(modulus//d,-1,d) for a,d in components)%modulus
 ck('distinct_original_numerical_label',modulus not in fixture)
 ck('odd_reduced_actual_original',modulus>1 and modulus%2 and 0<=residue<modulus)
 for a,d in components:ck('actual_global_CRT_phase',residue%d==a%d)
 fixture[modulus]=dict(label=label,modulus=modulus,residue=residue,components=components)
for p0 in HEAD:put('pure'+str(p0),[(2 if p0==3 else 4 if p0==5 else 0,p0)])
put('pure9',[(1,9)]);put('pure25',[(1,25)]);put('central15',[(0,3),(0,5)])
linear_types=[(1,0),(0,1),(1,1),(2,0),(0,2),(2,1),(1,2),(2,2)]
for q in Q:
 for e,f in linear_types:
  parts=([(0,3**e)] if e else [])+([(0,5**f)] if f else [])+[(1,q)]
  put('linear:'+str(q)+':'+str((e,f)),parts)
 for label,center,prefix in [('3q2',(1,3),2),('5q2',(2,5),3),('9q2',(7,9),4)]:
  put(label+':'+str(q),[center,(prefix,q*q)])
for q,s0 in combinations(Q,2):
 put('qs:'+str((q,s0)),[(1,q),(1,s0)])
 put('9qs:'+str((q,s0)),[(4,9),(2,q),(2,s0)])
 put('q2s:'+str((q,s0)),[(5,q*q),(5,s0)])
 put('qs2:'+str((q,s0)),[(5,q),(5,s0*s0)])
ck('fixed_low_inventory_108',len(fixture)==108)
# Check actual unary source/prefix bounds on all80 positive central cells.
for l,m in product(I,J):
 if l<3 and m<5:continue
 xi={}; roots={}
 for k,q in enumerate(Q):
  active=[]
  if l//3==1:active.append(2)
  if m//5==2:active.append(3)
  if l==5:active.append(4)
  if q!=7 and len(active)==3:active=[2,3] # original9q2 retains its guarded fee
  clean=[x for x in range(q*q) if x%q not in (0,1) and x not in active]
  actual_mass=F(len(clean),q*(q-1))
  target=z[k]-(F(int(l//3==1)+int(m//5==2)+int(l==5),35) if q==7 else 0)
  ck('actual_unary_thinning_possible',actual_mass>=target>0)
  weight=target/len(clean)
  law={x:weight for x in clean};xi[q]=law
  roots[q]={root:sum((mu for x,mu in law.items() if x%q==root),F(0)) for root in range(q)}
  ck('one_actual_unary_mass',sum(law.values(),F(0))==target)
  ck('actual_square_prefix_cap',max(law.values())<=a[k])
  ck('actual_first_root_cap',max(roots[q].values())<=r[k])
 for k,(ii,jj) in enumerate(edges):
  q,s0=Q[ii],Q[jj]
  actual_upper=xi[q].get(5,F(0))*roots[s0][5]+roots[q][5]*xi[s0].get(5,F(0))
  if l==4:actual_upper+=roots[q][2]*roots[s0][2]
  cap=a[ii]*r[jj]+r[ii]*a[jj]+r[ii]*r[jj]*int(l==4)
  ck('literal_three_original_edge_union_bound',actual_upper<=cap)
# Finite pure tails force every admitted source near the negative corner.
height=12
pure_tails={}
for p0,weak in ((3,7),(5,6)):
 rows=[]
 for e in range(3,height+1):
  phase=weak+p0**(e-1);put('pure'+str(p0**e),[(phase,p0**e)]);rows.append((e,phase))
 for (e,x),(f,y) in combinations(rows,2):
  ck('actual_pure_tail_cylinders_disjoint',x%p0**min(e,f)!=y%p0**min(e,f))
 pure_tails[p0]=rows
ck('complete_actual_fixture_128',len(fixture)==128)
eps3=F(1,3**height);eps5=F(1,3*5**height)
for p0,weak,cap,corner_mass,eps in ((3,7,F(2),F(1,9),eps3),(5,6,F(4,3),F(3,75),eps5)):
 haar=F(1,p0*p0)-sum((F(1,p0**e) for e,phase in pure_tails[p0]),F(0))
 ck('actual_weak_capacity',cap*haar==corner_mass+eps)
 ck('negative_corner_supported_on_actual_pure_survivor',corner_mass/haar<=cap)
 # All higher tails lie within the weak leaf, which differs from the null leaf.
 for e,phase in pure_tails[p0]:
  ck('actual_tail_in_weak_live_leaf',phase%(p0*p0)==weak and phase%p0!=(2 if p0==3 else 4) and phase%(p0*p0)!=1)
# Prescribed theta_eff has sup-norm Lipschitz constant3/5 in ternary leaf mass.
ck('theta_effective_derivative_bound_column2',18*(F(19,20)-F(11,12))==F(3,5))
ck('theta_effective_derivative_bound_other',18*(F(11,12)-F(8,9))==F(1,2)<=F(3,5))
perturbation=2*(g+sum(C))*(F(8,5)*eps3+eps5)
robust_upper=witness+perturbation
ck('all_cap_sources_prescribed_effective_field_negative',robust_upper<0)
# The family itself is not a cover: display one simultaneous actual survivor.
local={p0:(0 if p0==3 else 6 if p0 in (5,)+Q else 1) for p0 in HEAD}
resolving={p0:p0 for p0 in HEAD}
for row in fixture.values():
 for phase,d0 in row['components']:
  p0=next(p0 for p0 in HEAD if d0%p0==0);resolving[p0]=max(resolving[p0],d0)
modulus=prod(resolving.values())
survivor=sum(local[p0]*(modulus//d0)*pow(modulus//d0,-1,d0) for p0,d0 in resolving.items())%modulus
for n,row in fixture.items():ck('actual_CRT_survivor_avoids_original',survivor%n!=row['residue'])
result=dict(schema='leaf4-fixed661-fields-independent-v1',status='PASS',scope='Only central9qs activation moves toleaf4. Old661 fields,7squarestar roles(1,2,5),50incidences and complete512fees unchanged. Negative gate refutes this field certificate, not survivor existence or optimized-field feasibility.',new_lean_verification=False,read_same_round_producer=False,verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),source640_sha256=sha256(raw).hexdigest(),profiles=len(profiles),strict_induced_minima=strict,response_common_denominator=hden,coefficient_common_denominator=cden,minimum_gate=str(minimum),minimum_gate_decimal=float(minimum),minimizing_weak_pairs=mins,negative_corner_count=sum(F(row['gate'])<0 for row in gates),witness_corner_gate=str(witness),gates=gates,policies=policies,actual_fixture=[fixture[n] for n in sorted(fixture)],actual_fixture_count=len(fixture),actual_fixture_covering=False,all_thinnings_ruled_out=False,unrestricted_erdos7_resolved=False,actual_survivor=dict(local=local,modulus=modulus,residue=survivor),finite_pure_tail_height=height,eps3=str(eps3),eps5=str(eps5),prescribed_effective_field_perturbation=str(perturbation),prescribed_effective_field_perturbation_decimal=float(perturbation),all_cap_sources_prescribed_field_upper=str(robust_upper),all_cap_sources_prescribed_field_upper_decimal=float(robust_upper),check_count=sum(checks.values()),checks=checks)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','profiles','minimum_gate','minimum_gate_decimal','minimizing_weak_pairs','negative_corner_count','witness_corner_gate','check_count')}))
for p in policies:print(json.dumps({k:v for k,v in p.items() if k.endswith('decimal') or k in ('kind','K')}))
