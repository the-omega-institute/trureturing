#!/usr/bin/env python3
"""Independent direct finite-root reconstruction of the clustered source and capacity gates.
Reads numerical fixtures only, no same-round producer implementation. Standard library only.
"""
from pathlib import Path
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations,product
from math import prod,factorial
import json
HERE=Path(__file__).resolve().parent
p=ArgumentParser(description=__doc__)
p.add_argument('--fixture',type=Path,default=HERE/'clustered_global_phase_fixture.json')
p.add_argument('--source-table',type=Path,default=HERE/'clustered_exact_actual_source.json')
p.add_argument('--candidate',type=Path,default=HERE/'clustered_actual_boundary_gate_witness.json')
p.add_argument('--source640',type=Path,default=HERE/'remaining33_global_root_exclusion_certificate.json')
p.add_argument('--network657',type=Path,default=HERE/'ordinary_domain_five_parent_certificate.json')
p.add_argument('--output',type=Path,default=HERE/'clustered680_independent_check.json')
a=p.parse_args();checks={}
def ck(k,ok):
 checks[k]=checks.get(k,0)+1
 if not ok:raise RuntimeError(k)
raw=a.fixture.read_bytes();fixture=json.loads(raw);originals=fixture['actual_originals'];Q=(7,11,13,17,19)
ck('all_101_originals',len(originals)==len({o['modulus'] for o in originals})==101)
local=[[] for q in Q];pairs=[];central=[];outside=[];mixed=[]
for o in originals:
 m,b=o['modulus'],o['residue'];ck('odd_distinct_global_phase',m>1 and m%2==1 and 0<=b<m)
 c=m;qs=[]
 for i,q in enumerate(Q):
  if c%q==0:
   exp=0
   while c%q==0:exp+=1;c//=q
   qs.append((i,q**exp))
 if not qs:central.append((m,b));continue
 if len(qs)==1 and c==1:outside.append((m,b));continue
 mixed.append(o)
 if len(qs)==1:
  i,d=qs[0];local[i].append((c,b%c,d,b%d))
 else:pairs.append((c,b%c,qs,b))
ck('central_classes',set(central)=={(3,2),(9,1),(5,4),(25,1),(15,0)})
ck('outside_classes',set(outside)=={(q,0) for q in Q})
ck('mixed_count',len(mixed)==91 and len(pairs)==40 and sum(map(len,local))==51)
for i,q in enumerate(Q):
 ck('all_single_scopes',len(local[i])==(11 if i==0 else 10))
 for c,r,d,b in local[i]:ck('single_scope_depth',d in (q,q*q) and 225%c==0)
# The ten qs originals alone reject precisely simultaneous root1 at two sites.
for i,j in combinations(range(5),2):
 items=[x for x in pairs if [u for u,d in x[2]]==[i,j]]
 ck('all_four_pair_originals',len(items)==4 and {(c,tuple(d for u,d in qs)) for c,r,qs,b in items}=={(1,(Q[i],Q[j])),(9,(Q[i],Q[j])),(1,(Q[i]**2,Q[j])),(1,(Q[i],Q[j]**2))})
 for c,r,qs,b in items:ck('pair_root1_containment',all(b%Q[u]==1 for u,d in qs))
 ck('root_pair_present',any(c==1 and qs==[(i,Q[i]),(j,Q[j])] and b%(Q[i]*Q[j])==1 for c,r,qs,b in items))
# Enumerate the two root classes at all sites and test the actual root-pair exclusions.
allowed_words=[]
for word in product((0,1),repeat=5):
 legal=all(not(word[i] and word[j]) for i,j in combinations(range(5),2))
 if legal:allowed_words.append(word)
ck('six_binary_root_classes',len(allowed_words)==6)
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5);cells=[(l,m) for l,m in product(I,J) if not(l<3 and m<5)]
source_json=json.loads(a.source_table.read_text());source_by_cell={tuple(c['cell']):c for c in source_json['cells']}
ck('source_table_fixture_pin',source_json['source_fixture_sha256']==sha256(raw).hexdigest())
H={};Hfull={};masses={};counts_by_cell={};dead=[]
for l,m in cells:
 x9=l//3+3*(l%3);x25=m//5+5*(m%5)
 x=next(t for t in range(x9,225,9) if t%25==x25)
 ck('literal_central_survives',all(x%d!=b for d,b in central))
 rootcounts=[]
 for i,q in enumerate(Q):
  counts=[0]*q
  for residue in range(q*q):
   if residue%q==0:continue
   if any(x%c==r and residue%d==b for c,r,d,b in local[i]):continue
   counts[residue%q]+=1
  rootcounts.append(counts)
  ck('square_root_count',counts[1] in (0,q-1,q))
  ck('nonroot1_uniform_children',all(t in (0,q) for t in counts[2:]))
  if i:ck('root9_globally_available',counts[9]==q)
 counts_by_cell[l,m]=rootcounts
 def slice_response(T,root7):
  weights=[];den=1
  for i,q in enumerate(Q):
   cs=rootcounts[i]
   if T>>i&1:
    root=root7 if i==0 else 9
    weights.append((cs[root] if root!=1 else 0,cs[1] if root==1 else 0));den*=q
   else:
    weights.append((sum(cs[2:]),cs[1]));den*=q*(q-1)
  num=sum(prod(weights[i][word[i]] for i in range(5)) for word in allowed_words)
  return F(num,den)
 for T in range(32):
  roots=range(1,7) if T&1 else (None,)
  readings=[slice_response(T,r) for r in roots];Hfull[l,m,T]=readings
  ck('all_original_table_slices',readings==list(map(F,source_by_cell[l,m]['H_by_support_and_root7'][T])))
  for val in readings:ck('normalized_query_range',0<=val<=1)
  if T&1:
   for k in range(4):ck('global_root6_dominance',readings[k]<=readings[5])
   H[l,m,T]=[readings[4],readings[5]]
  else:H[l,m,T]=[readings[0],readings[0]]
 masses[l,m]=H[l,m,0][0]
 ck('actual_mass_matches',masses[l,m]==F(source_by_cell[l,m]['source_mass']))
 if not masses[l,m]:
  dead.append([l,m]);ck('all_dead_fibre_responses_zero',all(v==0 for T in range(32) for v in Hfull[l,m,T]))
w=[F(0) if l==3 else F(1,9) if l==4 else F(2,9) for l in range(6)]
v=[F(0) if m==5 else F(3,75) if m==10 else F(4,75) for m in range(20)]
mass=sum((w[l]*v[m]*masses[l,m] for l,m in cells),F(0))
ck('one_fixed_corner_mass',mass==F(305684996597,646498195200));ck('actual_dead_fibre',dead==[[0,6]])
result=dict(schema='clustered680-independent-check-v1',new_lean_verification=False,read_same_round_680_verifier_implementation=False,source_fixture_sha256=sha256(raw).hexdigest(),source_table_sha256=sha256(a.source_table.read_bytes()).hexdigest(),source_mass=str(mass),dead_cells=dead,cell_count=len(cells),source_slice_count=sum(len(v) for v in Hfull.values()))
print(json.dumps(dict(source_mass=str(mass),dead_cells=dead,checks=sum(checks.values()))),flush=True)
candidate_raw=a.candidate.read_bytes();candidate=json.loads(candidate_raw)
ck('candidate_schema',candidate['schema']=='clustered-same-law-boundary-gate-witness-v1')
for pp in (a.fixture,a.source_table,a.source640):ck('candidate_input_pin',sha256(pp.read_bytes()).hexdigest()==candidate['source_sha256'][pp.name])
ck('candidate_same_corner',candidate['corner']==[4,10] and candidate['coordinates']==[list(c) for c in cells])
C=list(map(F,json.loads(a.source640.read_text())['combined512_coefficients']));g=F(200163067,201247200)
for i,q in enumerate(Q):
 if i:C[288+(1<<i)]+=g*F(1,q*(q-2))
ck('complete_same_512_fees',len(C)==512 and min(C)>=0)
fden=candidate['field_denominator'];ck('small_field_denominator',fden==12)
nums=candidate['field_numerators'];ck('field_length',len(nums)==80)
for n in nums:ck('field_is_common_submeasure',isinstance(n,int) and 0<=n<=fden)
theta=dict(zip(cells,[F(n,fden) for n in nums]))
def menu_axis(weights,level,blocksize,deep,actual):
 live=[i for i,a0 in enumerate(weights) if a0]
 if level==0:return {0:list(weights)}
 if level==1:return {r:[a0 if i//blocksize==r else F(0) for i,a0 in enumerate(weights)] for r in range(len(weights)//blocksize)}
 if level==2:return {t:[a0 if i==t else F(0) for i,a0 in enumerate(weights)] for t in live}
 cap=max(weights)
 return {t:[deep*(weights[t]/cap if actual else 1) if i==t else F(0) for i in range(len(weights))] for t in live}
menus={}
for actual in (False,True):
 for mode in range(16):
  ex,ey=divmod(mode,4);xm=menu_axis(w,ex,3,F(1),actual);ym=menu_axis(v,ey,5,F(4,5),actual)
  menus[actual,mode]=(xm,ym)
ck('actual_weak_ternary_capacity',menus[True,12][0][4][4]==F(1,2))
ck('actual_weak_quinary_capacity',menus[True,3][1][10][10]==F(3,5))
for mode in range(16):
 gx,gy=menus[False,mode];ax,ay=menus[True,mode]
 ck('same_selector_addresses',gx.keys()==ax.keys() and gy.keys()==ay.keys())
 for key in gx:
  for l in range(6):ck('actual_ternary_bound_le_generic',0<=ax[key][l]<=gx[key][l])
 for key in gy:
  for m in range(20):ck('actual_quinary_bound_le_generic',0<=ay[key][m]<=gy[key][m])
# Maxima always use one fixed queried root over the entire selected region.
unitfees={False:F(0),True:F(0)};fieldfees={False:F(0),True:F(0)}
unit_screens={False:[],True:[]};field_screens={False:[],True:[]}
for actual in (False,True):
 for mode in range(16):
  xm,ym=menus[actual,mode]
  selectors=[[(l,m,xx[l]*yy[m]) for l,m in cells if xx[l]*yy[m]] for xx,yy in product(xm.values(),ym.values())]
  for T in range(32):
   root_indices=range(6) if T&1 else (0,)
   umax=F(0);fmax=F(0)
   for selector in selectors:
    for ri in root_indices:
     uv=F(0);fv=F(0)
     for l,m,coeff in selector:
      response=Hfull[l,m,T][ri];uv+=coeff*response;fv+=coeff*response*theta[l,m]
     umax=max(umax,uv);fmax=max(fmax,fv);ck('literal_global_root_selector',0<=fv<=uv)
   unitfees[actual]+=C[32*mode+T]*umax;fieldfees[actual]+=C[32*mode+T]*fmax
   unit_screens[actual].append(umax);field_screens[actual].append(fmax)
source_thinned=sum((w[l]*v[m]*masses[l,m]*theta[l,m] for l,m in cells),F(0))
unitgates={str(actual):g*mass-unitfees[actual] for actual in (False,True)}
fieldgates={str(actual):g*source_thinned-fieldfees[actual] for actual in (False,True)}
expected=candidate['expected']
ck('unit_same_for_both_interfaces',unitgates['False']==unitgates['True']==F(expected['unit_gate']))
ck('positive_actual_witness',fieldgates['True']==F(expected['actual_positive_gate']) and fieldgates['True']>F(193,100000))
# Every group is a convex combination of literal original screens with its exact C_j.
dden=candidate['dual_denominator'];ck('dual_denominator',dden==2**32)
residual={(l,m):g*w[l]*v[m]*masses[l,m] for l,m in cells};dualtermcount=0
for j in range(512):
 entries=candidate['generic_dual'].get(str(j),[]);ck('complete_dual_budget',sum(e['numerator'] for e in entries)<=dden)
 mode,T=divmod(j,32);xm,ym=menus[False,mode]
 for entry in entries:
  N=entry['numerator'];root=entry['root7'];left=entry['left'];right=entry['right']
  ck('legal_dual_literal_selector',isinstance(N,int) and N>=0 and left in xm and right in ym and root in (5,6))
  coeff=C[j]*F(N,dden);xx=xm[left];yy=ym[right];ri=root-1 if T&1 else 0
  for l,m in cells:residual[l,m]-=coeff*xx[l]*yy[m]*Hfull[l,m,T][ri]
  dualtermcount+=1
upper=sum((max(F(0),r) for r in residual.values()),F(0))
ck('exact_generic_upper',upper==F(expected['generic_upper']))
ck('generic_cap_obstruction',upper<F(1,10**10)<F(193,100000))
ck('source_mass_unchanged',mass==F(expected['source_mass']))
result.update(status='PASS',candidate_sha256=sha256(candidate_raw).hexdigest(),complete_fee_count=512,unit_gates={k:str(v) for k,v in unitgates.items()},field_gates={k:str(v) for k,v in fieldgates.items()},thinned_source_mass=str(source_thinned),generic_universal_upper=str(upper),dual_term_count=dualtermcount,field_denominator=fden,scope='One fixed clustered 101-original family with no higher pure originals and one actual central corner (4,10). Independent actual source and same 512 fees; every root is fixed across a selector. Generic deep-cap gate fails for all fields, while the supplied single rational field passes using actual uniform-in-leaf capacities. No all95, arbitrary-phase, higher-pure, continuation or covering claim.')
# A uniform factor thinning restores the omitted-coordinate mass premise without renormalizing.
Dq=[F(5,6)]+[F(q-2,q-1)-F(2,q*(q-2)) for q in Q[1:]]
ck('literal_factor_masses',Dq==list(map(F,('5/6','871/990','1549/1716','3793/4080','5455/5814'))))
for value in Dq:ck('factor_thinning_range',0<value<=1)
Dall=prod(Dq);ck('exact_thinning_product',Dall==F(429470970629,743970230784))
for l,m in cells:
 unarymass=[F(sum(counts_by_cell[l,m][i]),q*(q-1)) for i,q in enumerate(Q)]
 for i in range(5):ck('actual_thinned_unary_mass',0<=Dq[i]*unarymass[i]<=Dq[i])
 for T in range(32):
  omitted=prod(Dq[i]*unarymass[i] for i in range(5) if not(T>>i&1))
  required=prod(Dq[i] for i in range(5) if not(T>>i&1))
  for h in Hfull[l,m,T]:ck('thinned_omitted_coordinate_root_domination',Dall*h<=omitted<=required)
scaled=Dall*fieldgates['True'];ck('exact_scaled_gate',scaled==F(1005784428862661895329308405859299747631233,88672944375462709711523174183180697600000000))
ck('scaled_gate_pays_target',scaled>F(193,100000))
result.update(unary_thinning_factors=list(map(str,Dq)),uniform_thinning_product=str(Dall),scaled_actual_gate=str(scaled),omitted_coordinate_scope='The actual conditional-Haar unary factors have no higher pure originals; multiplication by Dq gives domination and mass at most Dq. Verified all existing root-query slices; deeper prefixes follow the same product domination and inherited caps. No continuation theorem is inferred from this interface lemma alone.')
# Separate stronger inventory case: full 9q² events require mode8, not the guarded mode9 screen.
full_charges=[];extra_fee=F(0)
for actual in (False,True):
 x8,y8=menus[actual,8];x9,y9=menus[actual,9]
 ck('same_9q_square_leaf_menu',x8==x9)
 for right in y9:
  for m in range(20):ck('full_screen_pointwise_dominates_guard',0<=y9[right][m]<=y8[0][m])
for i,q in enumerate(Q):
 if not i:continue
 T=1<<i;coefficient=g*F(1,q*(q-2))
 full=field_screens[True][256+T];guarded=field_screens[True][288+T]
 ck('full_nine_square_field_screen',full>=guarded)
 debit=coefficient*(full-guarded);extra_fee+=debit
 full_charges.append(dict(q=q,full_screen=str(full),guarded_screen=str(guarded),extra_debit=str(debit)))
full_gate=fieldgates['True']-extra_fee;full_scaled=Dall*full_gate
ck('full_inventory_raw_gate',full_gate==F(2144832980209210799160393676877,119188834050548855719526400000000))
ck('full_inventory_scaled_gate',full_scaled==F(921143501847540509401483050662119383445633,88672944375462709711523174183180697600000000))
ck('full_inventory_remains_positive',full_scaled>F(193,100000))
network_raw=a.network657.read_bytes();ck('network657_pin',sha256(network_raw).hexdigest()=='e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0')
net=json.loads(network_raw)
ck('network657_policy_identity',net['schema']=='ordinary-domain-five-parent-v1' and net['first_five_parent_owner']==67 and net['Euler_counts']==dict(head=10,finite=193,half=123))
def prime(n):return n>=2 and all(n%d for d in range(2,int(n**0.5)+1))
rows=net['finite_rows'];owners=[p for p in range(37,1253) if prime(p)]
ck('complete_193_owner_rows',[r['owner'] for r in rows]==owners and len(rows)==193)
for row in rows:
 owner=row['owner'];h=row['h'];cap=F(row['cap']);domain=F(owner-1)-F(65537,65536)
 ck('unchanged_owner_parent_count',row['r']==(4 if owner<67 else 5))
 ck('unchanged_finite_domain_threshold',F(row['D'])==domain and F(row['t'])==domain-h and 10<=h<domain)
 ck('unchanged_finite_owner_cap',cap==F(owner-1,h) and cap<F(owner,10))
 ck('inherited_finite_fee_interval',0<=F(row['fee_lower'])<=F(row['fee_upper']))
finite_fee=sum((F(row['fee_upper']) for row in rows),F(0));ck('all_finite_fees_counted',finite_fee==F(net['finite_fee_upper']))
common_fee=finite_fee+F(net['complete_five_parent_tail'])+F(net['ordinary_typeI_fee'])
ck('complete_common_budget',common_fee==F(net['fee_before_arbitrary']) and F(net['ordinary_typeI_fee'])==F(1,65536))
ck('full_head_exceeds_inherited_head',full_scaled>F(net['head_gate']))
alpha=F(net['projection_alpha']);ck('unchanged_projection',alpha==F(2673,110656))
Mplus=F(net['M0_upper']);Ctail=F(net['Ctail']);Pminus=F(net['Podd_lower']);ck('same_euler_tail_inputs',Ctail==F(2187,2186) and net['Euler_endpoint']==2187 and 0<F(net['M0_lower'])<=Mplus and 0<Pminus<=F(net['Podd_upper']))
policies=[]
for kind,K in (('RS_policy',46),('elementary_policy',68)):
 pol=net[kind];V=2**K;ck('same_arbitrary_parent_switch',pol['K']==K and pol['arbitrary_threshold']==V)
 if kind=='RS_policy':
  polynomial=sum((F(factorial(6),factorial(6-j))*F(7*K,10)**(6-j) for j in range(7)),F(0))
  tail=Mplus*Ctail*F(99,97)**6*F(V,V-3)**2*polynomial/(2*(V-1)*F(1841,240)**6)
 else:
  tail=2*Mplus*Ctail/Pminus**6*(4*(K+2))**6*F(1,2**K)/(1-F(1,2)*F(K+3,K+2)**6)
 ck('same_complete_arbitrary_parent_tail',tail==F(pol['fee']))
 rawmargin=full_scaled-common_fee-tail;projected=alpha*rawmargin
 ck('full_inventory_complete_policy_density',projected>F(1,50000))
 policies.append(dict(kind=kind,K=K,complete_fee=str(common_fee+tail),raw_margin=str(rawmargin),projected_margin=str(projected),projected_margin_decimal=float(projected),strict_density_denominator=50000))
result.update(full_nine_square_charges=full_charges,full_nine_square_extra_fee=str(extra_fee),full_inventory_raw_gate=str(full_gate),full_inventory_scaled_gate=str(full_scaled),full_inventory_generic_upper=str(upper),network657_sha256=sha256(network_raw).hexdigest(),network657_policies=policies,network_scope='Both complete pinned657 budgets are checked with unchanged193 rows, four parents before67, five from67 to the selected switch, and arbitrary finite parents afterward. Finite hinge and Euler enclosures are reused from the pinned certificate; all fee sums and full infinite-tail formulas are recalculated. The density conclusion is conditional on the independently required complete head, 23/29/31 kernels, pure-domain, ordinary/private and one-time original-assignment interfaces.')
result.update(checks=checks,check_count=sum(checks.values()),verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=result['check_count'],generic_upper=str(upper),actual_field_gate=str(fieldgates['True']),generic_field_gate=str(fieldgates['False']))),flush=True)
