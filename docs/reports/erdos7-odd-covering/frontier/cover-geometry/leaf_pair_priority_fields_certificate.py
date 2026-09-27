#!/usr/bin/env python3
"""Exact weak-marker priority fields and complete networks on fixed null faces.

Only the pinned640 coefficient JSON and658 network JSON are read. The
matching responses and all95 corner gates with literal512 screens are rebuilt.
No optimizer, phase scan or temporary helper is used.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from math import prod,lcm
from hashlib import sha256
from collections import Counter
import argparse,json
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--output',type=Path)
args=p.parse_args();checks=Counter()
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]+=1
pins={'remaining33_global_root_exclusion_certificate.json':'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','joint_square_pair_225_star_certificate.json':'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'}
sources={}
for name,pin in pins.items():
 raw=(args.directory/name).read_bytes();ck('input_pin',sha256(raw).hexdigest()==pin);sources[name]=json.loads(raw)
base=sources['remaining33_global_root_exclusion_certificate.json'];network=sources['joint_square_pair_225_star_certificate.json']
ck('network_status',network['status']=='PASS' and not network['new_lean_verification'])
Q=(7,11,13,17,19);g=F(200163067,201247200);alpha=F(2673,110656)
ck('source_gate_constants',F(base['constants']['g'])==g and F(network['g'])==g and F(network['projection_alpha'])==alpha)
r={q:F(1,q-1)for q in Q};a={q:F(1,q*(q-2))for q in Q}
C=list(map(F,base['combined512_coefficients']))
ck('complete_coefficient_shape',len(C)==512 and min(C)>=0)
for i,q in enumerate(Q):
 if q!=7:C[32*9+(1<<i)]+=g*a[q]
H=[[]for _ in range(32)];retention=[];matching_retention=[]
for l,m in product(range(6),range(20)):
 n=int(l//3==1)+int(m//5==2)+int(l==5)
 Z={q:(F(5,6)-F(n,35)if q==7 else F(q-2,q-1)-2*a[q])for q in Q}
 beta={(q,s):a[q]*r[s]+r[q]*a[s]+(r[q]*r[s]if l==5 else F())for q,s in combinations(Q,2)}
 lam=1-sum(beta[q,s]/(Z[q]*Z[s])for q,s in combinations(Q,2));ck('strict_shearer_via_union',lam>0);retention.append(lam)
 for T in range(32):
  U=[q for i,q in enumerate(Q)if not T>>i&1];edges=list(combinations(U,2))
  h=prod((Z[q]for q in U),start=F(1))-sum((beta[e]*prod((Z[q]for q in U if q not in e),start=F(1))for e in edges),F())
  h+=sum((beta[e]*beta[f]*prod((Z[q]for q in U if q not in e and q not in f),start=F(1))for e,f in combinations(edges,2)if not set(e)&set(f)),F())
  ck('matching_response_positive',h>0)
  if not T:matching_retention.append(h/prod(Z.values()))
  H[T].append(F()if l<3 and m<5 else h)
ck('union_retention_minimum',min(retention)==F(754111121894423,876550251053789))
ck('matching_retention_minimum',min(matching_retention)==F(3780354901112254,4382751255268945))
live3=(0,1,2,4,5);live5=tuple(m for m in range(20)if m!=5)
fields={}
for i in live3:
 vals=[]
 for l,m in product(range(6),range(20)):
  if l==3 or m==5 or(l<3 and m<5):t=F()
  elif l==5:t=F(1)
  elif m//5==2:t=F(19,20)if i==l else F(11,12)
  else:t=F(11,12)if i==l else F(8,9)
  ck('legal_thinning_entry',0<=t<=1);vals.append(t)
 fields[i]=vals
for l,m in product(live3,live5):
 for i in live3:
  ck('ternary_weak_priority',fields[l][20*l+m]>=fields[i][20*l+m])
# No quinary marker occurs in the field definition. Quinary priority is
# equality by construction, not an additional repeated numerical check.
Dc=lcm(g.denominator,*(c.denominator for c in C));gi=int(g*Dc);Ci=[int(c*Dc)for c in C]
records=[];screen_total=0;selector_total=0
for i in live3:
 ht=[[h*t for h,t in zip(row,fields[i])]for row in H]
 Dh=lcm(*(h.denominator for row in ht for h in row));Hi=[[int(h*Dh)for h in row]for row in ht]
 x=[0 if l==3 else 1 if l==i else 2 for l in range(6)]
 ck('ternary_corner_normalized',sum(x)==9)
 for j in live5:
  y=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
  ck('quinary_corner_normalized',sum(y)==75)
  MX=[[x],[[x[l]if l//3==b else 0 for l in range(6)]for b in range(2)],[[x[l]if l==b else 0 for l in range(6)]for b in live3],[[9 if l==b else 0 for l in range(6)]for b in live3]]
  MY=[[y],[[y[m]if m//5==b else 0 for m in range(20)]for b in range(4)],[[y[m]if m==b else 0 for m in range(20)]for b in live5],[[60 if m==b else 0 for m in range(20)]for b in live5]]
  screens=[]
  for e3,e5 in product(range(4),repeat=2):
   selectors=[[(20*l+m,xx[l]*yy[m])for l,m in product(range(6),range(20))if xx[l]and yy[m]]for xx in MX[e3]for yy in MY[e5]]
   for T in range(32):
    value=max(sum(Hi[T][c]*w for c,w in sel)for sel in selectors)
    ck('screen_nonnegative',value>=0);screens.append(value)
    selector_total+=len(selectors);screen_total+=1
  gate=F(gi*screens[0]-sum(c*s for c,s in zip(Ci,screens)),675*Dc*Dh)
  records.append(dict(weak3=i,weak5=j,source_mass=str(F(screens[0],675*Dh)),gate=str(gate)))
minimum=min(records,key=lambda row:F(row['gate']));gate=F(minimum['gate'])
minimizers=[dict(weak3=row['weak3'],weak5=row['weak5'])for row in records if F(row['gate'])==gate]
ck('all95_corners',len(records)==95)
ck('complete_screens',screen_total==95*512 and selector_total==95*17888)
ck('exact_uniform_gate',gate==F(1864487415907319442048626989,931162766019912935308800000000))
ck('positive_uniform_gate',gate>F(1,500))
# Elementary algebra for the explicit actual-field range; the full density bridge is Report645.
for col2 in (False,True):
 ts,tw=(F(11,12),F(19,20))if col2 else(F(8,9),F(11,12))
 ck('priority_level_order',0<=ts<=tw<=1)
finite=F(network['finite_fee_upper']);w5=F(network['complete_five_parent_tail']);typeI=F(network['ordinary_typeI_fee'])
ck('three_parent_reference',network['branch_parameters']['parents']==[3,5,7])
ck('unchanged_typeI',typeI==F(1,65536));ck('finite_schedule_count',len(network['finite_rows'])==193)
for row in network['finite_rows']:
 v=row['owner'];h=row['h'];cap=F(row['cap'])
 ck('fixed_finite_cap',cap==F(v-1,h) and cap<F(v,10))
policies=[]
for policy in network['policies']:
 K=policy['K'];fee=F(policy['fee']);raw=gate-finite-w5-typeI-fee;projected=alpha*raw
 ck('policy_switch',K in(46,68)and policy['arbitrary_threshold']==2**K and policy['max_parents_below_switch']==3)
 ck('complete_density',projected>F(1,420000))
 policies.append(dict(kind=policy['kind'],K=K,arbitrary_threshold=2**K,max_parents_below_switch=3,fee=str(fee),raw_margin=str(raw),projected_margin=str(projected),density_denominator=420000))
scope=dict(fixed_first_and_square_pure_roles=[[3,2],[9,1],[5,4],[25,1]],arbitrary_finite_higher_central_pure_phases=True,fixed_null_leaves=[3,5],central15_residue=0,square7_central_roles=dict(mod3=1,mod5=2,mod9=7),all_ten_9qs_mod9_residue=7,remaining_linear_star_incidences=40,remaining_qs_incidences=10,retains225q_incidence=True,arbitrary_null_faces=False,arbitrary_9qs_central_roles=False,network_scope='same declared ordinary/private interfaces as657/658; at most three parents below chosen switch')
out=dict(schema='leaf-pair-priority-fields-v1',status='PASS',new_lean_verification=False,scope=scope,source_sha256=pins,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),projection_alpha=str(alpha),g=str(g),corner_count=95,fields_by_ternary_weak={str(i):list(map(str,fields[i]))for i in live3},field_independent_of_quinary_weak=True,minimum=minimum,minimizers=minimizers,head_gate=str(gate),corner_gates=records,complete_screen_count=screen_total,literal_selector_candidate_count=selector_total,minimum_union_retention=str(min(retention)),minimum_matching_retention=str(min(matching_retention)),finite_fee_upper=str(finite),complete_five_parent_tail=str(w5),ordinary_typeI_fee=str(typeI),policies=policies,checks=dict(checks),check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=out['check_count'],corner_count=95,minimum=minimum,policies=[dict(kind=p['kind'],projected=float(F(p['projected_margin'])))for p in policies]),indent=2))
