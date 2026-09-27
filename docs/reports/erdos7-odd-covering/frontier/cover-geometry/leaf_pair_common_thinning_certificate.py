#!/usr/bin/env python3
"""Exact restricted-source common-thinning certificate and complete networks.

Only the pinned640 coefficient JSON and658 network JSON are read. The
central source, matching responses and all512 literal screens are rebuilt.
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
x=[2,2,2,0,1,2];y=[0 if m==5 else 3 if m==6 else 4 for m in range(20)]
ck('actual_source_normalized',sum(x)==9 and sum(y)==75)
for l in range(6):
 literal=l//3+3*(l%3)
 ck('actual_ternary_leaf',F(x[l],9)>=0 and F(x[l],9)<=F(2,9) and (literal!=1 or x[l]==0) and literal%3!=2)
for m in range(20):
 literal=m//5+5*(m%5)
 ck('actual_quinary_leaf',F(y[m],75)>=0 and F(y[m],75)<=F(4,75) and (literal!=1 or y[m]==0) and literal%5!=4)
H=[[]for _ in range(32)];retention=[];matching_retention=[];theta=[]
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
 if not x[l]*y[m]or(l<3 and m<5):t=F()
 elif l==5:t=F(1)
 elif l<3:t=F(11,12)if m//5==2 else F(8,9)
 else:t=F(19,20)if m//5==2 else F(11,12)
 ck('legal_common_thinning',0<=t<=1);theta.append(t)
ck('union_retention_minimum',min(retention)==F(754111121894423,876550251053789))
ck('matching_retention_minimum',min(matching_retention)==F(3780354901112254,4382751255268945))
MX=[[x],[[x[l]if l//3==j else 0 for l in range(6)]for j in range(2)],[[x[l]if l==j else 0 for l in range(6)]for j in range(6)if x[j]],[[9 if l==j else 0 for l in range(6)]for j in range(6)if x[j]]]
MY=[[y],[[y[m]if m//5==j else 0 for m in range(20)]for j in range(4)],[[y[m]if m==j else 0 for m in range(20)]for j in range(20)if y[j]],[[60 if m==j else 0 for m in range(20)]for j in range(20)if y[j]]]
Dh=lcm(*(h.denominator for grid in H for h in grid),*(t.denominator for t in theta))
Htheta=[[h*t for h,t in zip(grid,theta)]for grid in H];Dt=lcm(*(h.denominator for grid in Htheta for h in grid));Hi=[[int(h*Dt)for h in grid]for grid in Htheta]
screens=[];candidate_count=0
for e3,e5 in product(range(4),repeat=2):
 for T in range(32):
  vals=[sum(xx[l]*yy[m]*Hi[T][20*l+m]for l in range(6)for m in range(20))for xx in MX[e3]for yy in MY[e5]]
  candidate_count+=len(vals);best=max(vals);ck('complete_screen_nonnegative',best>=0);screens.append(F(best,675*Dt))
mass=sum((F(x[l]*y[m],675)*H[0][20*l+m]*theta[20*l+m]for l,m in product(range(6),range(20))),F())
ck('unit_screen_is_mass',mass==screens[0]);debit=sum(c*s for c,s in zip(C,screens));gate=g*mass-debit
ck('exact_head_gate',gate==F(1864487415907319442048626989,931162766019912935308800000000))
ck('strict_head_margin',gate>F(1,500));ck('literal_menu_count',candidate_count==17888)
finite=F(network['finite_fee_upper']);w5=F(network['complete_five_parent_tail']);typeI=F(network['ordinary_typeI_fee'])
ck('three_parent_reference',network['branch_parameters']['parents']==[3,5,7])
ck('unchanged_typeI',typeI==F(1,65536));ck('finite_schedule_count',len(network['finite_rows'])==193)
for row in network['finite_rows']:
 v=row['owner'];h=row['h'];cap=F(row['cap'])
 ck('fixed_finite_cap',cap==F(v-1,h) and cap<F(v,10))
policies=[]
for policy in network['policies']:
 K=policy['K'];fee=F(policy['fee']);raw=gate-finite-w5-typeI-fee;projected=alpha*raw
 ck('policy_switch',K in (46,68) and policy['arbitrary_threshold']==2**K and policy['max_parents_below_switch']==3)
 ck('complete_density',projected>F(1,420000))
 policies.append(dict(kind=policy['kind'],K=K,arbitrary_threshold=2**K,max_parents_below_switch=3,fee=str(fee),raw_margin=str(raw),projected_margin=str(projected),density_denominator=420000))
scope=dict(actual_central_pure_originals=[[3,2],[9,1],[5,4],[25,1]],additional_source_live_central_pure_originals=False,central15_residue=0,square7_central_roles=dict(mod3=1,mod5=2,mod9=7),all_ten_9qs_mod9_residue=7,outside_core_pure_phases='arbitrary at every finite original height',remaining_linear_star_incidences=40,remaining_qs_incidences=10,released_9qs_endpoint_incidences=10,released_square_pair_endpoint_incidences=20,retains225q_incidence=True,arbitrary_9qs_central_roles=False,arbitrary_central_pure_phases=False,network_scope='same declared ordinary/private interfaces as657/658; at most three parents below chosen switch')
out=dict(schema='leaf-pair-common-thinning-v1',status='PASS',new_lean_verification=False,scope=scope,source_sha256=pins,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),projection_alpha=str(alpha),g=str(g),central_source_corner=[3,4,5,6],central_source_weights3=[str(F(v,9))for v in x],central_source_weights5=[str(F(v,75))for v in y],theta=list(map(str,theta)),source_mass=str(mass),minimum_union_retention=str(min(retention)),minimum_matching_retention=str(min(matching_retention)),complete512_coefficients=list(map(str,C)),complete512_screens=list(map(str,screens)),literal_selector_candidate_count=candidate_count,complete_head_debit=str(debit),head_gate=str(gate),finite_fee_upper=str(finite),complete_five_parent_tail=str(w5),ordinary_typeI_fee=str(typeI),policies=policies,checks=dict(checks),check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=out['check_count'],head_gate=float(gate),policies=[dict(kind=p['kind'],raw=float(F(p['raw_margin'])),projected=float(F(p['projected_margin'])),denominator=p['density_denominator'])for p in policies]),indent=2))
