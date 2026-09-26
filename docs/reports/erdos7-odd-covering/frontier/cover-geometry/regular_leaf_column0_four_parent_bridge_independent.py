#!/usr/bin/env python3
"""Compose the certified regular-leaf unit head with the complete666 schedule.
Reads only the pinned666 numerical certificate and the new independent unit
certificate. No hinge reconstruction or full head scan is repeated.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--head',type=Path,default=Path(__file__).with_name('ell0_column0_unit_independent_driver.json'))
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args();checks={}
def ck(name,test):
    checks[name]=checks.get(name,0)+1
    if not test:raise RuntimeError(name)
path=a.directory/'four_parent_tail_fixed_schedule.json';fb=path.read_bytes();schedule=json.loads(fb)
hb=a.head.read_bytes();head=json.loads(hb)
ck('pinned_complete666',sha256(fb).hexdigest()=='fa79d1c28aea101da734ac687fe9ddb6e39bc6bd212a206183e049d1e929f758')
ck('pinned_independent_unit_head',sha256(hb).hexdigest()=='250d80c3027db14ff6b61d96426bb1b6c7025f2f79c018658d3b1f9c9896d649')
ck('both_certificates_pass',head['status']==schedule['status']=='PASS' and head['mode']=='full')
ck('one_exact_unit_field',head['family_count']==1 and head['field']=='exact unit1 on80 allowed cells;0 elsewhere')
ck('same658_origin',head['source_sha256']['joint_square_pair_225_star_certificate.json']==schedule['source_sha256']['joint_square_pair_225_star_certificate.json'])
ck('correct_roles',head['square7_roles']==[[0,0,0],[1,0,0]])
ck('response_scales',head['precisions']==dict(B=32,P=32,R=40))
head_bounds=[]
for branch in head['branches']:
    e=branch['enumeration']
    ck('full_S2_representatives',e['status']=='PASS' and e['canonical_layout_count']==4912337 and e['actual_layout_count']==9765625 and e['regular_class_counts']==[59049,4853288,0,0])
    ck('whole_unit_field_everywhere',e['family_selection_counts']==[4912337] and e['accepted_complete_corner_gates']==4912337*20 and e['accepted_complete_screen_maxima']==4912337*20*512)
    head_bounds.append(F(e['minimum_selected_lower_q40'],1<<40))
ck('both_role_branches',len(head_bounds)==2 and [b['square7_roles'] for b in head['branches']]==head['square7_roles'])
gamma=min(head_bounds);ck('new_common_head_lower_bound',gamma==F(3382155356,1<<40))
alpha=F(schedule['projection_alpha']);ck('fixed_projection_alpha',alpha==F(2673,110656))
rows=schedule['rows']
primes=[v for v in range(37,1253) if all(v%d for d in range(2,int(v**0.5)+1))]
ck('complete193_owner_window',len(rows)==193 and [r['owner'] for r in rows]==primes)
cut=61;finite_lower=F(0);finite_upper=F(0);selected=[]
for row in rows:
    v,h=row['owner'],row['h'];kind='three' if v<cut else 'four'
    ck('unchanged_full_Haar_cap',F(row['cap'])==F(v-1,h) and F(row['cap'])/v<F(1,10))
    ck('unchanged_actual_domain_threshold',F(row['threshold'])==F(v-2)-F(1,65536)-h)
    lo,hi=F(row[kind+'_lower']),F(row[kind+'_upper'])
    ck('certified_row_interval',0<=lo<=hi)
    finite_lower+=lo;finite_upper+=hi
    selected.append([v,kind,h,row['cap'],row['threshold'],str(lo),str(hi)])
ck('cut61_row_census',sum(r['owner']<cut for r in rows)==6 and sum(r['owner']>=cut for r in rows)==187)
old3=sum((F(row['three_upper']) for row in rows),F(0));ck('unchanged_old_three_sum',old3==F(schedule['old_three_parent_fee']))
five=F(schedule['unchanged_five_parent_tail']);typeI=F(schedule['unchanged_TypeI'])
ck('complete_five_parent_tail',five==F(215382309954767220434928870511633,262567468948404680792561991974400000000))
ck('complete_typeI',typeI==F(1,65536))
policies=[]
for policy in schedule['policies']:
    kind,K=policy['kind'],policy['K'];arbitrary=F(policy['arbitrary_tail'])
    ck('retained_policy_switch',((kind,K) in (('RS',46),('elementary',68))) and arbitrary>0)
    inherited=next(x for x in head['policies'] if (x['kind'],x['K'])==(kind,K))
    ck('same_original_complete_budget',F(inherited['complete_fee'])==old3+five+typeI+arbitrary and F(inherited['projection_alpha'])==alpha)
    full_upper=finite_upper+five+typeI+arbitrary;full_lower=finite_lower+five+typeI+arbitrary
    raw_lower=gamma-full_upper;projected=alpha*raw_lower
    ck('all_budget_parts_present',full_upper-finite_upper==five+typeI+arbitrary)
    ck('strict_density_above_one_over_two_hundred_thousand',projected>F(1,200000))
    policies.append(dict(kind=kind,K=K,final_switch=1<<K,finite_fee_lower=str(finite_lower),finite_fee_upper=str(finite_upper),five_parent_full_height_tail=str(five),ordinary_typeI=str(typeI),arbitrary_parent_complete_tail=str(arbitrary),complete_fee_upper=str(full_upper),complete_fee_lower=str(full_lower),raw_margin_lower=str(raw_lower),projected_margin_lower=str(projected),projected_margin_lower_decimal=float(projected),margin_over_required_density=str(projected-F(1,200000)),strict_density_denominator=200000,owner_limits=[dict(lower=37,upper_exclusive=61,max_parents=3),dict(lower=61,upper_exclusive=1253,max_parents=4),dict(lower=1253,upper_exclusive=1<<K,max_parents=5),dict(lower=1<<K,max_parents='arbitrary finite')]))
ck('both_complete_policies',[(p['kind'],p['K']) for p in policies]==[('RS',46),('elementary',68)])
result=dict(schema='regular-leaf-column0-four-parent-bridge-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,input_sha256={'four_parent_tail_fixed_schedule.json':sha256(fb).hexdigest(),a.head.name:sha256(hb).hexdigest()},verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),square7_roles=head['square7_roles'],common_head_gate=str(gamma),common_head_gate_q40=3382155356,projection_alpha=str(alpha),cutoff=61,finite_owner_count=193,three_parent_rows=6,four_parent_rows=187,selected_exact_row_endpoints_sha256=sha256(json.dumps(selected,separators=(',',':')).encode()).hexdigest(),policies=policies,checks=checks,check_count=sum(checks.values()),scope='Same actual source as the unit head and same666 normalized owner construction,193 h/caps,326 Euler factors,M0 bounds,full-height five-parent tail,TypeI and complete arbitrary-parent tail. Only the common head lower bound and declared finite parent-count cutoff change. Source domination and interface applicability are the ordinary mathematical bridge; this program recombines their pinned numerical certificates. No claim that61 is minimal, no actual parent independence, no new Lean, and no unrestricted odd-covering resolution.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],check_count=result['check_count'],head=float(gamma),cutoff=cut,margins={p['kind']:p['projected_margin_lower_decimal'] for p in policies})))
