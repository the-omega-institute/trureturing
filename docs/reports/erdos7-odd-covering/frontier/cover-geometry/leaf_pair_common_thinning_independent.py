#!/usr/bin/env python3
"""Reconstruct one fixed-source 9qs matching/thinning gate and the pinned658 budget.

The frozen candidate data is compared after reconstruction; its producer is not read. The actual-source, unbounded
height and network-transfer arguments remain ordinary mathematical obligations;
this program checks their finite rational coefficients and declared scope only.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import lcm, prod
from pathlib import Path
import json

PIN640='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4'
PIN658='cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'
PIN_CANDIDATE='083ec84a1a0f9f68316de6f333c933382040418263c98493081b26d7ec850c97'
parser=ArgumentParser(description=__doc__)
parser.add_argument('--source640',type=Path,default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
parser.add_argument('--network658',type=Path,default=Path(__file__).with_name('joint_square_pair_225_star_certificate.json'))
parser.add_argument('--candidate',type=Path,default=Path(__file__).with_name('leaf_pair_common_thinning_certificate.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
checks=Counter()
def check(ok,kind):
    checks[kind]+=1
    if not ok:raise ArithmeticError('independent certificate check failed: '+kind)
def load_pinned(path,pin,label):
    raw=path.read_bytes()
    check(sha256(raw).hexdigest()==pin,label+'_pin')
    return json.loads(raw)
old=load_pinned(args.source640,PIN640,'coefficient640')
network=load_pinned(args.network658,PIN658,'network658')
candidate=load_pinned(args.candidate,PIN_CANDIDATE,'candidate659')
Q=(7,11,13,17,19)
pairs=list(combinations(range(5),2))
a=[F(1,q*(q-2)) for q in Q]
r=[F(1,q-1) for q in Q]
g=F(old['constants']['g'])
alpha=F(old['constants']['alpha'])
check(g==F(200163067,201247200),'mass_coefficient')
check(alpha==F(2673,110656),'projection_coefficient')
C=[F(v) for v in old['combined512_coefficients']]
check(len(C)==512,'complete_coefficient_count')
check(all(c>=0 for c in C),'nonnegative_coefficients')
for i in range(1,5):C[32*9+(1<<i)]+=g*a[i]
x=[2,2,2,0,1,2]
y=[0 if m==5 else 3 if m==6 else 4 for m in range(20)]
check(sum(x)==9 and sum(y)==75,'normalized_central_weights')
check([l for l in range(6) if x[l]==0]==[3] and [m for m in range(20) if y[m]==0]==[5],'fixed_null_leaves')
check([l for l in range(6) if x[l]==1]==[4] and [m for m in range(20) if y[m]==3]==[6],'fixed_weak_leaves')

# Exact source data, using root-major reference coordinates.
a3=lambda l:3*(l%3)+l//3
a5=lambda m:5*(m%5)+m//5
check(sorted(a3(l) for l in range(6))==[0,1,3,4,6,7],'ternary_reference_map')
check(len({a5(m) for m in range(20)})==20,'quinary_reference_map')
check(a3(3)==1 and a5(5)==1,'pure_null_residues')
check(a3(5)==7 and a3(5)%3==1,'globally_fixed_9_leaf')
check(all(a5(m)%5==2 for m in range(10,15)),'square5_central_root')
# Density relative to Haar on a full mod9/mod25 leaf. These checks do not
# substitute for the theorem relating actual higher-digit laws to the source.
check(max(F(v,9)*9 for v in x)==2,'ternary_full_haar_density')
check(max(F(v,75)*25 for v in y)==F(4,3),'quinary_full_haar_density')

linear_factors=(3,5,15,9,25,45,75,225)
retained_linear=sorted(f*q for f in linear_factors for q in Q)
retained_pairs=sorted(Q[i]*Q[j] for i,j in pairs)
released_square_stars=sorted(f*q*q for f in (3,5,9) for q in Q)
released_square_pairs=sorted([Q[i]*Q[i]*Q[j] for i,j in pairs]+[Q[i]*Q[j]*Q[j] for i,j in pairs])
released9=sorted(9*Q[i]*Q[j] for i,j in pairs)
classes=[retained_linear,retained_pairs,released_square_stars,released_square_pairs,released9]
check(list(map(len,classes))==[40,10,15,20,10],'original_class_counts')
all_originals=[n for cls in classes for n in cls]
check(len(set(all_originals))==95,'distinct_numerical_originals')
check(all(n>1 and n%2 for n in all_originals),'odd_original_moduli')
check(all(225*q in retained_linear for q in Q),'225_incidence_retained')

scope={
 'actual_central_pure_slots':[[3,2],[9,1],[5,4],[25,1]],
 'additional_source_live_pure3_or5_originals_allowed':False,
 'missing_declared_pure_slots_may_be_auxiliary_deletions':True,
 'within_live_leaf_law':'uniform Haar before common thinning',
 'central15_residue':0,
 'central_weight_numerators3':x,'central_weight_denominator3':9,
 'central_weight_numerators5':y,'central_weight_denominator5':75,
 'square7_central_roles':[[147,3,1],[245,5,2],[441,9,7]],
 'square7_layout':[1,2,5],
 'square_stars_at_q_greater_than7_central_phases':'arbitrary globally fixed',
 'all_square_star_outside_phases':'arbitrary globally fixed',
 'all9qs_central_mod9_residue':7,
 'all9qs_outside_endpoints':'arbitrary globally fixed',
 'all_square_pair_outside_phases':'arbitrary globally fixed',
 'retained_linear_star_moduli':retained_linear,
 'retained_pair_moduli':retained_pairs,
 'released_square_star_moduli':released_square_stars,
 'released_square_pair_moduli':released_square_pairs,
 'released9qs_moduli':released9,
 'retained_root_incidence_count':50,
 '225_release_combined':False,
 'outside_pure_phases_and_heights':'arbitrary phases and finite heights under inherited648 construction',
 'remaining_inventory':'Report648 complete original and full-height query inventory',
 'continuation':'Rebuild23/29/31 and the Report658 three-parent ordinary/private network on the same actual source',
 'finite_owner_h_caps':'unchanged193 entries from pinned658/657; no reoptimization',
 'same_source':{'one_actual_family':True,'phases_fixed_globally':True,'theta_common_to_all32_responses':True,
                'actual_source_existence_proved_by_this_finite_check':False},
 'scope_exclusions':['all central phase layouts','all numerical comparison corners','unrestricted Erdos7','new Lean verification']}


def make_menus(weights,root_size,deep):
    n=len(weights);live=[i for i,v in enumerate(weights) if v]
    return [[weights],
            [[v if i//root_size==root else 0 for i,v in enumerate(weights)] for root in range(n//root_size)],
            [[v if i==leaf else 0 for i,v in enumerate(weights)] for leaf in live],
            [[deep if i==leaf else 0 for i in range(n)] for leaf in live]]
mx,my=make_menus(x,3,9),make_menus(y,5,60)
menus=[]
for mode in range(16):
    menus.append([[(20*l+m,xx[l]*yy[m]) for l in range(6) for m in range(20) if xx[l] and yy[m]]
                  for xx in mx[mode//4] for yy in my[mode%4]])
check([len(v) for v in mx]==[1,2,5,5] and [len(v) for v in my]==[1,4,19,19],'literal_menu_sizes')
check(sum(map(len,menus))*32==17888,'literal_selector_candidate_count')

# Reconstruct both sufficient envelopes from the actual fixed phase field.
union=[[F(0) for c in range(120)] for mask in range(32)]
matching=[[F(0) for c in range(120)] for mask in range(32)]
theta=[];retentions=[];matching_retentions=[]
for l in range(6):
    for m in range(20):
        c=20*l+m
        n=int(l//3==1)+int(m//5==2)+int(l==5)
        Z=[F(5,6)-F(n,35)]+[F(q-2,q-1)-2*a[i] for i,q in enumerate(Q) if i]
        beta={(i,j):a[i]*r[j]+r[i]*a[j]+(r[i]*r[j] if l==5 else 0) for i,j in pairs}
        check(min(Z)>0,'positive_coordinate_masses')
        p={e:beta[e]/(Z[e[0]]*Z[e[1]]) for e in pairs}
        retention=1-sum(p.values(),F(0))
        check(retention>0,'strict_shearer_from_union_region')
        retentions.append(retention)
        masked=l<3 and m<5
        for mask in range(32):
            U=[i for i in range(5) if not (mask>>i&1)]
            edges=list(combinations(U,2))
            h=prod((Z[i] for i in U),start=F(1))
            h-=sum((beta[e]*prod((Z[i] for i in U if i not in e),start=F(1)) for e in edges),F(0))
            extra=F(0)
            for e,f in combinations(edges,2):
                covered=set(e)|set(f)
                if len(covered)==4:
                    extra+=beta[e]*beta[f]*prod((Z[i] for i in U if i not in covered),start=F(1))
            check(h>0 and extra>=0,'positive_induced_responses')
            union[mask][c]=F(0) if masked else h
            matching[mask][c]=F(0) if masked else h+extra
            if mask==0:matching_retentions.append((h+extra)/prod(Z))
        if not x[l] or not y[m] or masked:t=F(0)
        elif l==5:t=F(1)
        elif l==4:t=F(19,20) if m//5==2 else F(11,12)
        else:t=F(11,12) if m//5==2 else F(8,9)
        check(0<=t<=1,'legal_common_thinning')
        theta.append(t)
check(min(retentions)==F(754111121894423,876550251053789),'minimum_union_retention')
check(min(matching_retentions)==F(3780354901112254,4382751255268945),'minimum_matching_retention')
thinned=[[matching[T][c]*theta[c] for c in range(120)] for T in range(32)]
for T in range(32):
    check(all(0<=thinned[T][c]<=matching[T][c] for c in range(120)),'common_thinning_domination')


def evaluate(table):
    screens=[F(0)]*512;argmax=[None]*512;literal_count=0
    for T in range(32):
        row=table[T];D=lcm(*(h.denominator for h in row))
        ints=[h.numerator*(D//h.denominator) for h in row]
        for mode in range(16):
            vals=[sum(ints[c]*w for c,w in sel) for sel in menus[mode]]
            best=max([0]+vals)
            j=32*mode+T
            screens[j]=F(best,675*D)
            argmax[j]=vals.index(best) if best in vals else -1
            literal_count+=len(vals)
            check(best>=0 and all(best>=v for v in vals),'complete_selector_maximum')
    mass=sum((F(x[l]*y[m],675)*table[0][20*l+m] for l in range(6) for m in range(20)),F(0))
    check(mass==screens[0],'empty_query_matches_mass')
    debit=sum((fee*s for fee,s in zip(C,screens)),F(0))
    return {'mass':str(mass),'weighted_mass':str(g*mass),'debit':str(debit),'gate':str(g*mass-debit),
            'complete512_screens':[str(s) for s in screens],'argmax_indices':argmax,
            'literal_selector_candidates':literal_count}
union_eval=evaluate(union);matching_eval=evaluate(matching);answer=evaluate(thinned)
check(F(union_eval['gate'])==F(-15205847902116555363365237,8277002364621448313856000000),'unthinned_union_gate')
check(F(matching_eval['gate'])==F(-149653176558100042691623,94594312738530837872640000),'unthinned_matching_gate')
gate=F(answer['gate'])
check(gate==F(1864487415907319442048626989,931162766019912935308800000000),'positive_thinned_gate')
check(gate>F(1,500),'head_gate_over_one500')
weighted_mass_cost=F(matching_eval['weighted_mass'])-F(answer['weighted_mass'])
fee_saving=F(matching_eval['debit'])-F(answer['debit'])
check(weighted_mass_cost==F(6761250336491948285528653,212230829862088418304000000),'exact_thinning_weighted_mass_cost')
check(fee_saving==F(10154652838156781489246540287,286511620313819364710400000000),'exact_thinning_fee_saving')
check(gate-F(matching_eval['gate'])==fee_saving-weighted_mass_cost,'thinning_gain_balance')

check(network['status']=='PASS' and not network['new_lean_verification'],'network_receipt_scope')
check(F(network['g'])==g and F(network['projection_alpha'])==alpha,'same_network_constants')
check(len(network['finite_rows'])==193 and not network['finite_row_parameters_reoptimized'],'unchanged_finite_row_schedule')
for row in network['finite_rows']:
    v,h=row['owner'],row['h']
    D=F(v-2)-F(1,65536)
    cap=F(v-1,h)
    check(row['r']==3 and row['N']==0 and h>=10 and h<D,'finite_row_scope')
    check(F(row['D'])==D and F(row['t'])==D-h,'ordinary_domain_and_hinge')
    check(F(row['cap'])==cap and cap<F(v,10),'inherited_full_haar_cap')
check(sum((F(row['fee_upper']) for row in network['finite_rows']),F(0))==F(network['finite_fee_upper']),'finite_budget_row_sum')
check(network['branch_parameters']['parents']==[3,5,7] and F(network['branch_parameters']['exact_EC'])==F(11,5),'three_parent_branch')
check(network['Euler_counts']=={'head':10,'finite':193,'half':123},'full_cap_table_counts')
finite=F(network['finite_fee_upper']);tail=F(network['complete_five_parent_tail']);typeI=F(network['ordinary_typeI_fee'])
check(finite>=0 and tail>0 and typeI==F(1,65536),'network_charge_signs')
check(finite+tail+typeI==F(network['fee_before_arbitrary']),'inherited_network_charge_sum')
check({(p['kind'],p['K']) for p in network['policies']}=={('RS',46),('elementary',68)},'complete_network_policies')
policies=[]
for policy in network['policies']:
    check(policy['arbitrary_threshold']==2**policy['K'] and policy['max_parents_below_switch']==3,'network_switch_and_parent_scope')
    fee=F(policy['fee'])
    old_raw=F(network['head_gate'])-finite-tail-typeI-fee
    check(old_raw==F(policy['raw_margin']) and alpha*old_raw==F(policy['projected_margin']),'inherited_policy_sum')
    raw_margin=gate-finite-tail-typeI-fee
    projected=alpha*raw_margin
    check(projected>F(1,420000),'new_complete_density_one420000')
    check(projected>F(1,500000),'new_complete_density_one500000')
    if policy['kind']=='elementary':check(projected<F(1,400000),'one400000_is_not_certified_by_this_bound')
    policies.append({'kind':policy['kind'],'K':policy['K'],'arbitrary_threshold':policy['arbitrary_threshold'],
                     'max_parents_below_switch':3,'fee':str(fee),'raw_margin':str(raw_margin),
                     'projected_margin':str(projected),'density_denominator':420000})

check(candidate['schema']=='leaf-pair-common-thinning-v1' and candidate['status']=='PASS' and candidate['new_lean_verification'] is False,'candidate_scope_header')
check(candidate['source_sha256']=={args.source640.name:PIN640,args.network658.name:PIN658},'candidate_source_pins')
expected_scope={
 'actual_central_pure_originals':[[3,2],[9,1],[5,4],[25,1]],
 'additional_source_live_central_pure_originals':False,
 'central15_residue':0,
 'square7_central_roles':{'mod3':1,'mod5':2,'mod9':7},
 'all_ten_9qs_mod9_residue':7,
 'outside_core_pure_phases':'arbitrary at every finite original height',
 'remaining_linear_star_incidences':40,'remaining_qs_incidences':10,
 'released_9qs_endpoint_incidences':10,'released_square_pair_endpoint_incidences':20,
 'retains225q_incidence':True,'arbitrary_9qs_central_roles':False,
 'arbitrary_central_pure_phases':False,
 'network_scope':'same declared ordinary/private interfaces as657/658; at most three parents below chosen switch'}
check(candidate['scope']==expected_scope,'candidate_original_scope_exact')
check(candidate['central_source_corner']==[3,4,5,6],'candidate_corner')
check([F(v) for v in candidate['central_source_weights3']]==[F(v,9) for v in x],'candidate_actual_ternary_weights')
check([F(v) for v in candidate['central_source_weights5']]==[F(v,75) for v in y],'candidate_actual_quinary_weights')
check([F(v) for v in candidate['theta']]==theta,'candidate_same_thinning120')
check([F(v) for v in candidate['complete512_coefficients']]==C,'candidate_complete512_coefficients')
check(candidate['literal_selector_candidate_count']==17888,'candidate_literal_selector_count')
for i,(actual,expected) in enumerate(zip(candidate['complete512_screens'],answer['complete512_screens'])):
    check(F(actual)==F(expected),'candidate_all512_screens')
check(len(candidate['complete512_screens'])==512,'candidate_all512_screens_length')
for name,expected in [('g',g),('projection_alpha',alpha),('source_mass',F(answer['mass'])),
                      ('minimum_union_retention',min(retentions)),('minimum_matching_retention',min(matching_retentions)),
                      ('complete_head_debit',F(answer['debit'])),('head_gate',gate),('finite_fee_upper',finite),
                      ('complete_five_parent_tail',tail),('ordinary_typeI_fee',typeI)]:
    check(F(candidate[name])==expected,'candidate_exact_'+name)
check(candidate['policies']==policies,'candidate_complete_policy_sums')

out={'schema':'leaf-pair-common-thinning-independent-v1','status':'PASS','new_lean_verification':False,
     'scope':scope,'source_sha256':{'640':PIN640,'658':PIN658},
     'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
     'candidate_producer_read':False,'candidate_data_read':True,'candidate_sha256':PIN_CANDIDATE,
     'minimum_union_retention':str(min(retentions)),'minimum_matching_retention':str(min(matching_retentions)),
     'unthinned_union_gate':union_eval['gate'],'unthinned_matching_gate':matching_eval['gate'],
     'unthinned_matching_complete512_screens':matching_eval['complete512_screens'],
     'unthinned_matching_source_mass':matching_eval['mass'],'unthinned_matching_debit':matching_eval['debit'],
     'thinning_weighted_mass_cost':str(weighted_mass_cost),'thinning_fee_saving':str(fee_saving),
     'theta120':[str(t) for t in theta],'head_gate':str(gate),'head_mass':answer['mass'],'complete_debit':answer['debit'],
     'complete512_screens':answer['complete512_screens'],'argmax_indices':answer['argmax_indices'],
     'literal_selector_candidates_per_gate':17888,'projection_alpha':str(alpha),
     'finite_fee_upper':str(finite),'complete_five_parent_tail':str(tail),'ordinary_typeI_fee':str(typeI),
     'policies':policies,'checks':dict(sorted(checks.items())),'check_count':sum(checks.values()),
     'verification_boundary':'Exact fixed-source coefficient certificate and reuse of pinned658 budget; source existence and transfer remain separately proved mathematical conditions.'}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'check_count':out['check_count'],'head_gate':str(gate),
                  'projected_margins':{p['kind']:float(F(p['projected_margin'])) for p in policies},
                  'density_denominator':420000,'producer_sha256':out['producer_sha256']},indent=2))
