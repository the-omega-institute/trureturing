#!/usr/bin/env python3
"""Independent exact rational replay; reads data only, never producer code.

Canonical paired rows and the old35713 runner-up are reconstructed from atomic
laws, using the complete mean and finite negative part. Global noncanonical
coverage uses the separately proved old655 exchange/runner-up theorem.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import prod
from pathlib import Path
import json
import sys

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
p = ArgumentParser(description=__doc__)
p.add_argument('--directory', type=Path, default=HERE)
p.add_argument('--candidate', type=Path, default=HERE/'paired_owner_fixed_rows_certificate.json')
p.add_argument('--output', type=Path, default=HERE/'paired_owner_fixed_rows_independent.json')
a = p.parse_args()
checks = {}
def ck(name, ok):
    checks[name] = checks.get(name, 0) + 1
    if not ok:
        raise RuntimeError(name)

candidate_bytes = a.candidate.read_bytes()
d = json.loads(candidate_bytes)
inputs = {}
for name, pin in d['input_sha256'].items():
    data = (a.directory/name).read_bytes()
    ck('pinned_source_input', sha256(data).hexdigest() == pin)
    inputs[name] = json.loads(data)
old4 = inputs['four_parent_tail_fixed_schedule.json']
old5 = inputs['ordinary_domain_five_parent_certificate.json']
old3 = inputs['joint_square_pair_225_star_certificate.json']
primes = [v for v in range(37,1253) if all(v % k for k in range(2, int(v**0.5)+1))]
ck('complete193actualowners', len(primes)==193 and [r['owner'] for r in d['rows']]==primes)
ck('same_old_owner_lists', [r['owner'] for r in old4['rows']]==primes
   and [r['owner'] for r in old5['finite_rows']]==primes
   and [r['owner'] for r in old3['finite_rows']]==primes)
N = max((F(r['s']).numerator-1)//F(r['s']).denominator for r in d['rows'])
ck('finite_negative_part_covers_all_thresholds', d['finite_negative_part_endpoint']==N+1)

Q=(7,11,13,17,19)
Z={q:F(q-2,q-1)-(F(0) if q==7 else F(2,q*(q-2))) for q in Q}
edges={frozenset((q,s)):F(1,q*(q-2)*(s-1))+F(1,s*(s-2)*(q-1))
       for q,s in combinations(Q,2)}
def matching(U):
    es=[e for e in edges if e<=U]
    return (prod(Z[q] for q in U)
      -sum(edges[e]*prod(Z[q] for q in U-e) for e in es)
      +sum(edges[e]*edges[f]*prod(Z[q] for q in U-e-f)
           for e,f in combinations(es,2) if not e&f))
R0,R7,R11,R711=[matching(set(Q)-set(T)) for T in ((),(7,),(11,),(7,11))]
c00=R0-F(1,6)*R7-F(1,10)*R11+F(1,60)*R711
c10=R7-F(1,10)*R711
c01=R11-F(1,6)*R711
ck('matching_constants', list(map(F,d['paired_response_constants']))==[R0,R7,R11,R711])
ck('positive_tau_coefficients', min(c00,c10,c01,R711)>0
   and list(map(F,d['tau_block_coefficients']))==[c00,c10,c01,R711])
ck('complete_tau_mass', c00+F(1,6)*c10+F(1,10)*c01+F(1,60)*R711==R0
   and F(d['complete_tau_mass'])==R0)

def survival(q, e):
    if e==0:return F(1)
    if q==3:return F(2,3**e)
    if q==5:return F(4,3*5**e)
    if e==1:return F(1,q-1)
    return F(1,(q-2)*q**(e-1))
def atom_law(q):
    return [F(0)]+[survival(q,j-1)-survival(q,j) for j in range(1,N+1)]
def mean(q):
    if q==3:return F(2)
    if q==5:return F(4,3)
    return F(q-1,q-2)
laws={q:atom_law(q) for q in (3,5,7,11,13)}
for q, law in laws.items():
    for x in law[1:]:ck('nonnegative_exact_atom', x>=0)
    ck('finite_atoms_plus_exact_tail', sum(law,F(0))+survival(q,N)==1)

def convolution(left,right):
    out=[F(0)]*(N+1)
    for x in range(1,N+1):
        if left[x]:
            for y in range(1,N//x+1):
                if right[y]:out[x*y]+=left[x]*right[y]
    return out

central=convolution(laws[3],laws[5])
positive7=laws[7][:];positive7[1]=F(0)
positive11=laws[11][:];positive11[1]=F(0)
joint=convolution(positive7,positive11)
tau_product=[c10*positive7[k]+c01*positive11[k]+R711*joint[k] for k in range(N+1)]
tau_product[1]+=c00
canonical=convolution(central,tau_product)
mean_tau=(c00+c10*(mean(7)-laws[7][1])+c01*(mean(11)-laws[11][1])
          +R711*(mean(7)-laws[7][1])*(mean(11)-laws[11][1]))
complete_mean=mean(3)*mean(5)*mean_tau
ck('complete_product_mean', complete_mean==F(d['complete_product_mean']))
three=convolution(central,laws[7])
four=convolution(three,laws[11])
runner=convolution(three,laws[13])
factor3=prod(Z[q] for q in (11,13,17,19))
factor4=prod(Z[q] for q in (13,17,19))
factor_runner=prod(Z[q] for q in (11,17,19))
ck('old_omitted_factors', factor3==F(old3['branch_parameters']['factor'])
   and factor4==F(old4['four_role_omitted_head_factor']))

def prefix(law):
    mass=[F(0)];first=[F(0)]
    for k in range(1,N+1):
        mass.append(mass[-1]+law[k]);first.append(first[-1]+k*law[k])
    return mass,first
prefixes={k:prefix(law) for k,law in (('paired',canonical),('three',three),('four',four),('runner',runner))}
def hinge(key,totalmean,totalmass,s):
    m,z=prefixes[key];n=(s.numerator-1)//s.denominator
    ck('exact_negative_part_address', 0<=n<=N)
    return totalmean-s*totalmass+s*m[n]-z[n]

paired_fees=[];old_four_fees=[];runner_fees=[];three_fees=[];rows=[]
for i,r in enumerate(d['rows']):
    v,h,s=r['owner'],r['h'],F(r['s'])
    f4,f5,f3=old4['rows'][i],old5['finite_rows'][i],old3['finite_rows'][i]
    cap=F(v-1,h);threshold=F(v-2)-F(1,65536)-h
    ck('unchanged_actual_h_cap_threshold', h==f4['h']==f5['h']==f3['h']
       and cap==F(f4['cap'])==F(f5['cap'])==F(f3['cap'])
       and cap/F(v)<F(1,10)
       and s==threshold+1==F(f4['threshold'])+1==F(f5['t'])+1==F(f3['t'])+1)
    paired=hinge('paired',complete_mean,R0,s)/h
    former=factor4*hinge('four',prod(mean(q) for q in (3,5,7,11)),F(1),s)/h
    second=factor_runner*hinge('runner',prod(mean(q) for q in (3,5,7,13)),F(1),s)/h
    fee3=factor3*hinge('three',prod(mean(q) for q in (3,5,7)),F(1),s)/h
    scale=int(d['output_rounding_scale'])
    paired_lo=F((paired*scale).__floor__(),scale)
    paired_hi=F((paired*scale).__ceil__(),scale)
    ck('exact_canonical_paired_row', paired_lo==F(r['paired_lower'])<=paired<=F(r['paired_upper'])==paired_hi and paired>=0)
    ck('exact_old_canonical_row', F(r['old_canonical_lower'])==F(f4['four_lower'])<=former<=F(f4['four_upper'])==F(r['old_canonical_upper']))
    ck('exact_old_three_row', F(f3['fee_lower'])<=fee3<=F(f3['fee_upper'])
       and F(f4['three_lower'])<=fee3<=F(f4['three_upper']))
    ck('runnerup_exact_inside_reported_interval', F(r['old_noncanonical_max_lower'])<=second<=F(r['old_noncanonical_max_upper']))
    ck('runnerup_address', r['maximizing_noncanonical_type']=={'head':[3,5,7,13],'outside_count':0})
    ck('paired_dominates_runnerup_and_oldthree', paired>F(r['old_noncanonical_max_upper'])>=second
       and paired>fee3 and paired<former)
    ck('canonical_lower_dominates_all_alternatives', paired_lo>F(r['old_noncanonical_max_upper']))
    ck('row_saving_interval', F(r['saving_lower'])<=former-paired<=F(r['saving_upper']))
    paired_fees.append(paired);old_four_fees.append(former);runner_fees.append(second);three_fees.append(fee3)
    rows.append(dict(owner=v,h=h,s=str(s),paired_exact=str(paired),runnerup_exact=str(second),
                     runnerup_gap=str(paired-second),old_three_exact=str(fee3)))
ck('all193canonical_branch_maxima', d['canonical_dominates_noncanonical_rows']==193
   and d['noncanonical_dominates_canonical_rows']==0)
paired_total=sum(paired_fees,F(0));old_total=sum(old_four_fees,F(0))
ck('all193totals', F(d['canonical_total']['lower'])<=paired_total<=F(d['canonical_total']['upper'])
   and F(d['old_four_total']['lower'])<=old_total<=F(d['old_four_total']['upper']))
rounded_upper_sum=sum((F(r['paired_upper']) for r in d['rows']),F(0))
ck('complete_allbranch_upper_sum', F(d['allbranch_upper_total']['lower'])==rounded_upper_sum==F(d['allbranch_upper_total']['upper']))
ck('complete_count_mean_uses_submeasure_mass', F(d['complete_count_mean'])==complete_mean-R0)
def digest(value):
    return sha256(json.dumps(value,separators=(',',':'),sort_keys=True).encode()).hexdigest()
ck('exact193canonical_row_digest', digest(list(map(str,paired_fees)))==d['exact_canonical_row_fees_sha256'])

# Audit the declared branch address census without rerunning the producer's
# directed arithmetic: the separate old655 exchange theorem bounds all385
# noncanonical branches by the exact runner-up evaluated above.
heads=(3,5,7,11,13,17,19,23,29,31)
expected_branches={(T,4-len(T)) for k in range(5) for T in combinations(heads,k)}
ck('386paddedbranch_addresses', len(expected_branches)==386)
actual_branches={(tuple(r['head']),r['outside_count']) for r in d['branch_census']}
ck('385noncanonicalbranch_addresses', len(d['branch_census'])==385
   and actual_branches==expected_branches-{((3,5,7,11),0)})
for i,v in enumerate(primes):
    ck('owner_eligible_branch_count', d['branch_counts'][i]==sum(o<=i for T,o in expected_branches))
for r in d['branch_census']:
    ck('branch_eligible_owner_count', r['eligible_rows']==193-r['outside_count'])

ck('no_reoptimization_or_Euler_change_claim', d['actual_rows_reoptimized'] is False
   and d['all326_Euler_factors_changed'] is False)
for key in ('complete_five_parent_tail','ordinary_typeI_fee','Euler_counts','M0_lower','M0_upper','Podd_lower','Podd_upper'):
    ck('same_inherited_tail_Euler_data', old3[key]==old5[key])
ck('same326Euler_scope', sum(old3['Euler_counts'].values())==326)
W5=F(old3['complete_five_parent_tail']);typeI=F(old3['ordinary_typeI_fee'])
ck('666retained_tail_and_typeI', W5==F(old4['unchanged_five_parent_tail'])
   and typeI==F(old4['unchanged_TypeI']))
gamma=F(193,100000);alpha=F(2673,110656)
ck('same_projection_and_weaker_gate', alpha==F(old3['projection_alpha'])==F(old4['projection_alpha'])
   and gamma==F(old4['head_gate']))
cutoff_grid=primes+[1253]
policies=[]
all_cutoffs_by_kind={}
for policy in d['policies']:
    source=next(x for x in old3['policies'] if x['kind']==policy['kind'])
    prior=next(x for x in old4['policies'] if x['kind']==policy['kind'])
    tail=F(source['fee'])
    ck('same_arbitrary_parent_tail_and_switch', tail==F(policy['unchanged_arbitrary_tail'])
       ==F(prior['arbitrary_tail']) and source['K']==prior['K']==policy['final_switch_power']
       and source['arbitrary_threshold']==2**source['K'])
    audit_rows=[]
    for P in cutoff_grid:
        low=sum((F(old3['finite_rows'][i]['fee_lower']) if v<P else F(d['rows'][i]['paired_lower'])
                 for i,v in enumerate(primes)),F(0))
        upper=sum((F(old3['finite_rows'][i]['fee_upper']) if v<P else F(d['rows'][i]['paired_upper'])
                   for i,v in enumerate(primes)),F(0))
        exact=sum((three_fees[i] if v<P else paired_fees[i] for i,v in enumerate(primes)),F(0))
        reserve_lo=alpha*(gamma-upper-W5-typeI-tail)
        reserve_hi=alpha*(gamma-low-W5-typeI-tail)
        old_low=sum((F(old4['rows'][i]['three_lower']) if v<P else F(old4['rows'][i]['four_lower'])
                     for i,v in enumerate(primes)),F(0))
        old_hi=sum((F(old4['rows'][i]['three_upper']) if v<P else F(old4['rows'][i]['four_upper'])
                    for i,v in enumerate(primes)),F(0))
        old_exact=sum((three_fees[i] if v<P else old_four_fees[i] for i,v in enumerate(primes)),F(0))
        old_reslo=alpha*(gamma-old_hi-W5-typeI-tail)
        old_reshi=alpha*(gamma-old_low-W5-typeI-tail)
        ck('exact_cutoff_enclosure', low<=exact<=upper and old_low<=old_exact<=old_hi)
        expected=dict(cutoff=P,three_parent_rows=sum(v<P for v in primes),four_parent_rows=sum(v>=P for v in primes),
                      finite_fee_lower=str(low),finite_fee_upper=str(upper),
                      projected_reserve_lower=str(reserve_lo),projected_reserve_upper=str(reserve_hi),
                      old_projected_reserve_lower=str(old_reslo),old_projected_reserve_upper=str(old_reshi))
        gain=alpha*(old_exact-exact)
        expected['projected_reserve_decimal']=float(reserve_lo)
        expected['reserve_improvement']=dict(lower=str(F((gain*scale).__floor__(),scale)),
                                             upper=str(F((gain*scale).__ceil__(),scale)),decimal=float(gain))
        audit_rows.append(expected)
        matches=[r for r in policy['decisive_cutoffs'] if r['cutoff']==P]
        for r in matches:
            ck('every_decisive_cutoff_exact', all(r[k]==value for k,value in expected.items()))
            ck('reserve_improvement_enclosure', F(r['reserve_improvement']['lower'])<=alpha*(old_exact-exact)
               <=F(r['reserve_improvement']['upper']))
    ck('complete194cutoff_count', policy['computed_cutoff_count']==len(audit_rows)==194)
    ck('all194cutoff_digest', digest(audit_rows)==policy['all_cutoffs_sha256'])
    ck('decisive_cutoff_addresses', len({r['cutoff'] for r in policy['decisive_cutoffs']})==len(policy['decisive_cutoffs'])
       and all(r['cutoff'] in cutoff_grid for r in policy['decisive_cutoffs']))
    first_positive=min(r['cutoff'] for r in audit_rows if F(r['projected_reserve_lower'])>0)
    first_density=min(r['cutoff'] for r in audit_rows if F(r['projected_reserve_lower'])>F(1,2000000))
    ck('new_policy_boundary_summary', policy['first_positive_cutoff']==first_positive
       and policy['first_density_2000000_cutoff']==first_density)
    ck('cutoffs_unchanged_from666', first_positive==prior['first_positive_cutoff']
       and first_density==prior['first_preserving_2000000_cutoff'])
    ck('boundary_predecessors_fail', F(audit_rows[cutoff_grid.index(first_positive)-1]['projected_reserve_upper'])<0
       and F(audit_rows[cutoff_grid.index(first_density)-1]['projected_reserve_upper'])<F(1,2000000))
    selected=[r for r in audit_rows if r['cutoff'] in (113,127,131,137,139,149,181,191)]
    policies.append(dict(kind=policy['kind'],K=source['K'],first_positive_cutoff=first_positive,
                         first_density_2000000_cutoff=first_density,selected_cutoffs=selected))
    all_cutoffs_by_kind[policy['kind']]=audit_rows

ck('candidate_unchanged_during_verification', a.candidate.read_bytes()==candidate_bytes)
def outward(value):
    return dict(lower=str(F((value*scale).__floor__(),scale)),
                upper=str(F((value*scale).__ceil__(),scale)),decimal=float(value))
min_gap_index=min(range(193),key=lambda i:paired_fees[i]-runner_fees[i])
result=dict(schema='paired-owner-fixed-rows-independent-v1',status='PASS',new_lean_verification=False,
            producer_source_read=False,arithmetic='exact fractions, complete mean, finite negative part',
            candidate_sha256=sha256(candidate_bytes).hexdigest(),
            program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
            input_sha256=d['input_sha256'],negative_part_endpoint=N,
            complete_tau_mass=str(R0),complete_product_mean=str(complete_mean),
            exact_canonical_row_fees_sha256=digest(list(map(str,paired_fees))),
            exact_runnerup_row_fees_sha256=digest(list(map(str,runner_fees))),
            exact_old_three_row_fees_sha256=digest(list(map(str,three_fees))),
            all194_cutoff_sha256={k:digest(v) for k,v in all_cutoffs_by_kind.items()},
            canonical_total=outward(paired_total),old_four_total=outward(old_total),
            absolute_all193_saving=outward(old_total-paired_total),
            smallest_runnerup_gap=dict(owner=primes[min_gap_index],
                **outward(paired_fees[min_gap_index]-runner_fees[min_gap_index])),
            row_count=193,policies=policies,checks=checks,check_count=sum(checks.values()),
            scope='All193 paired canonical and runner-up fees independently reconstructed exactly; old three/four intervals and every new policy cutoff checked. Coverage of all noncanonical branches uses the separately audited old655 exchange/runner-up theorem; individual385 branch interval widths were not independently recomputed. Existing analytic tail theorems and source construction are inherited, not re-proved here.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=result['check_count'],canonical_total=float(paired_total),
                      all193_saving=float(old_total-paired_total),
                      minimum_runnerup_gap=float(min(x-y for x,y in zip(paired_fees,runner_fees))),
                      policies=[{k:v for k,v in x.items() if k!='selected_cutoffs'} for x in policies])))
