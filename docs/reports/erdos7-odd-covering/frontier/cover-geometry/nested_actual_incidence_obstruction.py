#!/usr/bin/env python3
"""Actual high-power query incidences force unbounded fixed-law linear fees.

Recounts the full base survivor directly from the forty literal originals,
then verifies a twelve-label arithmetic extension and exact uniform-K bounds.
No extended trillion-point period is enumerated and no optimizer is used.
"""
import argparse
from array import array
from fractions import Fraction as F
from hashlib import sha256
import json
from math import gcd, lcm, prod
from pathlib import Path


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('linear_schedule_credit_obstruction_input.json'))
    parser.add_argument('--tie-input', type=Path, default=Path(__file__).with_name('nested_actual_incidence_tie_choices.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    raw = args.input.read_bytes()
    source = json.loads(raw)
    tie_raw = args.tie_input.read_bytes()
    tie_source = json.loads(tie_raw)
    fixed_choices = {r['modulus']:r['phase'] for r in tie_source['choices']}
    base = source['originals']
    primes = source['primes']
    checks = {}

    def require(name, value):
        if not value:
            raise ArithmeticError(name)
        checks[name] = True

    require('base_primes', primes == [3,5,7,11,13,17,19])
    require('forty_base_labels', len(base) == 40
            and len({r['modulus'] for r in base}) == 40)
    require('fixed_tie_inventory',len(tie_source['choices'])==40
            and set(fixed_choices)=={r['modulus'] for r in base})
    period = lcm(*(r['modulus'] for r in base))
    require('base_period', period == prod(primes) == 4849845)
    marked = bytearray(period)
    for row in base:
        d,a=row['modulus'],row['residue']
        require(f'base_original_{d}', d>1 and d%2==1 and period%d==0 and 0<=a<d)
        marked[a::d]=b'\1'*len(range(a,period,d))
    survivors = array('I',(x for x,hit in enumerate(marked) if not hit))
    count = len(survivors)
    h0=F(count,period)
    require('complete_base_survivor', count==741126 and h0==F(247042,1616615))
    require('least_two_survivors',list(survivors[:2])==[29,32])
    require('all_smaller_phases_killed',all(marked[a] for a in range(29)))

    A=prod(F(p,p-1) for p in primes)-1
    alpha=F(7235955529,6075000000000)
    target=F(566,49)
    charged=F(); reciprocal=F(); query_rows=[]; old_phase_rows=[]
    for row in base:
        d=row['modulus']
        bins=[0]*d
        for x in survivors:
            bins[x%d]+=1
        maximum=max(bins)
        # Removing less than half a base-cell unit only breaks ties at 32 mod d.
        unpenalized_maxima=[a for a,n in enumerate(bins) if n==maximum and a!=32%d]
        uniform_phase=min(unpenalized_maxima) if unpenalized_maxima else 32%d
        scores=[2*n-int(a==32%d) for a,n in enumerate(bins)]
        require(f'uniform_old_maximizing_phase_{d}',uniform_phase==scores.index(max(scores)))
        require(f'fixed_tie_maximizes_for_every_K_{d}',0<=fixed_choices[d]<d
                and scores[fixed_choices[d]]==max(scores))
        old_phase_rows.append(dict(label=d,least_maximizing_phase_for_every_K=uniform_phase,
                                   base_survivor_count=bins[uniform_phase],
                                   loses_added_mass=uniform_phase==32%d))
        factor=prod(F(p,p-1) for p in primes if d%p==0)
        require(f'base_cylinder_partition_{d}',sum(bins)==count and maximum<=period//d)
        charged+=factor*F(maximum,count)
        reciprocal+=factor/d
        query_rows.append(dict(label=d,least_maximizing_phase=bins.index(maximum),
                               maximum_survivor_count=maximum,height_coefficient=factor))
    all_height_base=charged+(A-reciprocal)/h0
    require('complete_base_all_height_query_bound',
            all_height_base==F(1506044247059,409813032960)<4)

    old_incidence=bytearray(period)
    for row in old_phase_rows:
        for x in range(row['least_maximizing_phase_for_every_K'],period,row['label']):
            old_incidence[x]+=1
    old_max=max(old_incidence[x] for x in survivors)
    old_max_witness=next(x for x in survivors if old_incidence[x]==old_max)
    old_at_29=old_incidence[29]
    require('old_incidence_maximum_attained',0<=old_at_29<=old_max<=40
            and not marked[old_max_witness])
    require('exact_base_incidence_constants',old_max==14 and old_at_29==1
            and old_max_witness==1190264 and old_max_witness not in (29,32))

    fixed_load=bytearray(period)
    for d,a in fixed_choices.items():
        for x in range(a,period,d):fixed_load[x]+=1
    fixed_hist=[0]*41
    for x in survivors:fixed_hist[fixed_load[x]]+=1
    fixed_max=max(i for i,n in enumerate(fixed_hist) if n)
    fixed_witness=next(x for x in survivors if fixed_load[x]==fixed_max)
    fixed_at29=fixed_load[29]
    require('fixed_tie_uniform_incidence_nine',fixed_max==9 and fixed_at29==2
            and fixed_witness not in (29,32)
            and fixed_hist[:10]==[62326,150925,212886,178681,87051,34577,11441,2831,390,18])
    require('fixed_tie_disjoint_chain_still_nine',max(fixed_max,fixed_at29+1)==9)

    kstar=12
    added=[]
    for k in range(1,kstar+1):
        d=period*3**k
        a=32+period*3**(k-1)
        require(f'extension_label_{k}',d>period and d%2==1 and 0<=a<d
                and a%period==32 and not marked[a%period])
        added.append(dict(level=k,modulus=d,residue=a,private_witness=a,
                          least_maximizing_query_phase=29))
    rows=base+added
    require('fifty_two_distinct_numerical_labels',len({r['modulus'] for r in rows})==52)
    for row in rows:
        d,a,z=row['modulus'],row['residue'],row['private_witness']
        require(f'private_witness_own_{d}',z%d==a)
        for other in rows:
            if other['modulus']!=d:
                require(f'private_witness_{d}_against_{other["modulus"]}',
                        z%other['modulus']!=other['residue'])
    for i,row in enumerate(added):
        for other in added[i+1:]:
            require(f'disjoint_added_{row["level"]}_{other["level"]}',
                    (row['residue']-other['residue'])%gcd(row['modulus'],other['modulus'])!=0)
        require(f'whole_29_cylinder_survives_level_{row["level"]}',
                all((29-r['residue'])%gcd(row['modulus'],r['modulus'])!=0 for r in rows))

    limit_mass=h0-F(1,2*period)
    new_period=period*3**kstar
    new_count=count*3**kstar-(3**kstar-1)//2
    hk=F(new_count,new_period)
    require('complete_extension_mass',
            hk==h0-F(3**kstar-1,2*period*3**kstar))
    require('twelve_extension_period_and_count',new_period==2577406476645
            and new_count==393864476846)
    require('uniform_survivor_mass_interval',F(3,20)<limit_mass<hk<h0<A/target)
    require('uniform_density_constant_comparison',0<alpha<F(1,800)
            and alpha/limit_mass<F(1,120))
    uniform_query=h0/limit_mass*all_height_base
    finite_query=h0/hk*all_height_base
    require('uniform_K_full_query_below_four',finite_query<uniform_query<4)
    linear_factor=F(119,120)
    require('twelve_actual_incidence_certificate_fails',
            kstar*linear_factor==F(119,10)>target
            and F(119,10)-target==F(171,490))
    occupied_chain=sum((F(1,r['modulus']*hk) for r in added),F())
    require('complete_new_occupied_query_mass',
            occupied_chain==F(1,2*period*hk)*(1-F(1,3**kstar))
            ==F(132860,196932238423)<F(1,1000000))
    alternative_queries=[]
    for row in added:
        k,d=row['level'],row['modulus']
        phase=29+period*3**(k-1)
        require(f'alternative_maximizing_phase_{k}',0<=phase<d and phase%period==29
                and all((phase-r['residue'])%gcd(d,r['modulus'])!=0 for r in rows))
        alternative_queries.append(dict(label=d,phase=phase,query_probability=F(1,d*hk)))
    for i,row in enumerate(alternative_queries):
        for other in alternative_queries[i+1:]:
            require(f'disjoint_query_{i+1}_{other["label"]}',
                    (row['phase']-other['phase'])%gcd(row['label'],other['label'])!=0)
    disjoint_max=max(old_max,old_at_29+1)
    nested_max=max(old_max,old_at_29+kstar)
    require('alternative_new_block_one_schedule',len(alternative_queries)==kstar
            and disjoint_max<=old_max+1<=41)
    require('same_marginal_new_query_sum',sum((r['query_probability'] for r in alternative_queries),F())==occupied_chain)
    common_pattern=F(1,new_period*hk)
    require('positive_complete_actual_chain_incidence',common_pattern==F(1,new_count)>0)
    # exp(1)<49/18<11/4; (e-1)/(3-e)<7, so log E exp N <7/(L0*h_K).
    exponential_majorant=F(5,2)+F(1,6)/(1-F(1,4))
    require('full_exponential_series_upper',exponential_majorant==F(49,18)<F(11,4)<3)
    require('geometric_chain_exponential_constant',(F(11,4)-1)/(3-F(11,4))==7)
    uniform_log_moment=F(7,period*limit_mass)
    require('uniform_chain_log_moment_small',uniform_log_moment==F(14,1482251)<F(1,100000))

    result=dict(schema='nested-actual-incidence-obstruction-v1',
                input=dict(file=args.input.name,sha256=sha256(raw).hexdigest()),
                fixed_tie_input=dict(file=args.tie_input.name,sha256=sha256(tie_raw).hexdigest()),
                scope=dict(family='For every finite K>=1, forty base originals plus distinct d_k=L0*3^k, phase 32+L0*3^(k-1)',
                           source='c=0, selected law is normalized Haar on the entire actual survivor U_K, with Haar higher tails',
                           phases='Least numerical maximizing phase for every occupied query; the new labels all have phase29',
                           certificate='Nonnegative credits only constrained at actual query incidences, with fractional coverage of every occupied label',
                           result='Certificate exceeds119K/120 while the same selected law has complete all-height query norm below4',
                           not_excluded='Optimizing c, other maximizing-phase ties, nonlinear incidence-frequency payments, unrestricted Erdos7',
                           lean_verified=False),
                base=dict(originals=base,period=period,survivor_count=count,survivor_mass=h0,
                          least_survivors=list(survivors[:2]),query_rows=query_rows,
                          exact_charged_query_sum=charged,remaining_Euler_reciprocal_tail=A-reciprocal,
                          full_all_height_query_upper=all_height_base),
                extension=dict(K=kstar,added_originals=added,period=new_period,survivor_count=new_count,
                               survivor_mass=hk,full_all_height_query_upper=finite_query,
                               new_occupied_query_sum=occupied_chain,common_actual_incidence_mass=common_pattern,
                               certificate_strict_lower=kstar*linear_factor),
                incidence_pair=dict(old_occupied_phase_choices=old_phase_rows,
                                    old_incidence_maximum=old_max,old_max_witness=old_max_witness,old_incidence_at_29=old_at_29,
                                    disjoint_maximizing_queries=alternative_queries,
                                    full_disjoint_incidence_maximum_for_every_K=disjoint_max,
                                    full_nested_incidence_maximum_at_K=nested_max,
                                    full_nested_incidence_maximum_formula='max(14,K+1)',
                                    full_disjoint_optimal_inside_schedule_weight=14,
                                    new_disjoint_block_fractional_schedule_weight=1),
                fixed_tie_result=dict(choices=tie_source['choices'],old_incidence_histogram=fixed_hist[:fixed_max+1],
                                      old_max_incidence=fixed_max,old_max_witness=fixed_witness,old_incidence_at_29=fixed_at29,
                                      full_disjoint_incidence_max_for_every_K=9,
                                      optimal_inside_schedule_weight_for_this_choice=9,
                                      global_phase_optimality_claimed=False,full_certificate_success_claimed=False),
                uniform=dict(survivor_mass_strict_lower=limit_mass,
                             full_all_height_query_upper=uniform_query,
                             alpha_over_h_strict_upper=F(1,120),linear_fee_per_new_label=linear_factor,
                             chain_log_exponential_moment_strict_upper=uniform_log_moment),
                constants=dict(alpha7=alpha,target=target,nonunit_Euler_reciprocal_mass=A),
                checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),base_count=count,K=kstar,
                                new_period=new_period,new_count=new_count,
                                uniform_query_upper=uniform_query,
                                certificate_strict_lower=kstar*linear_factor,
                                chain_log_moment_upper=uniform_log_moment,
                                old_incidence_max=old_max,old_at_29=old_at_29,
                                disjoint_full_max=disjoint_max,nested_full_max=nested_max,
                                fixed_tie_disjoint_full_max=fixed_max))))


if __name__=='__main__':
    main()
