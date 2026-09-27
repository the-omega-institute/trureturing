#!/usr/bin/env python3
"""Independent P3--P5 reconstruction with actual-domain lower bounds.

Only Python standard-library exact rationals. No oracle implementation or
numeric profile is imported. Every subset is rebuilt from conditioning;
all infinite sums use certified geometric-tail cells and a separate box
plus raw-support-tail bracket. These are parameter certificates, not Lean.

Usage: python3 -I five_core_cylinder_profiles.py [--output PATH]
The default output is the JSON file beside this script.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def subsets(mask):
    t=mask
    while True:
        yield t
        if t==0:
            break
        t=(t-1)&mask


def infinite_envelope(primes,mask,c):
    indices=tuple(i for i in range(len(primes)) if mask>>i&1)
    cutoffs={}
    checks=[]
    for i in indices:
        ratios=[(t,c[t|1<<i]/c[t]) for t in subsets(mask^(1<<i))]
        largest=max(ratio for t,ratio in ratios)
        L=0
        while primes[i]**(L+1)<largest:
            L+=1
        assert all(primes[i]**(L+1)*c[t]>=c[t|1<<i] for t,ratio in ratios)
        cutoffs[i]=L
        checks.append(dict(index=i,prime=primes[i],cutoff=L,largest_ratio=largest,
                           all_support_checks=[dict(support=t,ratio=ratio,
                                                    slack=primes[i]**(L+1)-ratio) for t,ratio in ratios]))
    cells=[]
    R_total=F();K_total=F()
    states=[tuple(range(cutoffs[i]+1))+(None,) for i in indices]
    for values in product(*states):
        tail=sum(1<<i for i,e in zip(indices,values) if e is None)
        positive=sum(1<<i for i,e in zip(indices,values) if e is not None and e>0)
        candidates={t:c[tail|t]/prod(primes[i]**e for i,e in zip(indices,values)
                                    if e is not None and t>>i&1) for t in subsets(positive)}
        selected=min(candidates,key=candidates.get)
        coefficient=candidates[selected]
        geometric=prod(F(1,primes[i]**cutoffs[i]*(primes[i]-1))
                       for i in indices if tail>>i&1)
        weighted_geometric=prod(F((2*cutoffs[i]+3)*(primes[i]-1)+2,
                                 primes[i]**cutoffs[i]*(primes[i]-1)**2)
                                for i in indices if tail>>i&1)
        bounded_weight=prod(2*e+1 for e in values if e is not None)
        rpart=coefficient*geometric
        kpart=coefficient*weighted_geometric*bounded_weight
        assert rpart>0 and kpart>0
        R_total+=rpart;K_total+=kpart
        cells.append(dict(exponents=values,tail_support=tail,bounded_positive_support=positive,
                          minimizing_bounded_support=selected,coefficient=coefficient,
                          geometric_tail_factor=geometric,R_including_zero_contribution=rpart,
                          weighted_geometric_tail_factor=weighted_geometric,K_contribution=kpart))
    return dict(R=R_total-1,K=K_total,cutoffs=tuple(cutoffs[i] for i in indices),
                cutoff_checks=checks,cell_count=len(cells),cells=cells)


def construct(primes,densities):
    n=len(primes)
    records={0:dict(profile={0:F(1)},R=F(),K=F(1),f=F(1))}
    for size in range(1,n+1):
        for indices in combinations(range(n),size):
            mask=sum(1<<i for i in indices)
            orders=[]
            for last in indices:
                oldmask=mask^(1<<last);old=records[oldmask]
                b=old['R']/((primes[last]-1)*densities[last])
                order=dict(last_index=last,last_prime=primes[last],old_mask=oldmask,
                           deletion_bound=b,conditioning_denominator=1-b,admissible=b<1)
                if b<1:
                    caps={t:old['profile'][t&oldmask]/(1-b)
                          /(densities[last] if t>>last&1 else 1) for t in subsets(mask) if t}
                    assert all(cap>0 for cap in caps.values())
                    order.update(prefix_caps=caps,f_candidate=old['f']*(1-b))
                orders.append(order)
            valid=[order for order in orders if order['admissible']]
            assert valid,('no valid last-coordinate order',primes,densities,mask)
            c={0:F(1)}
            chosen={}
            for t in subsets(mask):
                if t:
                    winner=min(valid,key=lambda order:order['prefix_caps'][t])
                    c[t]=winner['prefix_caps'][t]
                    chosen[t]=winner['last_index']
                    assert all(c[t]<=order['prefix_caps'][t] for order in valid)
            f=max(order['f_candidate'] for order in valid)
            assert 0<f<=1
            envelope=infinite_envelope(primes,mask,c)
            records[mask]=dict(mask=mask,primes=tuple(primes[i] for i in indices),
                               profile=c,profile_minimizing_last_indices=chosen,
                               f=f,orders=orders,**envelope)
    return records


def direct_box_bracket(primes,c,B=8):
    """Independent direct minimum, plus raw complete-support tail bound."""
    n=len(primes);lower=F()
    for exponents in product(range(B+1),repeat=n):
        support=sum(1<<i for i,e in enumerate(exponents) if e)
        if not support:
            continue
        value=min(c[t]/prod(primes[i]**e for i,e in enumerate(exponents) if t>>i&1)
                  for t in subsets(support))
        lower+=value
    tail=F();parts=[]
    for support in range(1,1<<n):
        indices=tuple(i for i in range(n) if support>>i&1)
        infinite=prod(F(1,primes[i]-1) for i in indices)
        bounded=prod((1-F(1,primes[i]**B))/(primes[i]-1) for i in indices)
        contribution=c[support]*(infinite-bounded)
        assert contribution>0
        tail+=contribution
        parts.append(dict(support=support,raw_coefficient=c[support],
                          infinite_geometric_product=infinite,bounded_geometric_product=bounded,
                          outside_box_upper=contribution))
    return dict(box_maximum_exponent=B,box_nonzero_vector_count=(B+1)**n-1,
                exact_box_lower=lower,raw_support_tail_upper=tail,
                rigorous_upper=lower+tail,tail_support_parts=parts)


def tree_density(p):
    return 1-F(1,p-1)-F(1,p**3*(p-1)**2)


def cactus_density(p,rho):
    return 1-F(1,p-1)-6*rho/F(p*(p-1))


def scalar_cases():
    missing=[]
    specs=(((3,5,11,13,17),(7,),F(39,40)),
           ((3,7,11,13,17),(5,),F(24,25)),
           ((3,11,13,17,19),(5,7),F(3,4)))
    for primes,absent,ceiling in specs:
        densities=[]
        for p in primes:
            pool=(F(1,p) if 5 in absent else F())+(F(1,p*p) if 7 in absent else F())+F(1,p**3*(p-1))
            density=1-F(1,p-1)-pool/(p-1)
            assert density>0
            densities.append(density)
        weights=tuple(1/((p-1)*d) for p,d in zip(primes,densities))
        degree_sums=tuple(sum((prod(t) for t in combinations(weights,k)),F()) for k in range(2,6))
        cost=sum(degree_sums,F())
        assert cost==prod(1+x for x in weights)-1-sum(weights,F())
        assert cost<ceiling and 1-cost>F(1,2048)
        missing.append(dict(primes=primes,absent_small_primes=absent,
                            density_lower_bounds=densities,weights=weights,
                            support_degree_2_through_5_costs=degree_sums,
                            exact_cost=cost,claimed_ceiling=ceiling,slack=ceiling-cost))
    def z(p):
        return F(p-1,(p-1)**2-(p-1)-1)
    finite_primes=(5,7,11,13,17,19,23)
    finite_square_sum=sum((z(p)**2 for p in finite_primes),F())
    odd_tail_bound=F(1,26**2)+F(1,52)
    square_sum_upper=finite_square_sum+odd_tail_bound
    assert square_sum_upper<F(57,250)
    edge5=z(5)/(F(1,2)+F(1,3))
    edge7=z(7)/(F(1,2)+F(1,9))
    edge_at_least11=2*z(11)
    assert edge5==F(24,55)>edge7==F(108,319)
    assert edge5>edge_at_least11==F(20,89)
    highweights=tuple(z(p) for p in (5,7,11,13,17))
    highdegrees=tuple(sum((prod(t) for t in combinations(highweights,k)),F()) for k in range(3,6))
    total=edge5+2*F(57,250)+z(5)**2/2+sum(highdegrees,F())
    assert total<F(249,250) and 1-total>F(1,2048)
    offcore=dict(finite_square_primes=finite_primes,
                 finite_square_sum=finite_square_sum,odd_tail_square_bound=odd_tail_bound,
                 square_sum_upper=square_sum_upper,claimed_square_ceiling=F(57,250),
                 first_edge_bounds=dict(q5=edge5,q7=edge7,q_at_least11=edge_at_least11),
                 pair_degree_bound=2*F(57,250)+z(5)**2/2,
                 core_support_degree_3_through_5_costs=highdegrees,
                 complete_mixed_cost_upper=total,claimed_ceiling=F(249,250),
                 cost_ceiling_slack=F(249,250)-total)
    pools=dict(odd_from11=F(1,16),nonprime15_fee=F(1,128),
               prime_pool_upper=F(1,16)-F(1,128),core11_fee=F(1,32),
               first_pool_odd_from17=F(1,128),
               second_pool=F(1,16)-F(1,128)-F(1,32),third_pool=F(7,128))
    assert pools['second_pool']==F(3,128) and pools['prime_pool_upper']==F(7,128)
    return dict(missing_small_prime_cases=missing,three_off_core=offcore,cactus_fee_pools=pools)


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):
        return [encode(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    baseprimes=(3,5,7,11)
    baseline=construct(baseprimes,tuple(F(p-2,p-1) for p in baseprimes))
    assert baseline[15]['R']==F(1514,145) and baseline[15]['K']==F(3885,29)
    assert baseline[15]['f']==F(58,405)
    assert baseline[15]['profile']=={0:F(1),1:F(378,29),2:F(216,29),4:F(117,29),8:F(75,29),
                                   3:F(540,29),5:F(468,29),9:F(420,29),6:F(288,29),
                                   10:F(240,29),12:F(180,29),7:F(648,29),11:F(600,29),
                                   13:F(540,29),14:F(360,29),15:F(720,29)}
    specs=(('tree_3571113',(3,5,7,11,13),None,F(273,25),F(67,500)),
           ('cactus_3571113',(3,5,7,11,13),F(1,128),F(10931,1000),F(67,500)),
           ('cactus_3571117',(3,5,7,11,17),F(3,128),F(12221,1000),F(23,200)),
           ('cactus_3571317',(3,5,7,13,17),F(7,128),F(12715,1000),F(109,1000)))
    results=[]
    for name,primes,rho,Rcap,f_floor in specs:
        d=tuple(tree_density(p) if rho is None else cactus_density(p,rho) for p in primes)
        assert all(0<x<1 for x in d)
        records=construct(primes[:4],d[:4]);top=records[15]
        assert top['R']<Rcap and top['f']>f_floor
        assert top['cutoffs']==(2,1,0,0) and top['cell_count']==48
        bracket=direct_box_bracket(primes[:4],top['profile'])
        assert bracket['exact_box_lower']<=top['R']<=bracket['rigorous_upper']<Rcap
        actual_fifth_gap=1-top['R']/((primes[4]-1)*d[4])
        rounded_fifth_gap=1-Rcap/((primes[4]-1)*d[4])
        assert actual_fifth_gap>rounded_fifth_gap>0
        exact_f5=top['f']*actual_fifth_gap
        displayed_f5=f_floor*rounded_fifth_gap
        assert exact_f5>displayed_f5>F(1,2048)
        summary=dict(name=name,primes=primes,rho=rho,density_lower_bounds=d,
                     exact_R4=top['R'],claimed_R4_upper=Rcap,R4_upper_slack=Rcap-top['R'],
                     exact_f4_bound=top['f'],claimed_f4_lower=f_floor,f4_lower_slack=top['f']-f_floor,
                     cutoff_tuple=top['cutoffs'],cell_count=top['cell_count'],
                     admissible_subset_order_count=sum(sum(o['admissible'] for o in rec.get('orders',[])) for rec in records.values()),
                     rejected_subset_orders=[dict(mask=mask,last=o['last_prime'],gap=o['conditioning_denominator'])
                                             for mask,rec in records.items() for o in rec.get('orders',[]) if not o['admissible']],
                     fifth_conditioning_gap=actual_fifth_gap,
                     exact_f5_bound=exact_f5,claimed_rounding_f5_bound=displayed_f5,
                     final_margin_above_1_over_2048=displayed_f5-F(1,2048))
        results.append(dict(summary=summary,all_subset_profiles=records,
                            independent_box_plus_geometric_tail=bracket))
    scalars=scalar_cases()
    data=dict(scope='Exact domain-robust P3-P5 parameter reconstruction. Geometry-to-domain hypotheses and all-height validity rely on the stated ordinary proofs, not numerical enumeration.',
              source='docs/reports/erdos7-odd-covering/problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md#a-four-prime-head-and-a-restricted-noncoverage-theorem',
              baseline_reproduced=dict(R=baseline[15]['R'],K=baseline[15]['K'],f=baseline[15]['f'],profile=baseline[15]['profile']),
              cases=results,scalar_cases=scalars)
    args.output.write_text(json.dumps(encode(data),separators=(',',':'))+'\n',encoding='utf-8')
    print(json.dumps(encode(dict(profile_cases=[result['summary'] for result in results],
                                scalar_cases=scalars)),indent=2))


if __name__=='__main__':
    main()
