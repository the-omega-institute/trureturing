#!/usr/bin/env python3
"""Exact same-law shallow-prefix bounds for the ideal K5 child core.

All-height P3--P5 profiles are reconstructed with exact geometric tails.
The parent-prefix aggregate test here concerns a specified relaxed comb
construction. Passing that test is NOT a K5 parent-fee theorem. No original
AP cover/counterexample is asserted. Requires Python 3.9+ and only the standard library.

Usage: python3 -I k5_parent_same_law_envelope.py [--output PATH]
"""
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

PRIMES=(5,7,11,13)


def subsets(mask):
    t=mask
    while True:
        yield t
        if not t:
            return
        t=(t-1)&mask


def envelope(mask,c):
    ids=tuple(i for i in range(4) if mask>>i&1)
    cutoffs=[];checks=[]
    for i in ids:
        ratios=tuple((t,c[t|1<<i]/c[t]) for t in subsets(mask^(1<<i)))
        L=0
        while PRIMES[i]**(L+1)<max(r for t,r in ratios):
            L+=1
        assert all(PRIMES[i]**(L+1)>=r for t,r in ratios)
        cutoffs.append(L)
        checks.append(dict(index=i,cutoff=L,ratios=ratios))
    total=F();cells=[]
    for exps in product(*(tuple(range(L+1))+(None,) for L in cutoffs)):
        tail=sum(1<<i for i,e in zip(ids,exps) if e is None)
        bounded=sum(1<<i for i,e in zip(ids,exps) if e is not None and e>0)
        coefficient=min(c[tail|t]/prod(PRIMES[i]**e for i,e in zip(ids,exps)
                                      if e is not None and t>>i&1) for t in subsets(bounded))
        geometric=prod(F(1,PRIMES[i]**L*(PRIMES[i]-1))
                       for i,L,e in zip(ids,cutoffs,exps) if e is None)
        value=coefficient*geometric;total+=value
        cells.append(dict(exponents=exps,coefficient=coefficient,
                          infinite_geometric_factor=geometric,value=value))
    return dict(R=total-1,cutoffs=cutoffs,tail_checks=checks,cells=cells)


def profiles(densities,multiplicity):
    records={0:dict(c={0:F(1)},R=F(),f=F(1))}
    for size in range(1,5):
        for ids in combinations(range(4),size):
            mask=sum(1<<i for i in ids);orders=[]
            for i in ids:
                old=records[mask^(1<<i)]
                gap=1-multiplicity*old['R']/((PRIMES[i]-1)*densities[i])
                row=dict(last=i,gap=gap,admissible=gap>0)
                if gap>0:
                    row['c']={t:old['c'][t&~(1<<i)]/gap/(densities[i] if t>>i&1 else 1)
                              for t in subsets(mask) if t}
                    row['f']=old['f']*gap
                orders.append(row)
            valid=[o for o in orders if o['admissible']]
            assert valid
            c={0:F(1)}|{t:min(o['c'][t] for o in valid) for t in subsets(mask) if t}
            records[mask]=dict(c=c,f=max(o['f'] for o in valid),orders=orders,**envelope(mask,c))
    return records


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
    original_d=tuple(F(p-2,p-1) for p in PRIMES)
    twice_d=tuple(F(p-3,p-1) for p in PRIMES)
    old=profiles(original_d,F(1));twice=profiles(twice_d,F(2))
    assert old[15]['R']==F(1301,1185) and old[15]['f']==F(79,99)
    assert old[15]['cutoffs']==[0,0,0,0]
    assert twice[15]['R']==F(3359,1050) and twice[15]['f']==F(21,64)
    density_ratio=prod(F(p-3,p-2) for p in PRIMES)
    C=density_ratio*twice[15]['f']
    assert density_ratio==F(128,297) and C==F(14,99)
    b=tuple(F(1,p-2) for p in PRIMES)
    mixed=sum((prod(t) for k in range(2,5) for t in combinations(b,k)),F())
    U=1-prod(1-x for x in b)+mixed
    assert U==sum(b,F())+2*sum((prod(t) for t in combinations(b,3)),F())==F(1148,1485)
    assert 1-C==F(85,99) and U/(U+C)==F(82,97)
    s0=old[15]['f'];c=old[15]['c'];raw={};weights={};terms=[]
    breakpoints={s0,F(1),U+C}
    for mask in range(1,16):
        raw[mask]=prod(1/original_d[i] for i in range(4) if mask>>i&1)
        weights[mask]=prod(F(1,PRIMES[i]-1) for i in range(4) if mask>>i&1)
        switch=raw[mask]/c[mask]
        if s0<=switch<=1:
            breakpoints.add(switch)
        terms.append(dict(support_mask=mask,profile_cap=c[mask],
                          raw_product_cap=raw[mask],geometric_weight=weights[mask],switch_s=switch))
    def R(s):
        return sum((weights[t]*min(c[t],raw[t]/s) for t in range(1,16)),F())
    def beta(s):
        return min(U/s,1-C/s)
    def gap(s):
        return 3-2*R(s)-beta(s)
    points=sorted(breakpoints);point_rows=[];pieces=[];zeros=[];refined_tail_checks=[]
    for s in points:
        assert R(s)<=old[15]['R']
        assert 0<beta(s)<=F(82,97)
        refined={0:F(1)}|{t:min(c[t],raw[t]/s) for t in range(1,16)}
        ratios=tuple(max(refined[t|1<<i]/refined[t] for t in subsets(15^(1<<i)))
                     for i in range(4))
        assert all(ratio<=p for ratio,p in zip(ratios,PRIMES))
        direct=envelope(15,refined)
        assert direct['cutoffs']==[0,0,0,0] and direct['R']==R(s)
        refined_tail_checks.append(dict(s=s,maximum_extension_cap_ratios=ratios,
                                        zero_cutoff_envelope_equals_support_sum=True))
        point_rows.append(dict(s=s,R=R(s),beta=beta(s),relaxed_comb_gap=gap(s)))
    for lo,hi in zip(points,points[1:]):
        mid=(lo+hi)/2
        fixed=[t for t in range(1,16) if c[t]<=raw[t]/mid]
        reciprocal=[t for t in range(1,16) if t not in fixed]
        A=sum((weights[t]*c[t] for t in fixed),F())
        B=sum((weights[t]*raw[t] for t in reciprocal),F())
        alpha,gamma=(F(1),-C) if mid<U+C else (F(),U)
        gap_constant=3-2*A-alpha;gap_reciprocal=-2*B-gamma
        assert all(R(s)==A+B/s and beta(s)==alpha+gamma/s and
                   gap(s)==gap_constant+gap_reciprocal/s for s in (lo,mid,hi))
        zero=-gap_reciprocal/gap_constant if gap_constant else None
        if zero is not None and lo<=zero<=hi:
            assert gap(zero)==0
            zeros.append(zero)
        pieces.append(dict(interval_closed=(lo,hi),R_constant=A,R_reciprocal=B,
                           beta_constant=alpha,beta_reciprocal=gamma,
                           gap_constant=gap_constant,gap_reciprocal=gap_reciprocal,
                           gap_derivative_sign=-1 if gap_reciprocal>0 else 1 if gap_reciprocal<0 else 0,
                           fixed_profile_supports=fixed,raw_over_s_supports=reciprocal))
    assert zeros==[F(8927,10494)]
    worst=min(point_rows,key=lambda row:row['relaxed_comb_gap'])
    assert worst==dict(s=F(79,98),R=F(326,297),beta=F(6449,7821),relaxed_comb_gap=-F(466,23463))
    assert gap(s0)==-F(22,1185) and beta(s0)==F(65,79)
    assert all((row['s']<zeros[0])==(row['relaxed_comb_gap']<0) for row in point_rows)
    witness=dict(s=s0,R=R(s0),beta=beta(s0),
                 nested_event_measure=R(s0)-beta(s0),
                 deep_level_cost=3-beta(s0)-R(s0),
                 deep_level_budget_slack=2*R(s0)+beta(s0)-3)
    assert witness['nested_event_measure']==F(326,1185)
    assert witness['deep_level_budget_slack']==F(22,1185)>0
    summary=dict(old_R=old[15]['R'],old_survival_lower=s0,
                 twice_multiplicity_R=twice[15]['R'],twice_multiplicity_survival_lower=twice[15]['f'],
                 same_old_domain_new_survival_lower=C,raw_new_union_upper=U,
                 uniform_same_law_single_level_cap=U/(U+C),
                 strongest_coupled_cap_at_old_s_lower=beta(s0),
                 worst_relaxed_comb_gap=worst,unique_comb_gap_zero=zeros[0],
                 same_law_comb_witness_parameters=witness)
    data=dict(scope='Ideal pure-domain child core5,7,11,13. Certified all-height envelope improvements, plus a remaining scalar/comb obstruction. No recursive K5 fee or actual AP counterexample.',
              original_label_scope='At a fixed original parent exponent k and prefix, each projected child modulus appears at most once from labels3^k*d; original child constraints plus projected constraints have multiplicity at most2. This is a conditional event representation, not replacement of original labels.',
              original_profiles=old,twice_multiplicity_profiles=twice,
              same_law_relations=dict(s='old complete-survivor mass in the actual old pure-domain product law',
                                      C='new complete-survivor mass in that same product law is at least14/99',
                                      U='new fixed-parent-level union has mass at most1148/1485 in that same product law',
                                      beta='min(U/s,1-C/s)',R='sum_T geometric_weight_T*min(profile_cap_T,raw_product_cap_T/s)'),
              summary=summary,exact_support_terms=terms,breakpoint_values=point_rows,piecewise_formulas=pieces,
              refined_zero_cutoff_checks=refined_tail_checks,
              between_breakpoints='Each refined cap is constant or a constant/s. Their ratios are constant or monotone in s, so endpoint checks certify the same zero cutoffs throughout each interval.',
              remaining_obligation='The comb events must additionally come from the same original AP child cylinders with one original3^k*d label per(k,d), common residues and all overlaps retained. The relaxed witness does not certify that arithmetic realizability.',
              zero_scope='A positive3-2R-beta excludes the stated full-mass comb-capacity construction only; it is not alone a universal parent-dead-fibre estimate.')
    args.output.write_text(json.dumps(encode(data),separators=(',',':'))+'\n',encoding='utf-8')
    print(json.dumps(encode(summary),indent=2))


if __name__=='__main__':
    main()
