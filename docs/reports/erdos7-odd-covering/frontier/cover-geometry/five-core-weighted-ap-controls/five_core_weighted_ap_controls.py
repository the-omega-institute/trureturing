#!/usr/bin/env python3
"""Two explicit five-core AP examples, weighted elimination and full sieve.

Standard library only. These finite regression controls do not establish
the general all-height theorem. Every original label and coordinate height
is retained; conditional product mass is distinguished from Haar mass.

Usage: python3 -I five_core_weighted_ap_controls.py [--output PATH]
The default output is the JSON file beside this script.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

CORE=(3,5,7,11,13)


def factor(n):
    result={};p=2
    while p*p<=n:
        while n%p==0:
            result[p]=result.get(p,0)+1;n//=p
        p+=1
    if n>1:
        result[n]=1
    return result


def exact_sieve(period,family):
    good=bytearray(b'\x01')*period
    for d,a in family.items():
        assert period%d==0 and d>1 and d%2 and 0<=a<d
        good[a::d]=bytes((period-1-a)//d+1)
    return good


def control(name,core_family,attachment,root,off_primes,expected_period):
    assert set(core_family).isdisjoint(attachment)
    family=core_family|attachment
    factors={d:factor(d) for d in family}
    primes=tuple(sorted(set().union(*(s.keys() for s in factors.values()))))
    assert set(primes)==set(CORE)|set(off_primes)
    heights={p:max(s.get(p,0) for s in factors.values()) for p in primes}
    sizes={p:p**heights[p] for p in primes}
    period=prod(sizes.values());core_period=prod(sizes[p] for p in CORE)
    off_period=prod(sizes[p] for p in off_primes)
    assert period==expected_period==core_period*off_period
    assert all(set(factors[d])<=set(CORE) for d in core_family)
    assert all(set(factors[d])<=set(off_primes)|{root} and set(factors[d])&set(off_primes)
               for d in attachment)
    pure={p:{d:a for d,a in core_family.items() if set(factors[d])=={p}} for p in CORE}
    conditions=[tuple((p,p**h,a%(p**h)) for p,h in factors[d].items())
                for d,a in attachment.items()]
    root_counts=[]
    # The original root word is fixed; every outside word is counted exactly.
    for x in range(sizes[root]):
        count=0
        for values in product(*(range(sizes[p]) for p in off_primes)):
            word={root:x}|dict(zip(off_primes,values))
            if all(not all(word[p]%power==a for p,power,a in condition) for condition in conditions):
                count+=1
        root_counts.append(count)
    local_period=sizes[root]*off_period
    local=exact_sieve(local_period,attachment)
    local_counts=[0]*sizes[root]
    for n,good in enumerate(local):
        if good:
            local_counts[n%sizes[root]]+=1
    assert local_counts==root_counts
    active_attachment_higher_labels=[]
    for d,a in attachment.items():
        if len(factors[d])>=3:
            before_label=exact_sieve(local_period,{e:b for e,b in attachment.items() if e!=d})
            private=next(n for n,good in enumerate(before_label)
                         if good and n%d==a and all(n%e!=b for e,b in pure[root].items()))
            assert not local[private]
            active_attachment_higher_labels.append(dict(modulus=d,residue=a,
                                                        actual_private_attachment_word=private))
    weights={};domains={};densities={}
    for p in CORE:
        row=[]
        for x in range(sizes[p]):
            pure_good=all(x%d!=a for d,a in pure[p].items())
            row.append(F(root_counts[x],off_period) if p==root and pure_good else F(1) if pure_good else F())
        weights[p]=tuple(row)
        domains[p]=tuple(x for x,w in enumerate(row) if w>0)
        densities[p]=F(len(domains[p]),sizes[p])
        assert domains[p]
    domain_tuple_count=prod(len(domains[p]) for p in CORE)
    density_product=prod(densities.values())
    assert density_product==F(domain_tuple_count,core_period)
    core_avoid=exact_sieve(core_period,core_family)
    admissible=[];core_extensions=[0]*core_period
    root_fibre_counts=[0]*sizes[root]
    weighted_sum=F()
    for n,allowed in enumerate(core_avoid):
        if allowed and all(n%sizes[p] in domains[p] for p in CORE):
            admissible.append(n)
            root_fibre_counts[n%sizes[root]]+=1
            weight=prod(weights[p][n%sizes[p]] for p in CORE)
            assert weight>0
            weighted_sum+=weight
            exact_extensions=weight*off_period
            assert exact_extensions.denominator==1
            core_extensions[n]=int(exact_extensions)
    conditional_product_reserve=F(len(admissible),domain_tuple_count)
    assert conditional_product_reserve>F(1,2048)
    haar_from_weighted_identity=weighted_sum/core_period
    full=exact_sieve(period,family)
    actual_core_extensions=[0]*core_period
    witness=None
    for n,good in enumerate(full):
        if good:
            actual_core_extensions[n%core_period]+=1
            if witness is None:
                witness=n
    assert witness is not None and all(witness%d!=a for d,a in family.items())
    assert actual_core_extensions==core_extensions
    survivor_count=sum(actual_core_extensions)
    haar=F(survivor_count,period)
    assert haar==haar_from_weighted_identity
    exact_projection_Haar=F(len(admissible),core_period)
    assert haar>=exact_projection_Haar/off_period
    claimed_transport_floor=density_product/(2048*off_period)
    assert haar>claimed_transport_floor
    label_support_counts=dict(sorted(Counter(len(s) for s in factors.values()).items()))
    assert label_support_counts[5]>0
    five_prime_activity=[]
    for d,a in core_family.items():
        if len(factors[d])==5:
            before_label=exact_sieve(core_period,{e:b for e,b in core_family.items() if e!=d})
            private=next(n for n,good in enumerate(before_label)
                         if good and n%d==a and all(n%sizes[p] in domains[p] for p in CORE))
            assert not core_avoid[private]
            five_prime_activity.append(dict(modulus=d,residue=a,
                                            actual_private_core_word=private,
                                            positive_outside_extension_count=root_counts[private%sizes[root]]))
    return dict(name=name,original_labels=[dict(modulus=d,residue=family[d],support=factors[d]) for d in sorted(family)],
                original_label_count=len(family),support_size_histogram=label_support_counts,
                five_prime_original_labels=[dict(modulus=d,residue=family[d]) for d in family if len(factors[d])==5],
                all_five_prime_labels_are_effective=five_prime_activity,
                core=CORE,attachment_root=root,off_primes=off_primes,
                full_original_prime_heights=heights,full_original_coordinate_sizes=sizes,
                original_period=period,core_period=core_period,off_period=off_period,
                attachment_original_labels=attachment,root_raw_extension_counts=root_counts,
                effective_attachment_higher_support_labels=active_attachment_higher_labels,
                actual_feasible_domains=domains,actual_Haar_domain_densities=densities,
                actual_extension_weight_vectors=weights,
                full_product_domain_tuple_count=domain_tuple_count,
                legal_core_tuple_count=len(admissible),legal_core_tuple_counts_by_root_word=root_fibre_counts,
                conditional_product_core_reserve=conditional_product_reserve,
                retained_projection_original_Haar=exact_projection_Haar,
                weighted_integral_original_Haar=haar_from_weighted_identity,
                exact_full_original_survivor_count=survivor_count,
                exact_full_original_Haar=haar,certified_transport_lower_bound=claimed_transport_floor,
                original_uncovered_residue=witness,
                complete_core_extension_count_histogram=dict(sorted(Counter(core_extensions).items())),
                every_retained_core_fibre_checked_against_full_sieve=True,
                checked_retained_core_fibre_count=core_period)


def complete_core_labels(lift_three):
    moduli={prod(subset) for k in range(2,6) for subset in combinations(CORE,k)}
    if lift_three:
        moduli|={3*d for d in tuple(moduli) if d%3==0}
    labels={d:(37*i*i+11*i+1)%d for i,d in enumerate(sorted(moduli),1)}
    labels.update({p:0 for p in CORE})
    if lift_three:
        labels[9]=2
    # Fix the five-prime residues at surviving core words so the full-support
    # classes are effective constraints, rather than redundant filler labels.
    full_support=sorted(d for d in labels if len(factor(d))==5)
    for d in full_support:
        del labels[d]
    core_period=45045 if lift_three else 15015
    for d in full_support:
        allowed=exact_sieve(core_period,labels)
        word=next(n for n,good in enumerate(allowed) if good)
        labels[d]=word%d
    return labels


def encode(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [encode(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    cases=[control('five_core_with_higher_three_and_hanging_tree',complete_core_labels(True),
                   {17:0,51:1,153:37},3,(17,),765765),
           control('five_core_with_hanging_triangle_and_full_triple',complete_core_labels(False),
                   {17:0,19:0,85:1,95:2,323:3,1615:8},5,(17,19),4849845)]
    assert cases[0]['full_original_prime_heights'][3]==2
    assert 1615 in cases[1]['attachment_original_labels']
    assert all(len(set(c['root_raw_extension_counts']))>1 for c in cases)
    data=dict(scope='Two independently constructed original AP finite controls. They test exact weighted elimination, not the all-height proof.',
              construction='All mixed core supports of sizes2..5 are present; first example adds every ternary height-two lift. Distinct fixed residues are listed explicitly.',
              probability_convention='Conditional product on actual Vp is different from the weighted global Haar survivor marginal. Full Haar uses the recorded extension weights.',
              controls=cases)
    args.output.write_text(json.dumps(encode(data),separators=(',',':'))+'\n',encoding='utf-8')
    keys=('name','original_label_count','original_period','core_period','off_period',
          'five_prime_original_labels','actual_Haar_domain_densities','root_raw_extension_counts',
          'full_product_domain_tuple_count','legal_core_tuple_count','conditional_product_core_reserve',
          'exact_full_original_survivor_count','exact_full_original_Haar','original_uncovered_residue',
          'checked_retained_core_fibre_count')
    print(json.dumps(encode([{k:case[k] for k in keys} for case in cases]),indent=2))


if __name__=='__main__':
    main()
