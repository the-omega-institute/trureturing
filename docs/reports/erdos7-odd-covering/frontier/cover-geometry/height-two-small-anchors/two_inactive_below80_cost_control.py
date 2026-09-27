#!/usr/bin/env python3
"""All necessary normalized two/three-inactive cost profiles below80.

Pure integer profile control, not actual-source enumeration or a mincut claim.
Reads no files and writes only --output; all checks remain active under -O.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from pathlib import Path
import json


def require(value, message):
    if not value:
        raise RuntimeError(message)


def roots(n, public):
    q = n-2
    for delta in range(3):
        a = n-delta
        for z in combinations_with_replacement(range(1 if public == 0 else 0,4), a):
            total = sum(z)
            contribution = 7*delta+2*total
            if contribution <= 20:
                p = sum(z[:q])
                require(total >= p+(a-q)*((p+q-1)//q), 'sorted integer bound')
                yield dict(n=n,q=q,delta=delta,z=z,Z=total,p=p,forward=contribution)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    two = []
    for kind,n1,n2 in (('FF',5,5),('GF',4,5)):
        for k in range(6):
            for a,b in product(roots(n1,k),roots(n2,k)):
                if kind == 'FF' and (a['delta'],a['z']) > (b['delta'],b['z']):
                    continue
                if a['p']+b['p'] < 9-k:
                    continue
                c = 42+7*k+a['forward']+b['forward']
                if c > 79:
                    continue
                require(k <= 1,'public token cost exceeds one')
                choices = (a,b)
                if k == 0:
                    witnesses = [i for i,r in enumerate(choices) if r['Z']+3*r['delta'] <= 9]
                    require(witnesses,'complete truncated-root consumer missing')
                    consumer = 'complete_root_truncated_cardinality_at_most9'
                else:
                    require(a['delta']+b['delta']==0,'one-public partial-root profile survived')
                    witnesses = [i for i,r in enumerate(choices) if r['p'] <= 2]
                    if witnesses:
                        consumer = 'whole_original_legal_projection_at_most3'
                    else:
                        witnesses = [i for i,r in enumerate(choices)
                                     if r['n']==5 and r['z'] in ((1,1,1,1,1),(1,1,1,1,2))]
                        require(witnesses,'four public-plus-private-singleton consumer missing')
                        consumer = 'four_original_fibres_with_one_public_plus_one_private_label'
                two.append(dict(kind=kind,c=c,k=k,roots=choices,consumer=consumer,witness_root=witnesses[0]))
    require(two,'empty necessary two-root inventory')
    three = []
    for n in (4,5):
        for k in range(3):
            for r in roots(n,k):
                c = 63+7*k+r['forward']
                if c > 79:
                    continue
                if k == 0:
                    require(r['Z']+3*r['delta'] <= 8,'three-inactive truncated consumer')
                    consumer = 'complete_root_truncated_cardinality_at_most8'
                else:
                    require(r['p']+k<=3,'three-inactive whole legal projection at most3')
                    consumer = 'whole_original_legal_projection_at_most3'
                three.append(dict(n=n,c=c,k=k,root=r,consumer=consumer))
    endpoint = F(2865,319)
    for bound in (F(249,28),F(893,100),F(5795,647)):
        require(bound <= endpoint < 9,'supplier comparisons')
    # Cardinality consumer is checked over every possible clipped nonempty size.
    cardinality = []
    for n in (4,5):
        for sizes in combinations_with_replacement(range(1,4),n):
            if sum(sizes)>9:
                continue
            ones,twos=sizes.count(1),sizes.count(2)
            if n==5:
                if ones>=3: family='whole_original_legal_projection_at_most3'
                elif ones==2:
                    require(twos>=2,'full1122 arbitrary fifth')
                    family='full1122_arbitrary_fifth'
                else:
                    require(ones==1 and twos==4,'full12222')
                    family='full12222'
            else:
                if ones:
                    require(ones+twos>=2,'gap12 arbitrary other two')
                    family='gap12_arbitrary_other_two'
                else:
                    require(twos>=3,'gap222 arbitrary fourth')
                    family='gap222_arbitrary_fourth'
            cardinality.append(dict(n=n,clipped_sizes=sizes,consumer=family))
    result=dict(status='PASS',scope='Necessary normalized integer profiles; no actual realizability or saturation claim',
                two_inactive=two,three_inactive=three,clipped_cardinality_profiles=cardinality,
                two_counts_by_capacity=dict(sorted(Counter(str(x['c']) for x in two).items())),
                two_counts_by_consumer=dict(Counter(x['consumer'] for x in two)),
                three_counts_by_capacity=dict(sorted(Counter(str(x['c']) for x in three).items())))
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',two_inactive_profiles=len(two),three_inactive_profiles=len(three),
                         clipped_cardinality_profiles=len(cardinality),
                         two_counts_by_capacity=result['two_counts_by_capacity'],
                         two_counts_by_consumer=result['two_counts_by_consumer'])))


if __name__=='__main__':
    main()
