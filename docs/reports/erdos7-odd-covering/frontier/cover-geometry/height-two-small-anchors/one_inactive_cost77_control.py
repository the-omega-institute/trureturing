#!/usr/bin/env python3
"""Necessary one-inactive normalized profiles through77; k0/k1 consumers.

Integer profiles only, not actual source realizability. No file reads.
"""
import argparse
from collections import Counter
from itertools import combinations_with_replacement, product
from pathlib import Path
import json


def check(value,message):
    if not value: raise RuntimeError(message)


def roots(n,k):
    q=n-2
    for delta in range(3):
        for z in combinations_with_replacement(range(1 if k==0 else 0,4),n-delta):
            Z=sum(z);A=7*delta+2*Z
            if A<=20:yield dict(n=n,q=q,delta=delta,z=z,Z=Z,p=sum(z[:q]),forward=A)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    rows=[]
    for k in range(9):
        full=list(roots(5,k));gap=list(roots(4,k))
        groups=((('FFF',rs) for rs in combinations_with_replacement(full,3)),
                (('GFF',(a,*bs)) for a,bs in product(gap,combinations_with_replacement(full,2))))
        for group in groups:
            for kind,rr in group:
                c=21+7*k+sum(x['forward'] for x in rr)
                if c>77 or any(rr[i]['p']+rr[j]['p']<9-k for i in range(3) for j in range(i)):
                    continue
                if k==0:
                    witness=[i for i,r in enumerate(rr) if r['Z']+3*r['delta']<=9]
                    check(witness,'complete clipped root consumer')
                    consumer='complete_root_truncated_size_at_most9'
                elif k==1:
                    witness=[i for i,r in enumerate(rr) if r['p']<=2]
                    if witness:
                        consumer='whole_original_projection_at_most3'
                    elif min(r['p'] for r in rr)==3:
                        witness=[i for i,r in enumerate(rr) if r['n']==5 and r['delta']==0 and
                                 r['z'] in ((1,1,1,1,1),(1,1,1,1,2))]
                        check(witness,'four_public_plus_private_singleton_consumer')
                        consumer='four_public_plus_private_singleton_consumer'
                    else:
                        check(all(r['delta']==0 and r['p']==4 and r['Z']==8 for r in rr),'tight p4 branch')
                        check(all(r['z'] in (((2,2,2,2),) if r['n']==4 else ((0,2,2,2,2),(1,1,2,2,2)))
                                  for r in rr),'tight p4 complete shape classification')
                        consumer='three_tight_vectors_then_full11222_supplier'
                else:
                    consumer='not_supplied_by_this_k0_k1_control'
                rows.append(dict(kind=kind,c=c,k=k,roots=rr,consumer=consumer))
    counts=dict(Counter(r['k'] for r in rows))
    check(counts=={0:34,1:13,2:5,3:8,4:2} and len(rows)==62,'complete necessary inventory')
    result=dict(status='PASS',scope='Necessary sorted integer profiles; actual realization not asserted',
                counts_by_public_token_cost=counts,rows=rows,
                counts_by_consumer=dict(Counter(r['consumer'] for r in rows)))
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',necessary_profiles=len(rows),counts_by_public_token_cost=counts,
                         k0_k1_profiles=47,remaining_k2_through4_profiles=15)))


if __name__=='__main__':main()
