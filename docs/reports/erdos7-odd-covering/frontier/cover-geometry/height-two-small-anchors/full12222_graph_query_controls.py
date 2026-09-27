#!/usr/bin/env python3
"""Exact 64-root-layout interfaces used in the four-edge graph reduction."""
import argparse
from fractions import Fraction as Q
from itertools import product
from math import lcm
import json

D=(1,5,7,25,35,49,175,245,1225)
P=tuple(d for d in D if d%5==0)


def check(name,w,owner,fine,column):
    pure={1:Q(1),7:3*w/5,49:w/5}
    other=dict(zip(P,(w/3,w/5,w/5,3*w/25,w/15,w/25)))
    inside=dict(zip(P,(1-w,(1-w)*owner,(1-w)*column,
                       (1-w)*owner,(1-w)*fine,(1-w)*fine)))
    rows=[]
    for layout in product((0,1),repeat=6):
        bits=dict(zip(P,layout)); z=Q(0)
        for d in D:
            for e in D:
                roots={bits[v] for v in (d,e) if v in bits};m=lcm(d,e)
                if len(roots)==2:continue
                z+=pure[m] if not roots else (inside if next(iter(roots)) else other)[m]
        rows.append((layout,z))
    maximum=max(z for _,z in rows)
    return {'name':name,'maximum':str(maximum),
            'maximizers':[list(b) for b,z in rows if z==maximum],
            'all_bounds':[{'bits':list(b),'bound':str(z)} for b,z in rows]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True);args=parser.parse_args()
    cases=[check('four_label_anchor_four_owner_matching',Q(495,647),Q(1,4),Q(1,4),Q(3,4)),
           check('two_P3_components',Q(3,4),Q(2,7),Q(1,7),Q(1)),
           check('singleton_in_edge_other_three_edges_disjoint',Q(3,4),Q(1,4),Q(1,8),Q(1))]
    expected=['5795/647','627/70','44/5']
    if [c['maximum'] for c in cases]!=expected:
        raise RuntimeError('exact maximum differs from candidate: '+str([c['maximum'] for c in cases]))
    result={'status':'PASS','layouts':192,'cases':cases,
            'scope':'Exact query cap certificates; original-source graph reductions must be proved separately.'}
    with open(args.output,'w',encoding='utf-8') as f:
        json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'status':'PASS','layouts':192,'maxima':expected}))


if __name__=='__main__':main()
