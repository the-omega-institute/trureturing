#!/usr/bin/env python3
"""Exact private-shape and overlap controls for an ordinary cut77 exclusion.
No actual source is asserted for the impossible 12222/12222/1333 whole case.
"""
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json

def req(p,message):
    if not p:raise ValueError(message)

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    full=[z for z in combinations_with_replacement(range(4),5) if sum(z)<=10]
    gap=[z for z in combinations_with_replacement(range(4),4) if sum(z)<=10]
    survivors=[]
    for a,b,c in product(full,full,gap):
        ps=(sum(a[:3]),sum(b[:3]),sum(c[:2]))
        if sum(a)+sum(b)+sum(c)==28 and all(ps[i]+ps[j]>=9 for i,j in combinations(range(3),2)):
            survivors.append([list(a),list(b),list(c)])
    req(len(survivors)==11,'eleven ordered sorted private shapes')
    unordered=sorted({tuple(tuple(x) for x in (min(a,b),max(a,b),c)) for a,b,c in survivors})
    req(len(unordered)==8,'eight shapes up to full-root exchange')
    pairs=[]
    for a,b in product(combinations(range(1,7),4),repeat=2):
        common=sorted(set(a)&set(b));req(len(common)>=2,'two four-subsets of six intersect in at least2')
        chosen=common[:2]
        # Fine label0 is z in common columnH=0; full singleton w has private-column fine0.
        left={(0,h)for h in chosen}|{(1,h)for h in [0,*chosen]}
        right={(0,h)for h in chosen}|{(2,h)for h in [0,*chosen]}
        projection=left|right
        branches=[g for g in range(7) if len({h for gg,h in projection if gg==g})>=3]
        req(branches==[1,2],'chosen literal pair has only two ternary branches')
        pairs.append({'left_H':a,'right_H':b,'shared_pair':chosen,'ternary_branches':branches})
    req(len(pairs)==225,'all ordered common-column patterns')
    out={'scope':'Exact finite controls for ordinary normalized k0 cut77 private inventory and the 12222/12222/1333 exclusion when any gapcost3 cut is a whole column. Not Lean, not general cut77 closure.','ordered_private_shapes':survivors,'unordered_private_shapes':unordered,'whole_gap1333_overlap_patterns':pairs,'overlap_count':len(pairs),'excluded_case':{'full_private_costs':[[1,2,2,2,2],[1,2,2,2,2]],'gap_private_costs':[1,3,3,3],'additional_condition':'At least one of the three cost3 gap cuts is one whole-column edge.'}}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'ordered_private_shapes':len(survivors),'unordered_private_shapes':len(unordered),'overlap_patterns':len(pairs)}))
if __name__=='__main__':main()
