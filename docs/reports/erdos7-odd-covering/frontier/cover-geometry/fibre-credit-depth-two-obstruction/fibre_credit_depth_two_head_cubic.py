#!/usr/bin/env python3
"""New cubic D2 upper certificates on the existing six uniform pruned laws."""
from itertools import product
from fractions import Fraction as F
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def calculate():
    MODS=(3,5,9,15,45)
    CATS=('same_other_column','other_same_column','other_other_column')
    CUBES=(1,8,27,64,125,216)
    SCALE=256
    results=[]

    for shape_index, (root,cat) in enumerate(product((1,2),CATS)):
        other=3-root
        row,col={'same_other_column':(root,2),'other_same_column':(other,1),
                 'other_other_column':(other,2)}[cat]
        a15=next(x for x in range(15) if x%3==root and x%5==1)
        a45=next(x for x in range(45) if x%9==row and x%5==col)
        originals=((3,0),(9,4),(5,0),(15,a15),(45,a45))
        points=[x for x in range(45) if all(x%m!=a for m,a in originals)]
        n=len(points)
        masks=[sorted({tuple(i for i,x in enumerate(points) if x%d==a)
                       for a in range(d)}-{()}) for d in MODS]
        layouts=[]
        for chosen in product(*masks):
            load=[1]*n
            for cylinder in chosen:
                for i in cylinder:load[i]+=1
            layouts.append(tuple(load))
        histograms=sorted(set(tuple(sorted(A)) for A in layouts))
        J={A:max(sum((a+b)**3 for a,b in zip(A,B)) for B in histograms)
           for A in histograms}
        records=[(5*sum(a**3 for a in A)+J[tuple(sorted(A))],tuple(a**3 for a in A))
                 for A in layouts]
        lines_by_cut={}

        def lines_for(cut):
            if cut not in lines_by_cut:
                perlayout=[]
                for base,cubes in records:
                    groups=[]
                    for group in masks:
                        lines=set()
                        for cylinder in group:
                            live=[cubes[i] for i in cylinder if cubes[i] <= cut]
                            lines.add((len(live),sum(live)))
                        groups.append(tuple(sorted(lines)))
                    perlayout.append((base,groups))
                lines_by_cut[cut]=perlayout
            return lines_by_cut[cut]

        def verify(p,q,early=True):
            cut=max((v for v in CUBES if v*q<=p),default=0)
            minslack=None
            for base,groups in lines_for(cut):
                lhs=q*base+sum(max(count*p-q*cost for count,cost in group) for group in groups)
                slack=6*n*p-lhs
                if slack<0 and early:return False,slack
                minslack=slack if minslack is None else min(minslack,slack)
            return minslack>=0,minslack

        high=(19573,19063,19063,19286,19342,19342)[shape_index]
        low=high-1
        passed,slack=verify(high,SCALE,False)
        need(passed and not verify(low,SCALE)[0],'rational certificate and preceding-grid failure')
        result={'shape':f'root{root}_{cat}','old_survivors':n,
                'query_layouts':len(layouts),'distinct_sorted_histograms':len(histograms),
                'sorted_histogram_pairs':len(histograms)**2,
                'cubic_upper':str(F(high,SCALE)),'previous_grid_value':str(F(low,SCALE)),
                'minimum_scaled_D2_slack':slack,
                'scope':'Upper certificate from D2 and sorted old-query coupling; no sharpness assertion.'}
        results.append(result)

    need(sum(row['query_layouts'] for row in results)==27720,'all six complete old layout families')
    out={'method':'Same uniform pruned315 source; D2 at h=t^3; J3 from all sorted-histogram pairs.',
         'rows':results,'uniform_cubic_upper':str(max(F(row['cubic_upper']) for row in results)),
         'existing_X_cubic_upper':str(F(87660407,1116882)),
         'ordinary_finite_verification_not_Lean':True}
    return out


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with all actual old-layout cubic inequalities')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
