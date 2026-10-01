#!/usr/bin/env python3
"""Quartic D2 comparison certificates on the existing six uniform pruned laws."""
from itertools import product
from fractions import Fraction as F
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


MODS=(3,5,9,15,45)
CATS=('same_other_column','other_same_column','other_other_column')
POWERS=(1,16,81,256,625,1296)
SCALE=256

def calculate():
    results=[]

    for root,cat in product((1,2),CATS):
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
        J={A:max(sum((a+b)**4 for a,b in zip(A,B)) for B in histograms)
           for A in histograms}
        records=[(5*sum(a**4 for a in A)+J[tuple(sorted(A))],tuple(a**4 for a in A))
                 for A in layouts]
        lines_by_cut={}

        def lines_for(cut):
            if cut not in lines_by_cut:
                perlayout=[]
                for base,powers in records:
                    groups=[]
                    for group in masks:
                        lines=set()
                        for cylinder in group:
                            live=[powers[i] for i in cylinder if powers[i] <= cut]
                            lines.add((len(live),sum(live)))
                        groups.append(tuple(sorted(lines)))
                    perlayout.append((base,groups))
                lines_by_cut[cut]=perlayout
            return lines_by_cut[cut]

        def verify(p,q,early=True):
            cut=max((v for v in POWERS if v*q<=p),default=0)
            minslack=None
            for base,groups in lines_for(cut):
                lhs=q*base+sum(max(count*p-q*cost for count,cost in group) for group in groups)
                slack=6*n*p-lhs
                if slack<0 and early:return False,slack
                minslack=slack if minslack is None else min(minslack,slack)
            return minslack>=0,minslack

        bounds=(F(18231,32),F(143033,256),F(143033,256),F(73199,128),F(1137,2),F(1137,2))
        high=int(bounds[len(results)]*SCALE)
        low=high-1
        passed,slack=verify(high,SCALE,False)
        need(passed and not verify(low,SCALE)[0],'rational certificate and preceding-grid failure')
        result={'shape':f'root{root}_{cat}','old_survivors':n,
                'query_layouts':len(layouts),'distinct_sorted_histograms':len(histograms),
                'sorted_histogram_pairs':len(histograms)**2,
                'quartic_upper':str(F(high,SCALE)),'previous_grid_value':str(F(low,SCALE)),
                'minimum_scaled_D2_slack':slack,
                'scope':'Upper certificate from D2 and sorted old-query coupling; no sharpness assertion.'}
        results.append(result)

    need(sum(row['query_layouts'] for row in results)==27720,'all six complete old layout families')
    out={'method':'Same uniform pruned315 source; D2 at h=t^4; J4 from all sorted-histogram pairs.',
         'rows':results,'uniform_quartic_upper':str(max(F(row['quartic_upper']) for row in results)),
         'existing_X_quartic_upper':str(F(0)),
         'ordinary_finite_verification_not_Lean':True}

    atoms=(1,2,3,4,5,6,8,12)
    weights=tuple(map(F,('581/6966','3031/6966','146/1053','425/2106','10/1443','45/481','1/37','1/74')))
    need(sum(weights)==1,'existing increasing-convex source comparator')
    old_raw=sum(w*x**4 for w,x in zip(weights,atoms))
    multiplier=F(1)
    for p in (11,13,17,19,23):multiplier*=1+F(15,p-1)
    delta0=F(1243487,13077504)
    old=old_raw*multiplier/delta0
    new_raw=max(F(row['quartic_upper']) for row in results)
    new=new_raw*multiplier/delta0
    need(old==F(3350218780205,16165331),'existing source quartic upper reproduced')
    out.update(existing_X_quartic_upper=str(old_raw),pure_prime_multiplier=str(multiplier),
               same_source_retained_mass_lower=str(delta0),existing_mu23_quartic=str(old),
               new_D2_mu23_quartic=str(new),strict_improvement=new<old,
               difference=str(old-new),ratio=str(new/old),
               same_source_square=str(F(2607189975,7283281)),
               same_source_cubic=str(F(906617738995,159166336)),
               no_new_source_or_reweighting=True)
    mean_excess=(F(185,86),F(178,85),F(178,85),F(2),F(157,77),F(157,77))
    pure_roots=(11,13,17,19,23)
    reciprocal_sum=sum((F(1,p-1) for p in pure_roots),F(0))
    prime_product=F(1)
    for p in pure_roots:prime_product*=F(p,p-1)
    expected_deltas=(F(1243487,13077504),F(7609619,64627200),F(7609619,64627200),
                     F(39317,253440),F(123881,887040),F(123881,887040))
    shape_bounds=[]
    for row,c1,expected_delta in zip(results,mean_excess,expected_deltas):
        delta=c1+2+reciprocal_sum-(c1+1)*prime_product
        need(delta==expected_delta>0,'inherited actual shape-specific retained mass from complete mean inventory')
        bound=F(row['quartic_upper'])*multiplier/delta
        row.update(inherited_head_mean_excess=str(c1),
                   inherited_same_shape_retained_mass_lower=str(delta),
                   same_shape_mu23_quartic_upper=str(bound))
        shape_bounds.append(bound)
    shape_max=max(shape_bounds)
    need(shape_max==F(4005807477705,19895792)<new,
         'paired shape-specific propagation strictly improves separate extreme bounds')
    out.update(shape_specific_mu23_quartic=str(shape_max),
               shape_specific_improvement_over_old=str(old-shape_max),
               shape_specific_ratio_to_old=str(shape_max/old),
               shape_specific_worst_case=results[shape_bounds.index(shape_max)]['shape'])
    return out


def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix(".json").read_text())==result,
             "retained result agrees with the complete quartic D2 certificate")
        print(rendered,end="")
    else:
        args.output.write_text(rendered)


if __name__=="__main__":
    main()
