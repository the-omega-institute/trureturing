#!/usr/bin/env python3
"""Exact deficit budgets and a genuine arithmetic example outside the old box."""
import argparse
import importlib.util
from fractions import Fraction as F
from math import prod
from pathlib import Path
import json


def need(ok,message):
    if not ok:
        raise RuntimeError(message)

def calculate():
    T=F(615,49)
    t=6
    gatefactor=T-t
    need(gatefactor==F(321,49) and gatefactor>0,'positive gate factor')
    qs=(5,7,11,13,17,19)
    rootof=(0,0,1,1,1)
    roots=(1,0,0,0,0,0)
    leaves=(3,1,0,1,1,0)
    b=tuple(F(1,q-2) for q in qs)
    m=tuple(tuple(1-b[i]*((rootof[l]==roots[i])+(l==leaves[i])) for i in range(6)) for l in range(5))
    w=(F(8,25),F(3,10),F(19,100),F(0),F(19,100))
    dependency=Path(__file__).resolve().with_name('fibre_credit_depth_two_shared.py')
    spec=importlib.util.spec_from_file_location('shared_certificate',dependency)
    evaluator=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(evaluator)
    source=evaluator.calculate()
    need(json.loads(dependency.with_suffix('.json').read_text()) == json.loads(json.dumps(source)),
         'source certificate agrees with exact replay')
    fixed=source['positive']
    box=source['actual_mask_box']['certificate']
    budgets={}
    for name,data,simple in (('fixed',fixed,F(3,200)),('box',box,F(1,220))):
        g,h=F(data['source_lower']),F(data['query_hinge_upper'])
        score=gatefactor*g-h
        cap=score/gatefactor
        need(cap>simple>0,'positive exact and simplified '+name+' budget')
        need(cap<g,'strict cap leaves positive normalized mass')
        budgets[name]=dict(G=str(g),H=str(h),score=str(score),
                          exact_deficit_limit=str(cap),limit_decimal=float(cap),
                          sufficient_weak_deficit_bound=str(simple),
                          gate_margin_at_weak_bound=str(score-gatefactor*simple))

    # Actual originals, exactly as proposed. Ternary pure3/pure9 survivors have
    # roots{4,7} and{2,5,8}. The full relevant ternary/nonternary period is225.
    family=((0,3),(1,9),(0,5),(11,15),(41,45),(76,225))
    need(len({modulus for _,modulus in family})==len(family),'distinct numerical original labels')
    need(all(modulus>1 and modulus%2 for _,modulus in family),'odd nonunit originals')
    leafres=(4,7,2,5,8)
    need(set(leafres)=={r for r in range(9) if r%3!=0 and r!=1},'actual pure ternary survivors')
    q5states=tuple(x for x in range(25) if x%5!=0)
    need(len(q5states)==20,'pure5 conditional carrier')
    star=family[3:]
    blocked=[]
    for leaf in leafres:
        bad=[]
        for x25 in q5states:
            lifts=[x for x in range(225) if x%9==leaf and x%25==x25]
            need(len(lifts)==1,'unique CRT coordinate pair')
            x=lifts[0]
            if any(x%modulus==a for a,modulus in star):
                bad.append(x25)
        blocked.append(F(len(bad),len(q5states)))
    need(tuple(blocked)==(F(1,20),F(0),F(1,4),F(1,4),F(1,4)),'actual shared-source star union masses')
    need(blocked[0]>F(1,100),'strictly outside old beta_DT plusone percent box')
    actual=tuple(tuple(1-blocked[l] if q==5 else F(1) for q in qs) for l in range(5))
    D=sum((w[l]*(prod(m[l])-prod(min(m[l][i],actual[l][i]) for i in range(6))) for l in range(5)),F(0))
    need(D==w[0]*F(1,20)*prod(m[0][1:]),'only leaf0 q5 has target deficit')
    need(D<F(3,200),'actual example passes simplified loss gate')
    g,h=F(fixed['source_lower']),F(fixed['query_hinge_upper'])
    retained=g-D
    score=gatefactor*retained-h
    query=t-1+h/retained
    need(retained>0 and score>0 and query<T-1,'same final supported law passes continuation')
    # Every source finite cylinder is represented here. Test the actual finite
    # dominated completion formula on the pure5 carrier for all five target masses.
    for l,leaf in enumerate(leafres):
        good={x25 for x25 in q5states if not any(
            x%modulus==a for a,modulus in star
            for x in range(225) if x%9==leaf and x%25==x25)}
        a=F(len(good),20)
        target=m[l][0]
        eta={}
        for x25 in q5states:
            if a>=target:
                eta[x25]=(target/a)*F(x25 in good,20)
            else:
                need(a<1,'bad-set completion denominator is positive')
                eta[x25]=F(x25 in good,20)+(target-a)/(1-a)*F(x25 not in good,20)
        need(sum(eta.values())==target,'target marginal mass')
        need(all(0<=mass<=F(1,20) for mass in eta.values()),'dominated by same pure5 law')
        need(sum(eta[x] for x in good)==min(target,a),'exact retained good mass')
        need(sum(eta[x] for x in q5states if x not in good)==max(target-a,F(0)),'exact bad deficit')
    result=dict(scope='Ordinary same-source finite measure construction and exact arithmetic. Not new Lean and not an unrestricted covering result.',
        threshold=t,gate_factor=str(gatefactor),deficit_budgets=budgets,
        actual_example=dict(originals=[{'residue':a,'modulus':modulus} for a,modulus in family],
           retained_ternary_leaf_order=leafres,pure5_period=25,pure5_carrier_count=20,
           actual_star_union_masses=list(map(str,blocked)),
           weights=list(map(str,w)),lost_target_mass=str(D),lost_target_decimal=float(D),
           survivor_mass_lower=str(retained),score=str(score),query_upper=str(query),query_decimal=float(query),
           strictly_outside_old_box=True,passes_new_gate=True,
           interpretation='A finite actual arithmetic realization witnesses strict enlargement of the sufficient-condition region; it is not a covering-system counterexample or a universal profile certificate.'))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with exact replay')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
