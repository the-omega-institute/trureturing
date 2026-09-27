#!/usr/bin/env python3
"""Exact obstruction to central covers after uniform outside-root mixing.

This audits only that query-mixture subclass. It does not solve the full gate
or a source LP. It reads canonical data, and imports no other implementation.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

checks = Counter()
def check(name, condition):
    checks[name] += 1
    if not condition:
        raise ValueError(name)
def prod(xs):
    out = F(1)
    for x in xs: out *= x
    return out

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    names = ['clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json']
    data = {name:json.loads((args.directory/name).read_text()) for name in names}
    originals = data[names[0]]['actual_originals']
    check('101_distinct_originals',len(originals)==len({r['modulus'] for r in originals})==101)
    high = next(r for r in data[names[1]]['depth_results'] if r['n']==4)
    check('actual109_depth4',high['original_count']==109 and len(high['added_higher_pure_originals'])==8)
    gamma3,gamma5 = F(high['gamma3']),F(high['gamma5'])
    check('actual_gamma3',gamma3==F(81,82))
    check('actual_gamma5',gamma5==F(1875,1876))
    for capacity in high['capacities']:
        check('positive_remaining_central_capacity',F(capacity['haar_capacity'])>0)
    Q = (7,11,13,17,19)
    for row in originals:
        support = tuple(q for q in Q if row['modulus']%q==0)
        if len(support)==2:
            check('pair_event_contained_in_both_root1',all(row['residue']%q==1 for q in support))
    bymod={r['modulus']:r['residue'] for r in originals}
    for i,p in enumerate(Q):
        for q in Q[i+1:]:
            check('whole_pair_root1_forbidden',bymod[p*q]%(p*q)==1)
    lefts=(0,1,2,4,5)
    rights=tuple(m for m in range(20) if m!=5)
    cells=[(l,m) for l,m in product(lefts,rights) if not(l<3 and m<5)]
    live=[]
    cell_support=[]
    raw_source=F(0)
    for l,m in cells:
        x3=3*(l%3)+l//3
        x5=5*(m%5)+m//5
        x=(100*x3+126*x5)%225
        counts=[]
        for q in Q:
            restrictions=[]
            for row in originals:
                M=row['modulus']
                if M%q or any(M%r==0 for r in Q if r!=q): continue
                central=M
                while central%q==0: central//=q
                outside=M//central
                check('source_single_coordinate_depth_at_most2',q*q%outside==0)
                if x%central==row['residue']%central:
                    restrictions.append((outside,row['residue']%outside))
            allowed=[a for a in range(q*q) if a%q and all(a%modulus!=phase for modulus,phase in restrictions)]
            counts.append((sum(a%q==1 for a in allowed),sum(a%q!=1 for a in allowed)))
        outside_count=prod(B for A,B in counts)+sum((A*prod(Bj for j,(Aj,Bj) in enumerate(counts) if i!=j) for i,(A,B) in enumerate(counts)),F(0))
        mu=F((2-(l==4))*(4-(m==10)),675)
        outside_mass=outside_count/prod(q*(q-1) for q in Q)
        raw_source += mu*outside_mass
        if outside_count:live.append((l,m))
        cell_support.append({'cell':[l,m],'root1_other_counts':[list(v) for v in counts],'outside_survivor_count':str(outside_count),'outside_mass':str(outside_mass),'mu':str(mu)})
    check('79_live_central_cells',len(live)==79)
    check('only_dead_cell06',set(cells)-set(live)=={(0,6)})
    check('actual_source_mass',raw_source==F(data[names[1]]['source_mass']))
    g=F(200163067,201247200)
    coefficients=list(map(F,data[names[2]]['combined512_coefficients']))
    check('512_original_fee_groups',len(coefficients)==512)
    for i,q in enumerate(Q):
        if q!=7:coefficients[256+(1<<i)]+=g/F(q*(q-2))
    totals=[sum(coefficients[32*m:32*(m+1)],F(0)) for m in range(16)]
    left_menus=((0,),(0,1),lefts,lefts)
    right_menus=((0,),(0,1,2,3),rights,rights)
    def coordinate(e,label,value,q):
        weak=4 if q==3 else 10
        ordinary=F((2 if q==3 else 4)-(value==weak),9 if q==3 else 75)
        if e==0:return ordinary
        if e==1:return ordinary if value//q==label else F(0)
        if e==2:return ordinary if value==label else F(0)
        gamma=(gamma3 if q==3 else gamma5) if value==weak else F(1)
        return (gamma if q==3 else F(4,5)*gamma) if value==label else F(0)
    maxima=[]
    menus=[]
    for mode in range(16):
        e,f=divmod(mode,4)
        records=[]
        for a,b in product(left_menus[e],right_menus[f]):
            mass=sum((coordinate(e,a,l,3)*coordinate(f,b,m,5) for l,m in live),F(0))
            check('nonnegative_central_screen_mass',mass>=0)
            records.append({'left':a,'right':b,'mass':str(mass)})
        mx=max(F(row['mass']) for row in records)
        maxima.append(mx)
        for row in records:check('every_literal_selector_bounded',F(row['mass'])<=mx)
        menus.append({'mode':mode,'fee_total':str(totals[mode]),'literal_count':len(records),'maximum_integrated_selector':str(mx),'selectors':records})
    check('559_central_selectors',sum(row['literal_count'] for row in menus)==559)
    live_mass=sum((F((2-(l==4))*(4-(m==10)),675) for l,m in live),F(0))
    check('live_test_weight',live_mass==F(547,675))
    reward=g*live_mass
    debit_upper=sum((total*mx for total,mx in zip(totals,maxima)),F(0))
    check('strict_separation_all_aggregate_covers',debit_upper<reward)
    product_factors3=[F(1),F(1,2),F(1,5),F(729,730)]
    product_factors5=[F(1),F(1,4),F(1,19),F(9375,11719)]
    product_cover=sum((totals[4*i+j]*product_factors3[i]*product_factors5[j] for i,j in product(range(4),repeat=2)),F(0))
    check('product_cover_fails',product_cover<g)
    loose3=[F(1),F(2,3),F(2,9),F(1)]
    loose5=[F(1),F(4,15),F(4,75),F(4,5)]
    relaxed_upper=sum((totals[4*i+j]*loose3[i]*loose5[j] for i,j in product(range(4),repeat=2)),F(0))
    check('simple_relaxed_upper_also_separates',debit_upper<=relaxed_upper<reward)
    # Uniform mixing all live outside roots gives pointwise multiplier1.
    root_tuple_counts=[]
    for T in range(32):
        support=[q for i,q in enumerate(Q) if T&(1<<i)]
        count=int(prod(q-1 for q in support))
        weight=prod(F(1,q-1) for q in support)
        check('uniform_root_mixture_budget',count*weight==1)
        check('uniform_root_mixture_pointwise',weight*prod(q-1 for q in support)==1)
        root_tuple_counts.append(count)
    outside_menu_total=sum(root_tuple_counts)
    check('all_support_root_tuple_count',outside_menu_total==int(prod(Q)))
    result={'schema':'uniform-outside-central-cover-obstruction-v1','status':'PASS','check_count':sum(checks.values()),'checks':dict(sorted(checks.items())),
       'scope':'Only query mixtures that, within each selected literal central selector, uniformly average every live outside first-root tuple for its support. This entire aggregated-central-cover subclass cannot give pointwise debit>=g source. No claim that arbitrary outside-dependent query mixtures fail; no positive gate or covering conclusion.',
       'optimizer_used':False,'new_lean_verification':False,
       'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
       'input_sha256':{n:sha256((args.directory/n).read_bytes()).hexdigest() for n in names},
       'live_central_cells':79,'dead_central_cells':[[0,6]],'live_test_mass':str(live_mass),
       'actual_source_mass':str(raw_source),'source_coefficient_g':str(g),
       'required_integrated_debit':str(reward),'maximum_integrated_debit_upper':str(debit_upper),
       'upper_to_required_ratio':str(debit_upper/reward),'strict_deficit':str(reward-debit_upper),
       'simple_relaxed_upper':str(relaxed_upper),'simple_relaxed_deficit':str(reward-relaxed_upper),
       'product_central_cover':str(product_cover),'product_cover_over_g':str(product_cover/g),
       'central_selectors':559,'central_mode_support_addresses':559*32,
       'uniform_root_tuples_over_all_supports':outside_menu_total,
       'unexpanded_literal_central_root_tuple_count':559*outside_menu_total,
       'mode_selector_menus':menus,'actual_cell_support':cell_support}
    args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','check_count','live_central_cells','maximum_integrated_debit_upper','required_integrated_debit','upper_to_required_ratio','strict_deficit')}))

if __name__=='__main__':main()
