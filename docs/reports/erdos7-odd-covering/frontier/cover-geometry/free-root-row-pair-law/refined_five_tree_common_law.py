#!/usr/bin/env python3
"""Refined arbitrary full-five selection criterion and sharp-source controls.

For K>=2, max_r(beta_r+3M_r)<=c_K certifies one actual uniform labelled
five-tree law against all independent original divisor phases. c_K rises
from 122/135 to 11/10. The uniform 9/10 criterion has margin >=1/90.
An explicit two-one-surplus sharp family forbids every equal-mass
three-root law but admits the certified five-tree law.
Exact standard-library runtime validation remains active under -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import copy
import importlib.util
import json

ROWS=(1,2,3,4)


def need(ok,message):
    if not ok:raise ValueError(message)


def sibling(filename,name):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:raise ImportError(filename)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


api=sibling('prime_layout_mixture_certificate.py','_refined_layout_api')


def integer(x,lo,name):
    need(type(x) is int and x>=lo,name+' must be a literal integer >= '+str(lo))


def row_order(order):
    need(type(order) in (tuple,list) and len(order)==4 and
         all(type(r) is int for r in order) and set(order)==set(ROWS),'permutation of four literal rows required')
    return tuple(order)


def points(height,source):
    need(type(source) in (set,frozenset,list,tuple) and source,'finite nonempty point collection required')
    need(all(type(p) in (tuple,list) and len(p)==2 and type(p[0]) is int and p[0] in ROWS
             and type(p[1]) is int and 0<=p[1]<7**height for p in source),'literal source points required')
    result=frozenset(map(tuple,source));need(len(result)==len(source),'duplicate source points')
    return result


def threshold(height):
    integer(height,2,'height')
    return F(11,10)-F(2*(height+2),3**(height+1))+F(4*height+7,6*5**height)


def upper(height,cap):
    integer(height,2,'height')
    need(type(cap) in (int,F) and cap>=F(8,9),'exact cap >=8/9 required')
    return F(27,10)+3*cap-F(4*height+7,2*5**height)


def prefix_masses(law,depth):
    plain,joint=defaultdict(F),defaultdict(F)
    for (r,y),mass in law.items():plain[y%7**depth]+=mass;joint[r,y%7**depth]+=mass
    return plain,joint


def root_maximum(law):
    _,joint=prefix_masses(law,1);best=F(-1);witness=None
    for a,b,s,d in product(range(5),range(7),range(5),range(7)):
        value=sum((m*(1+(r==a)+(c==b)+(r==s and c==d))**2 for (r,c),m in joint.items()),F())
        if value>best:best,witness=value,(a,b,s,d)
    return best,witness


def test_selection(height,source,selected):
    integer(height,2,'height');source=points(height,source);selected=points(height,selected)
    leaves={y for _,y in selected}
    need(selected<=source,'selected point outside actual source')
    need(len(selected)==len(leaves)==5**height,'one actual row per complete five-tree leaf required')
    need(api.contains_bary_tree(leaves,height,5),'selection is not a complete five-tree')
    law={p:F(1,5**height) for p in selected};_,root=prefix_masses(law,1)
    beta={r:sum((m for (s,_),m in root.items() if s==r),F()) for r in ROWS}
    maxima={r:max((m for (s,_),m in root.items() if s==r),default=F()) for r in ROWS}
    balance={r:beta[r]+3*maxima[r] for r in ROWS};b=max(balance.values());cap=max(b,F(8,9))
    return {'height':height,'beta':beta,'root_cell_maxima':maxima,'balance':balance,'largest_balance':b,
            'threshold':threshold(height),'used_cap':cap,'criterion_met':b<=threshold(height),
            'uniform_nine_tenths_met':b<=F(9,10),'old_408_criterion_met':b<=F(22,25),
            'scope':'one supplied selection; failure does not refute another selection or law'}


def make_common_law(height,source,selected):
    audit=test_selection(height,source,selected);need(audit['criterion_met'],'selection exceeds finite sufficient threshold')
    selected=tuple(sorted(points(height,selected)))
    return {'height':height,'selected':selected,'nu':{p:F(1,5**height) for p in selected}}


def verify_common_law(source,certificate):
    need(type(certificate) is dict and set(certificate)=={'height','selected','nu'},'complete certificate schema required')
    K=certificate['height'];audit=test_selection(K,source,certificate['selected']);need(audit['criterion_met'],'failed selection threshold')
    selected=points(K,certificate['selected']);nu=certificate['nu'];need(type(nu) is dict and nu,'nonempty actual law required')
    for p,m in nu.items():
        need(type(p) is tuple and len(p)==2 and all(type(x) is int for x in p) and p in selected,'literal supported law point required')
        need(type(m) in (int,F) and m==F(1,5**K),'exact uniform leaf mass required')
    need(set(nu)==selected and sum(nu.values(),F())==1,'actual selected probability mismatch')
    checks=[]
    for j in range(K+1):
        plain,joint=prefix_masses(nu,j)
        need(len(plain)==5**j and all(v==F(1,5**j) for v in plain.values()),'actual full-tree prefix masses')
        need(max(joint.values())<=F(1,5**j),'joint prefix cap')
        checks.append((j,max(plain.values()),max(joint.values())))
    root,witness=root_maximum(nu);cap=audit['used_cap'];limit=upper(K,cap);target=api.default_target(K)
    need(root<=F(8,5)+3*cap,'independent root phases exceed the root bound')
    need(limit==F(8,5)+3*cap+4*sum((F(2*j+1,5**j) for j in range(2,K+1)),F()),'tail shell identity')
    need(target-limit==3*(threshold(K)-cap)>=0,'exact finite selection margin')
    if audit['uniform_nine_tenths_met']:
        need(target-upper(K,F(9,10))>=F(1,90),'uniform nine-tenths margin')
    return {'selection':audit,'root_exact_maximum':root,'root_attaining_phases':witness,
            'root_layout_count':1225,'prefix_checks':checks,'bound':limit,'target':target,'target_margin':target-limit,
            'scope':'one actual probability and all original phases; no source minimax optimum'}


def five_leaves(height):
    integer(height,0,'height');leaves={0}
    for j in range(height):leaves={y+d*7**j for y in leaves for d in range(5)}
    return leaves


def one_surplus_source(height,missing):
    integer(height,0,'height')
    need(type(missing) in (tuple,list) and len(missing)==2 and all(type(r) is int and r in ROWS for r in missing)
         and missing[0]!=missing[1],'two distinct literal missing-pair rows required')
    source={(r,0) for r in ROWS if r not in missing}
    for h in range(1,height+1):
        tail=five_leaves(h-1)
        source={(r,7*y) for r,y in source}|{(r,r+7*y) for r in ROWS for y in tail}
    return source


def sharp_source(height,order=(1,2,3,4)):
    integer(height,1,'height');order=row_order(order);h=height-1
    source={(r,7*y) for r,y in one_surplus_source(h,(1,2))}
    source|={(r,1+7*y) for r,y in one_surplus_source(h,(1,3))}
    source|={(r,r+1+7*y) for r in (1,2,3) for y in five_leaves(h)}
    return {(order[r-1],y) for r,y in source}


def family_certificate(height,order=(1,2,3,4)):
    integer(height,2,'height');order=row_order(order);source=sharp_source(height,order)
    by_leaf=defaultdict(set)
    for r,y in source:by_leaf[y].add(r)
    chosen={(order[3] if order[3] in rows else next(iter(rows)),y) for y,rows in by_leaf.items()}
    need(all(len(rows)==1 or order[3] in rows for rows in by_leaf.values()),'noncanonical duplicate leaf')
    return source,make_common_law(height,source,chosen)


def ternary_root_obstruction(height,source):
    """Actual structural certificate against every equal-mass three-root law."""
    integer(height,1,'height');source=points(height,source);rowsets=defaultdict(set)
    for r,y in source:rowsets[y%7].add(r)
    mono={c:next(iter(rs)) for c,rs in rowsets.items() if len(rs)==1}
    applicable=len(rowsets)>=3 and len(rowsets)-len(mono)<=2
    witnesses=[]
    if applicable:
        for cols in combinations(sorted(rowsets),3):
            c=next(c for c in cols if c in mono);r=mono[c]
            # One independently assigned phase at each original divisor.
            phases=(0,r,c,c+7*((r-c)*3%5))+tuple(v for _ in range(2,height+1) for v in (0,0))
            api.validate_layout(height,phases)
            witnesses.append({'columns':cols,'monochromatic_column':c,'row':r,'phases':phases})
    return {'applicable':applicable,'root_row_sets':{c:sorted(rs) for c,rs in rowsets.items()},
            'witnesses':witnesses,'universal_lower_bound':F(6) if applicable else None,
            'scope':'all supported laws putting exactly 1/3 in three root columns; q=0 of409 excluded'}


def obstruction_controls(height,source,obstruction):
    need(obstruction['applicable'],'root architecture not obstructed')
    expectations=[]
    for w in obstruction['witnesses']:
        cells={c:{p for p in source if p[1]%7==c} for c in w['columns']}
        nu={p:F(1,3*len(cell)) for cell in cells.values() for p in cell}
        phase=w['phases'];divs=api.original_divisors(height)
        actual=sum((mass*api._cost(divs,phase,r,y) for (r,y),mass in nu.items()),F())
        r=w['row'];c=w['monochromatic_column'];rowmass=sum((m for (s,_),m in nu.items() if s==r),F())
        root=1+3*rowmass+12*F(1,3)
        need(actual>=root>=6>api.default_target(height),'actual original-layout root obstruction')
        expectations.append(actual)
    return {'tested_root_selections':len(expectations),'least_tested_actual_expectation':min(expectations)}


def family_control(height,order=(1,2,3,4)):
    source,cert=family_certificate(height,order);audit=verify_common_law(source,cert);K=height;order=row_order(order)
    need(len(source)==5**K+2 and {y for _,y in source}==five_leaves(K),'sharp source cardinality/projection')
    need(all(api.contains_bary_tree({y for r,y in source if r in pair},K,3) for pair in combinations(ROWS,2)),
         'six actual pair-ternary trees')
    beta=audit['selection']['beta'];low=F(3,10)-F(1,10*5**(K-1));high=F(1,10)+F(3,10*5**(K-1))
    need(all(beta[r]==low for r in order[:3]) and beta[order[3]]==high,'actual family row distribution')
    exact_root=F(43,10)-F(3,2*5**K)
    need(audit['root_exact_maximum']==exact_root,'exact family root maximum')
    sharpened=F(27,5)-F(2*K+5,5**K)
    need(sharpened==exact_root+4*sum((F(2*j+1,5**j) for j in range(2,K+1)),F()),'family exact root-shell identity')
    need(api.default_target(K)-sharpened>=F(16,225),'family stronger uniform margin')
    forced_balance=F(9,10)-F(1,10*5**(K-1))
    need(audit['selection']['balance'][order[0]]==forced_balance,'forced row-one balance')
    if K>=3:need(forced_balance>F(22,25),'all408 selections should fail')
    obstruction=ternary_root_obstruction(K,source)
    return {'height':K,'source_points':len(source),'selected_points':len(cert['nu']),'selection':audit['selection'],
            'root_exact_maximum':exact_root,'family_bound':sharpened,'family_margin':api.default_target(K)-sharpened,
            'general_bound':audit['bound'],'general_margin':audit['target_margin'],
            'all408_selections_excluded':K>=3,'uniform_ternary_root':obstruction_controls(K,source,obstruction)}


def self_check():
    tail_controls=[]
    for h in range(5):
        for missing in combinations(ROWS,2):
            source=one_surplus_source(h,missing)
            good=[p for p in combinations(ROWS,2) if api.contains_bary_tree({y for r,y in source if r in p},h,3)]
            need(len(source)==5**h+1 and {y for _,y in source}==five_leaves(h),'one-surplus source')
            need(good==[p for p in combinations(ROWS,2) if p!=missing],'exact one-surplus capabilities')
            tail_controls.append((h,missing))
    family=[family_control(K) for K in range(2,6)]+[family_control(2,(4,2,1,3))]
    source,cert=family_certificate(2);first=sharp_source(1);ob=ternary_root_obstruction(1,first)
    first_control=obstruction_controls(1,first,ob)
    # A different actual selection on the same source fails the finite
    # threshold. This is a method failure, while the source already has
    # the successfully certified selection above.
    chosen=set(cert['selected']);chosen.remove((4,1));chosen.add((2,1))
    flexible=test_selection(2,source,chosen)
    need(not flexible['criterion_met'],'alternate selection should exceed the sufficient threshold')
    for K in range(2,10):
        delta=F(2*(2*K+3),3)*(F(1,3**(K+1))-F(2,5**(K+1)))
        need(threshold(K+1)-threshold(K)==delta>0,'threshold monotonic identity')
        need(api.default_target(K)-upper(K,F(9,10))>=F(1,90),'nine-tenths finite margin')
    need(threshold(2)==F(122,135),'threshold endpoint')
    invalid=[lambda:threshold(True),lambda:threshold(1),lambda:upper(2,0.9),lambda:upper(2,F(4,5)),
             lambda:one_surplus_source(2,(1,1)),lambda:one_surplus_source(2,(True,2)),
             lambda:one_surplus_source(-1,(1,2)),lambda:sharp_source(2,(1,2,3,3)),
             lambda:family_certificate(1),lambda:test_selection(2,source,tuple(cert['selected'])+(cert['selected'][0],))]
    for key,value in [('height',True),('height',1),('selected',()),('nu',{})]:
        bad=copy.deepcopy(cert);bad[key]=value;invalid.append(lambda bad=bad:verify_common_law(source,bad))
    for value in (True,0.04,F(-1),F(),F(1,24)):
        bad=copy.deepcopy(cert);bad['nu'][next(iter(bad['nu']))]=value
        invalid.append(lambda bad=bad:verify_common_law(source,bad))
    point=next(iter(cert['nu']));invalid.append(lambda:verify_common_law(source-{point},cert))
    bad=copy.deepcopy(cert);bad['extra']=1;invalid.append(lambda:verify_common_law(source,bad))
    rejected=0
    for op in invalid:
        try:op()
        except ValueError:rejected+=1
    need(rejected==len(invalid),'invalid input accepted')
    return {'one_surplus_capability_controls':len(tail_controls),'family':family,'height_one_obstruction':first_control,
            'alternate_actual_selection':flexible,'rejected_inputs':rejected,
            'scope':'exact controls; proofs give all-height claims, with every original phase independent'}


def jsonable(x):
    if type(x) is F:return str(x)
    if type(x) is dict:return {str(k):jsonable(v) for k,v in x.items()}
    if type(x) in (tuple,list):return [jsonable(v) for v in x]
    return x


if __name__=='__main__':print(json.dumps(jsonable(self_check()),indent=2))
