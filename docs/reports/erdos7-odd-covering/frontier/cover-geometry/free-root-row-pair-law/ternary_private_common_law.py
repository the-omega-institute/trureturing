#!/usr/bin/env python3
"""One supported law from a five-decaying centre and four monochromatic tails.

make_common_law accepts one actual central probability and four actual
ternary trees in distinct root columns and distinct rows.  It never
infers monochromatic trees from a star capability signature.
All original divisor phases remain independent.
Only standard-library exact arithmetic and sibling research APIs are used.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import importlib.util
import json

ROWS=(1,2,3,4)

def need(ok,message):
    if not ok: raise ValueError(message)

def sibling(filename,name):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    if spec is None or spec.loader is None: raise ImportError(filename)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

API=sibling('prime_layout_mixture_certificate.py','ternary_private_original_api')
ROOT=sibling('refined_five_tree_common_law.py','ternary_private_root_api')

def integer(value,lo,hi,name):
    need(type(value) is int and lo<=value<=hi,name+' outside integer range')

def height(K):
    need(type(K) is int and K>=2,'height must be an integer at least two')

def point(K,q):
    need(type(q) is tuple and len(q)==2,'literal row/residue pair required')
    r,y=q
    integer(r,1,4,'row');integer(y,0,7**K-1,'residue')

def points(K,source):
    need(type(source) in (set,frozenset,list,tuple),'finite actual source required')
    for q in source: point(K,q)
    result=frozenset(source)
    need(len(result)==len(source),'duplicate source points')
    return result

def row_threshold(K):
    height(K)
    return F(4,15)+F(2*(K+2),15*3**K)

def parameters(b,mode='optimized'):
    need(type(b) in (int,F) and F(1,4)<=b<=F(1,3),'exact four-row cap required')
    need(mode in ('optimized','simple'),'known probability mode required')
    if mode=='simple': return F(5,17),F(3,17)
    return 7/(19+8*b),(3+2*b)/(19+8*b)

def bound(K,b,mode='optimized',parameter_cap=None):
    height(K)
    cap=b if parameter_cap is None else parameter_cap
    need(type(cap) in (int,F) and b<=cap,'parameter cap must bound actual row maximum')
    alpha,p=parameters(cap,mode)
    if mode=='simple': return (98+15*b-F(36*(K+2),3**K))/17
    return (324+209*cap)/(57+24*cap)-3*alpha*(cap-b)-12*p*F(K+2,3**K)

def make_common_law(K,source,centre_column,central_law,private_columns,private_trees,mode='optimized',parameter_cap=None):
    """Validate actual support and return the common law and exact certificate.

    central_law maps (row, tail residue) to a positive rational, summing
    to one.  Every pure tail prefix of depth j has mass <=5^-j.
    private_columns maps rows 1..4 to four distinct columns outside
    centre_column. private_trees maps the same rows to complete actual
    ternary trees of height K-1, contained in those row/column cells.
    The sufficient finite row threshold is checked, not presumed.
    An optional exact parameter_cap >=actual row maximum selects the
    optimized parameters using that cap.  The cap 18/65 gives the fixed
    integer weights alpha=65/197, p=33/197 at every height.
    """
    height(K);h=K-1;source=points(K,source)
    integer(centre_column,0,6,'central column')
    need(type(central_law) is dict and central_law,'actual central law required')
    eta={}
    for q,mass in central_law.items():
        point(h,q)
        need(type(mass) in (int,F) and mass>0,'positive exact central mass required')
        eta[q]=F(mass)
        need((q[0],centre_column+7*q[1]) in source,'central mass outside actual source')
    need(sum(eta.values())==1,'central law must have unit mass')
    for j in range(1,h+1):
        pure,_=ROOT.prefix_masses(eta,j)
        need(max(pure.values())<=F(1,5**j),'central pure prefix exceeds five-decay cap')
    b=max(sum(m for (r,y),m in eta.items() if r==row) for row in ROWS)
    cap=b if parameter_cap is None else parameter_cap
    need(type(cap) in (int,F) and b<=cap,'parameter cap must bound actual row maximum')
    alpha,p=parameters(cap,mode)
    need((cap<=F(18,65) if mode=='optimized' else b<=row_threshold(K)),
         'central row mass exceeds sufficient threshold')
    need(type(private_columns) is dict and set(private_columns)==set(ROWS),'one column per actual row')
    need(type(private_trees) is dict and set(private_trees)==set(ROWS),'one actual tree per row')
    for c in private_columns.values(): integer(c,0,6,'private column')
    need(len(set(private_columns.values()))==4 and centre_column not in private_columns.values(),
         'five distinct root columns required')
    trees={}
    for r in ROWS:
        leaves=private_trees[r]
        need(type(leaves) in (set,frozenset,list,tuple),'finite actual ternary leaves required')
        for y in leaves: integer(y,0,7**h-1,'private tail leaf')
        leaves=frozenset(leaves)
        need(len(leaves)==len(private_trees[r])==3**h,'exactly one complete ternary tree required')
        need(API.contains_bary_tree(leaves,h,3),'private leaves do not form a ternary tree')
        need(all((r,private_columns[r]+7*y) in source for y in leaves),'private tree outside actual source')
        trees[r]=leaves
    nu={(r,centre_column+7*y):alpha*m for (r,y),m in eta.items()}
    for r in ROWS:
        for y in trees[r]: nu[r,private_columns[r]+7*y]=p/F(3**h)
    U=bound(K,b,mode,cap);T=6-F(2*(K+2),3**K)
    gap=((4-15*b+F(2*(K+2),3**K))/17 if mode=='simple' else
         (18-65*cap)/(57+24*cap)+3*alpha*(cap-b)+(8*cap-2)/(19+8*cap)*F(K+2,3**K))
    need(T-U==gap>=0,'finite target margin')
    return {'height':K,'centre_column':centre_column,'central_law':eta,
            'private_columns':dict(private_columns),'private_trees':trees,
            'law':nu,'row_cap':b,'parameter_cap':cap,'mode':mode,'alpha':alpha,'private_mass':p,
            'upper':U,'target':T,'margin':T-U}

def verify_common_law(source,certificate):
    c=certificate
    fresh=make_common_law(c['height'],source,c['centre_column'],c['central_law'],
                          c['private_columns'],c['private_trees'],c['mode'],c['parameter_cap'])
    need(c==fresh,'certificate fields differ from reconstructed actual law')
    K=c['height'];nu=c['law'];b=c['row_cap']
    need(sum(nu.values())==1 and set(nu)<=set(source),'common law normalization/support')
    root,witness=ROOT.root_maximum(nu)
    alpha,p=c['alpha'],c['private_mass']
    need(root==1+15*p+3*alpha*b,'exhaustive independent root maximum')
    measured=root;checks=[]
    for j in range(2,K+1):
        pure,joint=ROOT.prefix_masses(nu,j)
        m0,m1=max(pure.values()),max(joint.values())
        cap=alpha/5 if c['mode']=='optimized' and j==2 else p/F(3**(j-1))
        need(m0<=cap and m1<=cap,'actual same-law prefix bound')
        measured+=(2*j+1)*(m0+3*m1)
        checks.append({'depth':j,'pure_max':m0,'joint_max':m1,'cap':cap})
    need(measured<=c['upper']<=c['target'],'original-divisor LCM shell certificate')
    return {'height':K,'law_support':len(nu),'central_row_cap':b,'parameter_cap':c['parameter_cap'],'mode':c['mode'],
            'alpha':alpha,'private_mass':p,
            'independent_root_layouts':1225,'root_maximum':root,'root_witness':witness,
            'prefix_checks':checks,'measured_shell_bound':measured,
            'upper':c['upper'],'target':c['target'],'margin':c['margin']}

def concentrated_star_fixture(K,mode='optimized',parameter_cap=None):
    height(K);h=K-1
    rec=sibling('recursive_minimum_source_common_law.py','ternary_private_fixture_recursive')
    sig=sibling('row_summary_interface_obstructions.py','ternary_private_fixture_stars')
    central=set(rec.law(h));fibres=defaultdict(list)
    for r,y in central: fibres[y].append(r)
    eta={(r,y):F(1,5**h*len(fibres[y])) for r,y in central}
    children=[central]+[sig.signature_source(h,'star',r,1) for r in ROWS]
    source={(r,c+7*y) for c,child in enumerate(children) for r,y in child}
    tails={sum(d*7**j for j,d in enumerate(ds)) for ds in product(range(3),repeat=h)}
    cert=make_common_law(K,source,0,eta,{r:r for r in ROWS},{r:tails for r in ROWS},mode,parameter_cap)
    need(len(source)==5**K+2,'sharp source size')
    need(API.contains_bary_tree({y for r,y in source},K,5),'full-five source projection')
    need(all(API.contains_bary_tree({y for r,y in source if r in pair},K,3)
             for pair in combinations(ROWS,2)),'six pair-ternary source trees')
    selection=[];fixed={(r,y) for r,y in source if y!=0}
    need(len(fixed)==5**K-1 and {r for r,y in source if y==0}=={1,2,3},'three and only three labellings')
    for r in (1,2,3):
        audit=ROOT.test_selection(K,source,fixed|{(r,0)})
        if K>=3: need(not audit['criterion_met'],'every 412 full-five selection fails')
        selection.append(audit['criterion_met'])
    audit=verify_common_law(source,cert)
    audit.update(source_size=len(source),all_three_412_results=selection)
    return source,cert,audit

def distinct_actual_tails_fixture(K):
    """Unequal central five-trees, arbitrary actual ternary tails and columns."""
    height(K);h=K-1;eta={};source=set();columns={1:0,2:5,3:2,4:4};trees={}
    for r in ROWS:
        def leaves(branching):
            return {sum(((r+2*j+d)%7)*7**j for j,d in enumerate(ds))
                    for ds in product(range(branching),repeat=h)}
        five=leaves(5);trees[r]=leaves(3)
        for y in five:
            eta[r,y]=F(1,4*5**h)
            source.add((r,6+7*y));source.add((r,columns[r]+7*y))
    cert=make_common_law(K,source,6,eta,columns,trees)
    need(API.contains_bary_tree({y for r,y in source},K,5),'generic full-five source projection')
    need(all(API.contains_bary_tree({y for r,y in source if r in pair},K,3)
             for pair in combinations(ROWS,2)),'generic six pair-ternary trees')
    return source,cert,verify_common_law(source,cert)

def weighted_central_fixture(K,a,mode='optimized'):
    height(K);h=K-1
    five={sum(d*7**j for j,d in enumerate(ds)) for ds in product(range(5),repeat=h)}
    three={sum(d*7**j for j,d in enumerate(ds)) for ds in product(range(3),repeat=h)}
    eta={(r,y):(a if r==1 else (1-a)/3)/5**h for r in ROWS for y in five}
    R={(r,7*y) for r in ROWS for y in five}|{(r,r+7*y) for r in ROWS for y in five}
    cert=make_common_law(K,R,0,eta,{r:r for r in ROWS},{r:three for r in ROWS},mode)
    return R,cert,verify_common_law(R,cert)

def self_check():
    families=[concentrated_star_fixture(K)[2] for K in (2,3,4,5)]
    simple=[concentrated_star_fixture(K,'simple')[2] for K in (2,3,4,5)]
    fixed=[concentrated_star_fixture(K,parameter_cap=F(18,65))[2] for K in (2,3,4,5)]
    for item in fixed:
        K=item['height'];a=item['central_row_cap']
        need(item['alpha']==F(65,197) and item['private_mass']==F(33,197),'fixed integer weights')
        need(item['margin']==(54-195*a)/197+F(2*(K+2),197*3**K),'fixed-parameter margin')
    generic=[distinct_actual_tails_fixture(K)[2] for K in (2,3,4)]
    boundary=[weighted_central_fixture(K,F(18,65))[2] for K in (2,3,4)]
    simple_boundary=weighted_central_fixture(2,row_threshold(2),'simple')[2]
    need(simple_boundary['margin']==0,'simple finite row threshold equality')
    R,c,_=concentrated_star_fixture(2)
    def build(**overrides):
        values={'K':2,'source':R,'centre_column':c['centre_column'],'central_law':c['central_law'],
                'private_columns':c['private_columns'],'private_trees':c['private_trees']}
        values.update(overrides);return make_common_law(**values)
    eta=dict(c['central_law']);first=next(iter(eta))
    negative=dict(eta);negative[first]=-1
    floating={q:float(m) for q,m in eta.items()}
    unnormalized=dict(eta);unnormalized[first]+=F(1,10)
    concentrated={(1,y):F(1,5) for y in range(5)}
    wrong=dict(c);wrong['upper']-=1
    outside=set(R)-{next(iter(c['law']))}
    duplicate_columns={1:1,2:1,3:3,4:4}
    tests=[lambda:build(K=True),lambda:build(K=1),lambda:build(centre_column=True),
           lambda:build(central_law=negative),lambda:build(central_law=floating),
           lambda:build(central_law=unnormalized),lambda:build(central_law=concentrated),
           lambda:build(source=outside),lambda:build(private_columns=duplicate_columns),
           lambda:build(private_columns={1:0,2:2,3:3,4:4}),
           lambda:build(private_trees={r:[0,1,1] for r in ROWS}),
           lambda:build(private_trees={r:[0,1,7] for r in ROWS}),
           lambda:weighted_central_fixture(2,F(18,65)+F(1,1000)),
           lambda:weighted_central_fixture(2,row_threshold(2)+F(1,1000),'simple'),
           lambda:build(parameter_cap=F(1,4)),
           lambda:build(parameter_cap=F(18,65)+F(1,1000)),
           lambda:build(parameter_cap=0.27),
           lambda:build(mode='unknown'),
           lambda:verify_common_law(R,wrong)]
    for test in tests:
        try: test()
        except ValueError: pass
        else: raise ValueError('invalid input accepted')
    return {'concentrated_stars':families,'fixed_integer_weights':fixed,'simple_law_comparison':simple,
            'distinct_actual_tails':generic,'optimized_row_boundary':boundary,
            'simple_row_boundary':simple_boundary,'invalid_inputs_rejected':len(tests)}

def jsonable(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):jsonable(v) for k,v in x.items()}
    if isinstance(x,(tuple,list,set,frozenset)): return [jsonable(v) for v in x]
    return x

if __name__=='__main__': print(json.dumps(jsonable(self_check()),indent=2))
