#!/usr/bin/env python3
"""Glue actual terminal probabilities under one complete ternary prefix tree.

General finite tail bounds are beta (row), pure_caps[j], joint_caps[j].
The two-budget test is sufficient for every prefix height, not necessary
for an arbitrary source to have a good law. Terminal laws may all differ.
Every result uses one actual supported law against all original phases.
No args checks the general gluer and report408's selection-boundary family.
Standard library only; exact runtime checks stay active under -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import copy
import importlib.util
import json

ROWS=(1,2,3,4)


def need(ok,message):
    if not ok:raise ValueError(message)


def _sibling(filename,name):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:raise ImportError(filename)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


_trees=_sibling('prime_layout_mixture_certificate.py','_ternary_prefix_trees')


def _integer(n,minimum,name):
    need(type(n) is int and n>=minimum,name+' must be a literal integer at least '+str(minimum))


def _exact(x,name):
    need(type(x) in (int,F) and 0<=x<=1,name+' must be exact in [0,1]')
    return F(x)


def _source(height,source):
    need(type(source) in (list,tuple,set,frozenset) and source,'finite nonempty actual source required')
    points=[]
    for point in source:
        need(type(point) in (list,tuple) and len(point)==2,'row/residue point required')
        r,y=point
        need(type(r) is int and r in ROWS and type(y) is int and 0<=y<7**height,'literal carrier point required')
        points.append((r,y))
    need(len(points)==len(set(points)),'duplicate source point')
    return frozenset(points)


def profile_test(beta,pure_caps,joint_caps):
    beta=_exact(beta,'beta')
    need(type(pure_caps) in (list,tuple) and pure_caps and type(joint_caps) in (list,tuple)
         and len(joint_caps)==len(pure_caps),'equal positive-length pure/joint cap lists required')
    m=tuple(_exact(x,'pure cap') for x in pure_caps)
    c=tuple(_exact(x,'joint cap') for x in joint_caps)
    d=len(m);A=1+3*beta
    b=tuple(x+3*y for x,y in zip(m,c));B=sum(b,F(0))
    C=sum((F(2*j+1)*value for j,value in enumerate(b,1)),F(0));z=F(1,3**d)
    slope=A-2*B-2*z;intercept=2*A-C-2*(d+2)*z
    return {'tail_depth':d,'A':A,'B':B,'C':C,'gap_constant':3*(2-A),
            'gap_slope':slope,'gap_intercept':intercept,
            'criterion_met':beta<=F(1,3) and slope>=0 and intercept>=0,
            'scope':'sufficient all-prefix-height profile test; failure does not refute other laws'}


def bound(prefix_height,beta,pure_caps,joint_caps):
    _integer(prefix_height,0,'prefix height')
    info=profile_test(beta,pure_caps,joint_caps);h=prefix_height
    return info['A']*(3-F(h+2,3**h))+F(2*h*info['B']+info['C'],3**h)


def _prefix_masses(law,depth):
    plain,joint=defaultdict(F),defaultdict(F)
    for (r,y),mass in law.items():
        plain[y%7**depth]+=mass;joint[r,y%7**depth]+=mass
    return plain,joint


def _components(prefix_height,source,prefix,tail_laws,beta,pure_caps,joint_caps):
    _integer(prefix_height,0,'prefix height')
    profile=profile_test(beta,pure_caps,joint_caps)
    h,d=prefix_height,profile['tail_depth'];source=_source(h+d,source)
    need(type(prefix) in (list,tuple,set,frozenset),'finite prefix leaves required')
    need(all(type(u) is int and 0<=u<7**h for u in prefix),'literal prefix residue required')
    need(len(prefix)==len(set(prefix))==3**h and _trees.contains_bary_tree(prefix,h,3),'complete ternary prefix required')
    need(type(tail_laws) is dict and all(type(u) is int for u in tail_laws)
         and set(tail_laws)==set(prefix),'one actual law per selected terminal prefix required')
    for u,law in tail_laws.items():
        need(type(law) is dict and law,'nonempty terminal probability dictionary required')
        for point,mass in law.items():
            need(type(point) is tuple and len(point)==2 and all(type(x) is int for x in point),'literal terminal point required')
            r,y=point
            need(r in ROWS and 0<=y<7**d and (r,u+7**h*y) in source,'unsupported terminal point')
            need(type(mass) in (int,F) and mass>0,'positive exact terminal mass required')
        need(sum(law.values(),F(0))==1,'terminal probability normalization')
        _,row=_prefix_masses(law,0)
        need(all(value<=beta for value in row.values()),'terminal row cap')
        for j,(m,c) in enumerate(zip(pure_caps,joint_caps),1):
            plain,joint=_prefix_masses(law,j)
            need(max(plain.values())<=m and max(joint.values())<=c,'terminal prefix caps')
    return source,profile


def make_common_law(prefix_height,source,prefix,tail_laws,beta,pure_caps,joint_caps):
    """Construct only after checking the actual tail laws and all-height profile."""
    _,profile=_components(prefix_height,source,prefix,tail_laws,beta,pure_caps,joint_caps)
    need(profile['criterion_met'],'tail profile fails the sufficient all-height criterion')
    h=prefix_height
    nu={(r,u+7**h*y):F(mass,3**h) for u,law in tail_laws.items() for (r,y),mass in law.items()}
    return {'prefix_height':h,'prefix':tuple(sorted(prefix)),'tail_laws':copy.deepcopy(tail_laws),
            'beta':F(beta),'pure_caps':tuple(map(F,pure_caps)),'joint_caps':tuple(map(F,joint_caps)),'nu':nu}


def verify_common_law(source,certificate):
    keys={'prefix_height','prefix','tail_laws','beta','pure_caps','joint_caps','nu'}
    need(type(certificate) is dict and set(certificate)==keys,'complete certificate schema required')
    h=certificate['prefix_height'];beta=certificate['beta'];m=certificate['pure_caps'];c=certificate['joint_caps']
    source,profile=_components(h,source,certificate['prefix'],certificate['tail_laws'],beta,m,c)
    need(profile['criterion_met'],'certificate tail profile fails the all-height criterion')
    d=profile['tail_depth'];nu=certificate['nu']
    need(type(nu) is dict and nu,'nonempty global probability required')
    for point,mass in nu.items():
        need(type(point) is tuple and len(point)==2 and all(type(x) is int for x in point)
             and point in source,'global law uses a nonliteral or unsupported point')
        need(type(mass) in (int,F) and mass>0,'positive exact global mass required')
    expected={(r,u+7**h*y):F(mass,3**h) for u,law in certificate['tail_laws'].items() for (r,y),mass in law.items()}
    need(nu==expected and sum(nu.values(),F(0))==1,'global law is not the actual glued probability')
    controls=[];shell=F(0)
    for j in range(h+d+1):
        plain,joint=_prefix_masses(nu,j)
        pm,jm=(F(1,3**j),F(beta,3**j)) if j<=h else (F(m[j-h-1],3**h),F(c[j-h-1],3**h))
        need(max(plain.values())<=pm and max(joint.values())<=jm,'global actual prefix caps')
        shell+=(2*j+1)*(pm+3*jm)
        controls.append({'depth':j,'plain_max':max(plain.values()),'joint_max':max(joint.values()),
                         'plain_cap':pm,'joint_cap':jm})
    upper=bound(h,beta,m,c);target=2*(3-F(h+d+2,3**(h+d)))
    gap=profile['gap_constant']+F(h*profile['gap_slope']+profile['gap_intercept'],3**h)
    need(shell==upper and target-upper==gap and gap>=0,'same-law shell and exact finite gap')
    return {'height':h+d,'prefix_height':h,'source_points':len(source),'law_points':len(nu),
            'profile':profile,'prefix_controls':controls,'bound':upper,'target':target,'target_margin':gap,
            'scope':'one actual common-law upper bound; no source minimax optimum'}


SEED_BETA=F(8,25)
SEED_PURE=(F(1,5),F(1,25))
SEED_JOINT=(F(4,25),F(1,25))


def boundary_certificate(steps):
    """Control every report408 concentrating source by its continuing subtree."""
    _integer(steps,0,'boundary steps')
    balanced=_sibling('balanced_five_tree_common_law.py','_ternary_boundary_seed')
    seed_source,selected=balanced.example_family(2)
    seed=balanced.make_common_law(2,seed_source,selected)['nu']
    height,source=balanced.boundary_family(steps)
    prefix={0}
    for j in range(steps):prefix={u+digit*7**j for u in prefix for digit in range(3)}
    laws={u:dict(seed) for u in prefix}
    cert=make_common_law(steps,source,prefix,laws,SEED_BETA,SEED_PURE,SEED_JOINT)
    audit=verify_common_law(source,cert)
    closed=F(147,25)-F(7*steps+27,25*3**steps)
    gap=F(3,25)+F(13*steps+43,225*3**steps)
    need(audit['bound']==closed and audit['target_margin']==gap>F(3,25),'seed closed bound and strict margin')
    if steps:
        need(all(y%7 in range(3) for _,y in cert['nu']),'added private root pieces get zero mass')
    return source,cert,audit


def varying_tail_control():
    balanced=_sibling('balanced_five_tree_common_law.py','_varying_ternary_seed')
    src,selected=balanced.example_family(2);base=balanced.make_common_law(2,src,selected)['nu']
    prefix={1,3,6};laws={}
    for u in prefix:
        transformed={}
        for (r,y),mass in base.items():
            first,last=y%7,y//7
            z=(2*first+u)%7+7*((3*last+first+u)%7)
            transformed[(r+u-1)%4+1,z]=mass
        laws[u]=transformed
    need(len({tuple(sorted(law)) for law in laws.values()})==3,'terminal laws must actually differ')
    source={(r,u+7*y) for u,law in laws.items() for r,y in law}
    cert=make_common_law(1,source,prefix,laws,SEED_BETA,SEED_PURE,SEED_JOINT)
    return source,cert,verify_common_law(source,cert)


def self_check():
    boundary=[boundary_certificate(h)[2] for h in range(4)]
    source,cert,varying=varying_tail_control()
    # General tail-depth-one example, distinct from the specified depth-two seed.
    tail={(r,y):F(1,28) for r in ROWS for y in range(7)}
    src=set(tail);simple=make_common_law(0,src,{0},{0:tail},F(1,4),(F(1,7),),(F(1,28),))
    general=verify_common_law(src,simple)
    invalid=[lambda h=h:boundary_certificate(h) for h in (True,False,-1,1.0,'1')]
    invalid += [lambda:profile_test(0.32,SEED_PURE,SEED_JOINT),lambda:profile_test(True,SEED_PURE,SEED_JOINT),
                lambda:profile_test(SEED_BETA,[],[]),lambda:profile_test(SEED_BETA,SEED_PURE,(F(1,25),))]
    for key,value in (('prefix_height',True),('prefix',(1,1,3)),('prefix',(1,3)),('beta',F(1,4)),
                      ('pure_caps',(F(1,6),F(1,25))),('joint_caps',(F(1,10),F(1,25))),('nu',{}),('tail_laws',{})):
        bad=copy.deepcopy(cert);bad[key]=value
        invalid.append(lambda bad=bad:verify_common_law(source,bad))
    for value in (0.01,True,F(-1),F(0),F(1,2)):
        bad=copy.deepcopy(cert);point=next(iter(bad['nu']));bad['nu'][point]=value
        invalid.append(lambda bad=bad:verify_common_law(source,bad))
    point=next(iter(cert['nu']))
    invalid.append(lambda:verify_common_law(source-{point},cert))
    bad=copy.deepcopy(cert);bad['extra']=1
    invalid.append(lambda:verify_common_law(source,bad))
    rejected=0
    for operation in invalid:
        try:operation()
        except ValueError:rejected+=1
    need(rejected==len(invalid),'invalid certificate accepted')
    failing=profile_test(F(2,5),(F(1,3),),(F(1,3),))
    need(not failing['criterion_met'],'nonqualifying profile must remain a method failure')
    return {'boundary_family':boundary,'independently_varying_tails':varying,'general_depth_one_profile':general,
            'rejected_inputs':rejected,'nonqualifying_profile':failing,
            'scope':'exact finite controls; analytic gluing and finite-budget proof handles all prefix heights'}


def _jsonable(x):
    if type(x) is F:return str(x)
    if type(x) is dict:
        if all(type(k) is str for k in x):return {k:_jsonable(v) for k,v in x.items()}
        return [{'key':_jsonable(k),'value':_jsonable(v)} for k,v in x.items()]
    if type(x) in (tuple,list):return [_jsonable(v) for v in x]
    return x


if __name__=='__main__':print(json.dumps(_jsonable(self_check()),indent=2))
