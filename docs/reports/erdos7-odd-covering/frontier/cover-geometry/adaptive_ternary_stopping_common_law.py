#!/usr/bin/env python3
"""One actual law from a finite heterogeneous ternary stopping frontier.

The finite first-level budget permits arbitrary stopping depths >=3 for
the 408 terminal profile, with uniform target margin 7/225. All original
divisor phases remain independent. No source-minimax optimality claim.
Standard library, exact Fraction arithmetic, checks active under -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
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


api=sibling('prime_layout_mixture_certificate.py','_stopping_layouts')
seed_api=sibling('balanced_five_tree_common_law.py','_stopping_seed')


def integer(x,lo,name):
    need(type(x) is int and x>=lo,name+' must be a literal integer >= '+str(lo))


def exact(x,name):
    need(type(x) in (int,F) and 0<=x<=1,name+' must be exact in [0,1]')
    return F(x)


def residue(word):return sum(d*7**j for j,d in enumerate(word))


def series(n):return 3-F(n+2,3**n)


def budget(height,initial_depth,beta,gamma):
    integer(height,1,'height');integer(initial_depth,0,'initial depth')
    need(initial_depth<height,'initial depth must be below height')
    beta=exact(beta,'beta');gamma=exact(gamma,'gamma')
    need(beta<=F(1,3)<=gamma,'require beta<=1/3<=gamma')
    A=1+3*beta;D=1+3*gamma
    bound=A*series(initial_depth)+D*(series(height)-series(initial_depth))
    uniform=3*(2-A)-F(D-A,3**initial_depth)*(initial_depth+2)
    margin=2*series(height)-bound
    need(margin==uniform+F(D-2,3**height)*(height+2),'finite budget identity')
    return {'A':A,'D':D,'bound':bound,'target':2*series(height),
            'target_margin':margin,'uniform_margin':uniform,'criterion_met':uniform>=0}


def frontier_tree(height,frontier):
    need(type(frontier) in (tuple,list,set,frozenset) and frontier,'nonempty finite frontier required')
    need(all(type(w) is tuple and len(w)<height and
             all(type(d) is int and 0<=d<7 for d in w) for w in frontier),
         'literal prefix tuples below total height required')
    need(len(set(frontier))==len(frontier),'duplicate frontier leaf')
    leaves=frozenset(frontier);children=defaultdict(set)
    for w in leaves:
        for j in range(len(w)):
            need(w[:j] not in leaves,'frontier is not prefix-free')
            children[w[:j]].add(w[j])
    need(all(len(ds)==3 for ds in children.values()),'each internal vertex needs exactly three children')
    need(sum((F(1,3**len(w)) for w in leaves),F())==1,'finite ternary Kraft identity')
    return leaves,dict(children)


def masses(law,depth):
    plain,joint=defaultdict(F),defaultdict(F)
    for (r,y),v in law.items():plain[y%7**depth]+=v;joint[r,y%7**depth]+=v
    return plain,joint


def points(height,source):
    need(type(source) in (list,tuple,set,frozenset) and source,'finite nonempty actual source required')
    need(all(type(p) in (list,tuple) and len(p)==2 and type(p[0]) is int
             and p[0] in ROWS and type(p[1]) is int and 0<=p[1]<7**height for p in source),
         'literal source points required')
    converted=frozenset(map(tuple,source))
    need(len(converted)==len(source),'duplicate source point')
    return converted


def components(height,source,frontier,tail_laws,beta,gamma,initial_depth):
    info=budget(height,initial_depth,beta,gamma)
    source=points(height,source);leaves,children=frontier_tree(height,frontier)
    need(min(map(len,leaves))>=initial_depth,'a frontier leaf stops before the initial budget')
    need(type(tail_laws) is dict and set(tail_laws)==set(leaves),'one actual tail law per leaf required')
    for w,law in tail_laws.items():
        h=len(w);u=residue(w);d=height-h
        need(type(law) is dict and law,'nonempty tail law required')
        for point,value in law.items():
            need(type(point) is tuple and len(point)==2 and type(point[0]) is int
                 and point[0] in ROWS and type(point[1]) is int and 0<=point[1]<7**d,
                 'literal tail point required')
            need(type(value) in (int,F) and value>0,'positive exact tail mass required')
            need((point[0],u+7**h*point[1]) in source,'tail point outside actual source')
        need(sum(law.values(),F())==1,'tail normalization')
        _,row=masses(law,0)
        need(max(row.values())<=beta,'tail row cap')
        for j in range(1,d+1):
            plain,joint=masses(law,j)
            need(max(plain.values())<=F(1,3**j),'tail pure cap')
            need(max(joint.values())<=F(gamma,3**j),'tail joint cap')
    return source,leaves,children,info


def make_common_law(height,source,frontier,tail_laws,beta=F(8,25),gamma=F(12,25),initial_depth=3):
    _,leaves,_,info=components(height,source,frontier,tail_laws,beta,gamma,initial_depth)
    need(info['criterion_met'],'initial budget does not certify all later heights')
    nu={(r,residue(w)+7**len(w)*y):F(value,3**len(w))
        for w in leaves for (r,y),value in tail_laws[w].items()}
    return {'height':height,'frontier':tuple(sorted(leaves)),'tail_laws':copy.deepcopy(tail_laws),
            'beta':F(beta),'gamma':F(gamma),'initial_depth':initial_depth,'nu':nu}


def verify_common_law(source,certificate):
    need(type(certificate) is dict and set(certificate)==
         {'height','frontier','tail_laws','beta','gamma','initial_depth','nu'},'complete certificate schema required')
    K=certificate['height'];a=certificate['initial_depth'];beta=certificate['beta'];gamma=certificate['gamma']
    source,leaves,_,info=components(K,source,certificate['frontier'],certificate['tail_laws'],beta,gamma,a)
    need(info['criterion_met'],'failed initial budget')
    nu=certificate['nu'];need(type(nu) is dict and nu,'actual global probability required')
    for p,v in nu.items():
        need(type(p) is tuple and len(p)==2 and all(type(x) is int for x in p) and p in source,
             'literal supported global point required')
        need(type(v) in (int,F) and v>0,'positive exact global mass required')
    expected={(r,residue(w)+7**len(w)*y):F(value,3**len(w))
              for w in leaves for (r,y),value in certificate['tail_laws'][w].items()}
    need(nu==expected and sum(nu.values(),F())==1,'global law must be the actual stopping mixture')
    checks=[];actual_shell=F();envelope=F()
    for n in range(K+1):
        plain,joint=masses(nu,n);m=max(plain.values());c=max(joint.values())
        mc=F(1,3**n);cc=F(beta if n<=a else gamma,3**n)
        need(m<=mc and c<=cc,'actual global prefix bounds')
        actual_shell+=(2*n+1)*(m+3*c);envelope+=(2*n+1)*(mc+3*cc)
        checks.append({'depth':n,'positive_prefixes':len(plain),'pure_max':m,'joint_max':c})
    need(envelope==info['bound'] and actual_shell<=envelope,'same-law original-label shell bound')
    return {'height':K,'source_points':len(source),'law_points':len(nu),'stopping_leaves':len(leaves),
            'minimum_stop':min(map(len,leaves)),'maximum_stop':max(map(len,leaves)),
            'budget':info,'actual_shell_bound':actual_shell,'prefix_checks':checks,
            'scope':'one supported probability against every original layout; no minimax optimum'}


def comb_frontier(initial_depth,last_stop):
    integer(initial_depth,0,'initial depth');integer(last_stop,initial_depth,'last stop')
    leaves=set(product(range(3),repeat=initial_depth))
    w=(0,)*initial_depth
    for _ in range(initial_depth,last_stop):
        leaves.remove(w);leaves.update(w+(d,) for d in range(3));w=w+(0,)
    return tuple(sorted(leaves))


def five_leaves(depth):
    leaves={0}
    for j in range(depth):leaves={y+d*7**j for y in leaves for d in range(5)}
    return leaves


def seed_tail(depth,rotation=0):
    integer(depth,2,'seed depth');integer(rotation,0,'rotation')
    src,selected=seed_api.example_family(2);tail=five_leaves(depth-2)
    rotate=lambda r:(r-1+rotation)%4+1
    source={(rotate(r),y+49*z) for r,y in src for z in tail}
    law={(rotate(r),y+49*z):F(1,5**depth) for r,y in selected for z in tail}
    return source,law


def adaptive_family(initial_depth,last_stop,vary_rows=False):
    """Admissible family with private five-ary padding in fixed row one."""
    need(type(vary_rows) is bool,'vary_rows must be a literal Boolean')
    frontier=comb_frontier(initial_depth,last_stop);K=last_stop+2
    leaves,children=frontier_tree(K,frontier);source=set();laws={}
    for i,w in enumerate(sorted(leaves)):
        sub,law=seed_tail(K-len(w),i%4 if vary_rows else 0);laws[w]=law
        source.update((r,residue(w)+7**len(w)*y) for r,y in sub)
    for w,ds in children.items():
        private=sorted(set(range(7))-ds)[:2];tail=five_leaves(K-len(w)-1)
        source.update((1,residue(w)+7**len(w)*(c+7*y)) for c in private for y in tail)
    cert=make_common_law(K,source,frontier,laws,initial_depth=initial_depth)
    return source,cert


def old_interface_audit(certificate,readout):
    """Audit every synchronized cut for this law; no claim about other laws."""
    K=certificate['height'];control=readout['prefix_checks'];reports=[]
    for q in range(K+1):
        if control[q]['positive_prefixes']!=3**q:
            reports.append({'cut':q,'reason':'wrong number of positive ternary prefixes'});continue
        prefixes={y%7**q for (r,y),mass in certificate['nu'].items() if mass>0}
        if not api.contains_bary_tree(prefixes,q,3):
            reports.append({'cut':q,'reason':'positive prefixes do not form a complete ternary tree'});continue
        if q==K:
            reports.append({'cut':q,'reason':'409 requires a positive remaining tail depth'});continue
        # The verified global cap is 3^-q; exactly 3^q positive prefixes
        # therefore forces each to have mass 3^-q. Conditional row maxima
        # and tight common tail maxima are their normalized global maxima.
        d=K-q;b=[3**q*(control[q+j]['pure_max']+3*control[q+j]['joint_max']) for j in range(1,d+1)]
        B=sum(b,F());C=sum((2*j+1)*x for j,x in enumerate(b,1));z=F(1,3**d)
        minimum_beta=max(3**q*control[q]['joint_max'],(2*B+2*z-1)/3,(C+2*(d+2)*z-2)/6)
        reports.append({'cut':q,'minimum_admissible_beta':minimum_beta,'passes_409':minimum_beta<=F(1,3),
                        'best_slope':2-2*B-2*z,'best_intercept':4-C-2*(d+2)*z})
    return reports


def check_layouts(certificate):
    K=certificate['height'];divs=api.original_divisors(K);nu=certificate['nu']
    # Deterministic independent choices, plus compatible point layouts.
    phases=[tuple((s*(i+1)*(i+3)+i*i)%d for i,d in enumerate(divs)) for s in range(12)]
    for r,y in list(nu)[:4]:
        phases.append(tuple(y%d if d%5 else next(y%(d//5)+t*(d//5) for t in range(5)
                            if (y%(d//5)+t*(d//5))%5==r) for d in divs))
    limit=budget(K,certificate['initial_depth'],certificate['beta'],certificate['gamma'])['bound']
    maximum=F()
    for phase in phases:
        api.validate_layout(K,phase)
        value=sum((mass*api._cost(divs,phase,r,y) for (r,y),mass in nu.items()),F())
        need(value<=limit,'literal independent layout exceeds proved envelope');maximum=max(maximum,value)
    return {'literal_layout_controls':len(phases),'largest_tested_expectation':maximum}


def family_control(a,H,vary=False):
    source,cert=adaptive_family(a,H,vary);audit=verify_common_law(source,cert);K=cert['height']
    need(len({y for _,y in source})==5**K,'exact five-tree projection size')
    need(api.contains_bary_tree({y for _,y in source},K,5),'full five-tree source')
    need(all(api.contains_bary_tree({y for r,y in source if r in pair},K,3)
             for pair in combinations(ROWS,2)),'six actual pair-ternary source witnesses')
    need(not any(api.contains_bary_tree({y for r,y in source if r!=omit},K,5) for omit in ROWS),
         'unexpected proper-row full tree')
    forced=1-F(len({y for r,y in source if r!=1}),5**K)
    need(forced>=1-F(3,5)**a>F(11,20),'all uniform full-tree selections must fail balance')
    audit['forced_row_one_mass']=forced
    if not vary:
        old=old_interface_audit(cert,audit);audit['synchronized_409_audit']=old
        if H>=6:need(all(not x.get('passes_409',False) for x in old),'expected strict certificate extension failed')
    audit.update(check_layouts(cert))
    return source,cert,audit


def self_check():
    source,cert,short=family_control(3,4)
    _,_,varying=family_control(3,4,True)
    _,_,separation=family_control(3,6)
    need(separation['synchronized_409_audit'][0]['best_intercept']==-F(473,164025),
         'exact strongest-beta obstruction')
    invalid=[lambda:budget(True,0,F(1,4),F(1,2)),lambda:budget(5,3,0.32,F(12,25)),
             lambda:budget(5,5,F(8,25),F(12,25)),lambda:budget(5,3,F(2,5),F(12,25)),
             lambda:frontier_tree(5,[(0,),(0,)]),lambda:frontier_tree(5,[(0,),(1,)]),
             lambda:frontier_tree(5,[(0,),(0,1),(1,),(2,)]),lambda:frontier_tree(5,[(True,),(1,),(2,)])]
    for key,value in [('height',True),('initial_depth',4),('beta',F(1,4)),('gamma',F(1,3)),('nu',{}),('tail_laws',{})]:
        bad=copy.deepcopy(cert);bad[key]=value;invalid.append(lambda bad=bad:verify_common_law(source,bad))
    for value in (True,0.01,F(-1),F(),F(1,2)):
        bad=copy.deepcopy(cert);bad['nu'][next(iter(bad['nu']))]=value
        invalid.append(lambda bad=bad:verify_common_law(source,bad))
    point=next(iter(cert['nu']));invalid.append(lambda:verify_common_law(source-{point},cert))
    bad=copy.deepcopy(cert);bad['extra']=1;invalid.append(lambda:verify_common_law(source,bad))
    rejected=0
    for operation in invalid:
        try:operation()
        except ValueError:rejected+=1
    need(rejected==len(invalid),'malformed certificate accepted')
    fail=budget(6,2,F(8,25),F(12,25));need(not fail['criterion_met'],'insufficient initial budget claimed')
    # Nine depth-two prefixes with four root children have the right
    # cardinality, but cannot be a complete ternary prefix tree.
    bad_shape={0,1,2,3,7,8,9,10,17}
    tail={(r,p+49*d):F(1,180) for r in ROWS for p in bad_shape for d in range(5)}
    topology_controls=[]
    for a in (0,3):
        frontier=tuple(product(range(3),repeat=a));K=a+3
        laws={w:dict(tail) for w in frontier}
        src={(r,residue(w)+7**a*y) for w in frontier for r,y in tail}
        cert=make_common_law(K,src,frontier,laws,F(1,4),F(1,3),a)
        audit=verify_common_law(src,cert);cut=a+2
        result=old_interface_audit(cert,audit)[cut]
        need(audit['prefix_checks'][cut]['positive_prefixes']==3**cut,
             'topology control must have the correct prefix count')
        need(result.get('reason')=='positive prefixes do not form a complete ternary tree',
             'cardinality must not stand in for complete ternary topology')
        topology_controls.append({'initial_depth':a,'cut':cut,'result':result})
    return {'heterogeneous_depths':short,'varying_terminal_row_laws':varying,
            'strict_interface_extension':separation,'rejected_inputs':rejected,
            'nonternary_equal_cardinality_controls':topology_controls,
            'scope':'exact controls; the analytic stopping-frontier proof supplies all heights and all phases'}


def jsonable(x):
    if type(x) is F:return str(x)
    if type(x) is dict:return {str(k):jsonable(v) for k,v in x.items()}
    if type(x) in (tuple,list):return [jsonable(v) for v in x]
    return x


if __name__=='__main__':print(json.dumps(jsonable(self_check()),indent=2))
