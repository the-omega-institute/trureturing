#!/usr/bin/env python3
"""One supported law from a balanced labelled complete five-ary tree.

At height K>=2, test_selection checks one supplied actual full-five tree
and its row labels. The sufficient condition is beta_r+3*M_r<=22/25,
where M_r is its largest row/root-column mass under uniform leaf weight.
A valid unbalanced selection returns criterion_met=False; that does not
rule out another selection or another good supported probability.
make_common_law and verify_common_law construct/check the same actual
uniform law. Its all-original-layout bound has margin at least 11/180
against 2*t_K, by the report's analytic proof, not a finite height cutoff.

Only the standard library and the sibling original-layout API are used.
No args runs exact controls. --stdin accepts {"height":K,"source":[[r,y],...],
"selected":[[r,y],...]}; it returns the selection test and, if successful,
the law and verification. Output goes only to stdout. Checks survive -O.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import copy
import importlib.util
import json
import sys

ROWS=(1,2,3,4)
BALANCE=F(22,25)
ROOT_BOUND=F(17,4)
MARGIN=F(11,180)


def need(ok,message):
    if not ok:
        raise ValueError(message)


def _sibling(filename,name):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:
        raise ImportError(filename)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_trees=_sibling('prime_layout_mixture_certificate.py','_balanced_five_trees')


def _height(height):
    need(type(height) is int and height>=2,'height must be an integer at least two')


def _points(height,points):
    _height(height)
    need(type(points) in (set,frozenset,list,tuple) and points,'nonempty finite point collection required')
    result=[]
    for point in points:
        need(type(point) in (list,tuple) and len(point)==2,'row/residue point required')
        r,y=point
        need(type(r) is int and r in ROWS and type(y) is int and 0<=y<7**height,'point outside carrier')
        result.append((r,y))
    need(len(set(result))==len(result),'duplicate point')
    return frozenset(result)


def _root_maximum(joint):
    """All 1225 independent original root layouts on actual root mass."""
    best=F(-1);attainer=None
    for a,b,s,d in product(range(5),range(7),range(5),range(7)):
        cost=sum((w*(1+(r==a)+(c==b)+(r==s and c==d))**2
                  for (r,c),w in joint.items()),F(0))
        if cost>best:
            best,attainer=cost,(a,b,s,d)
    return best,attainer


def finite_bound(height):
    _height(height)
    return ROOT_BOUND+4*sum((F(2*j+1,5**j) for j in range(2,height+1)),F(0))


def test_selection(height,source,selected):
    """Decide the sufficient criterion for the supplied selection, not all selections."""
    source=_points(height,source)
    selected=_points(height,selected)
    leaves={y for _,y in selected}
    need(selected<=source,'selected point outside source')
    need(len(selected)==len(leaves)==5**height,'one row label per full-tree leaf required')
    need(_trees.contains_bary_tree(leaves,height,5),'selected leaves are not a complete five-tree')
    rows=Counter(r for r,_ in selected)
    cells=Counter((r,y%7) for r,y in selected)
    beta={r:F(rows[r],5**height) for r in ROWS}
    maxima={r:F(max(cells[r,c] for c in range(7)),5**height) for r in ROWS}
    balance={r:beta[r]+3*maxima[r] for r in ROWS}
    return {'height':height,'selected_points':len(selected),'beta':beta,
            'root_cell_maxima':maxima,'balance':balance,
            'criterion_met':all(x<=BALANCE for x in balance.values()),
            'scope':'tests only the supplied actual selection; failure does not refute other selections or laws'}


def make_common_law(height,source,selected):
    audit=test_selection(height,source,selected)
    need(audit['criterion_met'],'selected tree fails the sufficient balance criterion')
    points=tuple(sorted(_points(height,selected)))
    return {'height':height,'selected':points,'nu':{p:F(1,5**height) for p in points}}


def verify_common_law(height,source,certificate):
    _height(height)
    need(type(certificate) is dict and set(certificate)=={'height','selected','nu'},'certificate schema')
    need(type(certificate['height']) is int and certificate['height']==height,'certificate height')
    source=_points(height,source)
    selected=_points(height,certificate['selected'])
    audit=test_selection(height,source,selected)
    need(audit['criterion_met'],'certificate selection is unbalanced')
    nu=certificate['nu']
    need(type(nu) is dict and nu,'probability dictionary required')
    for point,mass in nu.items():
        need(type(point) is tuple and len(point)==2 and all(type(x) is int for x in point)
             and point in selected,'nonliteral or unsupported law point')
        need(type(mass) in (int,F) and mass==F(1,5**height),'exact uniform leaf mass required')
    need(set(nu)==selected and sum(nu.values(),F(0))==1,'law must contain exactly the selected tree')
    prefix_controls=[]
    for depth in range(height+1):
        plain,joint=defaultdict(F),defaultdict(F)
        for (r,y),mass in nu.items():
            plain[y%7**depth]+=mass
            joint[r,y%7**depth]+=mass
        need(len(plain)==5**depth and all(v==F(1,5**depth) for v in plain.values()),'actual full-tree prefix masses')
        need(all(v<=F(1,5**depth) for v in joint.values()),'actual joint-prefix cap')
        prefix_controls.append((depth,max(plain.values()),max(joint.values())))
    root=defaultdict(F)
    for (r,y),mass in nu.items():root[r,y%7]+=mass
    root_max,phases=_root_maximum(root)
    need(root_max<=ROOT_BOUND,'all independent root layouts exceed analytic root bound')
    target=2*(3-F(height+2,3**height));bound=finite_bound(height)
    need(target-bound>=MARGIN,'finite target margin')
    return {'selection':audit,'root_exact_maximum':root_max,'root_attaining_phases':phases,
            'root_layout_count':1225,'prefix_controls':prefix_controls,'bound':bound,
            'target':target,'target_margin':target-bound,'uniform_margin':MARGIN,
            'scope':'one actual supported law for every original layout; no source minimax optimality'}


# A reusable whole-height family: an inclusion-minimal nonminimum admissible
# depth-two source, with a selected balanced tree and arbitrary varying
# five-ary tails. This accompanies the general criterion, not a finite
# positive-instance theorem.
BASE_CELLS={
 1:({3,4},{2,3},{0,1},set(),{0,1}),
 2:({1,2},{2},{4},set(),{1,2,3}),
 3:({0},{0,4},set(),{2},{4}),
 4:(set(),{1},{0,2,3},{0,1,3,4},set()),
}


def example_family(height):
    _height(height)
    base={(r,c+7*d) for r,cells in BASE_CELLS.items() for c,ds in enumerate(cells) for d in ds}
    chosen={(min(r for r,z in base if z==y),y) for y in {z for _,z in base}}
    source,selected=set(),set()
    for r,y in base:
        tails={0}
        for j in range(height-2):
            tails={z+7**j*((r+y+j+z+2*d)%7) for z in tails for d in range(5)}
        points={(r,y+49*z) for z in tails}
        source.update(points)
        if (r,y) in chosen:selected.update(points)
    return source,selected


def boundary_family(steps,row=1):
    """Admissible sources forcing every uniform full-tree law toward one row.

    Each added root has three copies of the previous source and two
    private full-five trees in the same row. At two or more added roots,
    no supported labelling of a complete five-tree meets the criterion.
    This does not rule out a different, nonuniform good common law.
    """
    need(type(steps) is int and steps>=0,'nonnegative integer boundary depth required')
    need(type(row) is int and row in ROWS,'literal dominant row required')
    source,_=example_family(2)
    for _ in range(steps):
        leaves={y for _,y in source}
        source=({(r,c+7*y) for c in range(3) for r,y in source}
                |{(row,c+7*y) for c in (3,4) for y in leaves})
    return steps+2,source


def _boundary_control(steps):
    height,source=boundary_family(steps)
    leaves={y for _,y in source}
    need(len(leaves)==5**height and _trees.contains_bary_tree(leaves,height,5),'exact boundary projection')
    need(all(_trees.contains_bary_tree({y for r,y in source if r in pair},height,3)
             for pair in combinations(ROWS,2)),'boundary pair trees')
    need(not any(_trees.contains_bary_tree({y for r,y in source if r!=omit},height,5)
                 for omit in ROWS),'boundary proper-row full tree')
    optional_other={y for r,y in source if r!=1}
    forced_mass=1-F(len(optional_other),5**height)
    lower=1-F(3,5)**steps
    need(forced_mass>=lower,'all-labellings concentration lower bound')
    if steps>=2:
        need(lower>F(11,20),'boundary fails the necessary balanced-row cap')
    return {'steps':steps,'height':height,'source_points':len(source),
            'forced_dominant_row_mass':forced_mass,'analytic_lower_bound':lower,
            'excludes_every_balanced_selection':steps>=2}


def _family_control(height):
    source,selected=example_family(height)
    certificate=make_common_law(height,source,selected)
    audit=verify_common_law(height,source,certificate)
    def has(rows,branch):
        return _trees.contains_bary_tree({y for r,y in source if r in rows},height,branch)
    need(has(ROWS,5) and all(has(pair,3) for pair in combinations(ROWS,2)),'family admissibility')
    need(not any(has(tuple(s for s in ROWS if s!=r),5) for r in ROWS),'proper three-row full tree')
    good_root_columns={c for r,c in product(ROWS,range(7))
                       if _trees.contains_bary_tree({y//7 for s,y in source if s==r and y%7==c},height-1,3)}
    need(good_root_columns=={2,3,4},'individual ternary root columns')
    projected={(r,y%49) for r,y in source}
    forced={y for r,y in projected if r==4 and y%7==3 and {s for s,z in projected if z==y}=={4}}
    need(forced=={3,10,24,31},'four forced row-four second digits')
    return {'height':height,'source_points':len(source),'selected_points':len(selected),
            'selection':audit['selection'],'root_exact_maximum':audit['root_exact_maximum'],
            'bound':audit['bound'],'margin':audit['target_margin'],
            'individual_ternary_root_columns':sorted(good_root_columns),'forced_second_digit_residues':sorted(forced)}


def self_check():
    family=[_family_control(height) for height in (2,3,4)]
    boundary=[_boundary_control(steps) for steps in (0,1,2)]
    source,selected=example_family(2)
    cert=make_common_law(2,source,selected)
    # A source may contain extra points and need not satisfy pair-tree conditions.
    verify_common_law(2,selected,cert)
    verify_common_law(2,source|{(1,48)},cert)
    # Failure of this particular witness does not negate the source theorem.
    unbalanced={(1,y) for _,y in selected}
    test=test_selection(2,unbalanced,unbalanced)
    need(not test['criterion_met'],'monochromatic tree must fail balance test')
    invalid=[lambda h=h:make_common_law(h,source,selected) for h in (True,False,0,1,-1,2.0,'2')]
    malformed=[[],[(True,0)],[(1,False)],[(1,0.0)],[(1,49)],[(0,0)],[(1,0),(1,0)],[(1,)],'points']
    invalid.extend(lambda s=s:make_common_law(2,s,selected) for s in malformed)
    invalid.extend((lambda:make_common_law(2,source,selected-{next(iter(selected))}),
                    lambda:make_common_law(2,unbalanced,unbalanced),
                    lambda:test_selection(2,source,{(1,y) for y in range(25)})))
    invalid.extend((lambda:boundary_family(True),lambda:boundary_family(-1),
                    lambda:boundary_family(1,True),lambda:boundary_family(1,0)))
    for key,value in (('height',True),('height',3),('selected',tuple(selected)+((1,48),)),('nu',{})):
        bad=copy.deepcopy(cert);bad[key]=value
        invalid.append(lambda bad=bad:verify_common_law(2,source,bad))
    for weight in (True,0.04,0,F(-1),F(1,24)):
        bad=copy.deepcopy(cert);bad['nu'][next(iter(bad['nu']))]=weight
        invalid.append(lambda bad=bad:verify_common_law(2,source,bad))
    bad=copy.deepcopy(cert);bad['extra']=1
    invalid.append(lambda:verify_common_law(2,source,bad))
    rejected=0
    for operation in invalid:
        try:operation()
        except ValueError:rejected+=1
    need(rejected==len(invalid),'malformed data accepted')
    need(finite_bound(2)==F(101,20) and F(46,9)-finite_bound(2)==MARGIN,'initial target margin')
    return {'family':family,'boundary_family':boundary,'rejected_inputs':rejected,'limiting_upper_bound':F(107,20),
            'uniform_margin':MARGIN,'unbalanced_selection_test':test,
            'scope':'exact controls supporting the analytic all-height criterion; no automatic balanced selection theorem'}


def _jsonable(value):
    if type(value) is F:return str(value)
    if type(value) is dict:
        if all(type(k) is str for k in value):return {k:_jsonable(v) for k,v in value.items()}
        return [{'key':_jsonable(k),'value':_jsonable(v)} for k,v in value.items()]
    if type(value) in (tuple,list):return [_jsonable(v) for v in value]
    return value


def main():
    if len(sys.argv)==1:result=self_check()
    else:
        need(sys.argv[1:]==['--stdin'],'usage: balanced_five_tree_common_law.py [--stdin]')
        data=json.load(sys.stdin)
        need(type(data) is dict and set(data)=={'height','source','selected'},'height/source/selected input required')
        result={'selection':test_selection(data['height'],data['source'],data['selected'])}
        if result['selection']['criterion_met']:
            cert=make_common_law(data['height'],data['source'],data['selected'])
            result.update(certificate=cert,verification=verify_common_law(data['height'],data['source'],cert))
    print(json.dumps(_jsonable(result),indent=2))


if __name__=='__main__':main()
