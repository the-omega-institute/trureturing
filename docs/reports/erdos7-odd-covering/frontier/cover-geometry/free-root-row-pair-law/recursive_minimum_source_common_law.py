#!/usr/bin/env python3
"""Construct one recursive source family and its exact common probability.

law(K) returns {(row, residue): Fraction} on the source of size 5^K+2.
coloured_law(K, colour) permits Klein-four translations depending on each
private tail leaf, while keeping one actual common probability.
Heights must be nonnegative integers; construction size grows with K.
With no arguments, print JSON for the exact source, prefix, root-layout
and height-two original-divisor controls. No output files are written.

These finite controls accompany the all-height proof for these recursive
families. They are not an all-source theorem or a covering conclusion.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import importlib.util
import json

ALPHA=F(2,7)
PRIVATE=F(5,28)
ROOTS=list(product(range(5),range(7),range(5),range(7)))


def _load_certificate_api():
    path=Path(__file__).with_name('prime_layout_mixture_certificate.py')
    spec=importlib.util.spec_from_file_location('recursive_source_certificate',path)
    if spec is None or spec.loader is None:
        raise RuntimeError('cannot load sibling layout certificate module')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


api=_load_certificate_api()


def need(ok,message):
    if not ok:raise RuntimeError(message)


def _height(height,minimum=0):
    if type(height) is not int or height<minimum:
        raise ValueError('height must be an integer at least '+str(minimum))


def five_leaves(height):
    """Return the full low-digit-first five-ary subtree in Z/7^height."""
    _height(height)
    leaves=[0]
    for j in range(height):leaves=[y+digit*7**j for y in leaves for digit in range(5)]
    return leaves


def law(height):
    """Return the exact common law, with central mass 2/7 and private 5/28."""
    _height(height)
    if height==0:return {(r,0):F(1,3) for r in (1,2,3)}
    result={(r,7*y):ALPHA*mass for (r,y),mass in law(height-1).items()}
    for r in range(1,5):
        for y in five_leaves(height-1):result[r,r+7*y]=PRIVATE/F(5**(height-1))
    return result


def last_digit_colour(tail_height,leaf):
    """Klein element determined by deepest tail digit, with counts 2,1,1,1."""
    if tail_height==0:return 0
    return (0,0,1,2,3)[leaf//7**(tail_height-1)]


def coloured_law(height,colour=None):
    """Return the leaf-coloured common law; colour=None recovers law(height).

    colour(h,y) must return an integer in 0..3 for every leaf y of the
    standard height-h five-ary tree. Private column g+1 assigns that leaf
    to row (g XOR colour(h,y))+1. The all-height theorem also permits
    transporting the construction along arbitrary prefix-preserving
    embeddings into four different actual five-ary trees.
    """
    _height(height)
    if height==0:return law(0)
    result={(r,7*y):ALPHA*mass for (r,y),mass in coloured_law(height-1,colour).items()}
    for y in five_leaves(height-1):
        c=0 if colour is None else colour(height-1,y)
        if type(c) is not int or not 0<=c<4:
            raise ValueError('colour must be an integer Klein element in 0..3')
        for g in range(4):result[(g^c)+1,g+1+7*y]=PRIVATE/F(5**(height-1))
    return result


def validate_coloured_family(height,colour=last_digit_colour):
    """Check actual source trees, all root phases, and the same-law prefix caps."""
    _height(height,1)
    distribution=coloured_law(height,colour);source=set(distribution)
    need(len(source)==5**height+2 and sum(distribution.values())==1,'coloured source size and probability')
    pair_checks=[api.contains_bary_tree({y for r,y in source if r in pair},height,3)
                 for pair in combinations(range(1,5),2)]
    need(all(pair_checks) and api.contains_bary_tree({y for r,y in source},height,5),
         'coloured source tree premises')
    row=[sum(mass for (r,y),mass in distribution.items() if r==j) for j in range(1,5)]
    need(row==[F(1,4)+ALPHA**height/12]*3+[F(1,4)-ALPHA**height/4],
         'coloured row balance is unchanged')
    roots=defaultdict(F)
    for (r,y),mass in distribution.items():roots[r,y%7]+=mass
    root_values=[sum(mass*(1+(r==a)+(c==b)+((r,c)==(u,v)))**2
                     for (r,c),mass in roots.items()) for a,b,u,v in ROOTS]
    root_max=max(root_values)
    root_bound=F(109,28)+ALPHA**(height-1)/14
    need(root_max<=root_bound,'coloured root bound need not be equality')
    caps=[]
    measured_envelope=root_max
    for depth in range(1,height+1):
        plain=defaultdict(F);joint=defaultdict(F)
        for (r,y),mass in distribution.items():
            plain[y%7**depth]+=mass;joint[r,y%7**depth]+=mass
        m0,m1=max(plain.values()),max(joint.values())
        need(m0<=ALPHA**depth and m1<=PRIVATE*ALPHA**(depth-1),'coloured prefix caps')
        if depth>=2:measured_envelope+=(2*depth+1)*(m0+3*m1)
        caps.append({'depth':depth,'plain_max':str(m0),'joint_max':str(m1)})
    target=6-F(2*(height+2),3**height)
    need(measured_envelope<=upper(height)<target,'coloured full original-label envelope')
    individual=[api.contains_bary_tree({y for r,y in source if r==j},height,5) for j in range(1,5)]
    omitted=[api.contains_bary_tree({y for r,y in source if r!=j},height,5) for j in range(1,5)]
    cells={(r,y%7) for r,y in source}
    joint_ternary=[api.contains_bary_tree({y//7 for r,y in source if (r,y%7)==cell},height-1,3)
                   for cell in cells]
    second=defaultdict(set)
    if height>=2:
        for r,y in source:second[r,y%7].add((y//7)%7)
    return {'height':height,'source_points':len(source),'root_cells':len(cells),
            'all_six_pair_trees':all(pair_checks),'full_five_tree':True,
            'row_masses':list(map(str,row)),'root_maximum':str(root_max),
            'root_upper_bound':str(root_bound),'independent_root_layouts':len(root_values),
            'caps':caps,'actual_prefix_shell_bound':str(measured_envelope),
            'upper':str(upper(height)),'target':str(target),
            'any_individual_five_tree':any(individual),'all_omitted_row_five_trees':all(omitted),
            'every_joint_tail_lacks_ternary':not any(joint_ternary),
            'maximum_second_digits':max(map(len,second.values())) if second else None}


def root_maximum(t):
    """Check all independent root layouts at exact parameter 0<=t<=1."""
    if type(t) not in (int,F) or not 0<=t<=1:
        raise ValueError('t must be an integer or Fraction in [0,1]')
    t=F(t)
    distribution={(r,0):ALPHA*(F(1,4)+(t/12 if r<=3 else -t/4)) for r in range(1,5)}
    distribution.update({(r,r):PRIVATE for r in range(1,5)})
    need(sum(distribution.values())==1,'root law normalization')
    values=[]
    for a,b,u,v in ROOTS:
        values.append(sum(mass*(1+(r==a)+(c==b)+((r,c)==(u,v)))**2
                          for (r,c),mass in distribution.items()))
    expected=F(109,28)+t/14
    need(max(values)==expected,'root maximum formula')
    witness=(1,1,1,1)
    need(values[ROOTS.index(witness)]==expected,'common affine attainer')
    return {'t':str(t),'maximum':str(expected),'layouts':len(values),'attainer':witness}


def upper(height):
    """Return the proved original-layout upper envelope at positive height."""
    _height(height,1)
    g=F(109,28)+F(1,14)*ALPHA**(height-1)
    return g+F(23,28)*sum((2*b+1)*ALPHA**(b-1) for b in range(2,height+1))


def validate_family(height):
    _height(height,1)
    distribution=law(height);source=set(distribution)
    need(all(mass>0 for mass in distribution.values()) and sum(distribution.values())==1,'common law')
    need(len(source)==5**height+2,'source cardinality')
    pair_checks=[api.contains_bary_tree({y for r,y in source if r in pair},height,3)
                 for pair in combinations(range(1,5),2)]
    full_check=api.contains_bary_tree({y for r,y in source},height,5)
    need(all(pair_checks) and full_check,'source tree premises')
    row=[sum(mass for (r,y),mass in distribution.items() if r==j) for j in range(1,5)]
    need(row==[F(1,4)+ALPHA**height/12]*3+[F(1,4)-ALPHA**height/4],'row recursion')
    caps=[]
    for depth in range(1,height+1):
        plain=defaultdict(F);joint=defaultdict(F)
        for (r,y),mass in distribution.items():
            plain[y%7**depth]+=mass;joint[r,y%7**depth]+=mass
        pure_max=max(plain.values());joint_max=max(joint.values())
        need(pure_max==ALPHA**depth,'pure cap is not exact')
        need(joint_max==PRIVATE*ALPHA**(depth-1),'joint cap is not exact')
        caps.append({'depth':depth,'plain_max':str(pure_max),'joint_max':str(joint_max)})
    target=6-F(2*(height+2),3**height)
    u=upper(height)
    closed=F(4059,700)-F(115*height+206,50)*ALPHA**height
    need(u==closed,'closed form mismatch')
    need(u<target,'finite comparison failed')
    return {'height':height,'source_points':len(source),'row_masses':list(map(str,row)),
            'all_six_pair_trees':all(pair_checks),'full_five_tree':full_check,
            'caps':caps,'upper':str(u),'target':str(target),'gap':str(target-u)}


def exact_height_two_layout_maximum(colour=None):
    distribution=coloured_law(2,colour);denom=lcm(*(mass.denominator for mass in distribution.values()))
    units={point:int(mass*denom) for point,mass in distribution.items()}
    all_points=list(product(range(5),range(49)))
    best=-1;witness=None
    for a,b,u,v in ROOTS:
        root=sum(mass*(1+(r==a)+(y%7==b)+((r,y%7)==(u,v)))**2 for (r,y),mass in units.items())
        pure=[0]*49;point={}
        for r,y in all_points:
            mass=units.get((r,y),0)
            base=1+(r==a)+(y%7==b)+((r,y%7)==(u,v))
            point[r,y]=(2*base+1)*mass;pure[y]+=point[r,y]
        # Exactly maximize the two tail phases: the diagonal coincidence
        # is the only correction to the independent additive costs.
        free=max(pure)+max(point.values())
        same=max(pure[y]+point[r,y]+2*units.get((r,y),0) for r,y in all_points)
        score=root+max(free,same)
        if score>best:
            best=score
            if same>=free:
                q=max(all_points,key=lambda q:pure[q[1]]+point[q]+2*units.get(q,0));p=q[1]
            else:
                p=max(range(49),key=lambda y:pure[y]);q=max(all_points,key=lambda q:point[q])
            witness=(a,b,u,v,p,q)
    a,b,u,v,p,q=witness
    literal=sum(mass*(1+(r==a)+(y%7==b)+((r,y%7)==(u,v))+(y==p)+((r,y)==q))**2
                for (r,y),mass in units.items())
    need(literal==best,'literal maximizing layout mismatch')
    exact=F(best,denom)
    need(exact<=upper(2),'actual full square exceeds claimed upper')
    # Independently encode the CRT phases as literal original residues and
    # use the existing certificate evaluator, rather than the local load
    # expansion, to verify the attaining layout on the actual common law.
    def literal_crt(row,residue,modulus):
        return residue+modulus*((row-residue)*pow(modulus,-1,5)%5)
    phases=(0,a,b,literal_crt(u,v,7),p,literal_crt(q[0],q[1],49))
    original_costs=api.evaluate_layout_mixture(2,[(F(1),phases)])
    original_expectation=sum(mass*original_costs[point] for point,mass in distribution.items())
    need(original_expectation==exact,'independent original-divisor witness mismatch')
    return {'exact_gamma':str(exact),'probability_denominator':denom,'root_layouts':1225,
            'tail_phase_pairs_per_root':49*245,'witness':witness,
            'original_divisors':api.original_divisors(2),'original_phases':phases,
            'independent_original_divisor_expectation':str(original_expectation),
            'upper':str(upper(2)),'upper_slack':str(upper(2)-exact),
            'scope':'one explicit common law; tail phases exactly maximized by free/coincidence split'}


def unbalanced_private_law_counterexample():
    """Two good private children per pair do not justify equal private masses.

    This refutes a specified probability-construction rule. It does not
    refute existence of a different common law on the same actual source.
    """
    distribution={(r,7*y):ALPHA*mass for (r,y),mass in law(1).items()}
    for c in (1,2):
        for digit in range(5):distribution[1,c+7*digit]=PRIVATE/5
    for c in (3,4):
        for digit,r in enumerate((2,2,3,3,4)):distribution[r,c+7*digit]=PRIVATE/5
    source=set(distribution)
    need(len(source)==27 and all(mass>0 for mass in distribution.values())
         and sum(distribution.values())==1,'actual unbalanced 27-point supported law')
    private_counts=[]
    for pair in combinations(range(1,5),2):
        need(api.contains_bary_tree({y for r,y in source if r in pair},2,3),
             'unbalanced source pair-ternary condition')
        good=sum(api.contains_bary_tree({y//7 for r,y in source if r in pair and y%7==c},1,3)
                 for c in (1,2,3,4))
        need(good==2,'every pair has exactly two good private children')
        private_counts.append(good)
    need(api.contains_bary_tree({y for r,y in source},2,5),'unbalanced source full-fiveary condition')
    row_one=sum(mass for (r,y),mass in distribution.items() if r==1)
    need(row_one==F(64,147),'unbalanced row-one mass')
    phases=(0,1,1,1,1,1)
    costs=api.evaluate_layout_mixture(2,[(F(1),phases)])
    expectation=sum(mass*costs[point] for point,mass in distribution.items())
    target=F(46,9)
    need(expectation==F(253,49) and expectation-target==F(23,441),
         'literal original-divisor witness refutes this probability rule')
    return {'height':2,'source_points':len(source),'all_source_premises':True,
            'good_private_child_counts':private_counts,'row_one_mass':str(row_one),
            'original_divisors':api.original_divisors(2),'original_phases':phases,
            'independent_original_divisor_expectation':str(expectation),
            'target':str(target),'excess':str(expectation-target),
            'scope':'specified equal-private-mass rule fails; existence of another common law is not refuted'}


def invalid_input_controls():
    rejected=0
    for function in (law,five_leaves,upper,validate_family,coloured_law,validate_coloured_family):
        for height in (True,False,-1,0.0,1.5,'1'):
            try:
                function(height)
            except ValueError:
                rejected+=1
            else:
                raise RuntimeError('invalid height accepted by '+function.__name__)
    for function in (upper,validate_family,validate_coloured_family):
        try:
            function(0)
        except ValueError:
            rejected+=1
        else:
            raise RuntimeError('nonpositive height accepted by '+function.__name__)
    for t in (True,False,0.0,1.5,F(-1),F(2)):
        try:
            root_maximum(t)
        except ValueError:
            rejected+=1
        else:
            raise RuntimeError('invalid root parameter accepted')
    need(law(0)=={(1,0):F(1,3),(2,0):F(1,3),(3,0):F(1,3)},'height-zero constructor')
    for bad in (True,False,-1,4,0.0,'0'):
        try:
            coloured_law(1,lambda h,y:bad)
        except ValueError:
            rejected+=1
        else:
            raise RuntimeError('invalid Klein colour accepted')
    return {'rejected_inputs':rejected,'height_zero_law':'verified',
            'height_types':'int only; bool, float, string and negative values rejected'}


def self_check():
    endpoints=[root_maximum(F(0)),root_maximum(F(1))]
    family=[validate_family(k) for k in range(1,6)]
    coloured=[validate_coloured_family(k) for k in range(1,6)]
    for k in range(6):need(coloured_law(k)==law(k),'constant zero colour recovers original law')
    for item in coloured[1:]:
        need(not item['any_individual_five_tree'] and not item['all_omitted_row_five_trees']
             and item['every_joint_tail_lacks_ternary'],'last-digit fixed-source scope')
    for item in coloured[2:]:need(item['maximum_second_digits']==5,'last-digit sparse-cell scope')
    need([r['gap'] for r in family[:2]]==['1/28','43/1764'],'initial gaps')
    # Symbolic polynomial identity behind monotonicity of the ratio of
    # increments: coefficient arrays are exact integers.
    lhs=[7*5*32-6*3*55,
         7*(2*32+5*23)-6*(2*55+3*23),7*2*23-6*2*23]
    need(lhs==[130,179,46],'increment-ratio polynomial')
    ratio2=F(3*(23*2+32),28*(2*2+3))*F(6,7)**2
    need(ratio2==F(2106,2401)<1,'increment ratio base')
    return {'alpha':str(ALPHA),'private_mass':str(PRIVATE),'root_endpoints':endpoints,
            'family_controls':family,
            'coloured_family_controls':coloured,
            'exact_height_two_layout':exact_height_two_layout_maximum(),
            'exact_coloured_height_two_layout':exact_height_two_layout_maximum(last_digit_colour),
            'unbalanced_private_law_counterexample':unbalanced_private_law_counterexample(),
            'invalid_input_controls':invalid_input_controls(),
            'increment_ratio_base':str(ratio2),'positive_cross_difference_coefficients':lhs,
            'limit_upper':'4059/700','limit_gap':'141/700',
            'scope':'recursive minimum-cardinality families including Klein-four leaf translations; analytic proof and exact controls, no all-source theorem'}


if __name__=='__main__':
    print(json.dumps(self_check(),indent=2,sort_keys=True))
