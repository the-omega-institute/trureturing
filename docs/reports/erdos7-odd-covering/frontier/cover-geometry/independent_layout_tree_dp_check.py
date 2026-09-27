#!/usr/bin/env python3
"""Independent CRT enumeration, old-K2 comparison, and higher-K DP controls."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import lcm, prod
import json
import random
import sys
sys.path.insert(0,str(Path(__file__).parent))
from independent_layout_tree_dp import IndependentLayoutTreeDP,ResourceLimitError

from concentrated_sharp_source_relabel_transport import family_certificate


def need(ok,message):
    if not ok:raise ValueError(message)


def direct(K,points,weights):
    # Independent full CRT integer, then ordinary integer remainder at every d.
    Q=7**K
    integers=[r+5*((y-r)*pow(5,-1,Q)%Q) if K else r for r,y in points]
    moduli=[d for j in range(K+1) for d in (7**j,5*7**j)]
    choices=[sorted({x%d for x,w in zip(integers,weights) if w}) for d in moduli]
    best=-1
    for phases in product(*choices):
        score=sum(w*sum(x%d==a for d,a in zip(moduli,phases))**2 for x,w in zip(integers,weights))
        best=max(best,score)
    return F(best,sum(weights)),prod(len(c) for c in choices)


def run():
    rng=random.Random(415);tiny=[]
    for K in range(4):
        for case in range(3):
            points=rng.sample(list(product(range(1,5),range(7**K))),3)
            weights=[rng.randrange(1,9) for _ in points]
            if case==2:weights[0]=0
            result=IndependentLayoutTreeDP(K,points).separate(weights)
            expected,count=direct(K,points,weights)
            need(result['value']==expected,'independent CRT brute-force mismatch')
            tiny.append({'height':K,'case':case,'value':str(expected),'layouts':count})
    points=[(1,7*i) for i in range(7)]+[(1,1)];weights=[1]*7+[3]
    separate=IndependentLayoutTreeDP(2,points).separate(weights)
    actual,layouts=direct(2,points,weights)
    coherent=F(max(sum(w*(2+2*(y%7==a%7)+2*(y==a))**2 for (r,y),w in zip(points,weights))
                   for a in range(49)),sum(weights))
    need(separate['value']==actual==16 and coherent==F(72,5),'independent-prefix control failed')
    families=[]
    for K in (2,3,4):
        law=family_certificate(K)['nu'];pts=list(law)
        D=lcm(*(x.denominator for x in law.values()));ws=[int(D*law[p]) for p in pts]
        result=IndependentLayoutTreeDP(K,pts).separate(ws,max_states=300000,max_operations=5000000)
        if K==2:need(result['value']==F(10483,1755),'known literal height-two family value mismatch')
        counts=[]
        for j in range(K+1):counts.extend([len({y%7**j for r,y in pts}),len({(r,y%7**j) for r,y in pts})])
        result={k:str(v) if isinstance(v,F) else v for k,v in result.items() if k!='point_costs'}
        result['active_phase_combinations']=prod(counts);families.append(result)
    pts=list(product(range(1,5),range(343)))
    dense=IndependentLayoutTreeDP(3,pts).separate([1]*len(pts))
    need(dense['value']==F(7,4)*sum((F(2*j+1,7**j) for j in range(4)),F())==F(19,7),'dense uniform original-LCM control')
    invalid=[('boolean_height',lambda:IndependentLayoutTreeDP(True,[(1,0)])),
             ('malformed_point',lambda:IndependentLayoutTreeDP(1,[1])),
             ('duplicate_point',lambda:IndependentLayoutTreeDP(1,[(1,0),(1,0)])),
             ('row_zero',lambda:IndependentLayoutTreeDP(1,[(0,0)])),
             ('negative_weight',lambda:IndependentLayoutTreeDP(1,[(1,0)]).separate([-1])),
             ('zero_total',lambda:IndependentLayoutTreeDP(1,[(1,0)]).separate([0])),
             ('float_weight',lambda:IndependentLayoutTreeDP(1,[(1,0)]).separate([1.])),
             ('boolean_limit',lambda:IndependentLayoutTreeDP(1,[(1,0)]).separate([1],max_states=True))]
    rejected=[]
    for name,operation in invalid:
        try:operation()
        except ValueError:rejected.append(name)
        else:raise ValueError('invalid input accepted: '+name)
    oracle=IndependentLayoutTreeDP(2,[(1,0),(2,1)])
    for name,kwargs in [('state_limit',{'max_states':1}),('operation_limit',{'max_operations':1})]:
        try:oracle.separate([2,3],**kwargs)
        except ResourceLimitError:rejected.append(name)
        else:raise ValueError('requested resource limit ignored')
    need(oracle.separate([2,3])['value']==direct(2,[(1,0),(2,1)],[2,3])[0],'failed solve contaminated oracle')
    return {'tiny_controls':tiny,'independent_prefix_control':{'exact':'16','coherent':'72/5','direct_layouts':layouts},
            'families':families,'dense_K3':{k:str(v) if isinstance(v,F) else v for k,v in dense.items()
                                           if k not in ('point_costs','layout')},'rejected_inputs':rejected}


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
