#!/usr/bin/env python3
"""Exact column-vector and original-LCM controls for the c76 branch.

These checks certify the displayed finite arithmetic, not all actual sources
or the ordinary owner-membership arguments.
"""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from math import lcm
from pathlib import Path
import json

def require(condition,message):
    if not condition:raise RuntimeError(message)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    vectors=[v for v in product(range(5),repeat=7) if sum(v)==4]
    require(len(vectors)==210,'weak composition count')
    neighbours={i:set() for i in range(len(vectors))}
    for i,v in enumerate(vectors):
        for j,w in enumerate(vectors):
            summed=tuple(v[k]+w[k]+(k==0) for k in range(7))
            if sorted(summed)==[0,0,0,0,3,3,3]:neighbours[i].add(j)
    triples=[]
    for i in neighbours:
        for j in neighbours[i]:
            for k in neighbours[i]&neighbours[j]:
                roots=[vectors[x] for x in (i,j,k)]
                private=[]
                for v in roots:
                    require(v[0]==1 and sorted(v[1:])==[0,0,0,0,0,3],'three-pair vector classification')
                    private.append(v.index(3))
                    require(any(entry%2 for entry in v),'even-vector exclusion')
                require(len(set(private))==3,'private columns repeat')
                triples.append(private)
    require(len(triples)==120,'ordered triple count')
    divisors=(1,5,7,25,35,49,175,245,1225)
    caps=dict(zip(divisors,map(Fraction,('1','1/3','1/4','7/90','1/4','1/12','1/20','1/12','1/20'))))
    coefficients=Counter(lcm(d,e) for d in divisors for e in divisors)
    require([coefficients[d] for d in divisors]==[1,3,3,5,9,5,15,15,25],'original LCM coefficients')
    envelope=sum((caps[lcm(d,e)] for d in divisors for e in divisors),Fraction(0))
    require(envelope==Fraction(163,18),'full simultaneous envelope')
    pairs49=[(d,e) for d in divisors for e in divisors if lcm(d,e)==49]
    require(len(pairs49)==5 and all(d==49 or e==49 for d,e in pairs49),'every LCM49 pair contains queried49')
    cases=[]
    for col49,col7,col35 in product(('H_private','H_public','outside'),repeat=3):
        if col49!='H_public':
            saving=5*(Fraction(1,12)-Fraction(1,20));reason='five pure49 terms'
        elif col7!='H_public':
            saving=2*Fraction(1,12);reason='7/49 incompatible'
        elif col35!='H_public':
            saving=2*Fraction(1,4);reason='7/35 incompatible'
        else:
            saving=3*(Fraction(1,4)-Fraction(1,12));reason='35 public-column root cap'
        bound=envelope-saving
        require(bound<=Fraction(80,9),'joint-query saving')
        cases.append({'49':col49,'7':col7,'35':col35,'reason':reason,'saving':str(saving),'bound':str(bound)})
    data={'scope':'Finite vector/LCM arithmetic controls; ordinary complete-source proof is separate; no Lean.','vector_count':len(vectors),'ordered_compatible_root_triples':len(triples),'private_column_triples':triples,'LCM_coefficients':{str(d):coefficients[d] for d in divisors},'LCM49_pairs':pairs49,'mass':str(15*Fraction(1,20)+9*Fraction(1,36)),'envelope':str(envelope),'joint_cases':cases,'uniform_bound':'80/9','strict_margin':'1/9','PASS':True}
    require(data['mass']=='1','common law normalization')
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('private_column_triples','joint_cases')}))

if __name__=='__main__':main()
