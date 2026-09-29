#!/usr/bin/env python3
"""Exact rational checks for two original-parent two-depth fee bounds.
Ordinary arithmetic certificate, not a Lean proof. No numerical optimizer.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
import json
if not __debug__:
    raise RuntimeError('Assertions must remain enabled')
J=15
SUP=tuple(range(1,16))
FEE={5:F(7,24),7:F(1,8),11:F(1,24),13:F(1,48),17:F(1,256)}
FB=F(187,384)
def compute(primes):
    M=sum(FEE[p] for p in primes)
    E=FB-M
    density=tuple(1-F(1,p-1)-(F(3,10) if p==5 else F(2,p-1))*E for p in primes)
    b=tuple(1/((p-1)*d) for p,d in zip(primes,density))
    bs=[prod(b[i] for i in range(4) if s>>i&1) for s in range(16)]
    w=[F(0) if s.bit_count()<2 else bs[s] for s in range(16)]
    top=[w[s]+(bs[s] if s else 0) for s in range(16)]
    def recurrence(v):
        z=[F(1)]+[F(0)]*15
        for A in SUP:
            i=A&-A
            z[A]=z[A^i]-sum(v[s]*z[A^s] for s in SUP if s&A==s and s&i)
        return z
    families=[]
    for size in range(5):
        for fam in combinations(SUP,size):
            seen=0
            for s in fam:
                if seen&s:break
                seen|=s
            else:families.append((fam,seen))
    assert len(families)==52
    def direct(v,A):
        return sum((-1)**len(fam)*prod(v[s] for s in fam) for fam,u in families if u&A==u)
    old=recurrence(w); last=recurrence(top)
    for v,z in ((w,old),(top,last)):
        assert all(z[A]==direct(v,A) for A in range(16))
    assert all(x>0 for x in last)
    L=sum(bs[s]*old[J^s] for s in SUP)
    disjoint=lambda S:sum(bs[T]*old[J^(S|T)] for T in SUP if not S&T)
    common={'primes':primes,'fee':M,'unused_descendant_budget':E,'density_lower':density,'b':b,
            'old_residuals':old,'upper_box_residuals':last,'Z0':old[J],'L':L}
    if primes==(5,11,13,17):
        h=M-F(1,3)
        assert h==F(19,768)
        full_shapes=(((3,0,0),1),((2,1,0),0),((2,1,0),1),((2,1,0),2),((1,1,1),0))
        dominance=[256*last[J^s]-57*old[J^s] for s in SUP]
        derivative_upper=[-768*last[J^s]+57*old[J^s]+256*disjoint(s) for s in SUP]
        assert min(dominance)>0 and max(derivative_upper)<0
        exact_min=(768*last[J]+57*old[J]-256*sum(bs[s]*last[J^s] for s in SUP))/2304-L/18
        assert exact_min==F(19521746462501,812093148345600)>0
        rows=[]
        for full,partial in full_shapes[1:]:
            alpha=[F(k,9)+(h if j==partial else 0) for j,k in enumerate(full)]
            maxima=[F(1,9) if k else h if j==partial else F(0) for j,k in enumerate(full)]
            gap=M*old[J]-(max(alpha)+max(maxima)+F(1,18))*L
            assert gap>0
            rows.append({'full_slots':full,'partial_root':partial,'alpha':alpha,'slot_max':maxima,'tangent_margin':gap})
        common.update({'type1_dominance_scaled2304':dominance,'type1_derivative_upper_scaled2304':derivative_upper,
                       'type1_exact_minimum_margin':exact_min,'other_types':rows})
    else:
        assert primes==(7,11,13,17)
        h=M-F(1,9)
        assert h==F(185,2304)
        different=M*old[J]-F(5,18)*L
        derivative_upper=[-M*last[J^s]+F(1,9)*disjoint(s) for s in SUP]
        same=M*last[J]-F(1,9)*sum(bs[s]*last[J^s] for s in SUP)-L/18
        assert different==F(906202683555331,92849814758781696)>0
        assert same==F(13175440576419,2813630750266112)>0
        assert max(derivative_upper)<0
        common.update({'partial_slot_mass':h,'same_root_derivative_upper':derivative_upper,
                       'same_root_minimum_margin':same,'different_roots_tangent_margin':different})
    return common

def encode(obj):
    if isinstance(obj,F):return str(obj)
    if isinstance(obj,(tuple,list)):return [encode(x) for x in obj]
    if isinstance(obj,dict):return {k:encode(v) for k,v in obj.items()}
    return obj
def certificate():
    return {'scope':'Ordinary exact rational certificate for parent 3 and exactly two listed child tuples, using the established FB descendant rectangle, a first-depth Shearer box, and a second-depth conditional union bound. This does not prove arbitrary repeated five-prime recursion or unrestricted Erdos #7.',
            'rows':[compute((5,11,13,17)),compute((7,11,13,17))]}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    result=encode(certificate())
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
