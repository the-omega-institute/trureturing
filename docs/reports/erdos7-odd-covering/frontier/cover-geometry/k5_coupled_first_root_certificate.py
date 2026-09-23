#!/usr/bin/env python3
"""Independent exact support-polynomial certificate for one exceptional K5.

Checks arithmetic only; the conditional-Shearer/actual-AP transfer remains
an ordinary mathematical argument. Python 3.10+ and only the standard library.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Assertions must be enabled; do not run with -O.")

P=(5,7,11,13)
ALL=15
FEE={5:F(7,24),7:F(1,8),11:F(1,24),13:F(1,48)}
TOTAL_F=F(187,384)
OUTSIDE=TOTAL_F-sum(FEE.values(),F())
C={5:F(3,10),7:F(2,6),11:F(2,10),13:F(2,12)}
DENS=tuple(1-F(1,q-1)-C[q]*OUTSIDE for q in P)
B=tuple(1/((q-1)*d) for q,d in zip(P,DENS))
N=tuple(b.numerator for b in B)
D=tuple(b.denominator for b in B)
NUM=[prod(N[i] for i in range(4) if s>>i&1) for s in range(16)]
DEN=[prod(D[i] for i in range(4) if s>>i&1) for s in range(16)]
BASE=[0]+[int(s.bit_count()>=2) for s in range(1,16)]
assert OUTSIDE==F(1,128)
assert B==(F(320,957),F(64,319),F(64,575),F(64,703))

@lru_cache(None)
def families(a):
    """Direct enumeration: all pairwise-disjoint nonempty support families.
    Build independently from the first available coordinate: omit it or
    place it in a unique block, then recurse on unused coordinates.
    """
    if not a:
        return ((),)
    low=a&-a
    ans=list(families(a^low))
    s=a
    while s:
        if s&low:
            ans.extend((s,)+f for f in families(a^s))
        s=(s-1)&a
    return tuple(ans)

# Separate direct list from all 2^15 support subsets, not using recurrence.
DIRECT=[]
for allocation in range(1<<15):
    used=0;fam=[]
    for s in range(1,16):
        if allocation>>(s-1)&1:
            if used&s:
                break
            used|=s;fam.append(s)
    else:
        DIRECT.append(tuple(fam))
assert {frozenset(f) for f in families(ALL)}=={frozenset(f) for f in DIRECT}
assert len(DIRECT)==52

TERMS={a:[] for a in range(16)}
for a in range(16):
    for fam in DIRECT:
        used=0
        for s in fam:
            used|=s
        if used&~a:
            continue
        weight=(-1)**len(fam)*NUM[used]*DEN[a^used]
        TERMS[a].append((fam,weight))

def recurrence(coeff):
    z=[0]*16;z[0]=1
    for a in range(1,16):
        low=a&-a;i=low.bit_length()-1
        v=D[i]*z[a^low]
        s=a
        while s:
            if s&low:
                v-=coeff[s]*NUM[s]*z[a^s]
            s=(s-1)&a
        z[a]=v
    return z

def direct(a,coeff):
    return sum(weight*prod(coeff[s] for s in fam) for fam,weight in TERMS[a])

def values(coeff):
    nums=recurrence(coeff)
    assert all(nums[a]==direct(a,coeff) for a in range(16))
    return [F(nums[a],DEN[a]) for a in range(16)]

def certificate():
    OLD=values(BASE)
    FULL=values([0]+[BASE[s]+1 for s in range(1,16)])
    assert all(FULL[a]>F(1,8) for a in range(1,16))
    L=sum((F(NUM[s],DEN[s])*OLD[ALL^s] for s in range(1,16)),F())
    Z0=OLD[ALL]
    TARGET=16*L
    MIN=None;MINVERT=[];vertex_count=0
    for vertex in range(1<<15):
        first=[0]+[BASE[s]+((vertex>>(s-1))&1) for s in range(1,16)]
        second=[0]+[BASE[s]+1-((vertex>>(s-1))&1) for s in range(1,16)]
        n1=recurrence(first)[ALL];n2=recurrence(second)[ALL]
        # Both calculation methods check all 32768 vertices.
        assert n1==direct(ALL,first)
        assert n2==direct(ALL,second)
        gnum=32*n1+13*n2
        assert F(gnum,DEN[ALL])>TARGET
        if MIN is None or gnum<MIN:
            MIN=gnum;MINVERT=[vertex]
        elif gnum==MIN:
            MINVERT.append(vertex)
        vertex_count+=1

    # Derivative wrt y_S: -32 Z_(J\S)(w+y)+13 Z_(J\S)(w+b-y).
    # All residual polynomials are positive on the box; hence monotonicity
    # gives derivative <= -(32 Z_(J\S)(w+b)-13 Z_(J\S)(w)).
    MARGINS={s:32*FULL[ALL^s]-13*OLD[ALL^s] for s in range(1,16)}
    FORCED=[s for s in range(1,16) if s.bit_count()>=2 or s in (1,2)]
    assert all(MARGINS[s]>0 for s in FORCED)
    CASES=[]
    for y11,y13 in product((0,1),repeat=2):
        ys=set(FORCED)
        if y11:ys.add(4)
        if y13:ys.add(8)
        v=sum(1<<(s-1) for s in ys)
        first=[0]+[BASE[s]+int(s in ys) for s in range(1,16)]
        second=[0]+[BASE[s]+int(s not in ys) for s in range(1,16)]
        z1=values(first)[ALL];z2=values(second)[ALL]
        g=32*z1+13*z2
        CASES.append({'singleton11_to_first':bool(y11),'singleton13_to_first':bool(y13),
                      'vertex':v,'Z_first':str(z1),'Z_second':str(z2),'G':str(g),
                      'gap':str(g-TARGET),'gap_times_D0':str((g-TARGET)*DEN[ALL])})
    assert min(F(r['G']) for r in CASES)==F(MIN,DEN[ALL])
    assert all((F(r['G'])>TARGET) for r in CASES)

    # Worst two-coordinate residual derivative bound is at primes5,7.
    PAIR_LOWER=19-32*(B[0]+B[1])-19*B[0]*B[1]
    ONE_LOWER=19-32*B[0]
    assert PAIR_LOWER>0 and ONE_LOWER>0
    for a in range(1,16):
        if a.bit_count()==2:
            assert 32*FULL[a]-13*OLD[a]>=PAIR_LOWER
        elif a.bit_count()==1:
            assert 32*FULL[a]-13*OLD[a]>=ONE_LOWER

    # Existing fee and root-reserve bookkeeping, in original Haar.
    block_fee=F(15,32)
    root_reserve=1-F(1,2)-block_fee-OUTSIDE
    assert block_fee<sum(FEE.values(),F())
    assert root_reserve==F(3,128)>0

    out={
     'scope':'Ordinary exact rational certificate for the coupled-first-root polynomial on the complete FB descendant rectangle. No Lean verification and no unrestricted Erdos#7 conclusion.',
     'primes':P,'fees':{str(q):str(FEE[q]) for q in P},'total_F':str(TOTAL_F),'outside_expense':str(OUTSIDE),
     'descendant_multipliers':{str(q):str(C[q]) for q in P},
     'density_lower':list(map(str,DENS)),'b':list(map(str,B)),'D0':DEN[ALL],
     'positivity':{str(a):str(FULL[a]) for a in range(1,16)},
     'old_Z':{str(a):str(OLD[a]) for a in range(16)},'Z0':str(Z0),'L':str(L),'16L':str(TARGET),
     'direct_disjoint_families':len(DIRECT),'vertex_count':vertex_count,
     'minimum_G':str(F(MIN,DEN[ALL])),'minimum_gap':str(F(MIN,DEN[ALL])-TARGET),
     'minimizing_vertices':MINVERT,
     'forced_derivative_margins':{str(s):str(MARGINS[s]) for s in FORCED},
     'two_residual_worst_margin':str(PAIR_LOWER),'one_residual_worst_margin':str(ONE_LOWER),
     'four_cases':CASES,'block_fee':str(block_fee),'root_coordinate_reserve':str(root_reserve),
     'checks':'All15 residual positivities and all32768 allocations agree between integer recurrence and direct52-family enumeration. Four-case analytic derivative reduction independently has same minimum.'
    }
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
    args=parser.parse_args()
    out=certificate()
    args.output.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    keys=("density_lower","b","D0","Z0","L","minimum_G","minimum_gap","minimizing_vertices","vertex_count","four_cases","root_coordinate_reserve")
    print(json.dumps({k:out[k] for k in keys},indent=2))


if __name__=="__main__":
    main()
