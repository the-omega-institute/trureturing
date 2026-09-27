#!/usr/bin/env python3
"""Independent exact countercontrol for fixed 431 terminal-law gluing.
No repository imports. This refutes only this law recipe, not source minimax.
"""
from fractions import Fraction as F
from itertools import product, combinations
from collections import Counter

def require(ok, message):
    if not ok:
        raise AssertionError(message)

N9={(a,y):F(1,9) for a,y in product(range(3),repeat=2)}
AT={(0,1):F(1,6),(1,2):F(1,12),(2,2):F(1,12),
    (0,3):F(1,9),(1,3):F(1,9),(2,3):F(1,9),
    (3,0):F(1,6),(4,0):F(1,6)}
for name,law in (('N9',N9),('A_transpose',AT)):
    require(sum(law.values())==1, name+' normalized')
    for rows in combinations(range(5),3):
        for cols in combinations(range(7),5):
            require(any((a,y) in law for a in rows for y in cols), name+' literal rectangle blocker')

def audit(H):
    require(H>=2,'height at least two')
    h=H-1
    leaves=[(r,)+tail for r in (1,2,3) for tail in product(range(3),repeat=h-1)]
    e=(1,)+(0,)*(h-1)
    f=(1,)+(0,)*(h-2)+(1,) if h>=2 else (2,)
    def value(u): return sum(v*5**j for j,v in enumerate(u))
    law={}
    baseline={}
    for u in leaves:
        for (a,y),w in (AT if u==f else N9).items():
            law[value(u)+5**h*a,y]=w/F(3**h)
        for (a,y),w in N9.items():
            baseline[value(u)+5**h*a,y]=w/F(3**h)
    require(sum(law.values())==1,'full law normalized')
    require(len(law)==9*3**h-1,'actual source cardinality')
    def crt(x,y,period):return x+period*((y-x)*pow(period,-1,7)%7)
    pure=[(0,1)]+[(value(e)%5**a,5**a) for a in range(1,H+1)]
    mixed=[(crt(value(e)%5**a,0,5**a),7*5**a) for a in range(H)]
    mixed.append((crt(value(f)+3*5**h,0,5**H),7*5**H))
    labels=pure+mixed
    require(len({m for r,m in labels})==2*(H+1),'distinct original divisor labels')
    common_labels=labels[:-1]
    old_mark=(crt(value(e),0,5**H),7*5**H)
    centered_labels=common_labels+[old_mark]
    old_point=(value(e),0)
    new_point=(value(f)+3*5**h,0)
    require(baseline[old_point]==F(1,3**(H+1)),'old marked atom mass')
    require(new_point not in baseline,'child3 is absent from baseline N9 support')
    require(law[new_point]==F(1,6*3**h),'new marked atom mass under changed law')
    def price(probability,layout):
        return sum(weight*sum(crt(x,y,5**H)%m==r for r,m in layout)**2
                   for (x,y),weight in probability.items())
    direct=F(0)
    histogram=Counter()
    for (x,y),weight in law.items():
        z=crt(x,y,5**H)
        require(z%5**H==x and z%7==y,'literal CRT')
        load=sum(z%m==r for r,m in labels)
        direct+=weight*load**2
        histogram[load]+=weight
    target=2*sum(F(2*a+1,3**a) for a in range(H+1))
    # Stage1: all-N9 law and all centered phases have price2t_H.
    # Stage2: remove the old final mixed hit. Its other load is2H+1,
    # so this loses(4H+3)*3^(-(H+1)). The relocated child3 point has
    # zero baseline mass, so moving the label adds nothing here.
    # Stage3: replace the f fibre by AT. Without the final mixed
    # label its load is(H-1)*(1+1_{y=0}); both fibre laws have
    # column0 mass1/3, so the baseline second moment is unchanged.
    # The new marked atom has mass1/(6*3^h), other load2H-2, and
    # therefore adds(4H-3)/(6*3^h).
    baseline_centered=price(baseline,centered_labels)
    baseline_removed=price(baseline,common_labels)
    baseline_relocated=price(baseline,labels)
    changed_removed=price(law,common_labels)
    removal=F(4*H+3,3**(H+1))
    addition=F(4*H-3,6*3**h)
    require(baseline_centered==target,'centered all-N9 moment equals2t_H')
    require(baseline_centered-baseline_removed==removal,'actual old-hit removal price')
    require(baseline_relocated==baseline_removed,'relocated hit is absent under baseline')
    require(changed_removed==baseline_removed,'fibre replacement preserves common-label price')
    require(direct-changed_removed==addition,'new marked atom contribution')
    expected_gap=addition-removal
    require(expected_gap==F(4*H-15,18*3**h),'simplified general-height difference')
    require(direct-target==expected_gap,'direct labels and analytic all-height identity')
    if H==4:
        require(labels==[(0,1),(1,5),(1,25),(1,125),(1,625),
                        (0,7),(21,35),(126,175),(126,875),(4151,4375)],'height4 label fixture')
        require(direct==F(2845,486) and expected_gap==F(1,486),'height4 strict failure')
        require(all((972*w).denominator==1 for w in law.values()),'common integer denominator')
        print('H4: labels=',labels)
        print('H4: weighted histogram times972=',{k:int(972*v) for k,v in sorted(histogram.items())})
    print('height',H,'points',len(law),'load',direct,'target',target,'gap',expected_gap)

for H in range(2,8):audit(H)
print('PASS: actual robust fibres, normalization, literal CRT, all independent divisor labels, exact gap. No source impossibility claim.')
