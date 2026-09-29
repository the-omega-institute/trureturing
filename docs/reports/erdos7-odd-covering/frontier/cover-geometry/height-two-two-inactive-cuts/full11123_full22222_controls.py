"""Full11123/full22222 actual-support bridge and whole-prefix controls.
The controls have matching flow/cut78; no exact77 saturation is assumed.
"""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import combinations,combinations_with_replacement,product
from pathlib import Path
import json


def require(ok,msg):
    if not ok:raise ValueError(msg)


def vector(labels):return tuple(labels.count(i) for i in range(7))


def source_control(whole):
    H,K,L=0,1,2
    fibres={}
    for c in range(3):fibres[0,c]={(H,c)}
    fibres[0,3]={(H,3),(H,4)}
    fibres[0,4]={(H,h) for h in (range(7) if whole else (4,5,6))}
    for c in range(5):fibres[1,c]={(K,c),(L,c)}
    for r in (2,3):
        for c in range(5 if r==2 else 4):fibres[r,c]=set(product(range(7),repeat=2))
    tests=0
    for r,s in combinations(range(4),2):
        for cs in combinations(range(4 if r==3 else 5),2 if r==3 else 3):
            for ds in combinations(range(4 if s==3 else 5),2 if s==3 else 3):
                projection=set().union(*(fibres[r,c] for c in cs),*(fibres[s,c] for c in ds))
                require(sum(sum(g==i for g,h in projection)>=3 for i in range(7))>=3,'original pair tree')
                tests+=1
    require(tests==480,'complete original selected pair tests')
    projection=set().union(*fibres.values())
    require(sum(sum(g==i for g,h in projection)>=5 for i in range(7))>=5,'standalone five-tree')
    psi=defaultdict(Q)
    for r in (1,2,3):
        selections=list(combinations(range(4 if r==3 else 5),2 if r==3 else 3))
        for cs in selections:
            proj=set().union(*(fibres[r,c] for c in cs))
            columns=[g for g in range(7) if g!=H and sum(gg==g for gg,h in proj)>=3]
            require(len(columns)>=2,'actual two outside-H branches')
            for g in columns[:2]:
                hs=sorted(h for gg,h in proj if gg==g)[:3]
                for h in hs:
                    owner=next(c for c in cs if (g,h) in fibres[r,c])
                    psi[r,owner,g,h]+=Q(1,3*len(selections)*6)
    require(sum(psi.values())==1 and all(g!=H for r,c,g,h in psi),'one actual outside-H law')
    nu=defaultdict(Q,{point:Q(6,7)*weight for point,weight in psi.items()})
    for c in range(4):nu[0,c,H,c]+=Q(1,28)
    require(sum(nu.values())==1 and all((g,h) in fibres[r,c] for r,c,g,h in nu),'one actual common probability')
    cap_targets=[Q(1),Q(2,7),Q(3,7),Q(6,35),Q(1,7),Q(1,7),Q(3,35),Q(1,21),Q(1,28)]
    indices=[(),(0,),(2,),(0,1),(0,2),(2,3),(0,1,2),(0,2,3),(0,1,2,3)]
    measured=[]
    for ix,target in zip(indices,cap_targets):
        sums=defaultdict(Q)
        for point,weight in nu.items():sums[tuple(point[i] for i in ix)]+=weight
        cap=max(sums.values())
        require(cap<=target,'common cylinder cap '+str(ix))
        measured.append(cap)
    coeff=(1,3,3,5,9,5,15,15,25)
    require(sum(c*w for c,w in zip(coeff,cap_targets))==Q(249,28),'existing four-H consumer envelope')
    flow=defaultdict(Q)
    for c in range(4):
        for g,h in fibres[0,c]:flow[0,c,g,h]=2
    for h in (4,5,6):flow[0,4,H,h]=2
    for c in range(5):
        for g,h in fibres[1,c]:flow[1,c,g,h]=2
    for r,g in ((2,3),(3,4)):
        for c,row in enumerate(((2,2,2,0),(2,2,1,0),(2,1,0,2),(1,0,2,2))):
            for h,w in enumerate(row):
                if w:flow[r,c,g,h]=w
    require(sum(flow.values())==78,'explicit flow78')
    require(all((g,h) in fibres[r,c] for r,c,g,h in flow),'actual flow support')
    for ix,cap in (((0,),21),((0,1),7),((0,1,2),6),((0,1,2,3),2),((2,3),7),((2,),21)):
        sums=defaultdict(Q)
        for point,weight in flow.items():sums[tuple(point[i] for i in ix)]+=weight
        require(max(sums.values())<=cap,'original flow cap '+str(ix))
    require(2*21+2*(1+1+1+2+3)+2*10==78,'actual forward cut cost')
    require(all(r>=2 or r==1 or (r,c)!=(0,4) or g==H for (r,c),ys in fibres.items() for g,h in ys),'whole cost3 coverage')
    return dict(cost3='whole H column' if whole else 'three H leaves',points=sum(map(len,fibres.values())),pair_tests=tests,
                maximum_flow=78,matching_cut=78,law_caps=list(map(str,measured)),
                measured_envelope=str(sum(c*w for c,w in zip(coeff,measured))),uniform_bound='249/28',
                scope='Actual source control for the support theorem; this fixture has max78, not max77.')


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    solutions=[]
    for s in combinations_with_replacement(range(7),3):
        sv=vector(s)
        for d in combinations_with_replacement(range(7),2):
            dv=vector(d)
            counts=tuple(a+3*b for a,b in zip(sv,dv))
            if all(x in (0,3) for x in counts):
                require(len(set(s))==1 and len(set(d))==2 and s[0] not in d,'balanced-three locking')
                solutions.append((s,d))
    require(len(solutions)==105,'all labelled anchor locking solutions')
    singleton_set=set(range(3))
    valid=0
    for size in range(3):
        for es in combinations(range(7),size):
            E=set(es)
            if all(len(set(pair)|E)>=3 for pair in combinations(singleton_set,2)):
                require(bool(E-singleton_set),'new actual H leaf beyond all singletons')
                valid+=1
    require(valid==22,'all H-neighborhood extension solutions')
    result=dict(result='PASS',column_lock_solutions=len(solutions),double_H_extension_solutions=valid,
                controls=[source_control(False),source_control(True)],
                scope='Finite arithmetic and two actual-source controls; universal support proof supplied separately; not Lean.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
