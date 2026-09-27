"""Exact original-source controls for the two tight-nine capacity78 profiles."""
from argparse import ArgumentParser
from itertools import combinations,product
from fractions import Fraction as Q
from collections import defaultdict
from pathlib import Path
import json

def require(ok,msg):
    if not ok:raise RuntimeError(msg)

# Independent necessary column tests after tight-nine exchange normal form.
H,K,L=0,1,2
def unit(g,m=1):return tuple(m*(i==g) for i in range(7))
def add(*vv):return tuple(sum(v[i] for v in vv) for i in range(7))
LH=unit(L);HH=unit(H);LK=add(unit(L),unit(K));HK=add(unit(H),unit(K))
def counttest(A,B):
    return all(sum(n>=3 for n in add(*(A[i] for i in I),*(B[j] for j in J)))>=3
               for I in combinations(range(5),3) for J in combinations(range(5),3))
finite=[];whole=[]
for kind in (1,2):
    good=[];wholegood=[]
    for W in product(range(4),repeat=7):
        if sum(W)!=3:continue
        A=[LH,LH,LK,LK,W] if kind==1 else [LH,LH,LK,LK,LK]
        B=[HH,HK,HK,HK,HK] if kind==1 else [HH,HK,HK,HK,W]
        if counttest(A,B):good.append(W)
    expected={add(unit(K),unit(L if kind==1 else H),unit(g)) for g in range(7)}
    require(set(good)==expected,'finite third-child column structure')
    for g in range(7):
        W=unit(g,7)
        A=[LH,LH,LK,LK,W] if kind==1 else [LH,LH,LK,LK,LK]
        B=[HH,HK,HK,HK,HK] if kind==1 else [HH,HK,HK,HK,W]
        if counttest(A,B):wholegood.append(g)
    require(not wholegood,'whole third-child impossible')
    finite.append(len(good));whole.append(wholegood)

# Actual sources, retaining original roles A/B/C full and gap root3.
# Four full finite W-column variants at each of the two source shapes.
mat=((2,2,2,0),(2,2,1,0),(2,1,0,2),(1,0,2,2))

def source(kind,extra,high=False):
    H,K,L,M,D,E,T=range(7)
    fibres={}
    if kind==1:
        fibres[0,0]={(L,0)};fibres[0,1]={(L,1)}
        fibres[0,2]={(L,2),(K,0)};fibres[0,3]={(L,3),(K,0)}
        bonus={'H':(H,6),'L':(L,5),'K':(K,5),'M':(M,0)}[extra]
        fibres[0,4]={(L,4),(K,0),bonus}
        fibres[1,0]={(H,0)}
        for c in range(1,5):fibres[1,c]={(H,c),(K,c)}
    else:
        fibres[0,0]={(L,0)};fibres[0,1]={(L,1)}
        for c in range(2,5):fibres[0,c]={(L,c),(K,0)}
        fibres[1,0]={(H,0)}
        for c in range(1,4):fibres[1,c]={(H,c),(K,c)}
        bonus={'H':(H,5),'L':(L,6),'K':(K,0 if high else 5),'M':(M,0)}[extra]
        fibres[1,4]={(H,4),(K,4),bonus}
    for c in range(5):fibres[2,c]=set(product(range(7),repeat=2)) if high else {(D,c),(E,c)}
    for c in range(4):fibres[3,c]=set(product(range(7),repeat=2))
    require([len(fibres[0,c]) for c in range(5)]==([1,1,2,2,3] if kind==1 else [1,1,2,2,2]),'A actual shape')
    require([len(fibres[1,c]) for c in range(5)]==([1,2,2,2,2] if kind==1 else [1,2,2,2,3]),'B actual shape')
    tests=0
    for r,s in combinations(range(4),2):
        for I in combinations(range(4 if r==3 else 5),2 if r==3 else 3):
            for J in combinations(range(4 if s==3 else 5),2 if s==3 else 3):
                S=set().union(*(fibres[r,c] for c in I),*(fibres[s,c] for c in J))
                require(sum(sum(g==i for g,h in S)>=3 for i in range(7))>=3,'original actual legal pair')
                tests+=1
    require(tests==480,'all pair tests')
    allpts=set().union(*fibres.values())
    require(sum(sum(g==i for g,h in allpts)>=5 for i in range(7))>=5,'standalone five tree')
    f=defaultdict(Q)
    for r in (0,1):
        for c in range(5):
            for g,h in fibres[r,c]:f[r,c,g,h]=2
    if high:
        f[1,4,K,0]=1
        for c,row in enumerate(mat):
            for h,w in enumerate(row):
                if w:f[2,c,D,h]=w
    else:
        for c in range(5):
            for g,h in fibres[2,c]:f[2,c,g,h]=2
    for c,row in enumerate(mat):
        for h,w in enumerate(row):
            if w:f[3,c,T,h]=w
    require(sum(f.values())==77,'integral flow77')
    require(all((g,h) in fibres[r,c] and w.denominator==1 and w>=0 for (r,c,g,h),w in f.items()),'actual integer support')
    for name,idx,cap in [('root',(0,),21),('child',(0,1),7),('privatecol',(0,1,2),6),('entry',(0,1,2,3),2),('publicleaf',(2,3),7),('publiccol',(2,),21)]:
        sums=defaultdict(Q)
        for p,w in f.items():sums[tuple(p[i] for i in idx)]+=w
        require(all(v<=cap for v in sums.values()),name+' cap')
    require(sum(len(fibres[r,c]) for r in (0,1) for c in range(5))==18,'private78 count')
    cut78=42+2*18
    if high:
        nonx=[(r,c,g,h) for r in (0,1) for c in range(5) for g,h in fibres[r,c] if (g,h)!=(K,0)]
        require(len(nonx)==14,'public leaf replaces four original private arcs')
        require(sum(f[p] for p in f if p[2:]==(K,0))==7,'public x saturated7')
        cut77=42+7+2*len(nonx)
    else:
        cut77=21+2*sum(len(fibres[r,c]) for r in (0,1,2) for c in range(5))
    require(cut78==78 and cut77==77,'matching source cuts')
    mult=defaultdict(int)
    for r in (0,1):
        for c in range(5):
            for p in fibres[r,c]:mult[p]+=1
    frequent=[p for p,n in mult.items() if n>=3]
    require(len(frequent)<=1 and all(p[0]==K for p in frequent),'only repeated K label')
    if frequent:
        x=frequent[0]
        choices=[c for c in range(2,4 if kind==1 else 5) if x in fibres[0,c]]
        require(len(choices)>=2,'repeated x anchor owners')
        S=fibres[0,0]|fibres[0,choices[0]]|fibres[0,choices[1]]
        require(len([p for p in S if p[0]==L])==3 and S-{p for p in S if p[0]==L}=={x},'actual thin anchor')
    coarse={g:sum(2*n for (gg,h),n in mult.items() if gg==g) for g in range(7)}
    return {'shape':'11223/12222' if kind==1 else '11222/12223','extra':extra,'four_owner_x':high,
            'points':sum(map(len,fibres.values())),'pair_tests':tests,'flow':77,'cuts':[77,78],
            'active_coarse_before_slack':coarse,'max_active_fine_owner_count':max(mult.values())}

controls=[source(kind,extra) for kind in (1,2) for extra in ('H','L','K','M')]
controls.append(source(2,'K',True))
result={'result':'PASS','finite_column_patterns_per_shape':finite,'whole_column_patterns_per_shape':whole,
        'actual_controls':controls,'scope':'Necessary column-pattern checks and nine concrete original sources. General source theorem in separate proof; not Lean.'}
parser=ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
