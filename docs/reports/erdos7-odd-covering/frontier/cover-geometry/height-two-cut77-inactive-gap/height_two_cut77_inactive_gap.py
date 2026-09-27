"""Exact cut77 inactive-gap cost inventories and four actual-source controls.
No source is fabricated for impossible k2; no enumeration proves a source theorem.
"""
from itertools import combinations,combinations_with_replacement,product
from collections import Counter,defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import argparse

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output",type=Path,required=True)
args=parser.parse_args()


def require(ok,msg):
    if not ok:raise ValueError(msg)


inventory={}
shapes=list(combinations_with_replacement(range(4),5))
for k in (0,2,4,6,8):
    Z=(56-7*k)//2
    allowed=[s for s in shapes if sum(s)<=10 and (k>0 or min(s)>0)]
    rows=[]
    for ss in combinations_with_replacement(allowed,3):
        if sum(map(sum,ss))!=Z:continue
        if all(sum(a[:3])+sum(b[:3])>=9-k for a,b in combinations(ss,2)):
            rows.append('/'.join(''.join(map(str,s)) for s in ss))
    inventory[k]=rows
require(inventory[4]==['01111/11111/11111'],'unique k4 inventory')
require(inventory[2]==['02222/02222/11111','02222/11111/11222','11111/11222/11222'],'all k2 zero-inclusive inventories')
require(len(inventory[0])==9 and not inventory[6] and not inventory[8],'k0 count and large-public exclusions')
# All partial-child profiles, retaining the cut-inactive original child fibres.
root_shapes=[]
for delta in range(3):
    for costs in combinations_with_replacement(range(4),5-delta):
        contribution=7*delta+2*sum(costs)
        if contribution<=20:
            root_shapes.append((delta,costs,contribution,sum(costs[:3])))
partial_inventory={}
for k in range(9):
    rows=[]
    for rr in combinations_with_replacement(root_shapes,3):
        if not any(r[0] for r in rr):continue
        if k==0 and any(0 in r[1] for r in rr):continue
        if 7*k+sum(r[2] for r in rr)!=56:continue
        if any(a[3]+b[3]<9-k for a,b in combinations(rr,2)):continue
        rows.append([(r[0],''.join(map(str,r[1])),r[2],r[3]) for r in rr])
    if rows:partial_inventory[k]=rows
require(partial_inventory=={3:[[(0,'11111',10,3),(0,'11111',10,3),(1,'1111',15,3)]]},'unique partial-child exact77 inventory')
partial_lower_bounds={}
lower_shapes=[(d,p,7*d+2*p+2*(2-d)*((p+2)//3)) for d in range(3) for p in range(10)]
lower_shapes=[r for r in lower_shapes if r[2]<=20]
for k in range(9):
    rows=[rr for rr in combinations_with_replacement(lower_shapes,3)
          if any(r[0] for r in rr) and all(a[1]+b[1]>=9-k for a,b in combinations(rr,2))]
    partial_lower_bounds[k]=min(sum(r[2] for r in rr) for rr in rows)
require(list(partial_lower_bounds.values())==[55,51,45,35,33,29,25,21,17],'rounded lower-budget table')
# If two public leaves occupy one K column, tight6 at11222 gives exactly
# these two token shapes, up to naming the other column L.
V=[(2,0),(1,1),(0,2)]
solutions=[]
for u,v in combinations_with_replacement(((1,0),(0,1)),2):
    for d in V:
        if tuple(2*(j==0)+u[j]+v[j]+d[j] for j in range(2))==(3,3):
            solutions.append((u,v,d))
require(set(solutions)=={((0,1),(0,1),(1,1)),((1,0),(0,1),(0,2))},'exact k2 K/L decomposition')
require(2*7+2*3+2*3==26>21,'surviving split shape violates original public K cap')


def k4_source(whole):
    G,K,H,J,T=0,1,2,3,5
    public={(G,h) for h in range(7 if whole else 3)}|{(K,0)}
    fibres={(0,c):set(product(range(7),repeat=2)) for c in range(4)}
    for r in (1,2,3):
        for c in range(5):
            private=({(K,c)} if c>0 else set()) if r==1 else {(H if r==2 else J,c)}
            fibres[r,c]=public|private
    tests=0
    for r,s in combinations(range(4),2):
        for cs in combinations(range(4 if r==0 else 5),2 if r==0 else 3):
            for ds in combinations(range(4 if s==0 else 5),2 if s==0 else 3):
                union=set().union(*(fibres[r,c] for c in cs),*(fibres[s,d] for d in ds))
                require(sum(sum(g==i for g,h in union)>=3 for i in range(7))>=3,'actual original pair tree')
                tests+=1
    require(tests==480,'all original pair tests')
    projection=set().union(*fibres.values())
    require(sum(sum(g==i for g,h in projection)>=5 for i in range(7))>=5,'actual standalone tree')
    f=defaultdict(Q)
    for c in range(1,5):f[1,c,K,c]=2
    for r,g in ((2,H),(3,J)):
        for c in range(5):f[r,c,g,c]=2
    for c,w in enumerate((2,2,2,1)):f[1,c,K,0]+=w
    for c in range(3):f[1,c,G,c]+=2
    for c,h,w in ((0,0,2),(1,1,2),(2,2,2),(3,0,2)):f[2,c,G,h]+=w
    for c,h,w in ((0,0,1),(1,1,2),(2,2,2),(3,1,1),(4,2,1)):f[3,c,G,h]+=w
    matrix=((2,2,2,0),(2,2,1,0),(2,1,0,2),(1,0,2,2))
    for c,row in enumerate(matrix):
        for h,w in enumerate(row):
            if w:f[0,c,T,h]+=w
    require(sum(f.values())==77,'explicit integral flow value')
    require(all((g,h) in fibres[r,c] and w>=0 and w.denominator==1 for (r,c,g,h),w in f.items()),'actual integral source support')
    totals={}
    for name,indices,cap in (('root',(0,),21),('child',(0,1),7),('private_column',(0,1,2),6),('entry',(0,1,2,3),2),('public_leaf',(2,3),7),('public_column',(2,),21)):
        sums=defaultdict(Q)
        for p,w in f.items():sums[tuple(p[i] for i in indices)]+=w
        require(all(w<=cap for w in sums.values()),name+' cap')
        totals[name]=sums
    private={(r,c,g,h) for (r,c),ys in fibres.items() if r>0 for g,h in ys-public}
    require(len(private)==14,'fourteen original private leaf edges')
    require(all(r==0 or (g,h) in public or (r,c,g,h) in private for (r,c),ys in fibres.items() for g,h in ys),'complete actual cut cover')
    require(21+28+2*len(private)==77,'matching cut capacity')
    require(totals['public_column'][(G,)]==21 and totals['public_column'][(K,)]==15,'fixed public G/K totals')
    require(totals['public_column'][(H,)]==totals['public_column'][(J,)]==10,'fixed private H/J totals')
    require(all(totals['public_leaf'][(g,h)]==7 for g,h in public if g!=G) and all(f[p]==2 for p in private),'exact private and public-y saturation')
    return dict(public='whole G plus y' if whole else 'three G leaves plus y',points=sum(map(len,fibres.values())),pair_tests=tests,
                flow=77,cut=77,root_totals={str(k[0]):str(v) for k,v in totals['root'].items()},
                active_column_totals={'G':21,'K':15,'H':10,'J':10},
                scope='One actual source and matching flow/cut; no universal inference from this fixture')


def k3_partial_source(whole):
    G,H,J,K,T,R=0,1,2,3,5,6
    public={(G,h) for h in range(7 if whole else 3)}
    fibres={(0,c):set(product(range(7),repeat=2)) for c in range(4)}
    fibres[1,0]=set(product(range(7),repeat=2))
    for c in range(1,5):fibres[1,c]=public|{(H,c)}
    for r,g in ((2,J),(3,K)):
        for c in range(5):fibres[r,c]=public|{(g,c)}
    tests=0
    for r,s in combinations(range(4),2):
        for cs in combinations(range(4 if r==0 else 5),2 if r==0 else 3):
            for ds in combinations(range(4 if s==0 else 5),2 if s==0 else 3):
                union=set().union(*(fibres[r,c] for c in cs),*(fibres[s,d] for d in ds))
                require(sum(sum(g==i for g,h in union)>=3 for i in range(7))>=3,'partial original pair tree')
                tests+=1
    require(tests==480,'partial all original pair tests')
    projection=set().union(*fibres.values())
    require(sum(sum(g==i for g,h in projection)>=5 for i in range(7))>=5,'partial standalone tree')
    f=defaultdict(Q)
    for c in range(1,5):f[1,c,H,c]=2
    for r,g in ((2,J),(3,K)):
        for c in range(5):f[r,c,g,c]=2
    for h in range(3):f[1,0,R,h]=2
    f[1,0,H,0]=1
    for c in range(1,4):f[1,c,G,c-1]=2
    for c,h,w in ((0,0,2),(1,1,2),(2,2,2),(3,0,2)):f[2,c,G,h]+=w
    for c,h,w in ((0,0,1),(1,1,2),(2,2,2),(3,1,1),(4,2,1)):f[3,c,G,h]+=w
    for c,row in enumerate(((2,2,2,0),(2,2,1,0),(2,1,0,2),(1,0,2,2))):
        for h,w in enumerate(row):
            if w:f[0,c,T,h]+=w
    require(sum(f.values())==77,'partial explicit integral flow')
    require(all((g,h) in fibres[r,c] and w>=0 and w.denominator==1 for (r,c,g,h),w in f.items()),'partial actual support')
    totals={}
    for name,indices,cap in (('root',(0,),21),('child',(0,1),7),('private_column',(0,1,2),6),('entry',(0,1,2,3),2),('public_leaf',(2,3),7),('public_column',(2,),21)):
        sums=defaultdict(Q)
        for p,w in f.items():sums[tuple(p[i] for i in indices)]+=w
        require(all(w<=cap for w in sums.values()),'partial '+name+' cap')
        totals[name]=sums
    private={(r,c,g,h) for (r,c),ys in fibres.items() if r>0 and (r,c)!=(1,0) for g,h in ys-public}
    require(len(private)==14,'partial fourteen private leaves')
    require(all(r==0 or (r,c)==(1,0) or (g,h) in public or (r,c,g,h) in private
                for (r,c),ys in fibres.items() for g,h in ys),'partial complete actual cut cover')
    require(21+7+21+2*len(private)==77,'partial matching cut')
    require(totals['root'][(0,)]==21 and totals['child'][(1,0)]==7 and totals['public_column'][(G,)]==21,'partial root-child-public saturation')
    require(all(f[p]==2 for p in private),'partial private leaf saturation')
    require(all(w==0 or g!=G for (r,c,g,h),w in f.items() if r==0 or (r,c)==(1,0)),'partial backward public support carries zero')
    return dict(public='whole G' if whole else 'three G leaves',points=sum(map(len,fibres.values())),pair_tests=tests,
                flow=77,cut=77,root_totals={str(k[0]):str(v) for k,v in totals['root'].items()},
                inactive_child_total=7,maximum_active_block=str(max(v for (r,g),v in
                    {(r,g):sum(w for (rr,c,gg,h),w in f.items() if rr==r and gg==g) for r in (1,2,3) for g in range(7)}.items())),
                scope='One actual partial-child source; all original fibres retained; no universal inference from this fixture')

require(1+Q(614,77)==Q(691,77)<9,'reused same-source consumer arithmetic')
result=dict(result='PASS',necessary_inventory=inventory,partial_inventory=partial_inventory,
            partial_lower_bounds=partial_lower_bounds,k2_two_column_vectors=solutions,
            k4_controls=[k4_source(False),k4_source(True)],
            k3_partial_controls=[k3_partial_source(False),k3_partial_source(True)],
            scope='Necessary integer/vector checks and four actual controls. General proofs are separate; not Lean.')
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
