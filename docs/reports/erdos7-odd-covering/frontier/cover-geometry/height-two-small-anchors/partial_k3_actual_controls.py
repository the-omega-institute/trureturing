#!/usr/bin/env python3
"""Actual complete-source controls for the unrestricted-fifth-child supplier."""
import argparse
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
from collections import defaultdict
import json

def require(t,m):
    if not t:raise RuntimeError(m)

D=(1,5,7,25,35,49,175,245,1225)
N=1615
G,HA,HB,HC,K=0,1,2,3,4

def crt(r,c,g,h):
    a=r+5*c;b=g+7*h
    z=a+25*((b-a)*pow(25,-1,49)%49)
    require(0<=z<1225 and z%25==a and z%49==b,'literal CRT')
    return z

def root_type(r):return 2 if r==0 else 0 if r==1 else 1

def col_type(g):return {G:0,HA:1,HB:2,HC:2,K:3}.get(g,-1)

def upper(d,r,c):
    if d==1:return N
    if d==5:return (635,580,135)[r]
    if d==25:return (215,188,135)[r]
    if c<0:return 0
    if d==7:return (360,320,400,135)[c]
    if d==49:return (120,80,80,45)[c]
    return {35:((180,320,0,135),(180,0,400,0),(0,0,0,135)),
      175:((135,80,0,135),(108,0,80,0),(0,0,0,135)),
      245:((80,80,0,45),(80,0,80,0),(0,0,0,45)),
      1225:((60,80,0,45),(48,0,80,0),(0,0,0,45))}[d][r][c]

def control(whole,geometry,placement):
    public={(G,h) for h in range(7 if whole else 3)}
    fibres={}
    for c in range(4):fibres[1,c]=public|{(HA,c)}
    for r,g in ((2,HB),(3,HC)):
        for c in range(5):fibres[r,c]=public|{(g,c)}
    if geometry=='unrestricted':
        fibres[1,4]=set(product(range(7),repeat=2))
        for c in range(4):fibres[0,c]=set(product(range(7),repeat=2))
    else:
        require(placement=='all_at_fifth','whole-column control placement')
        fibres[1,4]=public|{(K,h) for h in range(7)}
        for c in range(4):fibres[0,c]={(g,h) for g in (G,HA,HB,HC) for h in range(7)}
    require(len(fibres)==19,'all original owners')
    pairs=0
    for r,s in combinations(range(4),2):
        for cs in combinations(range(4 if r==0 else 5),2 if r==0 else 3):
            for ds in combinations(range(4 if s==0 else 5),2 if s==0 else 3):
                U=set().union(*(fibres[r,c] for c in cs),*(fibres[s,c] for c in ds))
                require(sum(sum(g==j for g,h in U)>=3 for j in range(7))>=3,'original pair ternary tree')
                pairs+=1
    require(pairs==480,'all original pair queries')
    U=set().union(*fibres.values())
    require(sum(sum(g==j for g,h in U)>=5 for j in range(7))>=5,'standalone five tree')
    kappa=defaultdict(F)
    for r in (1,2,3):
        children=4 if r==1 else 5
        for c in range(children):
            for h in range(3):kappa[r,c,G,h]+=F(1,9*children)
    require(sum(kappa.values())==1,'one public law')
    for indices,bound in (((0,),F(1,2)),((2,3),F(1,3)),((0,2,3),F(2,9))):
        sums=defaultdict(F)
        for p,w in kappa.items():sums[tuple(p[i] for i in indices)]+=w
        require(max(sums.values())<=bound,'public joint cap')
    nu=defaultdict(F)
    for p,w in kappa.items():nu[p]+=360*w
    private=[]
    for r,g in ((1,HA),(2,HB),(3,HC)):
        for c in range(4 if r==1 else 5):
            p=(r,c,g,c);private.append(p);nu[p]+=80
    require(len({p[:2] for p in private})==14 and len({p[2:] for p in private})==14,'private owners and fine labels')
    exterior=[]
    for h in range(3):
        owner=(1,4) if placement=='all_at_fifth' or (placement=='split' and h==0) else (0,0)
        p=(*owner,K,h);exterior.append(p);nu[p]+=45
    require(sum(nu.values())==N,'one normalized actual law')
    require(all((g,h) in fibres[r,c] for (r,c,g,h) in nu),'actual original owner support')
    numeric={p:crt(*p) for p in nu}
    checks=0
    for d in D:
        sums=[F(0)]*d
        for p,w in nu.items():sums[numeric[p]%d]+=w
        for a,w in enumerate(sums):
            r=root_type(a%5) if d%5==0 and a%5 in range(4) else -1
            c=col_type(a%7) if d%7==0 else -1
            bound=0 if d%5==0 and r<0 else upper(d,r,c)
            require(w<=bound,'literal cylinder table')
            checks+=1
    require(checks==1767,'all numerical cylinders')
    max_moment=F(0)
    for centre in range(1225):
        value=sum(w*sum(z%d==centre%d for d in D)**2 for p,w in nu.items() for z in (numeric[p],))/N
        require(value<=F(2779,323),'centred numerical query control')
        max_moment=max(value,max_moment)
    if geometry=='whole_new_column':
        require(not any(g==K for (r,c),ys in fibres.items() if r==0 for g,h in ys),'no gap exterior K labels')
    return {'public':'whole G' if whole else 'three fine leaves in G','fifth_geometry':geometry,'exterior_placement':placement,'owners':len(fibres),'source_points':sum(map(len,fibres.values())),'original_pairs':pairs,'literal_cylinders':checks,'centred_queries':1225,'centred_max':str(max_moment),'exterior_points':exterior,'source':[{'r':r,'c':c,'g':g,'h':h,'literal_crt':crt(r,c,g,h)} for (r,c),labels in sorted(fibres.items()) for g,h in sorted(labels)],'law':[{'point':p,'literal_crt':numeric[p],'mass':str(w/N)} for p,w in sorted(nu.items())]}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    controls=[control(whole,'unrestricted',placement) for whole in (False,True) for placement in ('all_at_fifth','all_at_gap','split')]
    controls.extend(control(whole,'whole_new_column','all_at_fifth') for whole in (False,True))
    result={'scope':'Eight actual source controls, retaining all original fibres and owners. These finite instances are not a universal theorem or a mincut claim.','controls':controls,'original_pair_checks':sum(x['original_pairs'] for x in controls),'literal_cylinder_checks':sum(x['literal_cylinders'] for x in controls),'centred_query_checks':sum(x['centred_queries'] for x in controls),'PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='controls'}))

if __name__=='__main__':main()
