#!/usr/bin/env python3
"""Original-source controls for the fourteen-private-point supplier."""
import argparse,json
from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import combinations,product
from math import lcm
from pathlib import Path

def need(test,msg):
    if not test:raise RuntimeError(msg)

D=(1,5,7,25,35,49,175,245,1225)
CAPS=tuple(F(v,397) for v in (397,145,100,47,100,30,27,20,20))
def crt(a,b):return next(x for x in range(a,1225,25) if x%49==b)
def tree(labels,n):
    columns=defaultdict(set)
    for y in labels:columns[y%7].add(y)
    live=[sorted(v)[:n] for _,v in sorted(columns.items()) if len(v)>=n]
    return live[:n] if len(live)>=n else None

def root_data(shape,h):
    leaf=lambda j:h+7*j
    if shape=='11111':return [{leaf(j)} for j in range(5)],list(range(5)),[]
    if shape=='11112':return [{leaf(j)} for j in range(4)]+[{leaf(4),6}],list(range(5)),[]
    if shape=='11113':return [{leaf(j)} for j in range(4)]+[set(map(leaf,range(7)))],list(range(4)),[(4,h)]
    if shape=='11122':return [{leaf(j)} for j in range(3)]+[{leaf(3),leaf(0)},{leaf(3),leaf(1)}],list(range(4)),[]
    if shape=='01222':return [set(),{leaf(0)},{leaf(1),leaf(2)},{leaf(1),leaf(3)},{leaf(2),leaf(3)}],[1,2,3,4],[]
    if shape=='1222':return [{leaf(0)},{leaf(1),leaf(2)},{leaf(1),leaf(3)},{leaf(2),leaf(3)}],list(range(4)),[]
    if shape=='01111':return [set()]+[{leaf(j)} for j in range(4)],[1,2,3,4],[]
    if shape=='1111':return [{leaf(j)} for j in range(4)],list(range(4)),[]
    raise RuntimeError(shape)

def fixture(shapes,k):
    active_gap=any(len(s)==4 for s in shapes)
    Q=3;nq=5 if active_gap else 4
    public={7*j for j in range(7)}
    if k==4:public.add(1+7*6)
    fibres={};private={};whole=set();selected=[];sizes={Q:nq}
    for r,shape in enumerate(shapes):
        h=r+1;sets,owners,wc=root_data(shape,h);sizes[r]=len(sets)
        for c,ys in enumerate(sets):private[r,c]=ys;fibres[r,c]=ys|public
        for c,g in wc:whole.add((r,c,g))
        used=set()
        # A matching on the listed actual private owners; enumerate only <=5 rows.
        def match(pos,out):
            if pos==len(owners):return out
            c=owners[pos]
            for y in sorted(y for y in sets[c] if y%7==h and y not in used):
                used.add(y);answer=match(pos+1,out+[(r,c,y)])
                if answer:return answer
                used.remove(y)
            return None
        points=match(0,[]);need(points is not None,'private owner matching')
        selected+=points
    selected=selected[:14];need(len(selected)==14,'fourteen points')
    for c in range(nq):fibres[Q,c]={g+7*j for g in (4,5) for j in range(5)}
    source={(r,c,y) for (r,c),ys in fibres.items() for y in ys}
    projections={r:[set().union(*(fibres[r,c] for c in cs)) for cs in combinations(range(n),n-2)] for r,n in sizes.items()}
    pairs=[]
    for r,s in combinations(range(4),2):
        for i,A in enumerate(projections[r]):
            for j,B in enumerate(projections[s]):
                T=tree(A|B,3);need(T is not None,'original legal pair')
                if r!=Q and s!=Q:need(len((A|B)&{7*j for j in range(7)})>=3,'whole public branch')
                pairs.append((r,s,i,j,T))
    need(len(pairs)==480,'pair count')
    standalone=tree({y for _,_,y in source},5);need(standalone is not None,'standalone five-tree')
    need(len({(r,c) for r,c,y in selected})==14 and len({y for r,c,y in selected})==14,'distinct private owners and fine labels')
    law=defaultdict(F)
    for p in selected:law[p]+=F(20,397)
    for r in range(3):
        for c in range(sizes[r]):
            for j in range(7):law[r,c,7*j]+=F(90,397)*F(1,3*sizes[r]*7)
    exterior=[(Q,0,4+7*j) for j in range(3)]
    for p in exterior:law[p]+=F(9,397)
    need(set(law)<=source and sum(law.values())==1,'actual normalized law')
    numerals={p:crt(p[0]+5*p[1],p[2]) for p in source}
    table={}
    for d,cap in zip(D,CAPS):
        values=[F(0)]*d
        for p,m in law.items():values[numerals[p]%d]+=m
        need(max(values)<=cap,'original numerical cylinder')
        table[str(d)]=list(map(str,values))
    # Complete original network, with all dead private stubs retained.
    side={'s':True,'t':False};edges=[]
    def edge(u,v,cap):edges.append((u,v,cap))
    for r,n in sizes.items():
        R=f'r{r}';side[R]=r!=Q;edge('s',R,21)
        for c in range(n):
            C=f'c{r},{c}';side[C]=r!=Q;edge(R,C,7)
            for g in range(7):
                B=f'b{r},{c},{g}';side[B]=r!=Q and (r,c,g) not in whole;edge(C,B,6)
                for j in range(7):
                    y=g+7*j;L=f'l{r},{c},{y}'
                    side[L]=side[B] and y not in private.get((r,c),set())
                    edge(B,L,2)
                    if y in fibres[r,c]:edge(L,f'p{y}',126)
    for y in range(49):side[f'p{y}']=y in public;edge(f'p{y}',f'g{y%7}',7)
    for g in range(7):side[f'g{g}']=g==0;edge(f'g{g}','t',21)
    crossing=[(u,v,c) for u,v,c in edges if side[u] and not side[v]]
    need(all(c!=126 for _,_,c in crossing),'original bridge crosses')
    cut=sum(c for _,_,c in crossing)
    expected=21+7*k+2*sum(map(int,''.join(shapes)))
    need(cut==expected,'displayed original cut')
    centred=[]
    for a in range(1225):
        value=sum((m*sum(numerals[p]%d==a%d for d in D)**2 for p,m in law.items()),F(0))
        need(value<=F(3572,397),'literal centred query')
        centred.append(str(value))
    return dict(shapes=shapes,public_cost=k,actual_points=len(source),owners=len(fibres),original_pairs=len(pairs),
      cut=cut,network_edges=len(edges),private_points=selected,exterior_points=exterior,standalone=standalone,
      source=[[*p,numerals[p]] for p in sorted(source)],law=[[*p,str(m)] for p,m in sorted(law.items())],
      numerical_cylinders=table,centred_queries=centred,cut_crossings=crossing,original_pair_trees=pairs)

def cost3_exterior_counterexample(whole):
    # G=0, private columns1,2,3, exterior L=4; inactive gap root3.
    G={7*j for j in range(7)};fibres={}
    for c in range(4):fibres[0,c]=G|{1+7*c}
    fibres[0,4]=G|{4+7*j for j in range(7 if whole else 3)}
    for r in (1,2):
        for c in range(5):fibres[r,c]=G|{r+1+7*c}
    gap={1+7*4}|{g+7*j for g in (2,3) for j in range(3)}
    if not whole:gap|={4+7*j for j in (3,4)}
    for c in range(4):fibres[3,c]=gap
    source={(r,c,y) for (r,c),ys in fibres.items() for y in ys}
    projections={r:[set().union(*(fibres[r,c] for c in cs)) for cs in combinations(range(4 if r==3 else 5),2 if r==3 else 3)] for r in range(4)}
    count=0
    for r,s in combinations(range(4),2):
        for A,B in product(projections[r],projections[s]):
            need(tree(A|B,3) is not None,'cost3 counterexample legal pair');count+=1
    standalone=tree({y for _,_,y in source},5);need(standalone is not None,'cost3 counterexample standalone')
    exterior={y for r,c,y in source if r==3 and y%7 not in (0,1,2,3)}
    need(len(exterior)==(0 if whole else 2),'cost3 counterexample inactive exterior count')
    need(count==480,'cost3 counterexample pair count')
    return dict(scope='Counterexample to automatic inactive three-exterior-label property only.',
      private_cost3_form='whole_column' if whole else 'three_fine_leaves',original_pairs=count,
      inactive_exterior_labels=sorted(exterior),standalone=standalone,
      source=[[*p,crt(p[0]+5*p[1],p[2])] for p in sorted(source)])

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    shapes=[('11111','11111','11111'),('11111','11111','11112'),('01222','11111','11111'),
      ('11111','11111','11122'),('11111','11112','11112'),
      ('1222','11111','11111'),('01111','11111','11111'),('1111','11111','11111')]
    controls=[fixture(s,3 if i<6 else 4) for i,s in enumerate(shapes)]
    counters=[cost3_exterior_counterexample(whole) for whole in (True,False)]
    coeff=Counter(lcm(d,e) for d in D for e in D)
    envelope=sum((coeff[d]*cap for d,cap in zip(D,CAPS)),F(0));need(envelope==F(3622,397),'LCM envelope')
    savings=(F(50,397),F(60,397),F(200,397),F(165,397));need(envelope-min(savings)==F(3572,397),'universal query case bound')
    result=dict(scope='Eight supplier controls and two distinct cost3-interface counterexamples; not source exhaustion, minimum-cut certification or Lean.',
      fixtures=len(controls),original_pairs=3840,numerical_cylinders=14136,centred_queries=9800,
      cost3_counterexample_pairs=960,cost3_counterexamples=counters,
      fixed_caps=list(map(str,CAPS)),LCM_coefficients={str(d):coeff[d] for d in D},envelope=str(envelope),
      universal_savings=list(map(str,savings)),universal_bound='3572/397',controls=controls,PASS=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('controls','cost3_counterexamples')}))

if __name__=='__main__':main()
