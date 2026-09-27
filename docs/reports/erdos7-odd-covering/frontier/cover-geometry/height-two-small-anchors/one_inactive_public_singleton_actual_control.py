#!/usr/bin/env python3
"""One complete original c76 source and its fixed 24-point common law.

This is an actual-source construction control, not a minimum-cut assertion or
an exhaustive query/source enumeration. The general proof is separate.
"""
import argparse
from collections import Counter,defaultdict
from fractions import Fraction
from itertools import combinations,product
from math import lcm
from pathlib import Path
import json

def require(condition,message):
    if not condition:raise RuntimeError(message)

def crt(a,m,b,n):
    x=a+m*((b-a)*pow(m,-1,n)%n)
    require(x%m==a%m and x%n==b%n,'CRT mismatch')
    return x

def actual_tree(labels):
    columns=defaultdict(list)
    for label in sorted(labels):columns[label%7].append(label)
    eligible=[g for g,ls in sorted(columns.items()) if len(ls)>=3]
    if len(eligible)<3:return None
    return [columns[g][:3] for g in eligible[:3]]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    fibres={}
    gap=set(g+7*h for g in (4,5) for h in range(5))
    for c in range(4):fibres[0,c]=set(gap)
    private={}
    for r in (1,2,3):
        for c in range(5):
            private[r,c]={r+7*c}
            if c>=2:private[r,c].add(7*r)
            fibres[r,c]={0}|private[r,c]
    source=sorted((r,c,y) for (r,c),ys in fibres.items() for y in ys)
    require(len(source)==79 and len(fibres)==19,'complete source size')
    source_set=set(source)
    restrictions={r:list(combinations(range(4 if r==0 else 5),2 if r==0 else 3)) for r in range(4)}
    pair_trees=[]
    for r,s in combinations(range(4),2):
        for A,B in product(restrictions[r],restrictions[s]):
            labels=set().union(*(fibres[r,c] for c in A),*(fibres[s,c] for c in B))
            tree=actual_tree(labels)
            require(tree is not None,'original legal pair fails')
            pair_trees.append({'roots':[r,s],'children':[A,B],'tree':tree})
    require(len(pair_trees)==480,'all original legal pairs')
    projections={r:set().union(*(fibres[r,c] for c in range(4 if r==0 else 5))) for r in range(4)}
    robust=[]
    for r in range(4):
        robust.append(all(actual_tree(set().union(*(fibres[r,c] for c in A))) is not None for A in restrictions[r]))
    require(not any(robust),'an individual root became robust')
    total_projection=set().union(*projections.values())
    five_columns=[g for g in range(7) if len([y for y in total_projection if y%7==g])>=5]
    require(len(five_columns)>=5,'standalone five-tree absent')
    standalone=[[y for y in sorted(total_projection) if y%7==g][:5] for g in five_columns[:5]]
    law={}
    for r in (1,2,3):
        for c in range(5):law[r,c,r+7*c]=Fraction(1,20)
        for c in range(2,5):law[r,c,7*r]=Fraction(1,36)
    require(len(law)==24 and set(law)<=source_set,'law not on actual points')
    require(sum(law.values())==1,'law not normalized')
    numerals={point:crt(point[0]+5*point[1],25,point[2],49) for point in source}
    require(len(set(numerals.values()))==79,'actual CRT duplicates')
    divisors=(1,5,7,25,35,49,175,245,1225)
    caps=dict(zip(divisors,map(Fraction,('1','1/3','1/4','7/90','1/4','1/12','1/20','1/12','1/20'))))
    cylinder_tables={}
    for d in divisors:
        table=[Fraction(0)]*d
        for point,mass in law.items():table[numerals[point]%d]+=mass
        require(max(table)<=caps[d],f'original modulus {d} cap fails')
        cylinder_tables[str(d)]=[str(x) for x in table]
    require(sum(divisors)==1767,'numerical cylinder count')
    require(all(sum(m for (r,c,y),m in law.items() if y==z)<=Fraction(1,20) for z in range(49) if z%7 in (1,2,3)),'private fine cap')
    require(all(sum(m for (r,c,y),m in law.items() if r==root and y%7==0)<=Fraction(1,12) for root in range(5)),'root/public-column cap')

    # Complete network including unoccupied private fine leaves and all public nodes.
    side={'s':True,'t':False};edges=[]
    def edge(u,v,capacity):edges.append((u,v,capacity))
    for r in range(4):
        root=f'r{r}';side[root]=r!=0;edge('s',root,21)
        for c in range(4 if r==0 else 5):
            child=f'c{r},{c}';side[child]=r!=0;edge(root,child,7)
            for g in range(7):
                branch=f'b{r},{c},{g}';side[branch]=r!=0;edge(child,branch,6)
                for h in range(7):
                    y=g+7*h;leaf=f'l{r},{c},{y}'
                    side[leaf]=r!=0 and y not in private.get((r,c),set())
                    edge(branch,leaf,2)
                    if y in fibres[r,c]:edge(leaf,f'p{y}',126)
    for y in range(49):side[f'p{y}']=y==0;edge(f'p{y}',f'g{y%7}',7)
    for g in range(7):side[f'g{g}']=False;edge(f'g{g}','t',21)
    crossing=[(u,v,c) for u,v,c in edges if side[u] and not side[v]]
    require(all(c!=126 for _,_,c in crossing),'actual bridge crosses cut')
    require(sum(c for _,_,c in crossing)==76,'displayed cut capacity')
    require(Counter(c for _,_,c in crossing)=={21:1,7:1,2:24},'cut term classification')
    require(all(sorted(len(private[r,c]) for c in range(5))==[1,1,2,2,2] for r in (1,2,3)),'private root shape')

    # Literal original phase queries exercising all three-column classification cases.
    query_controls=[]
    representative={'H_private':1,'H_public':0,'outside':6}
    default_point=crt(11,25,7,49)
    for a,b,c in product(representative,repeat=3):
        phases={d:default_point%d for d in divisors}
        phases[49]=representative[a]+7
        phases[7]=representative[b]
        phases[35]=crt(1,5,representative[c],7)
        moment=sum((mass*sum(numerals[p]%d==phases[d] for d in divisors)**2 for p,mass in law.items()),Fraction(0))
        if a!='H_public':saving=Fraction(1,6)
        elif b!='H_public':saving=Fraction(1,6)
        else:saving=Fraction(1,2)
        ceiling=Fraction(163,18)-saving
        require(moment<=ceiling<=Fraction(80,9),'literal numerical query case bound')
        query_controls.append({'column_cases':[a,b,c],'phases':{str(d):phases[d] for d in divisors},'actual_moment':str(moment),'proved_case_ceiling':str(ceiling)})
    result={'scope':'One complete actual-source/cylinder/query control, not source exhaustion or minimum-cut certification.','actual_points':79,'owners':19,'original_legal_pairs':480,'standalone_five_tree':standalone,'individual_roots_robust':robust,'law_atoms':24,'numerical_cylinders':1767,'displayed_cut_capacity':76,'network_edge_count':len(edges),'cut_edges':crossing,'private_shapes':['11222']*3,'source':[{'r':r,'c':c,'fine':y,'x':numerals[r,c,y]} for r,c,y in source],'law':[{'r':r,'c':c,'fine':y,'x':numerals[r,c,y],'mass':str(m)} for (r,c,y),m in sorted(law.items())],'caps':{str(d):str(caps[d]) for d in divisors},'cylinder_tables':cylinder_tables,'original_pair_trees':pair_trees,'literal_query_controls':query_controls,'uniform_general_bound':'80/9','PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','law','cylinder_tables','original_pair_trees','literal_query_controls','cut_edges')}))

if __name__=='__main__':main()
