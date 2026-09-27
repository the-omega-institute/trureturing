#!/usr/bin/env python3
"""Complete c77 source control for the two-public-label common-law supplier."""
import argparse
from collections import Counter,defaultdict
from fractions import Fraction
from itertools import combinations,product
from math import lcm
from pathlib import Path
import json

def require(test,message):
    if not test:raise RuntimeError(message)

def crt(a,m,b,n):return a+m*((b-a)*pow(m,-1,n)%n)

def get_tree(labels,anchor=None):
    groups={g:sorted(y for y in labels if y%7==g) for g in range(7)}
    eligible=[g for g in range(7) if len(groups[g])>=3]
    if len(eligible)<3:return None
    tree=[]
    for g in eligible[:3]:
        chosen=sorted(y for y in (anchor or set()) if y%7==g)
        require(len(chosen)<=3,'too many anchor labels per column')
        chosen+= [y for y in groups[g] if y not in chosen][:3-len(chosen)]
        require(len(chosen)==3 and set(chosen)<=labels,'nonactual normalized tree')
        tree.append(chosen)
    return tree

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    R=1;H=1;J=0;public={0,7};shared=14
    fibres={};private={}
    gap={g+7*h for g in (4,5) for h in range(5)}
    for c in range(4):fibres[0,c]=set(gap)
    for r in (1,2,3):
        for c in range(5):
            private[r,c]={r+7*c}
            if r!=R and c>=2:private[r,c].add(shared)
            fibres[r,c]=public|private[r,c]
    source=sorted((r,c,y) for (r,c),ys in fibres.items() for y in ys)
    source_set=set(source)
    require(len(source)==91 and len(fibres)==19,'source size')
    restrictions={r:list(combinations(range(4 if r==0 else 5),2 if r==0 else 3)) for r in range(4)}
    pair_count=0
    for r,s in combinations(range(4),2):
        for A,B in product(restrictions[r],restrictions[s]):
            union=set().union(*(fibres[r,c] for c in A),*(fibres[s,c] for c in B))
            require(get_tree(union) is not None,'original legal pair fails')
            pair_count+=1
    require(pair_count==480,'complete legal pair count')
    robust=[all(get_tree(set().union(*(fibres[r,c] for c in C))) is not None for C in restrictions[r]) for r in range(4)]
    require(not any(robust),'individual robust root unexpectedly present')
    projection={y for _,_,y in source}
    five_columns=[g for g in range(7) if sum(y%7==g for y in projection)>=5]
    require(len(five_columns)>=5,'standalone tree absent')
    standalone=[[y for y in sorted(projection) if y%7==g][:5] for g in five_columns[:5]]
    anchor=set().union(*(fibres[R,c] for c in (0,1,2)))
    require(anchor=={0,7,1,8,15},'complete original anchor')
    psi=defaultdict(Fraction);constructions=[]
    for q in (0,2,3):
        for selected in restrictions[q]:
            union=anchor|set().union(*(fibres[q,c] for c in selected))
            tree=get_tree(union,anchor)
            require(tree is not None,'paired normalized tree absent')
            survivors=sorted(y for branch in tree for y in branch if y%7!=H and y not in public)
            require(len(survivors)>=4,'too few complete-anchor survivors')
            chosen=survivors[:4]
            require(len(set(chosen))==4 and sum(y%7==J for y in chosen)<=1,'survivor J cap')
            owned=[]
            for y in chosen:
                owners=[c for c in selected if y in fibres[q,c]]
                require(owners,'survivor lacks original other owner')
                point=(q,owners[0],y);owned.append(point)
                psi[point]+=Fraction(1,3*len(restrictions[q])*4)
            constructions.append({'root':q,'restriction':selected,'tree':tree,'selected_actual_points':owned})
    eta={}
    for c in range(5):eta[R,c,R+7*c]=Fraction(1,7)
    eta[R,0,0]=Fraction(1,7);eta[R,1,7]=Fraction(1,7)
    alpha=Fraction(302,477);beta=Fraction(175,477)
    nu={p:alpha*psi.get(p,0)+beta*eta.get(p,0) for p in set(psi)|set(eta)}
    laws={'psi':dict(psi),'eta':eta,'nu':nu}
    for name,law in laws.items():
        require(set(law)<=source_set and sum(law.values())==1,f'{name} actual normalization')
    require(not ({p[2] for p in psi}&{p[2] for p in eta}),'global fine supports overlap')
    require(any(p[0]==2 and p[2]==shared for p in psi) and any(p[0]==3 and p[2]==shared for p in psi),'shared fine label not exercised across roots')
    numerals={p:crt(p[0]+5*p[1],25,p[2],49) for p in source}
    require(len(set(numerals.values()))==91,'numerical CRT collision')
    D=(1,5,7,25,35,49,175,245,1225)
    tables={};checks=0
    for name,law in laws.items():
        tables[name]={}
        for d in D:
            values=[Fraction(0)]*d
            for p,m in law.items():values[numerals[p]%d]+=m
            for residue,value in enumerate(values):
                at_R=d%5==0 and residue%5==R
                rootfree=d%5!=0
                g=residue%7 if d%7==0 else None
                if d==1:p_cap=e_cap=Fraction(1)
                else:
                    p_cap=Fraction(0) if at_R or g==H else {5:Fraction(1,3),7:Fraction(1,4) if g==J else Fraction(3,4),25:Fraction(1,5),35:Fraction(1,12) if g==J else Fraction(1,4),49:Fraction(1,4),175:Fraction(1,20) if g==J else Fraction(3,20),245:Fraction(1,12),1225:Fraction(1,20)}[d]
                    if d%49==0 and residue%49 in public:p_cap=Fraction(0)
                    e_cap=Fraction(0) if (not rootfree and not at_R) or (g is not None and g not in (H,J)) else {5:Fraction(1),7:Fraction(5,7) if g==H else Fraction(2,7),25:Fraction(2,7),35:Fraction(5,7) if g==H else Fraction(2,7),49:Fraction(1,7),175:Fraction(1,7),245:Fraction(1,7),1225:Fraction(1,7)}[d]
                if name=='psi':bound=p_cap
                elif name=='eta':bound=e_cap
                elif d==49:bound=max(alpha*p_cap,beta*e_cap)
                else:bound=alpha*p_cap+beta*e_cap
                require(value<=bound,f'{name} modulus{d} residue{residue} cap failed')
                checks+=1
            tables[name][str(d)]=[str(x) for x in values]
    require(checks==5301,'three complete numerical cylinder tables')

    side={'s':True,'t':False};edges=[]
    def edge(u,v,c):edges.append((u,v,c))
    for r in range(4):
        root=f'r{r}';side[root]=r!=0;edge('s',root,21)
        for c in range(4 if r==0 else 5):
            child=f'c{r},{c}';side[child]=r!=0;edge(root,child,7)
            for g in range(7):
                branch=f'b{r},{c},{g}';side[branch]=r!=0;edge(child,branch,6)
                for h in range(7):
                    y=g+7*h;leaf=f'l{r},{c},{y}'
                    side[leaf]=r!=0 and y not in private.get((r,c),set());edge(branch,leaf,2)
                    if y in fibres[r,c]:edge(leaf,f'p{y}',126)
    for y in range(49):side[f'p{y}']=y in public;edge(f'p{y}',f'g{y%7}',7)
    for g in range(7):side[f'g{g}']=False;edge(f'g{g}','t',21)
    cut=[(u,v,c) for u,v,c in edges if side[u] and not side[v]]
    require(sum(c for _,_,c in cut)==77 and Counter(c for _,_,c in cut)=={21:1,7:2,2:21},'explicit cut77')
    require(not any(c==126 for _,_,c in cut),'actual bridge crosses cut')
    phases_controls=[]
    for reference in [numerals[p] for p in source]:
        phases={d:reference%d for d in D}
        moment=sum((m*sum(numerals[p]%d==phases[d] for d in D)**2 for p,m in nu.items()),Fraction(0))
        require(moment<=Fraction(4252,477),'actual centered original query')
        phases_controls.append({'reference':reference,'phases':{str(d):phases[d] for d in D},'actual_moment':str(moment)})
    result={'scope':'One complete actual-source control; not a minimum-cut assertion, all-source enumeration, or Lean.','actual_points':91,'owners':19,'original_legal_pairs':pair_count,'original_punctures':len(constructions),'numerical_cylinder_checks':checks,'standalone_five_tree':standalone,'individual_roots_robust':robust,'displayed_cut_capacity':77,'network_edges':len(edges),'cut_edges':cut,'source':[{'r':r,'c':c,'fine':y,'x':numerals[r,c,y]} for r,c,y in source],'laws':{name:[{'r':r,'c':c,'fine':y,'x':numerals[r,c,y],'mass':str(m)} for (r,c,y),m in sorted(law.items())] for name,law in laws.items()},'components_weights':{'psi':str(alpha),'eta':str(beta)},'constructions':constructions,'cylinder_tables':tables,'actual_centered_queries':phases_controls,'shared_private_J_label':shared,'general_bound':'4252/477','PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','laws','constructions','cylinder_tables','actual_centered_queries','cut_edges')}))

if __name__=='__main__':main()
