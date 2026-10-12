---
slug: shapiro-2026-unweighted-fourth-moment-inversion
bibkey: shapiro2026spectrum
doi: null
url: https://arxiv.org/abs/2605.17501v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.result
---

## Problem

Boris Shapiro, “The (n−2,2)-Spectrum of a Graph”, arXiv:2605.17501v2,
Section 12, Outlook item 1:

> Compute an explicit closed formula for the unweighted fourth moment and invert it, modulo Laplacian and cubic data, on the finite list of four-edge support forests. The degree-three inversion is complete by the cubic inversion theorem above.

This settlement refutes the inversion implication SHAP-1 of #14353. It does
not assert that an explicit fourth-moment formula is impossible.
The source locator is `Library/GraphInvariants/shapiro2026spectrum.md`.

## Motivation

The character is $\chi(\sigma)=\binom{c_1(\sigma)}2+c_2(\sigma)-c_1(\sigma)$.
The moment $M_r^{(2)}(G)$ is the sum of this character over all ordered
$r$-tuples of graph edges, with each edge acting by its endpoint transposition.
The count $N_H(G)$ counts edge subsets whose endpoint graph is isomorphic to
$H$; it does not impose ambient inducedness.

## Gap

SHAP-1 asks whether trees of the same order with equal Laplacian
characteristic polynomials, equal $N_F$ for every forest without isolated
vertices with at most three edges, and equal $M_2^{(2)},M_3^{(2)},M_4^{(2)}$
must have equal $N_F$ for every four-edge forest without isolated vertices.
The lower-count condition uses every such forest, not only connected ones.

## Route

The supporting module `SupportAndEdgeWordReflection` proves
`twoPoints_card` by permutation cycle induction and `evalMoment_sound` by
sound reflection of the literal edge-word sum. The settling module
`ShapiroQuarticInversionRefutation` uses the twelve-vertex trees

$E(A)=\{(0,5),(0,10),(0,11),(0,1),(1,2),(2,3),(3,4),(5,6),(5,9),(6,7),(6,8)\}$,

$E(B)=\{(0,8),(0,1),(1,2),(1,5),(1,7),(2,3),(2,4),(5,6),(8,9),(9,10),(9,11)\}$.

`result : ¬ claim` uses a rational invertible Laplacian intertwiner,
explicit bijections between edge-subset enumerations through three edges,
and reflected moment certificates. Every instance belongs to this base pair.

## Falsifier

The path $P_5$ has four edges, is acyclic and has no isolated vertex.
The private declarations `A_P5` and `B_P5` establish
$N_{P_5}(A)=12$ and $N_{P_5}(B)=10$.
`result` applies the universal inversion implication to this pair and this
forest, obtaining the contradiction $12=10$.

## Evidence

Kernel-checked in the settling module: both graphs are trees, their Laplacian
characteristic polynomials agree, every lower support count agrees, and their
moments are $M_2^{(2)}=3164$, $M_3^{(2)}=26730$, $M_4^{(2)}=234836$.
The axiom closure of each public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The computations below use exact integer arithmetic and SymPy; they are
computed evidence, not additional Lean declarations.

## Triage

### What the settlement shows

- **Proved in this module:** `result` refutes SHAP-1 for the displayed base
  pair. Equal Laplacian, cubic and unweighted quartic data do not determine
  every four-edge support count.
- **Computed mechanism:** in the order $K_{1,4}$, the five-vertex tree of
  degrees $(3,2,1,1,1)$, $P_5$, $P_4+K_2$, $K_{1,3}+K_2$, $2P_3$,
  $P_3+2K_2$, $4K_2$, the realizable difference $N_F(B)-N_F(A)$ is
  $(0,0,-2,4,0,2,-6,2)$. The degree-four character coefficients are
  $(336,336,336,240,240,216,168,144)$, whose dot product with that
  difference is zero. A four-distinct-edge word on a forest has one
  permutation cycle on each nontrivial component; the $4!$ orderings give
  the displayed coefficients. The lower support contributions agree.
  Thus the unweighted sum loses information that the individual counts retain.
- **Paper argument; open extension:** attaching $k$ pendant vertices at
  each of the twelve original vertices has order $12+12k=12(k+1)$,
  contradicting the stated order $12+k$ for $k>0$. The proposed family is
  false as stated. Whether infinitely many pairs satisfying SHAP-1's
  hypotheses and differing in a four-edge count exist remains **open**;
  no uniform extension is proved here.
- **Computed full-spectrum comparison:** $M_5^{(2)}(A)=2123466$ and
  $M_5^{(2)}(B)=2123306$, with difference $160$. Hence this base pair has
  different full $(n-2,2)$-spectra. The computation uses the action on
  two-element vertex subsets minus the vertex action. For each permutation
  the two traces are $\binom{c_1}2+c_2$ and $c_1$, so their difference is
  exactly the source character. Trace of the fifth power sums the same
  character over edge words. Equal spectra would imply equal fifth moments.
- **Paper argument:** Shapiro's Conjectures 1 and 2 and the Subtree
  separation form use all moments. This refutation of recovery from data
  through degree four does not refute them; the fifth moment separates the
  displayed pair. The explicit closed fourth-moment formula is a separate
  part of Outlook item 1 and remains **open in this delivery**.

### Reproducible computations

The tested scope is precisely the displayed two trees on twelve vertices,
all edge subsets through four edges, and moments of orders two through five.
The forest degree-sequence classification below is used only for four-edge
forests, where it distinguishes the eight types. No assertion about larger
supports or a uniform family is made. Install `sympy` for the scripts.

#### Base-pair recomputation

Command: `python3 /tmp/op-shapiro/check.py`. Exit: 0.

SHA-256: `199ff43d538b58e9cd4ae8a464b2c934be3216d3d60ed0226d3196796fbccf53`. Save the exact fenced source as the named script;
create its output directory when the program uses an absolute path.

```python
import itertools, sympy as sp
from math import comb
A=[(0,5),(0,10),(0,11),(0,1),(1,2),(2,3),(3,4),(5,6),(5,9),(6,7),(6,8)]
B=[(0,8),(0,1),(1,2),(1,5),(1,7),(2,3),(2,4),(5,6),(8,9),(9,10),(9,11)]
def lap(E,n):
    L=sp.zeros(n)
    for a,b in E: L[a,a]+=1;L[b,b]+=1;L[a,b]-=1;L[b,a]-=1
    return L
def perm_of(tr,n):
    p=list(range(n)); a,b=tr; p[a],p[b]=p[b],p[a]; return p
def compose(p,q): return [p[q[i]] for i in range(len(q))]
def chi(p):
    n=len(p);seen=[False]*n;c1=c2=0
    for i in range(n):
        if not seen[i]:
            l=0;j=i
            while not seen[j]: seen[j]=True;j=p[j];l+=1
            if l==1:c1+=1
            elif l==2:c2+=1
    return comb(c1,2)+c2-c1
def moment(E,n,r):
    s=0
    for tup in itertools.product(E,repeat=r):
        p=list(range(n))
        for t in tup: p=compose(p,perm_of(t,n))
        s+=chi(p)
    return s
def pathcount(E,n,k):
    # number of edge subsets of size k forming a path P_{k+1}
    cnt=0
    for S in itertools.combinations(E,k):
        deg={}
        for a,b in S: deg[a]=deg.get(a,0)+1; deg[b]=deg.get(b,0)+1
        if len(deg)!=k+1 or max(deg.values())>2: continue
        par={v:v for v in deg}
        def f(v):
            while par[v]!=v: v=par[v]
            return v
        for a,b in S: par[f(a)]=f(b)
        if len({f(v) for v in deg})==1: cnt+=1
    return cnt
def extend(E,n,k):
    # attach k leaves uniformly? test: attach k pendant leaves to vertex 4 in A and its correspondent? use same label pattern: attach to all leaves? simple: attach k leaves to vertex 0? (seat: 'uniformly attaching k leaves')
    return E,n
x=sp.symbols('x')
for name,E in (('A',A),('B',B)):
    n=12
    print(name,'charpoly',sp.expand(lap(E,n).charpoly(x).as_expr()))
    print(name,'M2',moment(E,n,2),'M3',moment(E,n,3))
for name,E in (('A',A),('B',B)):
    print(name,'M4',moment(E,12,4),'P5',pathcount(E,12,4))
```

#### Probe support and edge-word recomputation

Command: `python3 /tmp/op-shapiro/probe-r1/check-independent.py`. Exit: 0.

SHA-256: `168f11818f12cda7cc49a51a57378a9432c2e5b92ee1074346298cc9a78d7bf9`. Save the exact fenced source as the named script;
create its output directory when the program uses an absolute path.

```python
import sys,pathlib,json,itertools,collections
sys.path.insert(0,'/tmp/op-shapiro/probe-r1/pydeps')
import sympy as sp
A=[(0,5),(0,10),(0,11),(0,1),(1,2),(2,3),(3,4),(5,6),(5,9),(6,7),(6,8)]
B=[(0,8),(0,1),(1,2),(1,5),(1,7),(2,3),(2,4),(5,6),(8,9),(9,10),(9,11)]
def lap(E,n):
 L=sp.zeros(n)
 for a,b in E:L[a,a]+=1;L[b,b]+=1;L[a,b]-=1;L[b,a]-=1
 return L
def ptype(p):
 seen=set();ls=[]
 for v in range(len(p)):
  if v not in seen:
   j=v;l=0
   while j not in seen:seen.add(j);l+=1;j=p[j]
   ls.append(l)
 return tuple(sorted(ls))
def moment_hist(E,n,r):
 hist=collections.Counter()
 for w in itertools.product(range(len(E)),repeat=r):
  p=list(range(n))
  for i in w:
   a,b=E[i];p[a],p[b]=p[b],p[a]
  hist[ptype(p)]+=1
 chi=lambda t:sp.binomial(t.count(1),2)+t.count(2)-t.count(1)
 return int(sum(c*chi(t) for t,c in hist.items())),{str(t):c for t,c in sorted(hist.items())}
def forest_code(E):
 adj={v:set() for e in E for v in e}
 for a,b in E:adj[a].add(b);adj[b].add(a)
 def rooted(v,par):return '('+''.join(sorted(rooted(w,v) for w in adj[v] if w!=par))+')'
 comps=[];seen=set()
 for v in adj:
  if v not in seen:
   todo=[v];vs=[]
   while todo:
    x=todo.pop()
    if x in seen:continue
    seen.add(x);vs.append(x);todo.extend(adj[x]-seen)
   comps.append(min(rooted(x,None) for x in vs))
 return '|'.join(sorted(comps))
def subsets(E,r):
 h=collections.Counter(forest_code([E[i] for i in S]) for S in itertools.combinations(range(len(E)),r))
 return dict(sorted(h.items()))
def p5(E,n):
 adj=[set() for _ in range(n)]
 for a,b in E:adj[a].add(b);adj[b].add(a)
 pairs=[]
 for v in range(n):
  d={v:0};todo=[v]
  while todo:
   a=todo.pop(0)
   for b in adj[a]:
    if b not in d:d[b]=d[a]+1;todo.append(b)
  pairs.extend((v,w) for w in range(v+1,n) if d[w]==4)
 return pairs
x=sp.Symbol('x');data={}
for nm,E in [('A',A),('B',B)]:
 d={'edges':E,'lap':[[int(v) for v in row] for row in lap(E,12).tolist()],'charpoly_coeffs':[int(c) for c in lap(E,12).charpoly(x).all_coeffs()],'forests':{r:subsets(E,r) for r in range(5)},'moments':{r:moment_hist(E,12,r) for r in [2,3,4]},'p5_pairs':p5(E,12)}
 data[nm]=d
 print(nm,'charpoly',d['charpoly_coeffs'],'moments',{r:m[0] for r,m in d['moments'].items()},'P5',len(d['p5_pairs']),flush=True)
 print(nm,'low forest hist',d['forests'],flush=True)
assert data['A']['charpoly_coeffs']==data['B']['charpoly_coeffs']
for r in range(4):assert data['A']['forests'][r]==data['B']['forests'][r]
for r in [2,3,4]:assert data['A']['moments'][r][0]==data['B']['moments'][r][0]
assert len(data['A']['p5_pairs'])==12 and len(data['B']['p5_pairs'])==10
pathlib.Path('/tmp/op-shapiro/probe-r1/independent-readings.json').write_text(json.dumps(data,indent=2)+'\n')
print('ALL BASE WITNESS READINGS MATCH',flush=True)
```

#### Mechanism and fifth moment

Command: `python3 /Users/auric/.sshx/86b22ae3f3c84a7b76c368b8/attempt-1/stageb/IndependentFiniteChecks.py`. Exit: 0.

SHA-256: `97327e32651b05e15a6748447c5dc5472570f6b16080b921e6bb742c11a700a6`. Save the exact fenced source as the named script;
create its output directory when the program uses an absolute path.

```python
from itertools import combinations
from collections import Counter
from math import comb,factorial
from pathlib import Path
import json,sympy as sp
A=[(0,5),(0,10),(0,11),(0,1),(1,2),(2,3),(3,4),(5,6),(5,9),(6,7),(6,8)]
B=[(0,8),(0,1),(1,2),(1,5),(1,7),(2,3),(2,4),(5,6),(8,9),(9,10),(9,11)]
def matrices(edges,n):
    pairs=list(combinations(range(n),2)); index={e:i for i,e in enumerate(pairs)}
    pair=sp.zeros(len(pairs));vertex=sp.zeros(n)
    for a,b in edges:
        def tau(v):return b if v==a else a if v==b else v
        for j,v in enumerate(range(n)):vertex[tau(v),j]+=1
        for j,(u,v) in enumerate(pairs):pair[index[tuple(sorted((tau(u),tau(v))))],j]+=1
    return pair,vertex
def forest_type(edges):
    adj={}
    for u,v in edges:adj.setdefault(u,set()).add(v);adj.setdefault(v,set()).add(u)
    seen=set();components=[]
    for v in adj:
        if v in seen:continue
        todo=[v];component=[]
        while todo:
            u=todo.pop()
            if u in seen:continue
            seen.add(u);component.append(u);todo.extend(adj[u]-seen)
        components.append(tuple(sorted((len(adj[u]) for u in component),reverse=True)))
    return tuple(sorted(components,reverse=True))
rows={}
for name,edges in [('A',A),('B',B)]:
    pair,vertex=matrices(edges,12)
    pair_trace=int(sp.trace(pair**5));vertex_trace=int(sp.trace(vertex**5));m5=pair_trace-vertex_trace
    hist=Counter(forest_type(s) for s in combinations(edges,4))
    rows[name]={'pair_trace_M5':pair_trace,'vertex_trace_M5':vertex_trace,'M5':m5,'hist':hist}
    print(name,'M5=',m5,'pair_trace=',pair_trace,'vertex_trace=',vertex_trace,flush=True)
types=sorted(set(rows['A']['hist'])|set(rows['B']['hist']))
forest_rows=[]
for key in types:
    diff=rows['A']['hist'][key]-rows['B']['hist'][key]
    fixed=12-sum(map(len,key));twocycles=sum(len(c)==2 for c in key)
    coefficient=factorial(4)*(comb(fixed,2)+twocycles-fixed)
    forest_rows.append({'component_degree_sequences':key,'A':rows['A']['hist'][key],'B':rows['B']['hist'][key],'A_minus_B':diff,'degree_four_character_coefficient':coefficient})
print('forest_rows',json.dumps(forest_rows),flush=True)
print('character_dot_difference',sum(r['A_minus_B']*r['degree_four_character_coefficient'] for r in forest_rows),flush=True)
assert rows['A']['M5']==2123466 and rows['B']['M5']==2123306
assert sum(r['A_minus_B']*r['degree_four_character_coefficient'] for r in forest_rows)==0
out={'M5':{name:{k:v for k,v in row.items() if k!='hist'} for name,row in rows.items()},'four_edge_forests':forest_rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')

order=[((4,1,1,1,1),),((3,2,1,1,1),),((2,2,2,1,1),),((2,2,1,1),(1,1)),((3,1,1,1),(1,1)),((2,1,1),(2,1,1)),((2,1,1),(1,1),(1,1)),((1,1),(1,1),(1,1),(1,1))]
bytype={tuple(tuple(c) for c in row['component_degree_sequences']):row for row in forest_rows}
difference=[-bytype[key]['A_minus_B'] for key in order]
coefficients=[bytype[key]['degree_four_character_coefficient'] for key in order]
assert difference==[0,0,-2,4,0,2,-6,2]
assert sum(c*d for c,d in zip(coefficients,difference))==0
out['brief_order']=['K1,4','five-vertex tree with degrees 3,2,1,1,1','P5','P4 + K2','K1,3 + K2','2P3','P3 + 2K2','4K2']
out['B_minus_A']=difference;out['coefficients']=coefficients;out['dot_product']=0
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('brief_vector_B_minus_A',difference,'coefficients',coefficients,'dot',0,flush=True)
```

## ASSUMED-UNVERIFIED

The infinite-family extension has no proof in this delivery. The fifth-moment
and coefficient computations are exact executable results, with the scope
specified above; their soundness is not formalized in Lean. Information-escape
registration is paused under CLAUDE.md §3.9.
