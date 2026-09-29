#!/usr/bin/env python3
"""Exact shared-column and decorrelated-mask controls on a literal four-root source.
All arithmetic is integral up to final division by24; no optimizer or repo imports.
"""
from itertools import product, combinations
from fractions import Fraction as F
from collections import deque

def require(ok,msg):
 if not ok:raise AssertionError(msg)

def select_distinct_pairs(source):
 """Integral flow: three different children in each root, globally distinct pairs.

 Returns a sufficient source witness, or None. None is not a source-law refutation.
 A child can select a pair only if both literal neighbor columns occur in source.
 """
 neighbors={(r,a):set() for r in range(1,5) for a in range(5)}
 for r,a,y in source:
  require((r,a) in neighbors and y in range(7),'literal carrier input')
  neighbors[r,a].add(y)
 graph={}; original_child_pair=[]
 start=('start',);finish=('finish',)
 def edge(u,v,cap):
  graph.setdefault(u,{})[v]=cap
  graph.setdefault(v,{})[u]=0
 for r in range(1,5):
  root=('root',r);edge(start,root,3)
  for a in range(5):
   child=('child',r,a);edge(root,child,1)
   for pair in combinations(sorted(neighbors[r,a]),2):
    node=('pair',)+pair;edge(child,node,1)
    original_child_pair.append((child,node))
 for pair in combinations(range(7),2):edge(('pair',)+pair,finish,1)
 flow=0
 while flow<12:
  parent={start:None};queue=deque([start])
  while queue and finish not in parent:
   u=queue.popleft()
   for v,cap in graph[u].items():
    if cap>0 and v not in parent:parent[v]=u;queue.append(v)
  if finish not in parent:return None
  v=finish
  while parent[v] is not None:
   u=parent[v];graph[u][v]-=1;graph[v][u]+=1;v=u
  flow+=1
 chosen=[(u[1],u[2],v[1:]) for u,v in original_child_pair if graph[u][v]==0]
 require(len(chosen)==12 and len({pair for r,a,pair in chosen})==12,'twelve distinct pairs')
 require(all(len({a for root,a,pair in chosen if root==r})==3 for r in range(1,5)),
         'three different children per actual root')
 require(all(set(pair)<=neighbors[r,a] for r,a,pair in chosen),'selected pairs occur literally')
 return chosen

def controls():
 fibres={r:tuple((a,y) for a in range(3) for y in (r-1,4+a)) for r in range(1,5)}
 S=tuple((r,a,y) for r,points in fibres.items() for a,y in points)
 require(len(S)==24,'source size')
 bad={}
 for r,points in fibres.items():
  bad[r]=tuple(E for E in combinations(range(7),2)
               if len({a for a,y in points if y not in E})<3)
  require(set(bad[r])=={(r-1,4+a) for a in range(3)},'three literal bad edges')
 require(all(set(bad[r]).isdisjoint(bad[s]) for r in range(1,5) for s in range(r+1,5)),
         'root bad sets are pairwise edge-disjoint')
 require(len({y for r,a,y in S})==7,'all seven columns occur')
 require(all(len({a for a,y in fibres[r]})==3 for r in range(1,5)),
         'each root has only three active children, so no four-matching')
 selected=select_distinct_pairs(S)
 require(selected is not None,'flow finds the sufficient distinct-pair witness')
 forced=tuple((r,a,y) for r in range(1,5) for a in range(3) for y in (0,r))
 require(select_distinct_pairs(forced) is None,'repeated-pair control does not satisfy this certificate')
 
 local={};calls=0
 for r,points in fibres.items():
  for b in range(7):
   for mask in range(16):
    p,m,e,f=(bool(mask&(1<<j)) for j in range(4))
    choices=(range(7) if m else (0,),range(5) if e else (0,),
             tuple(product(range(5),range(7))) if f else ((0,0),))
    best=-1
    for d,u,(v,z) in product(*choices):
     cost=sum((1+p+(y==b)+m*(y==d)+e*(a==u)+f*((a,y)==(v,z)))**2
              for a,y in points)
     if cost>best:best=cost
     calls+=1
    local[r,b,mask]=best
 
 def masks_of(assignment):
  return tuple(sum(1<<j for j in range(4) if assignment[j]==r) for r in range(1,5))
 shared=(-1,None);forgotten=(-1,None)
 for assignment in product(range(1,5),repeat=4):
  masks=masks_of(assignment)
  for b in range(7):
   cost=sum(local[r,b,masks[r-1]] for r in range(1,5))
   if cost>shared[0]:shared=(cost,(b,masks))
  cost=sum(max(local[r,b,masks[r-1]] for b in range(7)) for r in range(1,5))
  if cost>forgotten[0]:forgotten=(cost,masks)
 require(shared[0]==103,'literal common-column maximum')
 require(forgotten[0]==130,'independent per-root column maximum')
 require(F(shared[0],24)<F(46,9)<F(forgotten[0],24),'straddles target')
 
 # Generic same-law cap certificate for four roots, three selected children
 # per root, two selected distinct columns per child, all selected pairs distinct.
 row=F(1,4);child=F(1,12);col=F(1,4);rootcol=F(1,8);atom=F(1,24)
 cap=1+3*col+3*(row+3*rootcol)+5*(child+3*atom)
 require(cap==F(14,3)<F(46,9),'general twelve-distinct-pair certificate')
 # More generally a supplied24-point configuration with at most9 incidences
 # in any column has a sufficient cap; within each root at most3 occur.
 relaxed=1+3*F(9,24)+3*(row+3*rootcol)+5*(child+3*atom)
 require(relaxed==F(121,24)<F(46,9),'general maximum-column-incidence9 certificate')
 print('source=',S)
 print('bad_pairs=',bad)
 print('local_phase_checks=',calls,'shared_outer_checks=',7*4**4)
 print('shared_exact=',F(shared[0],24),'witness=',shared[1])
 print('forgotten_exact=',F(forgotten[0],24),'witness=',forgotten[1])
 print('general_distinct_pairs_bound=',cap,'relaxed_degree9_bound=',relaxed)
 print('PASS: shared b0 is necessary in the mask test; explicit source has no robust root or four-matching. Generic certificates are sufficient, not arbitrary-source claims.')


if __name__ == '__main__':
 controls()
