#!/usr/bin/env python3
"""Exact shared-column certificate: one three-child column and three matchings.
Standard library, no repository imports or optimizer. Checks active under-O.
"""
from itertools import product,combinations
from fractions import Fraction as F

def require(ok,message):
 if not ok:raise AssertionError(message)
def bits(mask):return tuple(int(bool(mask&(1<<j))) for j in range(4))
def W(mask,hit):
 p,m,e,f=bits(mask);c=1+p+m+hit
 return (c+e+f)**2+2*c*c

def A(mask,hit):
 p,m,e,f=bits(mask);c=1+p
 return (c+hit+m+e+f)**2+2*c*c

# Each function is three times the normalized local expectation. Independently
# enumerate all literal local phases to check the claimed exact formulas.
local_checks=0
for kind,points,global_columns in (
 ('weak',((0,6),(1,6),(2,6)),((0,0),(6,1))),
 ('matching',((0,0),(1,1),(2,2)),((6,0),(0,1)))):
 for b,hit in global_columns:
  for mask in range(16):
   p,m,e,f=bits(mask);best=-1
   for d,u,(v,z) in product(range(7) if m else (0,),range(5) if e else (0,),
                           tuple(product(range(5),range(7))) if f else ((0,0),)):
    val=sum((1+p+(y==b)+m*(y==d)+e*(a==u)+f*((a,y)==(v,z)))**2 for a,y in points)
    best=max(best,val);local_checks+=1
   require(best==(W(mask,hit) if kind=='weak' else A(mask,hit)),
           'literal local phases give the exact weak/matching formula')

# Strong roots all have the same weight and the same three-point matching
# local kernels. If b!=c, at most two contain b. Adding a hit only increases
# a local kernel; permuting the strong roots then gives the second profile.
profiles=((1,0,0,0),(0,1,1,0))
maxima=[]
for profile in profiles:
 best=-1;winners=[]
 for assignment in product(range(4),repeat=4):
  masks=tuple(sum(1<<j for j in range(4) if assignment[j]==r) for r in range(4))
  price=2*W(masks[0],profile[0])+3*sum(A(masks[r],profile[r]) for r in range(1,4))
  require(price<=165,'one law with masses2/11 and3/11 passes every allocation')
  if price>best:best=price;winners=[masks]
  elif price==best:winners.append(masks)
 maxima.append((best,winners))
require([v for v,ws in maxima]==[163,165],'exact two canonical profile maxima')

# An actual admissible source, with one full-star bad graph and three triangles.
triangles=((0,1,2),(2,3,4),(0,4,5));c=6
require(not set.intersection(*(set(t) for t in triangles)),'no common strong column')
source={(1,a,c) for a in range(3)}
law={(1,a,c):F(2,33) for a in range(3)}
for r,t in enumerate(triangles,2):
 pairs=tuple(combinations(t,2))
 for a,pair in enumerate(pairs):
  for y in pair:source.add((r,a,y))
 chosen=(t[0],t[2],t[1])
 for a,y in enumerate(chosen):
  require(y in pairs[a],'three-column matching belongs to literal triangle support')
  law[r,a,y]=F(1,11)
require(len(source)==21 and len(law)==12 and sum(law.values())==1,'source,law,normalization')
bad={}
for r in range(1,5):
 bad[r]={E for E in combinations(range(7),2)
         if len({a for rr,a,y in source if rr==r and y not in E})<3}
require(bad[1]=={(v,6) for v in range(6)},'weak full-star bad graph')
for r,t in enumerate(triangles,2):require(bad[r]==set(combinations(t,2)),'strong triangle bad graph')
require(all(bad[r].isdisjoint(bad[s]) for r,s in combinations(range(1,5),2)),
        'literal product-tree condition')
require(len({y for r,a,y in source})==7,'standalone seven projection')

def crt(x,y):return x+25*((y-x)*2%7)
labels=(1,5,25,7,35,175);phases=(0,2,7,2,2,107)
price=sum(w*sum(crt(r+5*a,y)%m==phase for m,phase in zip(labels,phases))**2
          for (r,a,y),w in law.items())
require(price==5,'literal attaining six-label layout')
print('local_phase_checks=',local_checks,'canonical_profile_allocations=',2*4**4)
print('profile_maxima_numerator_over33=',maxima)
print('common_law_bound=5; target=46/9; margin=1/9')
print('actual_source=',sorted(source))
print('bad_graphs=',{r:sorted(es) for r,es in bad.items()})
print('positive_law=',[(p,str(w)) for p,w in sorted(law.items())])
print('literal_moduli=',labels,'literal_phases=',phases,'price=',price)
print('PASS: conditional source theorem and exact arithmetic; no unrestricted-source or Lean-certification claim.')
