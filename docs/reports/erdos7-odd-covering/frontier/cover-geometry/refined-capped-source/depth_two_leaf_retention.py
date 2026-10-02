#!/usr/bin/env python3
"""Exact fixed-profile retained-leaf source certificates; no whole-profile scan."""
from fractions import Fraction as Q
from itertools import combinations,product
from collections import Counter
from math import prod
from pathlib import Path
import json
import argparse
import runpy

checks=0
def chk(b,m):
 global checks
 checks+=1
 if not b:raise ValueError(m)
P=(5,7,11,13,17,19,23)
roles=tuple((r,l)for r in range(2)for l in range(5))
group=(0,0,1,1,1)
rolevec=tuple(tuple(1+int(group[i]==r)+int(i==t)for i in range(5))for r,t in roles)
supports=tuple(frozenset(s)for k in range(2,8)for s in combinations(range(7),k))
edges=tuple((s,t)for s,t in combinations(supports,2)if s.isdisjoint(t))
triples=tuple((s,t,u)for s,t,u in combinations(supports,3)if s.isdisjoint(t)and s.isdisjoint(u)and t.isdisjoint(u))
deg=Counter(s for edge in edges for s in edge)
chk((len(supports),len(edges),len(triples))==(120,546,210),'support inventories')
a=Q(525243426,2350861343);b=(1-2*a)/3;w=(a,a,b,b,b)
profiles={'first':(((1,2),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1)),(1,1,0,1,1)),'opposite':(((0,0),(1,2),(1,3),(1,4),(1,3),(1,4),(1,4)),(0,1,1,1,1))}
bs=tuple(Q(1,p-2)for p in P)

def mass(profile,mask):
 weights=tuple(x*k for x,k in zip(w,mask))
 chk(all(0<=h<=x for h,x in zip(weights,w)),'nonnegative retained weights bounded by original weights')
 star=tuple(tuple(1-bs[k]*(int(group[i]==r)+int(i==t))for i in range(5))for k,(r,t)in enumerate(profile))
 chk(all(x>0 for row in star for x in row),'positive exact star submeasure masses')
 for support in supports:
  chk(deg[support]==2**(7-len(support))-1-(7-len(support)),'exact endpoint sharing degrees')
 co={}
 for subset in {frozenset()}|set(supports):
  co[subset]=tuple(weights[i]*prod(bs[k]if k in subset else star[k][i]for k in range(7))for i in range(5))
 def dot(c,v):return sum((x*y for x,y in zip(c,v)),Q(0))
 first={s:tuple(dot(co[s],v)for v in rolevec)for s in supports}
 maxima={s:max(v)for s,v in first.items()}
 base0=sum(co[frozenset()],Q(0));base1=sum(maxima.values(),Q(0));base2=Q(0);credits=Q(0);positive=0
 for s,t in edges:
  values=[[dot(co[s|t],tuple(x*y for x,y in zip(v,u)))for u in rolevec]for v in rolevec]
  minimum=min(map(min,values));base2+=minimum
  credit=min((maxima[s]-first[s][i])/deg[s]+(maxima[t]-first[t][j])/deg[t]+values[i][j]-minimum for i in range(10)for j in range(10))
  chk(credit>=0,'nonnegative shared edge credit');credits+=credit;positive+=credit>0
 counts=Counter(s|t|u for s,t,u in triples);base3=Q(0)
 for U,multiplicity in counts.items():
  maximum=max(dot(co[U],tuple(x*y*z for x,y,z in zip(v,u,t)))for v,u,t in product(rolevec,repeat=3))
  base3+=multiplicity*maximum
 baseline=base0-base1+base2-base3
 return {'effective_weights':list(map(str,weights)),'baseline_terms':list(map(str,(base0,base1,base2,base3))),'baseline':str(baseline),'pair_credit':str(credits),'positive_edge_credits':positive,'mass_lower':str(baseline+credits)},baseline+credits

r=max(2*a,3*b);v=max(a,b)
mean=(1+r+Q(3,2)*v)*prod(Q(p-1,p-2)for p in P)
def tail(p,e):
 if e==0:return Q(1)
 if p==3:return r if e==1 else v/Q(3**(e-2))
 return Q(p-1,(p-2)*p**e)
N=28;dist={1:Q(1)}
for p in (3,)+P:
 law={j:tail(p,j-1)-tail(p,j)for j in range(1,N+1)}
 out={}
 for x,px in dist.items():
  for j,pj in law.items():
   if x*j<=N:out[x*j]=out.get(x*j,Q(0))+px*pj
 dist=out

def hinge(t):return mean-t+sum(((t-x)*mass for x,mass in dist.items()if x<t),Q(0))
def continuation_helpers(path):
 data=runpy.run_path(str(path))
 return data['a4'],data['cutoff_tail']

def calculate(helpers_path):
 global checks
 checks=0
 chk(sum(w)==1,'one original full probability law')
 chk((len(supports),len(edges),len(triples))==(120,546,210),'complete original support inventories')
 chk(sum(deg[s]==0 for s in supports)==8,'isolated deficits discarded')
 a4,cutoff_tail=continuation_helpers(helpers_path)
 rawK=(1+15*r+216*v)*prod(1+Q(p-1,p-2)*a4(p)for p in P)
 chk(rawK==Q(1995816314082394584902043010164181,6513156637804234575590400000),'same full original792 fourth envelope')
 K29factor=1+Q(28,27)*a4(29)
 tau=cutoff_tail(3000,7)
 result={'scope':'Two specified depth-two star contracts, original common weights retained for all queries. No uniform star claim and no clipped-vertex reduction. Ordinary exact arithmetic, no Lean.','original_weights':list(map(str,w)),'root_cap':str(r),'leaf_cap':str(v),'full_comparator_mean':str(mean),'raw_fourth':str(rawK),'pure29_fourth_factor':str(K29factor),'complete_tail3000':str(tau),'profiles':{}}
 expected={'first':Q(213065879798534401,5346615788877513150),'opposite':Q(1321375770143402,42887292424151175)}
 for name,(profile,mask)in profiles.items():
  item,alpha=mass(profile,mask)
  chk(alpha==expected[name],'exact retained-leaf source lower bound')
  options=[(t+hinge(t)/alpha,t)for t in range(1,N+1)]
  B,t=min(options)
  pgt=1-sum((z for x,z in dist.items()if x<=t),Q(0));pge=1-sum((z for x,z in dist.items()if x<t),Q(0))
  chk(pgt<=alpha<=pge,'global full-hinge minimizer quantile')
  chk(B<28,'full-source normalized B below28')
  m29=(28-B)/27;K8=rawK/alpha;K29=K8*K29factor;final=m29-K29*tau
  chk(final>Q(7,100),'same-source full tail strictly exceeds7/100')
  chk(final>(Q(3,20)if name=='first' else Q(7,100)),'separate simple final lower bound')
  item.update(profile=profile,mask=mask,optimal_threshold=t,comparator_H=str(hinge(t)),probability_M_gt_threshold=str(pgt),probability_M_ge_threshold=str(pge),B_upper=str(B),B_decimal=float(B),m29_lower=str(m29),m29_decimal=float(m29),K8=str(K8),K29=str(K29),final_tail3000_lower=str(final),final_decimal=float(final))
  result['profiles'][name]=item
 result['checks']=checks
 return result

if __name__=='__main__':
 parser=argparse.ArgumentParser(description='Two fixed-star retained-leaf mass certificates on the original full source, with all-height29 and prime-tail continuation.')
 parser.add_argument('--helpers',type=Path,default=Path(__file__).with_name('local_ternary_height_lift.py'))
 parser.add_argument('--expected',type=Path,default=Path(__file__).with_suffix('.json'))
 parser.add_argument('--write-result',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate(args.helpers)))
 if args.write_result:args.write_result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:chk(json.loads(args.expected.read_text())==result,'full exact replay matches retained data')
 print(json.dumps({name:{key:value[key]for key in ('mass_lower','optimal_threshold','B_decimal','final_decimal')}for name,value in result['profiles'].items()},indent=2))
