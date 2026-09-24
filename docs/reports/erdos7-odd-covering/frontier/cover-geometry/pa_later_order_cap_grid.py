#!/usr/bin/env python3
"""Exact PA constant-cap certificate grid with all later-prime orders.

The hinge expression is the one in report348's positive/zero cap-grid
producers: complete first moments plus exact subthreshold products. A
16-subset shortest-path dynamic program selects a legal order for each
cap tuple. Actual classes are assigned to their last prime in that order;
no original full numerical label or phase is modified.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations,product
from pathlib import Path
from math import prod
import argparse,hashlib,json,time

PRIMES=(11,13,17,19)
ANCHORS=((5,F(1),F(1,2)),(7,F(1),F(1,3)))
OLD=F(28165018706892770299,5469152872511772242)
TARGET=F(257,51)
checks={}
def require(name,condition):
 checks[name]=bool(condition)
 if not condition: raise ValueError(name)

# Same PA hinge expression as both canonical fixed-order grid programs.
@lru_cache(None)
def hinge(coords,t):
 mass=mean=F(1);low={1:F(1)} if t>1 else {}
 for p,c,u in coords:
  mass*=1-u;mean*=1-u+c/(p-1)
  probs={1:1-u-c/p}
  probs.update({n:c*F(p-1,p**n) for n in range(2,t)})
  nxt={}
  for x,v in low.items():
   for y,w in probs.items():
    if x*y<t:nxt[x*y]=nxt.get(x*y,F(0))+v*w
  low=nxt
 return mean-t*mass+sum((t-x)*v for x,v in low.items())

def solve(ts):
 caps=tuple(F(p-1,p-1-2*t) for p,t in zip(PRIMES,ts))
 aa=tuple(F(2,p-1-2*t) for p,t in zip(PRIMES,ts))
 cs={mask:ANCHORS+tuple((p,c,F(0)) for i,(p,c) in enumerate(zip(PRIMES,caps)) if mask>>i&1) for mask in range(16)}
 edges={(mask,i):aa[i]*hinge(cs[mask],ts[i]) for mask in range(16) for i in range(4) if not(mask>>i&1)}
 dp={0:F(0)};path={0:()};ties={0:1}
 for mask in range(1,16):
  opts=[(dp[mask^(1<<i)]+edges[mask^(1<<i),i],path[mask^(1<<i)]+(i,),ties[mask^(1<<i)]) for i in range(4) if mask>>i&1]
  val,order,_=min(opts)
  dp[mask]=val;path[mask]=order;ties[mask]=sum(count for cost,order,count in opts if cost==val)
 alpha=F(1,4)-dp[15]
 fixed=F(1,4)-sum((edges[((1<<i)-1),i] for i in range(4)),F(0))
 final=cs[15]
 best=min((h-1+hinge(final,h)/alpha,h) for h in range(1,7)) if alpha>0 else None
 fixedbest=min((h-1+hinge(final,h)/fixed,h) for h in range(1,7)) if fixed>0 else None
 return {'thresholds':ts,'caps':caps,'alpha':alpha,'loss':dp[15],'order':tuple(PRIMES[i] for i in path[15]),'order_indices':path[15],'optimal_order_count':ties[15],'query':None if best is None else best[0],'h':None if best is None else best[1],'fixed_alpha':fixed,'fixed_query':None if fixedbest is None else fixedbest[0],'fixed_h':None if fixedbest is None else fixedbest[1]},edges,final

start=time.monotonic();rows=[];best=None;fixed_best=None;zero_best=None;positive=0;fixed_positive=0;reordering_improves=0
for ts in product(range(5),range(6),range(8),range(9)):
 r,_,_=solve(ts);rows.append(r)
 require('DP_alpha_dominates_fixed_'+''.join(map(str,ts)),r['alpha']>=r['fixed_alpha'])
 reordering_improves+=r['alpha']>r['fixed_alpha']
 if r['alpha']>0:
  positive+=1
  key=(r['query'],ts,r['h'],r['order'])
  if best is None or key<best[0]:best=(key,r)
  if 0 in ts and (zero_best is None or key<zero_best[0]):zero_best=(key,r)
 if r['fixed_alpha']>0:
  fixed_positive+=1
  key=(r['fixed_query'],ts,r['fixed_h'])
  if fixed_best is None or key<fixed_best[0]:fixed_best=(key,r)
require('full_integer_grid',len(rows)==2160)
require('fixed_order_exact_baseline_recovered',fixed_best[0]==(OLD,(2,2,4,4),3))
require('fixed_order_positive_count',fixed_positive==999)
winner=best[1];_,edges,final=solve(winner['thresholds'])
explicit=[]
for order in permutations(range(4)):
 mask=0;loss=F(0)
 for i in order:
  loss+=edges[mask,i];mask|=1<<i
 explicit.append({'order':tuple(PRIMES[i] for i in order),'loss':loss,'alpha':F(1,4)-loss})
require('winner_DP_equals_24_order_min',winner['loss']==min(r['loss'] for r in explicit))
require('winner_order_tie_count',winner['optimal_order_count']==sum(r['loss']==winner['loss'] for r in explicit))
require('winner_finite_h_search_exact',winner['query']==winner['h']-1+hinge(final,winner['h'])/winner['alpha'])
require('winner_order_roundtrip',tuple(PRIMES[i] for i in winner['order_indices'])==winner['order'])

def encode(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x).__name__)
result={'scope':'Exact ordinary PA constant-cap comparison grid, fixed anchors5/7, arbitrary orders of11/13/17/19. Not an optimum over actual survivor laws. No Lean.','threshold_ranges':[list(range(n)) for n in (5,6,8,9)],'query_thresholds':list(range(1,7)),'cap_tuples':len(rows),'possible_later_orders':24,'positive_with_best_order':positive,'positive_with_fixed_order':fixed_positive,'cap_tuples_with_strict_order_loss_gain':reordering_improves,'target':str(TARGET),'old_fixed_order_optimum':str(OLD),'winner':winner,'strict_gain_over_fixed_optimum':OLD-winner['query'],'gap_to_target':winner['query']-TARGET,'crosses_target':winner['query']<TARGET,'best_zero_containing_with_h_1_to_6':zero_best[1],'fixed_order_winner':fixed_best[1],'winner_all_24_orders':explicit,'per_cap_minima':rows,'checks':checks,'passed_count':len(checks)}
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args();args.output.write_text(json.dumps(result,indent=2,default=encode)+'\n')
print(json.dumps({'cap_tuples':len(rows),'positive_any_order':positive,'positive_fixed_order':fixed_positive,'strict_order_loss_gain_tuples':reordering_improves,'winner':winner,'winner_decimal':float(winner['query']),'strict_gain_over_old':str(OLD-winner['query']),'crosses_target':winner['query']<TARGET,'passed_count':len(checks),'seconds':time.monotonic()-start,'output':str(args.output),'sha256':hashlib.sha256(args.output.read_bytes()).hexdigest()},indent=2,default=encode))
