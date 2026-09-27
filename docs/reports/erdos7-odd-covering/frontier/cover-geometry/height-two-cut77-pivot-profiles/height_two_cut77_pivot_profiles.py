#!/usr/bin/env python3
"""Sorted-private-cost enumeration for exact q4 and q5 m4 pivot conditions.
Necessary integer profiles only; no source realizability claim.
"""
from itertools import combinations_with_replacement,product
from collections import defaultdict
from pathlib import Path
import argparse,json


def options(n,dist,mandatory=None):
 out=[];q=n-2
 if not dist:out.append((0,0,0,()))
 allowed=(n-1,n) if dist else range(q,n+1)
 for a in allowed:
  if dist:
   required=mandatory if mandatory is not None else ((0,2,2) if n==5 else (2,2))
   shapes={tuple(sorted(required+extra)) for extra in combinations_with_replacement(range(4),a-len(required))}
  else:shapes=set(combinations_with_replacement(range(4),a))
  for sh in sorted(shapes):out.append((a,sum(sh[:q]),sum(sh),sh))
 return out


def enumerate_profiles(n,mandatory=None):
 opts=[options(v,i==0,mandatory if i==0 else None) for i,v in enumerate(n)];profiles=defaultdict(set)
 for k in range(12):
  choices=[]
  for i,oo in enumerate(opts):
   # All other active roots obey the actual duplicate-leaf discount.
   choices.append([v for v in oo if (not v[0] or i==0 or v[1]>=7-k) and (k>0 or not v[0] or min(v[3])>0)])
  def rec(selected,T,Z):
   if len(selected)==4:
    if 7*(T+k)+2*Z!=77:return
    if all(v[0]==n[i] for i,v in enumerate(selected)) and k+Z<15:return
    key=(tuple(v[0] for v in selected),T,k,Z)
    profiles[key].add('/'.join(''.join(map(str,v[3])) if v[0] else '-' for v in selected));return
   i=len(selected)
   for v in choices[i]:
    a,p,z,sh=v;t=3 if not a else n[i]-a
    if 7*(T+t+k)+2*(Z+z)>77:continue
    if a and any(u[0] and p+u[1]<9-k for u in selected):continue
    rec(selected+[v],T+t,Z+z)
  rec([],0,0)
 return [dict(active=list(a),T=T,public=k,private=Z,shapes=sorted(shapes)) for (a,T,k,Z),shapes in sorted(profiles.items())]

out=dict(scope='Necessary normalized exact-pivot integer profiles; private costs0..3, q4 distinguished0/2/2 or2/2, q5 m4 distinguished1/1/2, all literal pair lower bounds, duplicate-leaf discount, public0 nonemptiness and full-activity standalone lower bound. No source-existence conclusion; source exclusions are separate deductions in Report449.',
         distinguished_full=enumerate_profiles((5,5,5,4)),distinguished_gap=enumerate_profiles((4,5,5,5)),
         q5_m4_distinguished_full=enumerate_profiles((5,5,5,4),(1,1,2)))
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
args.output.write_text(json.dumps(out,indent=2)+'\n')
for typ in ('distinguished_full','distinguished_gap','q5_m4_distinguished_full'):
 print(typ)
 for r in out[typ]:print({k:v for k,v in r.items() if k!='shapes'},'shape_count',len(r['shapes']))
