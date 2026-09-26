#!/usr/bin/env python3
"""Complete48-layout joint-source certificate freeing every square-star phase.

Original labels stay global. Four guarded9q^2 events are charged once at
stronger central query type(2,1); they are not new45q^2 originals. Every
literal central comparison corner is retained. Exact integer/rational
arithmetic certifies the finite gate; the report supplies all-height scope.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from collections import Counter
from hashlib import sha256
import argparse
import json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-certificate',type=Path,default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
p=args.source_certificate;raw=p.read_bytes()
checks=Counter()
def ck(name,predicate):
 if not predicate:raise ArithmeticError(name)
 checks[name]+=1
ck('published640_source',sha256(raw).hexdigest()=='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4')
v=json.loads(raw);Q=(7,11,13,17,19);co=list(map(F,v['combined512_coefficients']));g=F(v['constants']['g']);alpha=F(v['constants']['alpha'])
ck('complete512_nonnegative',len(co)==512 and min(co)>=0)
ck('actual_continuation_constants',g==F(200163067,201247200) and alpha==F(2673,110656))
stars=set(v['inventory']['root_stars55']);pairs=set(v['inventory']['root_pairs40'])
squares={d*q*q for d in (3,5,9) for q in Q}
linear=stars-squares
ck('original_identity_partition',len(stars)==55 and len(squares)==15 and len(linear)==40 and len(pairs)==40 and not(stars & pairs) and squares<=stars)
ck('all_released_originals_arbitrary',squares=={d*q*q for q in Q for d in (3,5,9)})
original_co=co.copy();additional=[F()]*512
A=[F(q-2,q-1)-(F(2,q*(q-2))if q!=7 else 0) for q in Q]
for i,q in enumerate(Q):
 if q!=7:
  additional[32*9+(1<<i)]=F(1,q*(q-2))
  co[32*9+(1<<i)]+=g*additional[32*9+(1<<i)]
  ck('residual_original_not_new45square',9*q*q in squares and 45*q*q in v['inventory']['paid370'] and 9*q*q!=45*q*q)
ck('four_residual_queries_only',sum(x!=0 for x in additional)==4 and all(c==o+g*x for c,o,x in zip(co,original_co,additional)))
ck('positive_coordinate_masses',all(0<x<1 for x in A) and F(5,6)-F(3,35)>0)
h=[prod(A[i]for i in range(5)if not T>>i&1)for T in range(32)]
fees=[[sum((co[32*m+T]*h[T]for T in range(32)if(T&1)==b),F())for m in range(16)]for b in(0,1)]
cache={};records=[]
for ar,bc,leaf in product(range(2),range(4),range(6)):
 xs=[];ys=[]
 for z,w in product(range(6),repeat=2):
  if z==w:continue
  weights=[0 if i==z else 1 if i==w else 2 for i in range(6)]
  vectors=[[weights],[[weights[i]if i//3==r else 0 for i in range(6)]for r in range(2)],[[weights[i]if i==j else 0 for i in range(6)]for j in range(6)if weights[j]],[[9 if i==j else 0 for i in range(6)]for j in range(6)if weights[j]]]
  menus=tuple(tuple(sorted(set((sum(x),sum(x[:3]),sum(x[3*ar:3*ar+3])+x[leaf],(sum(x[:3])if ar==0 else 0)+(x[leaf]if leaf<3 else 0))for x in menu)))for menu in vectors)
  xs.append((z,w,menus))
 for z,w in product(range(20),repeat=2):
  if z==w:continue
  weights=[0 if i==z else 3 if i==w else 4 for i in range(20)]
  vectors=[[weights],[[weights[i]if i//5==r else 0 for i in range(20)]for r in range(4)],[[weights[i]if i==j else 0 for i in range(20)]for j in range(20)if weights[j]],[[60 if i==j else 0 for i in range(20)]for j in range(20)if weights[j]]]
  menus=tuple(tuple(sorted(set((sum(y),sum(y[:5]),sum(y[5*bc:5*bc+5]))for y in menu)))for menu in vectors)
  ys.append((z,w,menus))
 minimum=None;wit=None;ties=0;count=0
 for l,m in product(range(6),range(20)):
  active=(l//3==ar,m//5==bc,l==leaf)
  selected=tuple(i for i,a in enumerate(active)if a) if sum(active)<=2 else (0,1)
  remaining=tuple(i for i,a in enumerate(active)if a and i not in selected)
  ck('two_slot_selection_covers_except_guarded_original',len(selected)<=2 and all(i==2 for i in remaining))
  ck('remaining9square_has_one_global_rectangle',not remaining or (l==leaf and m//5==bc and leaf//3==ar))
 for z,w,xm in xs:
  for zz,ww,ym in ys:
   count+=1
   key=(xm,ym,bc==0)
   if key not in cache:
    original=[];new=[]
    for e3,e5 in product(range(4),repeat=2):
     forms=[]
     for x in xm[e3]:
      for y in ym[e5]:
       b=x[0]*y[0]-x[1]*y[1]
       n=x[2]*y[0]+x[0]*y[2]-x[3]*y[1]-(x[1]*y[1]if bc==0 else 0)
       ck('exact_masked_activation_form',0<=n<=3*b)
       forms.append((b,175*b-6*n))
     original.append(max(b for b,n in forms));new.append(max(n for b,n in forms))
    cache[key]=g*h[0]*F(new[0],118125)-sum((fees[0][m]*F(new[m],118125)+fees[1][m]*F(original[m],675)for m in range(16)),F())
   val=cache[key]
   if minimum is None or val<minimum:minimum=val;wit=[z,w,zz,ww];ties=1
   elif val==minimum:ties+=1
 ck('all11400_corners_per_layout',count==11400)
 ck('positive_gate_each_layout',minimum>0)
 records.append(dict(layout=[ar,bc,leaf],gate=str(minimum),corner=wit,minimizing_corners=ties,corners_accounted=count))
worst=min(records,key=lambda r:F(r['gate']));fee=F(1411,100000)+F(1,65536)+F(19740202146111572828188083,495176015714152109959649689600)
ck('complete48_global_layouts',len(records)==48 and sum(r['corners_accounted'] for r in records)==547200)
ck('exact_minimum',F(worst['gate'])==F(4761332019354554385809183,306555643134127715328000000))
ck('full_declared_network',alpha*(F(worst['gate'])-fee)>F(1,30300))
ck('head_haar_bound',alpha*F(worst['gate'])>F(1,2700))
out=dict(schema='all-square-star-phases-complete-network-v1',status='POSITIVE_ALL48_LAYOUTS',
 scope='Literal ten-prime head and fixed central pure/15 conventions; arbitrary phases of all15 square-star originals. One global cell-dependent single-root table still absorbs40linear stars and40pairs. Arbitrary higher pure phases, finite heights and all other head originals remain as640. Full declared625 network only. No unrestricted Erdos7 or new Lean claim.',
 source_certificate_sha256=sha256(raw).hexdigest(),producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
 inventory=dict(freed_square_stars=sorted(squares),remaining_linear_stars=sorted(linear),remaining_pairs=sorted(pairs)),
 constants=dict(g=str(g),alpha=str(alpha),full_network_fee=str(fee)),
 coordinate_floor_factors=list(map(str,A)),base32_support_responses=list(map(str,h)),
 residual_query_originals=[dict(original=9*q*q,guarded_query_modulus=45*q*q,coefficient=str(F(1,q*(q-2))),new_original=False)for q in Q if q!=7],
 additional512_loss_coefficients=list(map(str,additional)),complete512_coefficients=list(map(str,co)),
 unqueried7_fees=list(map(str,fees[0])),queried7_fees=list(map(str,fees[1])),
 worst=worst,layouts=records,source_corner_layout_pairs=547200,distinct_descriptors=len(cache),
 full_margin=str(alpha*(F(worst['gate'])-fee)),head_haar=str(alpha*F(worst['gate'])),
 checks=dict(checks),check_count=sum(checks.values()),new_lean_verification=False)
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in ('status','worst','source_corner_layout_pairs','distinct_descriptors','full_margin','head_haar','check_count')},indent=2))
