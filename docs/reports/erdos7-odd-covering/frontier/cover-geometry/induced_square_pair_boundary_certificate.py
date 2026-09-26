#!/usr/bin/env python3
"""Two common-source induced-response gates for twelve or twenty square pairs.

All646 square-star freedoms and the complete512 array remain. Exact finite
menus retain all48*11400 source addresses through480 complete descriptions.
Network comparison here uses646's published budget; a stronger budget must
be supplied by its own same-source continuation proof and exact certificate.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from math import prod, lcm
from collections import Counter
from hashlib import sha256
import argparse
import json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-certificate',type=Path,default=Path(__file__).with_name('all_square_star_phase_certificate.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
raw=args.source_certificate.read_bytes();v=json.loads(raw);checks=Counter()
def ck(name,predicate):
 if not predicate:raise ArithmeticError(name)
 checks[name]+=1
ck('published646_source',sha256(raw).hexdigest()=='53e8521c3f7efbb6d1d84ec18995ed254777d011574799d0de079d31c621577b')
Q=(7,11,13,17,19);co=list(map(F,v['complete512_coefficients']))
g=F(v['constants']['g']);alpha=F(v['constants']['alpha']);old_budget=F(v['constants']['full_network_fee'])
A=dict(zip(Q,map(F,v['coordinate_floor_factors'])))
a={q:F(1,q*(q-2))for q in Q};r={q:F(1,q-1)for q in Q}
ck('complete512_nonnegative',len(co)==512 and min(co)>=0)
ck('actual_full_height_caps',A=={q:(F(5,6)if q==7 else F(q-2,q-1)-2*a[q])for q in Q})
ck('old_full_network_budget',old_budget==F(1411,100000)+F(1,65536)+F(19740202146111572828188083,495176015714152109959649689600))
Dc=lcm(g.denominator,*(c.denominator for c in co));ci=[int(c*Dc)for c in co];gi=int(g*Dc)
ck('exact_integer_fee_encoding',F(gi,Dc)==g and all(F(x,Dc)==c for x,c in zip(ci,co)))
scopes=[]
for name,B in [('twelve',(11,13,17,19)),('twenty',Q)]:
 released=sorted(q*q*s for q in B for s in B if q!=s)
 remaining_pairs=sorted(set(v['inventory']['remaining_pairs'])-set(released))
 ck('distinct_original_partition',len(set(released))==len(released) and set(released)<=set(v['inventory']['remaining_pairs']) and len(remaining_pairs)+len(released)==40)
 edges=[(q,s,a[q]*r[s]+r[q]*a[s])for q,s in combinations(B,2)]
 affine=[]
 for T in range(32):
  U=[q for i,q in enumerate(Q)if not T>>i&1]
  H0=prod(A[q]for q in U)-sum((beta*prod(A[t]for t in U if t not in(q,s))for q,s,beta in edges if q in U and s in U),F())
  Hn=F()
  if 7 in U:
   Hn=a[7]*(prod(A[q]for q in U if q!=7)-sum((beta*prod(A[t]for t in U if t not in(q,s,7))for q,s,beta in edges if q in U and s in U and 7 not in(q,s)),F()))
  ck('positive_response_all_activation_counts',H0-3*Hn>0 and Hn>=0)
  for n in range(4):
   z={q:A[q]-(a[7]*n if q==7 else 0)for q in Q}
   direct=prod(z[q]for q in U)-sum((beta*prod(z[t]for t in U if t not in(q,s))for q,s,beta in edges if q in U and s in U),F())
   ck('literal_induced_response_equals_affine',direct==H0-n*Hn)
  affine.append((H0,Hn))
 Dh=lcm(*(x.denominator for pair in affine for x in pair))
 encoded=[(int(x*Dh),int(y*Dh))for x,y in affine]
 ck('exact_integer_response_encoding',all((F(x,Dh),F(y,Dh))==pair for (x,y),pair in zip(encoded,affine)))
 scopes.append(dict(name=name,block=B,released=released,remaining=remaining_pairs,edges=edges,affine=affine,encoded=encoded,denominator=675*Dc*Dh,records=[]))
cache={}
for ar,bc,leaf in product(range(2),range(4),range(6)):
 xs=[];ys=[]
 for z,w in product(range(6),repeat=2):
  if z==w:continue
  weights=[0 if i==z else 1 if i==w else 2 for i in range(6)]
  vectors=[[weights],[[weights[i]if i//3==r0 else 0 for i in range(6)]for r0 in range(2)],[[weights[i]if i==j else 0 for i in range(6)]for j in range(6)if weights[j]],[[9 if i==j else 0 for i in range(6)]for j in range(6)if weights[j]]]
  menus=tuple(tuple(sorted(set((sum(x),sum(x[:3]),sum(x[3*ar:3*ar+3])+x[leaf],(sum(x[:3])if ar==0 else 0)+(x[leaf]if leaf<3 else 0))for x in menu)))for menu in vectors)
  xs.append((z,w,menus))
 for z,w in product(range(20),repeat=2):
  if z==w:continue
  weights=[0 if i==z else 3 if i==w else 4 for i in range(20)]
  vectors=[[weights],[[weights[i]if i//5==r0 else 0 for i in range(20)]for r0 in range(4)],[[weights[i]if i==j else 0 for i in range(20)]for j in range(20)if weights[j]],[[60 if i==j else 0 for i in range(20)]for j in range(20)if weights[j]]]
  menus=tuple(tuple(sorted(set((sum(y),sum(y[:5]),sum(y[5*bc:5*bc+5]))for y in menu)))for menu in vectors)
  ys.append((z,w,menus))
 minima=[None]*len(scopes);witnesses=[None]*len(scopes);ties=[0]*len(scopes);count=0
 for z,w,xm in xs:
  for zz,ww,ym in ys:
   count+=1;key=(xm,ym,bc==0)
   if key not in cache:
    forms=[]
    for e3,e5 in product(range(4),repeat=2):
     fm=set()
     for x in xm[e3]:
      for y in ym[e5]:
       b=x[0]*y[0]-x[1]*y[1]
       n=x[2]*y[0]+x[0]*y[2]-x[3]*y[1]-(x[1]*y[1]if bc==0 else 0)
       ck('exact_masked_activation_form',0<=n<=3*b)
       fm.add((b,n))
     forms.append(tuple(sorted(fm)))
    vals=[]
    for scope in scopes:
     screens=[max(h0*b-hn*n for b,n in fm)for fm in forms for h0,hn in scope['encoded']]
     ck('full512_screen_shape',len(screens)==512 and min(screens)>=0)
     vals.append(F(gi*screens[0]-sum(c*s for c,s in zip(ci,screens)),scope['denominator']))
    cache[key]=tuple(vals)
   for i,val in enumerate(cache[key]):
    if minima[i]is None or val<minima[i]:minima[i]=val;witnesses[i]=[z,w,zz,ww];ties[i]=1
    elif val==minima[i]:ties[i]+=1
 ck('all11400_corners_per_layout',count==11400)
 for i,scope in enumerate(scopes):
  scope['records'].append(dict(layout=[ar,bc,leaf],gate=str(minima[i]),corner=witnesses[i],minimizing_corners=ties[i],corners_accounted=count))
results=[]
for scope in scopes:
 worst=min(scope['records'],key=lambda x:F(x['gate']));gamma=F(worst['gate']);old_margin=alpha*(gamma-old_budget)
 expected=(F(26988940112492901117737957,1881136901050329162240000000)if scope['name']=='twelve'else F(203129722400814193208791597,20692505911553620784640000000))
 ck('exact_scope_minimum',gamma==expected and gamma>0)
 ck('all48_layout_addresses',len(scope['records'])==48 and sum(x['corners_accounted']for x in scope['records'])==547200)
 if scope['name']=='twelve':ck('twelve_full_network_margin',old_margin>F(1,230000))
 else:ck('twenty_old_budget_obstruction',old_margin<0)
 results.append(dict(scope=scope['name'],block=scope['block'],released_square_pairs=scope['released'],remaining_pairs=scope['remaining'],edge_caps=[dict(primes=[q,s],union_cap=str(b))for q,s,b in scope['edges']],affine32_response_coefficients=[[str(x),str(y)]for x,y in scope['affine']],layouts=scope['records'],worst=worst,head_haar=str(alpha*gamma),old_network_haar_margin=str(old_margin),strict_total_network_fee_threshold=str(gamma),strict_owner_W3_threshold=str(gamma-F(1,65536)-F(19740202146111572828188083,495176015714152109959649689600))))
out=dict(schema='induced-square-pair-boundary-v1',status='EXACT_HEAD_GATES_TWELVE_AND_TWENTY',source_certificate_sha256=sha256(raw).hexdigest(),producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
 phase_scope='Both scopes keep all646 fifteen square-star phase freedoms and its literal head/central conventions; forty linear-star incidences remain. Twelve scope leaves28pair incidences; twenty scope leaves20. Arbitrary higher pure phases and finite query depths. A full network requires its separately valid total source-unit fee below the exact head gate.',
 constants=dict(g=str(g),alpha=str(alpha),published646_network_fee=str(old_budget)),unchanged512_coefficients=list(map(str,co)),previously_free_square_stars=v['inventory']['freed_square_stars'],remaining_linear_stars=v['inventory']['remaining_linear_stars'],source_addresses_per_scope=547200,distinct_complete_descriptors=len(cache),scopes=results,checks=dict(checks),check_count=sum(checks.values()),new_lean_verification=False)
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],descriptors=len(cache),checks=out['check_count'],scopes=[dict(scope=x['scope'],worst=x['worst'],old_network_haar_margin=x['old_network_haar_margin'],strict_owner_W3_threshold=x['strict_owner_W3_threshold'])for x in results]),indent=2))
