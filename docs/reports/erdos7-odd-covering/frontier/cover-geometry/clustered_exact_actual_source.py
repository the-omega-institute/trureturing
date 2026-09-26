#!/usr/bin/env python3
"""Exact finite actual survivor and normalized full-height query envelopes.
The91 global phases are the clustered diagnostic fixture. Outside pure laws
are Haar conditioned on nonzero first root, with no higher pure originals.
All original root/square conflicts are imposed on that same law. No matching
thinning or square-union subtraction is used.
"""
import argparse,json
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from hashlib import sha256
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--fixture',type=Path,default=Path(__file__).with_name('clustered_global_phase_fixture.json'));parser.add_argument('--output',type=Path);args=parser.parse_args()
source=args.fixture;source_raw=source.read_bytes();fixture=json.loads(source_raw)
base=dict(kind='clustered',seed=0,actual_originals=[],linear_stars=[],square_stars=[],pairs=[])
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(m for m in range(20)if m!=5);LIVE=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5));D=prod(q*(q-1)for q in Q);checks={}
def ck(k,c):
 if not c:raise ArithmeticError(k)
 checks[k]=checks.get(k,0)+1
ck('101_originals',len(fixture['actual_originals'])==101 and len({o['modulus']for o in fixture['actual_originals']})==101)
for original in fixture['actual_originals']:
 n=original['modulus'];b=original['residue'];c=n;powers=[]
 ck('odd_phase_range',n>1 and n%2==1 and 0<=b<n)
 for u,q in enumerate(Q):
  e=0
  while c%q==0:c//=q;e+=1
  if e:powers.append((u,e))
 if not powers:
  ck('central_pure_and15_inventory',(n,b)in((3,2),(9,1),(5,4),(25,1),(15,0)));continue
 if len(powers)==1 and c==1:
  ck('outside_pure_inventory',powers[0][1]==1 and b==0);continue
 base['actual_originals'].append(original)
 if len(powers)==1:
  u,e=powers[0];q=Q[u]
  if e==1:
   ck('linear_star_inventory',c in(3,5,15,9,25,45,75,225));base['linear_stars'].append((u,c,b%c,b%q))
  else:
   ck('square_star_inventory',e==2 and c in((3,5,9)if u==0 else(3,5)));base['square_stars'].append((u,c,b%c,b%(q*q)))
 else:
  ck('pair_inventory',len(powers)==2)
  (u,ep),(v,eq)=powers;e=tuple(combinations(range(5),2)).index((u,v))
  ck('pair_heights',(c,ep,eq)in((1,1,1),(9,1,1),(1,2,1),(1,1,2)))
  kind='left_square'if ep==2 else'right_square'if eq==2 else'leaf'if c==9 else'root'
  if ep==2:ck('left_square_lift0',b%(Q[u]*Q[u])==1)
  if eq==2:ck('right_square_lift0',b%(Q[v]*Q[v])==1)
  base['pairs'].append((e,kind,c,b%c,b%Q[u],b%Q[v]))
ck('retained_inventory_counts',len(base['linear_stars'])==40 and len(base['square_stars'])==11 and len(base['pairs'])==40)
ck('clustered_fixture',base['kind']=='clustered'and base['seed']==0)
ck('91_global_moduli',len(base['actual_originals'])==len({o['modulus']for o in base['actual_originals']})==91)
# Independently verify the fixed outside phases which support the partition.
for e,kind,c,h,t,s in base['pairs']:ck('every_pair_root1',t==s==1)
for u,c,h,t in base['square_stars']:ck('every_square_root1_lift0',t==1)
for u,c,h,t in base['linear_stars']:ck('coherent_central81',h==81%c)
for q in Q:
 ck('pure_q_partition',sum(F(1,q*(q-1))for root in range(1,q)for child in range(q))==1)
 ck('square_cap',F(1,q*(q-1))<=F(1,q*(q-2)))
 ck('root_dominates_deep_ratio',F(q-1,q)>F(q-2,q-1))
# All mixed events see only the first root, or root1's distinguished second digit.
# A category0 is an allowed root other than1;1 is root1/lift0;2 root1/other lift.
category_words=tuple(product(range(3),repeat=5));good_words=tuple(word for word in category_words if all(not(word[u]and word[v])for u,v in combinations(range(5),2)))
ck('exact_pair_conflict_partition',len(good_words)==11)
cells=[]
for l,m in LIVE:
 r3=3*(l%3)+l//3;r5=5*(m%5)+m//5;cv=r3+9*((r5-r3)*14%25);deleted=[set()for q in Q]
 for u,c,h,t in base['linear_stars']:
  if cv%c==h:deleted[u].add(t)
 weights=[];A=[];B=[]
 for u,q in enumerate(Q):
  raw=[0,0,0]
  for root in range(1,q):
   for child in range(q):
    atom=root+q*child
    if root in deleted[u]:continue
    if any(v==u and cv%c==h and atom==t for v,c,h,t in base['square_stars']):continue
    raw[0 if root!=1 else 1 if child==0 else 2]+=1
  weights.append(tuple(raw));A.append(F(raw[1]+raw[2],q*(q-1)));B.append(F(raw[0],q*(q-1)))
  ck('normal_other_root_atoms',raw[0]%q==0)
  ck('actual_root1_classes',(raw[1],raw[2])in((0,0),(0,q-1),(1,q-1)))
  if u>0:ck('root9_globally_free',9 not in deleted[u]and all(not(v==u and t%q==9)for v,c,h,t in base['square_stars']))
 # Test all category words against every actual paired numerical original.
 for word in category_words:
  exact_bad=False
  for e,kind,c,h,t,s in base['pairs']:
   if cv%c!=h:continue
   u,v=tuple(combinations(range(5),2))[e]
   left=word[u]>0 and(kind!='left_square'or word[u]==1)
   right=word[v]>0 and(kind!='right_square'or word[v]==1)
   exact_bad |= left and right
  ck('all40_pair_predicates',(not exact_bad)==(word in good_words))
 factor=lambda U:prod((B[u]for u in U),start=F(1))+sum((A[v]*prod((B[u]for u in U if u!=v),start=F(1))for v in U),F())
 exact_mass=sum(prod(weights[u][word[u]]for u in range(5))for word in good_words)
 ck('source_factorization',F(exact_mass,D)==factor(tuple(range(5))))
 responses=[]
 for T in range(32):
  rows=[]
  for root7 in(range(1,7)if T&1 else(None,)):
   fixed={u:(root7 if u==0 else 9)for u in range(5)if T>>u&1}
   ww=[list(v)for v in weights]
   for u,root in fixed.items():
    q=Q[u]
    if root in deleted[u]:ww[u]=[0,0,0]
    elif root==1:ww[u][0]=0
    else:ww[u]=[q,0,0]
   count=sum(prod(ww[u][word[u]]for u in range(5))for word in good_words)
   response=F(count*prod(Q[u]-1 for u in fixed),D)
   U=tuple(u for u in range(5)if u not in fixed)
   if any(root in deleted[u]for u,root in fixed.items()):formula=F()
   elif root7==1:formula=A[0]*(Q[0]-1)*prod((B[u]for u in U),start=F(1))
   else:formula=factor(U)
   ck('all_query_slices_exact',response==formula)
   ck('query_response_range',0<=response<=1)
   rows.append(str(response))
  if T&1:
   # The masks and the at-most-one condition make roots5/6 jointly sufficient.
   for k in range(4):ck('root6_dominates_1_to4',F(rows[k])<=F(rows[5]))
  responses.append(rows)
 ck('zero_source_all_queries_zero',exact_mass>0 or all(F(x)==0 for row in responses for x in row))
 cells.append(dict(cell=[l,m],central=cv,deleted_roots=[sorted(x)for x in deleted],local_atom_counts=weights,local_atom_denominators=[q*(q-1)for q in Q],root1_masses=list(map(str,A)),other_root_masses=list(map(str,B)),source_mass=str(F(exact_mass,D)),H_by_support_and_root7=responses))
out=dict(schema='clustered91-exact-actual-root-square-survivor-v1',status='PASS',new_lean_verification=False,source_fixture_sha256=sha256(source_raw).hexdigest(),program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),scope='One fixed91-original clustered phase family; outside pure root0 and no higher outside pure originals. Actual conditional Haar source, all root/square conflicts enforced exactly. Source cell weights come from separately specified central laws. H[T][0] for7notinT, H[T][root7-1] otherwise; other queried roots fixed9, which globally dominates their alternatives. These normalized first-root maxima bound all deeper queries using inherited prefix caps. Cells with zero source have all query responses zero. No unrestricted phase or covering claim.',Q=Q,nulls=[3,5],actual_originals=base['actual_originals'],outside_pure_originals=[dict(modulus=q,residue=0)for q in Q],central_pure_and_15=[dict(modulus=m,residue=r)for m,r in((3,2),(9,1),(5,4),(25,1),(15,0))],common_atom_denominator=D,cells=cells,checks=checks,check_count=sum(checks.values()))
p=args.output or Path(__file__).with_suffix('.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status='PASS',checks=out['check_count'],source_cells=len(cells),dead_cells=sum(F(x['source_mass'])==0 for x in cells),output=str(p),sha256=sha256(p.read_bytes()).hexdigest())),flush=True)
