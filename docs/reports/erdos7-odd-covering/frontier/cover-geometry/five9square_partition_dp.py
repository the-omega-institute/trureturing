#!/usr/bin/env python3
"""Exact six-leaf partition DP, all6^5 assignments, one declared source corner."""
import argparse,json,time
from hashlib import sha256
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from math import prod,lcm
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args();checks={}
def ck(name,condition):
 if not condition:raise ArithmeticError(name)
 checks[name]=checks.get(name,0)+1
source_raw=(args.source_dir/'conditional30_fixedstar_augmented_certificate.json').read_bytes()
source_pin=sha256(source_raw).hexdigest()
ck('source_pin',source_pin=='eb45a79b8943ac56b72153c72472bf40b098366574deb249840ea28f504a9345')
B=json.loads(source_raw)
Q=(7,11,13,17,19);D=[q*(q-2)*(q-1)for q in Q];rn=[q*(q-2)for q in Q];an=[q-1 for q in Q]
E=tuple(combinations(range(5),2));EM=[(1<<q)|(1<<s)for q,s in E];pairs=[(e,f)for e,f in combinations(range(10),2)if not(EM[e]&EM[f])];KN=[rn[q]*rn[s]+an[q]*rn[s]+rn[q]*an[s]for q,s in E]
DEN=[675000*prod(D[q]for q in range(5)if not(T>>q&1))for T in range(32)]
subsets=[[a for a in range(32)if a&S==a]for S in range(32)]
CATS=list(map(tuple,B['thinning_categories']));theta=[F(t)for t in B['common_thinning']];WN=(2,2,2,0,1,2);VN=(4,4,4,4,4,0,3,4,4,4,4,4,4,4,4,4,4,4,4,4)
g=F(B['constants']['g']);co=list(map(F,B['stages']['mixed370']['combined_coefficients']));start=time.monotonic()
def tn(l,m):
 if l<3 and m<5:return 0
 a=0 if l==0 else 1 if l<3 else 2;b=0 if m<5 else 2 if m==10 else 3 if 11<=m<15 else 1
 x=theta[CATS.index((a,b))]*1000
 ck('integer_thinning',x.denominator==1)
 return x.numerator
# Integer query numerator with fixed outside-support denominator; includes theta once.
H=[[[[0]*32 for m in range(20)]for l in range(6)]for T in range(32)]
for l,m in product(range(6),range(20)):
 t=tn(l,m)
 if not t:continue
 for A in range(32):
  Z=[D[q]-(rn[q]+an[q])*(int(l<3)+int(10<=m<15))-rn[q]*(int(l<3 and 10<=m<15)+int(l==0)+int(m==10))-an[q]*int(A>>q&1)for q in range(5)]
  raw=[prod(Z[q]for q in range(5)if not(T>>q&1))for T in range(32)]
  for T in range(32):
   value=raw[T]-sum(KN[e]*raw[T|EM[e]]for e in range(10)if not(T&EM[e]))+sum(KN[e]*KN[f]*raw[T|EM[e]|EM[f]]for e,f in pairs if not(T&(EM[e]|EM[f])))
   ck('positive_conditional_response',value>0)
   H[T][l][m][A]=t*value
# Every induced polynomial at uniform Z-a floor, checked exactly once.
r=[F(1,q-1)for q in Q];a=[F(1,q*(q-2))for q in Q];floor=[1-3*r[q]-3*a[q]for q in range(5)];up=[F(KN[e],D[q]*D[s])/(floor[q]*floor[s])for e,(q,s)in enumerate(E)]
strict=[]
for mask in range(1024):strict.append(1-sum((up[e]for e in range(10)if mask>>e&1),F())+sum((up[e]*up[f]for e,f in pairs if mask>>e&1 and mask>>f&1),F()))
ck('all1024_strict_positive',len(strict)==1024 and min(strict)>0)

def menus(n,block,w,deep,mode):
 if mode==0:return[tuple(w)]
 zero=(0,)*n
 if mode==1:return sorted({tuple(w[k]if k//block==j else 0 for k in range(n))for j in range(n//block)}|{zero})
 return sorted({tuple((w[k]if mode==2 else deep)if k==leaf else 0 for k in range(n))for leaf in range(n)if w[leaf]}|{zero})
MX=[menus(6,3,WN,9,e)for e in range(4)];MY=[menus(20,5,VN,60,e)for e in range(4)]

def extremum(fields,maximize=False,witness=False):
 # Zero leaves accept all unassigned coordinates for free.
 active=[(i,row)for i,row in enumerate(fields)if any(row)];free=len(active)<6
 opt=max if maximize else min
 dp={0:0};paths={0:[]}
 for leaf,row in active:
  nd={};np={}
  for S in range(32):
   candidates=[(dp[S^A]+row[A],A)for A in subsets[S]if S^A in dp]
   if not candidates:continue
   value,A=opt(candidates,key=lambda z:z[0]);nd[S]=value
   if witness:np[S]=paths[S^A]+[(leaf,A)]
  dp=nd
  if witness:paths=np
 S=opt(dp,key=dp.__getitem__)if free else 31
 if not witness:return dp[S]
 allocations=[0]*6
 for leaf,A in paths[S]:allocations[leaf]=A
 if free:allocations[next(i for i in range(6)if i not in{l for l,_ in active})]=31^S
 ck('coherent_partition_witness',sum(A.bit_count()for A in allocations)==5 and sum(allocations)==31)
 return dp[S],allocations

Efield=[[F()]*32 for _ in range(6)];regret=F();query_data=[];dp_calls=0;selector_counts=[]
for T in range(32):
 ypot={y:tuple(tuple(sum(y[m]*H[T][l][m][A]for m in range(20))for A in range(32))for l in range(6))for ys in MY for y in ys}
 for e3,e5 in product(range(4),repeat=2):
  j=32*(4*e3+e5)+T;vectors={tuple(tuple(x[l]*ypot[y][l][A]for A in range(32))for l in range(6))for x,y in product(MX[e3],MY[e5])};vectors=sorted(vectors)
  anchor=max(vectors,key=lambda v:sum(v[l][0]for l in range(6)));selector_counts.append(len(vectors))
  if j==0:
   for l,A in product(range(6),range(32)):Efield[l][A]+=g*F(anchor[l][A],DEN[T])
  if not co[j]:query_data.append((j,vectors));continue
  for l,A in product(range(6),range(32)):Efield[l][A]-=co[j]*F(anchor[l][A],DEN[T])
  worst=0
  for v in vectors:
   diff=tuple(tuple(v[l][A]-anchor[l][A]for A in range(32))for l in range(6))
   if sum(max(row)for row in diff)<=worst:continue
   score=extremum(diff,maximize=True);dp_calls+=1;worst=max(worst,score)
  regret+=co[j]*F(worst,DEN[T]);query_data.append((j,vectors))

common=lcm(*(x.denominator for row in Efield for x in row));integer=[[int(x*common)for x in row]for row in Efield]
v,alloc=extremum(integer,witness=True);reference_min=F(v,common);lower=reference_min-regret
actual=F()
for j,vectors in query_data:
 T=j%32;reading=max(sum(v[l][alloc[l]]for l in range(6))for v in vectors)
 if j==0:actual+=g*F(reading,DEN[T])
 actual-=co[j]*F(reading,DEN[T])
layout=[next(l for l,A in enumerate(alloc)if A>>q&1)for q in range(5)]
ck('full512_costs_and_menus',len(co)==len(query_data)==512 and min(co)>=0)
ck('old_theta_comparison_gate_negative',actual<0)
ck('regret_is_conservative_at_witness',lower<=actual)
ck('uniform_strict_value',min(strict)==F(414845761706,567846054963))
ck('complete_gate_value',actual==-F(934992879319436220663921430853,1489860425631860696494080000000000))
ck('partition_lower_value',lower==-F(8711574065190673896313336557113,2483100709386434494156800000000000))
result=dict(schema='five9square-partition-boundary-v1',status='COMPLETED_EXACT_PARTITION_DIAGNOSTIC',scope=__doc__,source_corner=[3,4,5,6],outside_primes=Q,global_layouts=6**5,strict_minimum=str(min(strict)),reference_minimum=str(reference_min),total_regret_upper=str(regret),uniform_gate_lower=str(lower),uniform_positive=lower>0,reference_minimizer_leaf_assignment=layout,comparison_cap_gate_at_reference_minimizer=str(actual),selector_potential_count=sum(selector_counts),exact_dp_calls=dp_calls,elapsed_seconds=time.monotonic()-start,checks_per_group=checks,check_count=sum(checks.values()),dependencies={'conditional30_fixedstar_augmented_certificate.json':source_pin},producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_lean_verification=False,quantifier_boundary='All coherent leaf assignments for exact fixed-selector DP extrema, at one comparison source corner and old635 theta. No positive arbitrary-phase theorem, no all-thinning optimality claim; reachability of this comparison corner by finite actual pure tails is not proved.')
args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
