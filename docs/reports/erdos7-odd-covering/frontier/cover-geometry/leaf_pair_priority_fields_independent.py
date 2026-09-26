#!/usr/bin/env python3
"""Independent reconstruction from pure mathematical field specification.
Reads only canonical640 coefficients and canonical658 network data.
Does not read the same-round priority95 producer, its data, or its algorithms.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,product
from math import prod,lcm
from hashlib import sha256
from argparse import ArgumentParser
import json
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
ROOT=args.directory
raw=(ROOT/'remaining33_global_root_exclusion_certificate.json').read_bytes()
netraw=(ROOT/'joint_square_pair_225_star_certificate.json').read_bytes()
base=json.loads(raw);net=json.loads(netraw)
checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c:raise RuntimeError(k)
ck('canonical640_pin',sha256(raw).hexdigest()=='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4')
ck('canonical658_pin',sha256(netraw).hexdigest()=='cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5')
Q=(7,11,13,17,19); edges=list(combinations(range(5),2))
r=[F(1,q-1) for q in Q]; a=[F(1,q*(q-2)) for q in Q]
z=[F(5,6)]+[F(q-2,q-1)-2*a[k] for k,q in enumerate(Q) if k]
g=F(200163067,201247200)
C=[F(x) for x in base['combined512_coefficients']]
for k in range(1,5):C[9*32+(1<<k)]+=g*a[k]
ck('complete512_nonnegative',len(C)==512 and min(C)>=0)
I=[0,1,2,4,5];J=[m for m in range(20) if m!=5]
# Six central profiles suffice algebraically; literal cells are retained below.
profiles={}
for l in I:
 for m in J:
  if l<3 and m<5:continue
  n=int(l//3==1)+int(m//5==2)+int(l==5)
  key=(n,int(l==5))
  zz=list(z);zz[0]-=F(n,35)
  beta=[a[i]*r[j]+r[i]*a[j]+r[i]*r[j]*int(l==5) for i,j in edges]
  profiles[key]=(zz,beta)
# Explicit induced polynomials for every subset of the dependency graph's10edges.
# Independent sets are zero, one or two disjoint edges.
strict={}; Hprofiles={}
for key,(zz,beta) in profiles.items():
 p=[b/(zz[i]*zz[j]) for b,(i,j) in zip(beta,edges)]
 vals=[]
 for mask in range(1024):
  chosen=[e for e in range(10) if mask>>e&1]
  val=1-sum((p[e] for e in chosen),F(0))
  val+=sum((p[e]*p[f] for e,f in combinations(chosen,2) if set(edges[e]).isdisjoint(edges[f])),F(0))
  ck('all_induced_shearer_polynomials_positive',val>0)
  vals.append(val)
 strict[str(key)]=str(min(vals))
 table=[]
 for support in range(32):
  U=set(i for i in range(5) if not(support>>i&1))
  val=prod(zz[i] for i in U)
  es=[e for e,ends in enumerate(edges) if set(ends)<=U]
  val-=sum((beta[e]*prod(zz[i] for i in U-set(edges[e])) for e in es),F(0))
  val+=sum((beta[e]*beta[f]*prod(zz[i] for i in U-set(edges[e])-set(edges[f])) for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])),F(0))
  ck('positive_response_below_unary_product',0<val<=prod(zz[i] for i in U))
  table.append(val)
 Hprofiles[key]=table
hden=lcm(*(x.denominator for hh in Hprofiles.values() for x in hh))
cden=lcm(g.denominator,*(x.denominator for x in C)); cnum=[int(x*cden) for x in C];gnum=int(g*cden)
THETA_DEN=180

def tnum(weak,l,m):
 if l==3 or m==5 or (l<3 and m<5):return 0
 if l==5:return 180
 if m//5==2:return 171 if l==weak else 165
 return 165 if l==weak else 160

for l in range(6):
 for m in range(20):
  for i,j in product(I,J):
   t=tnum(i,l,m)
   ck('theta_between_zero_and_one',0<=t<=180)
   if l in I:ck('ternary_weak_marker_priority',tnum(l,l,m)>=t)
   if m in J:ck('quinary_weak_marker_priority',tnum(i,l,m)==t)

H={}
for support in range(32):
 arr=[[0]*20 for _ in range(6)]
 for l,m in product(I,J):
  if l<3 and m<5:continue
  key=(int(l//3==1)+int(m//5==2)+int(l==5),int(l==5))
  arr[l][m]=int(Hprofiles[key][support]*hden)
 H[support]=arr
# Every selector is evaluated as an integer; no float comparison enters.
def maxima(mat,w,v):
 out=[]
 xgroups=[[w],[[w[l] if l//3==row else 0 for l in range(6)] for row in range(2)],[[w[l] if l==i else 0 for l in range(6)] for i in I],[[9 if l==i else 0 for l in range(6)] for i in I]]
 for family in xgroups:
  best=[0,0,0,0]
  for x in family:
   col=[sum(x[l]*mat[l][m] for l in I) for m in J]
   weighted=[col[k]*v[m] for k,m in enumerate(J)]
   local=[sum(weighted),max(sum(weighted[k] for k,m in enumerate(J) if m//5==root) for root in range(4)),max(weighted),60*max(col)]
   best=[max(a,b) for a,b in zip(best,local)]
  out.extend(best)
 return out

gates=[]; cornerfees={}
for i,j in product(I,J):
 w=[0 if l==3 else 1 if l==i else 2 for l in range(6)]
 v=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
 fields={};fees=0;mass=None
 for support in range(32):
  mat=[[H[support][l][m]*tnum(i,l,m) for m in range(20)] for l in range(6)]
  screen=maxima(mat,w,v)
  if support==0:mass=screen[0]
  for mode in range(16):
   fees+=cnum[32*mode+support]*screen[mode]
   ck('complete512_screens_nonnegative',screen[mode]>=0)
 numerator=gnum*mass-fees
 value=F(numerator,cden*9*75*THETA_DEN*hden)
 ck('each_corner_gate_above_one_over_five_hundred',value>F(1,500))
 gates.append(dict(weak3=i,weak5=j,gate=str(value),decimal=float(value)))
 cornerfees[str((i,j))]=dict(mass_numerator=mass,fees_numerator=fees)
minimum=min(F(row['gate']) for row in gates)
mins=[(row['weak3'],row['weak5']) for row in gates if F(row['gate'])==minimum]
ck('all_ninety_five_corners',len(gates)==95)
# The ordinary head source domination/caps remain658's fixedD interface.
policies=[]
for p in net['policies']:
 fee=F(net['fee_before_arbitrary'])+F(p['fee'])
 margin=minimum-fee;alpha=F(net['projection_alpha'])
 ck('complete_network_margin_positive',margin>0)
 ck('common_full_density_above_one_over_four_hundred_twenty_thousand',alpha*margin>F(1,420000))
 policies.append(dict(kind=p['kind'],K=p['K'],total_fee=str(fee),raw_margin=str(margin),raw_margin_decimal=float(margin),projected_margin=str(alpha*margin),projected_margin_decimal=float(alpha*margin)))
result=dict(schema='priority95-independent-reconstruction-v1',status='PASS',scope='Fixed null3/5, central9qs leaf5 and7squarestar roles(1,2,5),50retained incidences; arbitrary finite higher central pure phases via624actualsource and645priority.',new_lean_verification=False,read_same_round_producer=False,verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),source640_sha256=sha256(raw).hexdigest(),source658_sha256=sha256(netraw).hexdigest(),profiles=len(profiles),strict_induced_minima=strict,response_common_denominator=hden,coefficient_common_denominator=cden,minimum_gate=str(minimum),minimum_gate_decimal=float(minimum),minimizing_weak_pairs=mins,gates=gates,policies=policies,check_count=sum(checks.values()),checks=checks)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','profiles','minimum_gate','minimum_gate_decimal','minimizing_weak_pairs','check_count')}))
for p in policies:print(json.dumps({k:v for k,v in p.items() if k.endswith('decimal') or k in ('kind','K')}))
