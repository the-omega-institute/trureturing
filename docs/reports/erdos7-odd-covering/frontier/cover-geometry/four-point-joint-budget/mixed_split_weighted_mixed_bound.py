"""Weighted mixed budgets exclude triples with zero total-only bounds.
Report499: 24 retained exact certificates, no optimizer or search history.
Every axis vertex and pair zero witness is reconstructed with Fraction.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations,permutations
from functools import lru_cache
from collections import Counter
from math import prod
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate',type=Path,default=ROOT/'mixed_split_weighted_mixed_certificate.json')
parser.add_argument('--output',type=Path)
args=parser.parse_args()
def need(t,m):
 if not t:raise ValueError(m)
def signed(s):return tuple(max(1,z) for z in s),tuple(max(1,-z) for z in s)
def boxes(s):
 a,b=signed(s[:3]);return a+s[3:],b+s[3:]
def load(s):
 a,b=signed(s[:3]);return (prod(a)+prod(b)-1)*prod(s[3:])

# Independent finite Cartesian recursion, in the input's declared index order.
allrows=[]
def complete(s):
 if len(s)==7:allrows.append(s);return
 for f in range(1,39):
  child=s+(f,)
  if load(child)>38:break
  complete(child)
third=list(range(2,39))+list(range(-2,-39,-1))
for s3 in third:
 for s5 in third+[0]:
  for s7 in [0]+third:
   s=(s3,s5,s7)
   if load(s)<=38:complete(s)
need(len(allrows)==23408 and len(set(allrows))==23408,'full finite profile space')
rows=[s for s in allrows if load(s)>=20];need(len(rows)==20076,'middle profile order')
index={s:i for i,s in enumerate(rows)}

@lru_cache(None)
def literal_inventory(s):
 a,b=boxes(s)
 return set(product(*(range(f) for f in a))),set(product(*(range(f) for f in b)))
def literal_capacities(ids):
 ab=[literal_inventory(rows[i]) for i in ids];labels=set().union(*(a|b for a,b in ab))
 return tuple(sum(max(sum(d in ab[i][0] for i in range(len(ids)) if m&(1<<i)),sum(d in ab[i][1] for i in range(len(ids)) if m&(1<<i))) for d in labels) for m in range(1,1<<len(ids)))

# Every retained seed obtains a fresh exact vertex proof, no inherited solver
# conclusion. Distinct ordered capacities share only this exact verifier.
def det(A):
 return A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1])-A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0])+A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0])
def solve(A,b):
 d=det(A)
 if not d:return None
 return tuple(F(det(tuple(tuple(b[i] if j==col else A[i][j] for j in range(3)) for i in range(3))),d) for col in range(3))
def poly_vertices(N,axis):
 constraints=[(tuple(-int(j==i) for j in range(3)),0) for i in range(3)]
 for mask in range(1,8):
  b=N[mask-1]
  if mask in (1,2,4):b=min(axis,b)
  constraints.append((tuple(int(bool(mask&(1<<i))) for i in range(3)),b))
 out=set()
 for ix in combinations(range(10),3):
  v=solve(tuple(constraints[i][0] for i in ix),tuple(constraints[i][1] for i in ix))
  if v is not None and all(sum(a*x for a,x in zip(row,v))<=b for row,b in constraints):out.add(v)
 return sorted(out)
@lru_cache(None)
def triple_certificate(N):
 V,W=poly_vertices(N,22),poly_vertices(N,28);need(V and W,'seed polytope nonempty')
 k,i,j=min((sum((22-a)*(28-b) for a,b in zip(t,u))-N[-1],i,j) for i,t in enumerate(V) for j,u in enumerate(W))
 return {'capacity':list(N),'K3':str(k),'axis23_vertices':[[str(x) for x in v] for v in V],'axis29_vertices':[[str(x) for x in v] for v in W],'minimum_at':[i,j]}

def zero_witness(q,r,n):
 A=min(n,min(q,22)+min(r,22));B=min(n,min(q,28)+min(r,28))
 xt=(max(0,A-min(r,22)),min(q,22,A));yt=(max(0,B-min(r,28)),min(q,28,B))
 corners=((xt[0],yt[0]),(xt[1],yt[0]),(xt[1],yt[1]),(xt[0],yt[1]))
 def residual(t,u):return ((22-t)*(28-u),(22-A+t)*(28-B+u))
 for e0,e1 in zip(corners,corners[1:]+corners[:1]):
  v0=residual(*e0);v1=residual(*e1);lo,hi=F(0),F(1)
  for f0,f1 in ((v0[0]-q,v1[0]-q),(v0[1]-r,v1[1]-r),(sum(v0)-n,sum(v1)-n)):
   slope=f1-f0
   if slope>0:hi=min(hi,F(-f0,slope))
   elif slope<0:lo=max(lo,F(-f0,slope))
   elif f0>0:hi=F(-1)
  if lo>hi:continue
  t=F(e0[0])+lo*(e1[0]-e0[0]);u=F(e0[1])+lo*(e1[1]-e0[1]);a=(t,A-t);b=(u,B-u)
  need(all(0<=z<=min(22,cap) for z,cap in zip(a,(q,r))),'witness axis23 bounds')
  need(all(0<=z<=min(28,cap) for z,cap in zip(b,(q,r))),'witness axis29 bounds')
  need(sum(a)<=n and sum(b)<=n,'witness shared axis caps')
  rem=tuple((22-aa)*(28-bb) for aa,bb in zip(a,b))
  need(all(0<=z<=cap for z,cap in zip(rem,(q,r))) and sum(rem)<=n,'witness complete mixed deletion')
  return {'axis23':list(map(str,a)),'axis29':list(map(str,b)),'mixed_deletion':list(map(str,rem))}
 raise ValueError('no zero witness at '+str((q,r,n)))


inp=json.loads(args.certificate.read_text())
need(inp['new_primes']==[23,29] and inp['old_primes']==[3,5,7,11,13,17,19]
     and inp['split_positions']==[0,1,2] and inp['common_positions']==[3,4,5,6]
     and F(inp['theta'])==F(1,3696),'fixed chart and threshold')
need(len(inp['seeds'])==24,'declared finite seed family')
proofs=[];axis_cases={}
for seed in inp['seeds']:
 ids=tuple(seed['indices']);weight=tuple(seed['weight'])
 need(len(ids)==3 and len(set(ids))==3 and all(type(i) is int and 0<=i<len(rows) for i in ids),
      'three distinct profile indices')
 need([list(rows[i]) for i in ids]==seed['profiles'],'literal declared profiles')
 need(len(weight)==3 and all(type(w) is int and w>0 for w in weight),'positive integer weight')
 ab=[literal_inventory(rows[i]) for i in ids];labels=set().union(*(a|b for a,b in ab))
 patterns=Counter((tuple(int(d in a) for a,b in ab),tuple(int(d in b) for a,b in ab)) for d in labels)
 weighted_cap=sum(n*max(sum(w*x for w,x in zip(weight,a)),sum(w*x for w,x in zip(weight,b)))
                  for (a,b),n in patterns.items())
 N=literal_capacities(ids);V=poly_vertices(N,22);U=poly_vertices(N,28)
 oldmin=min(sum((22-t)*(28-u) for t,u in zip(v,z))-N[-1] for v in V for z in U)
 need(oldmin<=0,'old total-only relaxation has no positive sum bound')
 val,i,j=min((sum(w*(22-t)*(28-u) for w,t,u in zip(weight,v,z))-weighted_cap,i,j)
             for i,v in enumerate(V) for j,z in enumerate(U))
 need(val>=F(sum(weight),6),'new edge at the same theta1/3696')
 witnesses=[]
 for x,y in combinations(range(3),2):
  q,r,n=literal_capacities((ids[x],ids[y]))
  witnesses.append({'points':[x,y],'capacity':[q,r,n],'witness':zero_witness(q,r,n)})
 axis_cases.setdefault(N,{'capacities':list(N),'axis23_vertices':[list(map(str,v)) for v in V],
                        'axis29_vertices':[list(map(str,v)) for v in U]})
 proofs.append({'indices':list(ids),'profiles':[list(rows[i]) for i in ids],
  'weight':list(weight),'weighted_capacity':weighted_cap,'subset_capacities':list(N),
  'literal_label_count':len(labels),'membership_patterns':[{'A':list(a),'B':list(b),'count':n}
                                                        for (a,b),n in sorted(patterns.items())],
  'old_total_minimum':str(oldmin),'weighted_minimum':str(val),
  'vertex_counts':[len(V),len(U)],'vertex_pairs':len(V)*len(U),
  'minimum_at':[i,j],'minimizing_axes':[list(map(str,V[i])),list(map(str,U[j]))],
  'weighted_survivor_sum_lower':str(val/616),
  'isolated_strict_bad_threshold':str(val/(616*sum(weight))),
  'pair_zero_witnesses':witnesses})
need(len({tuple(p['indices']) for p in proofs})==24,'distinct ordered seeds')
# The first seed has an especially simple sharp weighted certificate.
first=proofs[0]
need(first['indices']==[2780,108,14353] and first['weight']==[2,7,4]
     and first['weighted_capacity']==252 and F(first['weighted_minimum'])==44,
     'distinguished common-selector certificate')
# Its mixed weight is in one of report498's linear cones: no hidden choice
# of a new selector in the three component budgets.
ids=tuple(first['indices']);ab=[literal_inventory(rows[i]) for i in ids]
labels=set().union(*(a|b for a,b in ab))
weights=((1,2,1),(0,1,1),(0,1,0));coefs=(2,2,1)
cs=[sum(max(sum(w[i]*int(d in ab[i][s]) for i in range(3)) for s in (0,1))
        for d in labels) for w in weights]
need(cs==[76,40,20] and sum(c*n for c,n in zip(coefs,cs))==252,
     'same-cone decomposition of the mixed bound')
# The simpler weight121 already gives a new positive edge.
N=tuple(first['subset_capacities']);V=poly_vertices(N,22);U=poly_vertices(N,28)
simple=min(sum(w*(22-t)*(28-u) for w,t,u in zip((1,2,1),v,z))-76 for v in V for z in U)
need(simple==4,'simple ten-direction mixed edge')
out={'verified':True,'certificate_sha256':hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
 'profile_count':len(rows),'seed_count':len(proofs),'axis_capacity_case_count':len(axis_cases),
 'axis_capacity_cases':[axis_cases[N] for N in sorted(axis_cases)],'seeds':proofs,
 'distinguished_simple_weight':[1,2,1],'distinguished_simple_capacity':76,
 'distinguished_simple_minimum':str(simple),'common_theta':'1/3696','Lean_rerun':False,
 'scope':'One fixed original full-label selector per numerical modulus, first-root split old coordinates3/5/7 and common11/13/17/19. Twenty-four positive weighted mixed constraints with every old pair bound and total-only triple bound permitting zero.',
 'boundary':'Ordinary uniform local proof and exact rational vertices, not arithmetic realization or a global source-mass bound. Weighted mixed constraints are used with the unchanged seven-subset axis polytopes; no solver optimality or new Lean claim.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({'seed_count':len(proofs),'axis_capacity_cases':len(axis_cases),
 'first_weighted_capacity':252,'first_weighted_minimum':44,'first_bound':'1/14',
 'first_vertex_pairs':first['vertex_pairs']},indent=2))
