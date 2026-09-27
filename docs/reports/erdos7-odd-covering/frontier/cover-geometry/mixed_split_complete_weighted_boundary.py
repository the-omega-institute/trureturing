"""Report501: complete axis and mixed budgets, orbit and exact subset repair.
No SciPy/NumPy, proposer import, cached producer vertices, or float arithmetic.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations,permutations
from collections import Counter
from functools import lru_cache
from math import prod
import json,hashlib
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args();R=args.input_dir
CERT=args.certificate or R/'mixed_split_complete_weighted_boundary_certificate.json'
cert=json.loads(CERT.read_text())
PROFILES=tuple(map(tuple,cert['profiles']));IDS=tuple(cert['profile_indices']);W=tuple(cert['weight'])
O=tuple(tuple((mask>>i)&1 for i in range(3)) for mask in range(1,8));EXTRA=tuple(sorted(set(permutations((1,1,2)))));FULL=O+EXTRA

def need(t,m):
 if not t:raise ValueError(m)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def boxes(s):
 a=tuple(max(x,1) for x in s[:3])+s[3:];b=tuple(max(-x,1) for x in s[:3])+s[3:]
 return set(product(*(range(x) for x in a))),set(product(*(range(x) for x in b)))
need(cert['reference']==[2,7,3,4] and cert['old_primes']==[3,5,7,11,13,17,19] and cert['new_primes']==[23,29], 'source chart and untouched axes')
need(cert['split_old_primes']==[3,5,7] and cert['common_old_primes']==[11,13,17,19] and F(cert['theta'])==F(1,3696),'source split/common and threshold')
need(tuple(map(tuple,cert['subset_directions']))==O and tuple(map(tuple,cert['complete_axis_directions']))==FULL,'complete direction definitions')
need(len(PROFILES)==3 and all(len(s)==7 and all(type(x) is int for x in s) for s in PROFILES) and len(IDS)==3 and len(set(IDS))==3 and all(type(i) is int and 0<=i<20076 for i in IDS) and len(W)==3 and all(type(x) is int and x>=0 for x in W) and sum(W)>0,'three labelled weight slots')
ab=list(map(boxes,PROFILES));labels=set().union(*(a|b for a,b in ab));patterns=Counter((tuple(int(d in a) for a,b in ab),tuple(int(d in b) for a,b in ab)) for d in labels)
def cap(w):return sum(n*max(dot(a,w),dot(b,w)) for (a,b),n in patterns.items())
need(tuple(map(cap,O))==(22,21,39,30,45,42,58),'literal seven capacities');need(tuple(map(cap,EXTRA))==(85,78,79),'literal extra three capacities');need(cap(W)==892,'literal mixed weighted capacity')
def solve(A,b):
 M=[[F(v) for v in row]+[F(r)] for row,r in zip(A,b)]
 for k in range(3):
  pivot=next((i for i in range(k,3) if M[i][k]),None)
  if pivot is None:return None
  M[k],M[pivot]=M[pivot],M[k];v=M[k][k];M[k]=[x/v for x in M[k]]
  for i in range(3):
   if i!=k:
    a=M[i][k];M[i]=[x-a*y for x,y in zip(M[i],M[k])]
 return tuple(M[i][3] for i in range(3))
def constraints(axis,ws):
 c=[(tuple(-int(i==j) for i in range(3)),0) for j in range(3)]
 for w in ws:c.append((w,min(axis,cap(w)) if sum(w)==1 else cap(w)))
 return c
def vertices(axis,ws):
 cons=constraints(axis,ws);found=set();ind=0
 for ix in combinations(range(len(cons)),3):
  v=solve([cons[i][0] for i in ix],[cons[i][1] for i in ix])
  if v is None:continue
  ind+=1
  if all(dot(row,v)<=b for row,b in cons):found.add(v)
 return sorted(found),ind
results={}
for name,ws in (('subset',O),('complete10',FULL)):
 V,vn=vertices(22,ws);U,un=vertices(28,ws);minimum,t,u=min((sum(w*(22-a)*(28-b) for w,a,b in zip(W,t,u))-cap(W),t,u) for t in V for u in U);total,tt,uu=min((sum((22-a)*(28-b) for a,b in zip(t,u))-cap((1,1,1)),t,u) for t in V for u in U)
 results[name]={'directions':ws,'capacities':list(map(cap,ws)),'vertex_counts':[len(V),len(U)],'nonsingular_bases':[vn,un],'vertex_pairs':len(V)*len(U),'minimum_weighted':str(minimum),'minimizing_axis23':list(map(str,t)),'minimizing_axis29':list(map(str,u)),'unweighted_total_minimum':str(total),'unweighted_minimizers':[list(map(str,tt)),list(map(str,uu))],'axis23_vertices':[list(map(str,v)) for v in V],'axis29_vertices':[list(map(str,v)) for v in U]}
need(F(results['subset']['minimum_weighted'])==-59,'old-axis selected weight fails');need(F(results['complete10']['minimum_weighted'])==32,'full-axis weighted exact positive');need(F(32)>=F(sum(W),6),'common threshold strict-bad exclusion')
p=R/cert['support_file'];need(hashlib.sha256(p.read_bytes()).hexdigest()==cert['support_sha256'],'retained binary support identity');s=json.loads(p.read_text());support=set(range(20076))-set(s['excluded_middle_indices']);need(len(support)==15799 and set(IDS)<=support,'new triple really contained in pinned binary support')
# Independently enumerate the profile order (instead of reading NPZ/producer).
def load(s):
 from math import prod
 return (prod(max(1,x) for x in s[:3])+prod(max(1,-x) for x in s[:3])-1)*prod(s[3:])
rows=[]
def fill(s):
 if len(s)==7:
  if load(s)>=20:rows.append(s)
  return
 for x in range(1,39):
  t=s+(x,)
  if load(t)>38:break
  fill(t)
third=list(range(2,39))+list(range(-2,-39,-1))
for a in third:
 for b in third+[0]:
  for c in [0]+third:
   if load((a,b,c))<=38:fill((a,b,c))
need(len(rows)==20076 and tuple(rows[i] for i in IDS)==PROFILES,'canonical profile indices')
basic=[]
V=[tuple(map(F,v)) for v in results['complete10']['axis23_vertices']];U=[tuple(map(F,u)) for u in results['complete10']['axis29_vertices']]
for w in FULL:
 k,t,u=min((sum(ww*(22-x)*(28-y) for ww,x,y in zip(w,v,z))-cap(w),v,z) for v in V for z in U)
 basic.append({'weight':list(w),'capacity':cap(w),'minimum':str(k),'minimizers':[list(map(str,t)),list(map(str,u))]})
need(all(F(e['minimum'])<=0 for e in basic),'no individual basic mixed direction certifies this edge')
need(tuple(12*a+b+3*c for a,b,c in zip((1,1,1),(2,1,1),(1,1,0)))==W,'common-cone weight decomposition')
need(12*cap((1,1,1))+cap((2,1,1))+3*cap((1,1,0))==cap(W),'same-cone capacity additivity')

CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
@lru_cache(None)
def shell(p,E,ref,cells,f):
 if f>E:return F(p-1,p**f) if ref in cells else F()
 def exact(x):
  if x==ref:return False
  n=x-ref;v=0
  while n%p==0:n//=p;v+=1
  return v==f-1
 return F(sum(map(exact,cells)),p**E)
@lru_cache(None)
def initial(s3,s5):
 r=2 if s3>0 else 1
 xs=tuple(x for x in range(27) if x%3==r and x%9!=1 and x!=4)
 ys=tuple(y for y in range(25) if y%5 and y!=1 and not(r==2 and y%5==2))
 a=shell(3,3,2 if s3>0 else 7,xs,abs(s3))
 if not s5:return a*F(sum(y%5 not in(3,4) for y in ys),25)
 ref=3 if s5>0 else 4
 return a*shell(5,2,ref,tuple(y for y in ys if y%5==ref),abs(s5))
@lru_cache(None)
def weight(s):
 w=initial(s[0],s[1]);f=s[2];p,C=CAPS[0]
 w*=1-2*C/p if f==0 else C*F(p-1,p**abs(f))
 for (p,C),f in zip(CAPS[1:],s[3:]):w*=1-C/p if f==1 else C*F(p-1,p**f)
 return w

# The pinned report500 result carries its already checked pair/1608 proof.
# Taking a subset inherits these upper constraints; it does not inherit order
# automatically, so all order arrows are reconstructed and checked below.
def pinned(filename,digest):
 raw=(R/filename).read_bytes()
 need(hashlib.sha256(raw).hexdigest()==digest,'pinned prerequisite '+filename)
 return json.loads(raw)
base_result=pinned(cert['base_result_file'],cert['base_result_sha256'])
need(base_result['certificate_sha256']==cert['support_sha256'] and
     base_result['support_vertices']==len(support) and base_result['hyperedges_checked']==1608,
     'base support/result binding')
M7=F(7235955529,450000000000)
need(F(base_result['m7'])==M7,'same source threshold')
oldedges={tuple(e['indices']) for e in base_result['hyperedges']}
need(len(oldedges)==1608 and all(not set(e)<=support for e in oldedges),'base declared triple support')
half=pinned(cert['fractional_file'],cert['fractional_sha256'])['cover_doubled']
need(len(half)==20076 and all(type(x) is int and x in(0,1,2) for x in half),'prior fractional witness')
index={s:i for i,s in enumerate(rows)}
@lru_cache(None)
def pattern(ids):
 ab=[boxes(rows[i]) for i in ids];labels=set().union(*(a|b for a,b in ab))
 return Counter(tuple(sorted((tuple(int(d in a) for a,b in ab),tuple(int(d in b) for a,b in ab)))) for d in labels)
pat=pattern(IDS);edges={};eligible=0
for a,b,flip in product(permutations(range(3)),permutations(range(3,7)),(-1,1)):
 transformed=[tuple(flip*rows[i][j] for j in a)+tuple(rows[i][j] for j in b) for i in IDS]
 need(all(s[0]!=0 and s in index for s in transformed),'all seed images are eligible')
 image=tuple(index[s] for s in transformed);edge=tuple(sorted(image));eligible+=1
 need(pattern(image)==pat,'literal selector patterns preserved')
 if edge not in edges:
  edges[edge]={'indices':list(edge),'ordered_image':list(image),'ordered_weight':list(W),
               'sorted_weight':[W[image.index(i)] for i in edge],
               'split_permutation':list(a),'common_permutation':list(b),'global_flip':flip}
need(eligible==288 and len(edges)==48 and not(set(edges)&oldedges),'48 new genuine orbit edges')
violations=sorted(e for e in edges if set(e)<=support)
need(violations==[(4405,5640,16010),(4407,5640,16010)],'exact base support violations')
cover_counts=Counter(sum(half[i] for i in e) for e in edges)
need(cover_counts=={2:40,3:8},'fractional witness survives every new edge')
pred=[[] for _ in rows];arrows=[];overflow_arrows=0
for i,s in enumerate(rows):
 for j in range(2,7):
  opts=(2,-2) if j==2 and s[j]==0 else ((s[j]+(1 if s[j]>0 else -1),) if j==2 else (s[j]+1,))
  for v in opts:
   child=s[:j]+(v,)+s[j+1:]
   if load(child)>=39:overflow_arrows+=1;continue
   need(child in index,'order domain');k=index[child];pred[k].append(i);arrows.append((i,k))
need(len(arrows)==16858 and overflow_arrows==88764,'complete order census')
@lru_cache(None)
def ancestors(i):
 out={i}
 for p in pred[i]:out.update(ancestors(p))
 return frozenset(out)
repairs=[]
for endpoints in product(*violations):
 removed=set().union(*(ancestors(i)&support for i in endpoints))
 cost=sum((weight(rows[i]) for i in removed),F())
 repairs.append({'chosen_endpoints':list(endpoints),'required_removed_indices':sorted(removed),'exact_loss':str(cost)})
minimum=min(F(r['exact_loss']) for r in repairs)
removed=cert['remove_indices'];need(removed==[4405,4407] and set(removed)<=support,'declared repair')
remaining=support-set(removed)
need(all(i not in remaining or j in remaining for i,j in arrows),'repaired support upward order')
need(all(not set(e)<=remaining for e in oldedges|set(edges)),'all1656 edges preserved')
loss=sum((weight(rows[i]) for i in removed),F())
need(loss==minimum==F(25797248,11816768588625),'complete nine-choice deletion-only optimum')
base_mass=F(base_result['support_exact_mass']);mass=base_mass-loss
need(mass>M7 and len(remaining)==15797,'repaired binary obstruction above same source threshold')
# Recompute the mass using exactly the same literal shells, not proposer weights.
need(sum((weight(rows[i]) for i in support),F())+F(base_result['overflow_mass'])==base_mass,
     'literal source weights agree with the pinned base mass')
orbit={'eligible_transformations':eligible,'new_edges':len(edges),'old_overlap':0,
 'combined_edges':len(oldedges|set(edges)),'base_violated_edges':[list(e) for e in violations],
 'hyperedges':[edges[e] for e in sorted(edges)],
 'fractional_cover_sum_counts':{str(k):v for k,v in sorted(cover_counts.items())},
 'finite_order_arrows':len(arrows),'overflow_order_arrows':overflow_arrows,
 'all_nine_endpoint_choices':repairs,'remove_indices':removed,'exact_minimum_deletion_only_loss':str(loss),
 'repaired_support_vertices':len(remaining),'repaired_mass':str(mass),'repaired_mass_float':float(mass),
 'm7':str(M7),'repaired_excess':str(mass-M7),'repaired_excess_float':float(mass-M7),
 'scope':'Optimal removal cost only among upward subsets of the pinned report500 support; no global optimality or actual source realization.'}
out={'verified':True,'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),'basic_mixed_minima':basic,'orbit_and_subset_repair':orbit,'base_result_sha256':cert['base_result_sha256'],'fractional_sha256':cert['fractional_sha256'],'support_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'indices':IDS,'profiles':PROFILES,'weight':W,'literal_weighted_capacity':cap(W),'label_count':len(labels),'membership_pattern_counts':[{'A':a,'B':b,'count':n} for (a,b),n in sorted(patterns.items())],'axis_results':results,'weighted_survivor_lower':str(F(32,616)),'weighted_threshold_sum':str(F(sum(W),3696)),'new_binary_support_violated':True,'scope':'One exact new triple inside the retained15799-point binary support, common theta1/3696. All complete10 axis inequalities and one weighted mixed inventory; fixed full-label selectors.','boundary':'The selected weight does not work with seven subset axes; no assertion that every possible old-axis separating weight has been ruled out. The specified1656-edge system still has an explicit binary mass obstruction after repair. No global upper-bound improvement or original source realization is claimed. No new Lean verification.'}

# Normalize tuple-valued internal coordinates before exact JSON replay.
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({'weighted_minimum':results['complete10']['minimum_weighted'],
 'old_axis_weighted_minimum':results['subset']['minimum_weighted'],
 'basic_mixed_minima':[e['minimum'] for e in basic],
 'new_orbit_edges':len(edges),'combined_edges':orbit['combined_edges'],
 'repaired_support_vertices':len(remaining),'repaired_mass':float(mass),
 'repaired_excess':float(mass-M7)},indent=2))
