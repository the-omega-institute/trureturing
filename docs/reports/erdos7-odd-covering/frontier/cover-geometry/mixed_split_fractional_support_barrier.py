"""Exact fractional obstruction with genuine triples and upward order. Report495.
Reconstructs all profiles, exact comparison weights, every potentially
violated pair, and the full declared nine-seed symmetry orbit. No pair graph,
optimizer or search history is an input. NumPy int64 and Fraction arithmetic.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,combinations,permutations
from collections import defaultdict
from math import prod
import argparse,hashlib,json
import numpy as np
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
INPUT=args.certificate or args.input_dir/'mixed_split_fractional_support_certificate.json' 
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
def need(x,msg):
 if not x:raise ValueError(msg)
# Source identity is checked without importing any comparison or pair producer.
source_inputs={
 'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d',
 'common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}
source_data={}
for name,digest in source_inputs.items():
 raw=(args.input_dir/name).read_bytes()
 need(hashlib.sha256(raw).hexdigest()==digest,'source identity '+name)
 source_data[name]=json.loads(raw)
source_rows=source_data['query_stoploss_completion.json']['rows']
common=source_data['common_law_mass_tail.json']['common_seven_core_law']
worst_rows=[r for r in source_rows if tuple(r['node'][:3])==(2,4,1)]
need(len(source_rows)==32 and len(worst_rows)==4,'same finite source vertices')
need(min(F(r['cores']['7']['live_mass_lower_cell_units'])/135 for r in worst_rows)==M7,
     'same worst-source mass')
need(F(common['unnormalized_mass_lower'])==M7,'common source lower mass')
need(tuple(map(F,common['conditional_caps']))==tuple(c for p,c in CAPS),'conditional caps')
need(F(common['unnormalized_joint_density_cap'])==F(27,2),'joint density cap')

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

# Direct counts in each literal source root, followed by geometric shell mass.
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
literal=sum(all(n%m!=r for r,m in ((0,3),(1,9),(4,27),(0,5),(1,25),(2,15))) for n in range(675))
need(F(literal,675)==F(221,675),'literal complete anchor mass')
weights=list(map(weight,rows))
safe=sum((weight(s) for s in allrows if load(s)<20),F())
all_middle=sum(weights,F());overflow=F(literal,675)-safe-all_middle
need(overflow>0,'all infinite valuation tails')

# Only the half-cover and nine seed triples are witness inputs.
inp=json.loads(INPUT.read_text());cover=inp['cover_doubled']
need(inp['reference']==[2,7,3,4] and inp['split_later_primes']==[7]
     and inp['common_later_primes']==[11,13,17,19] and F(inp['theta'])==F(1,3696),
     'fixed source chart and common threshold')
need(len(cover)==len(rows) and all(type(c) is int and c in (0,1,2) for c in cover),'half-cover schema')
counts={str(c):cover.count(c) for c in range(3)}
total=overflow+sum((w*F(2-c,2) for w,c in zip(weights,cover)),F())
need(total>M7,'strict fractional mass excess')
# Each immediate arrow generates the same fixed3/5 later-coordinate order.
finite_arrows=0;overflow_arrows=0
for i,s in enumerate(rows):
 for j in range(2,7):
  opts=(2,-2) if j==2 and s[j]==0 else ((s[j]+(1 if s[j]>0 else -1),) if j==2 else (s[j]+1,))
  for v in opts:
   child=s[:j]+(v,)+s[j+1:]
   if load(child)>=39:
    need(cover[i]>=0,'overflow order');overflow_arrows+=1
   else:
    need(child in index and cover[i]>=cover[index[child]],'finite upward order');finite_arrows+=1
need((finite_arrows,overflow_arrows)==(16858,88764),'complete middle order census')

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

seeds=[tuple(ids) for ids in inp['seed_indices']]
need(len(seeds)==9 and all(len(ids)==3 and len(set(ids))==3 and
     all(type(i) is int and 0<=i<len(rows) for i in ids) for ids in seeds),
     'nine declared triples of distinct profiles')
seedcerts=[]
for ids in seeds:
 N=literal_capacities(ids);c=triple_certificate(N)
 need(F(c['K3'])>=F(1,2),'triple bound at theta1/3696')
 seedcerts.append({'indices':list(ids),'profiles':[list(rows[i]) for i in ids],**c})
# Generate, deduplicate and check the entire declared symmetry family.
edges={};valid=excluded=0
for seed,ids in enumerate(seeds):
 N=tuple(seedcerts[seed]['capacity'])
 for a,b,f in product(permutations(range(3)),permutations(range(3,7)),(-1,1)):
  transformed=[tuple(f*rows[i][j] for j in a)+tuple(rows[i][j] for j in b) for i in ids]
  if any(s[0]==0 for s in transformed):excluded+=1;continue
  need(all(s in index for s in transformed),'valid orbit profile domain')
  image=tuple(index[s] for s in transformed)
  need(literal_capacities(image)==N,'literal capacities preserved by simultaneous symmetry')
  edge=tuple(sorted(image));valid+=1
  need(sum(cover[i] for i in edge)>=2,'triple half-cover inequality')
  edges.setdefault(edge,{'indices':list(edge),'seed':seed,
     'ordered_image':list(image),'split_permutation':list(a),
     'common_permutation':list(b),'global_flip':f})
need(len(edges)==432 and (valid,excluded)==(1632,960),'complete nine-seed symmetry orbit')

# Exact pointwise Boolean identity for the two-point literal inventory.
for a,b,c,d in product((0,1),repeat=4):
 rhs=(a+b-a*b)+(c+d-c*d)-a*d-b*c+a*b*c+a*b*d+a*c*d+b*c*d-2*a*b*c*d
 need(rhs==max(a+c,b+d),'all16 selector patterns')
# Split-coordinate triple/quad intersections equal the common-coordinate
# box, yielding N=Qx+Qy-I*(crossA+crossB-2) for every literal pair.
need(4*38**7+76<2**63,'signed int64 safety bound')
groups=defaultdict(list)
for i,s in enumerate(rows):
 if cover[i]<2:groups[(load(s),cover[i])].append((i,s))
mins={};scanned=0;blocks=0
for keyx in sorted(groups):
 q,cx=keyx
 for keyy in sorted(groups):
  r,cy=keyy
  if keyy<keyx or cx+cy>=2:continue
  gx,gy=groups[keyx],groups[keyy];Y=np.asarray([s for _,s in gy],dtype=np.int64)
  YA=np.maximum(Y[:,:3],1);YB=np.maximum(-Y[:,:3],1)
  best=1000;arg=None
  for start in range(0,len(gx),128):
   part=gx[start:start+128];X=np.asarray([s for _,s in part],dtype=np.int64)
   XA=np.maximum(X[:,:3],1);XB=np.maximum(-X[:,:3],1)
   cross1=np.ones((len(X),len(Y)),dtype=np.int64);cross2=cross1.copy();common=cross1.copy()
   for j in range(3):
    cross1*=np.minimum(XA[:,j,None],YB[None,:,j]);cross2*=np.minimum(XB[:,j,None],YA[None,:,j])
   for j in range(3,7):common*=np.minimum(X[:,j,None],Y[None,:,j])
   nn=q+r-common*(cross1+cross2-2)
   need(np.all(nn>=max(q,r)+1) and np.all(nn<=q+r),'literal pair capacity bounds')
   mn=int(nn.min());scanned+=nn.size
   if mn<best:
    ii,jj=np.unravel_index(int(nn.argmin()),nn.shape);best=mn;arg=(part[ii][0],gy[jj][0])
  need(literal_capacities(arg)[-1]==best,'literal sets at each cover/load minimum')
  pairkey=(q,r);old=mins.get(pairkey)
  if old is None or best<old[0]:mins[pairkey]=(best,arg)
  blocks+=1

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

deficient_distinct=counts['0']*(counts['0']-1)//2+counts['0']*counts['1']
extra_equal_group_symmetry=sum(len(v)*(len(v)-1)//2 for (q,c),v in groups.items() if c==0)
need(scanned==deficient_distinct+counts['0']+extra_equal_group_symmetry,'independent complete deficient pair census')
witnesses=[{'q':q,'r':r,'minimum_N':n,'representative_indices':list(arg),'zero_witness':zero_witness(q,r,n)} for (q,r),(n,arg) in sorted(mins.items())]
overflow_zero=zero_witness(20,39,40)
# All deficient repeated profiles have already appeared on the diagonal.
# Every overflow pair dominates(20,39,40): both Q>=20 and the common unit
# label gives N>=max(Qx,Qy)+1. Swapping aligns the larger-Q point with39.
out={'verified':True,'certificate_sha256':hashlib.sha256(INPUT.read_bytes()).hexdigest(),
 'source_inputs':source_inputs,'profile_count':len(rows),'safe_profile_count':len(allrows)-len(rows),
 'half_cover_counts':counts,'all_Q_le19_support_value':0,'all_Q_ge39_support_value':1,
 'safe_mass':str(safe),'middle_mass':str(all_middle),'overflow_mass':str(overflow),
 'fractional_support_exact_mass':str(total),'fractional_support_mass_float':float(total),
 'm7':str(M7),'fractional_support_excess':str(total-M7),
 'fractional_support_excess_float':float(total-M7),
 'finite_order_arrows_checked':finite_arrows,'overflow_order_arrows_checked':overflow_arrows,
 'seed_count':len(seeds),'seed_exact_vertex_certificates':seedcerts,
 'hyperedges_checked':len(edges),'hyperedges':[edges[e] for e in sorted(edges)],
 'valid_symmetry_images':valid,'excluded_zero_s3_images':excluded,
 'deficient_unordered_distinct_pairs':deficient_distinct,
 'integer_pairs_scanned_including_group_diagonals_and_symmetry':scanned,
 'cover_load_group_pairs':blocks,'load_class_pairs':len(mins),'witnesses':witnesses,
 'overflow_zero_witness':overflow_zero,'integer_scan_dtype':'numpy.int64',
 'integer_intermediate_bound':4*38**7+76,'Lean_rerun':False,
 'scope':'Fixed six-anchor reference(2,7,3,4), split old primes3/5/7 and common11/13/17/19. Every theoretical positive pair exclusion, exactly432 symmetry-generated three-point edges at theta1/3696, and complete fixed3/5 later-coordinate order.',
 'boundary':'Feasible fractional support z=1-cover/2, with Q<=19 assigned0 and Q>=39 assigned1. Its mass exceeds m7, so these fractional constraints cannot prove a mass upper bound below m7. Not a binary support, actual source or original cover. Integer optimization, other genuine triples, eight-anchor sources and unrestricted Erdos7 remain unresolved.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({k:out[k] for k in ('profile_count','hyperedges_checked',
 'deficient_unordered_distinct_pairs','fractional_support_mass_float',
 'fractional_support_excess_float')},indent=2))
