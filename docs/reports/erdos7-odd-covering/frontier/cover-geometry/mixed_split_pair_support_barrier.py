"""Exact mixed split/common pair-support obstruction. Report492.
No producer, graph or optimizer is imported; pinned source inputs are checked.
Exact integer NumPy pair scan; ordinary Fraction checks for all weights and
explicit zero-survivor witnesses. The support is auxiliary, not a cover.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
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
INPUT=args.certificate or args.input_dir/'mixed_split_pair_support_certificate.json' 
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
# Every generated factor is <=38. Products in the scan are bounded by this
# deliberately loose seven-coordinate bound, well within signed int64.
need(4*38**7+76<2**63,'bounded exact integer arithmetic')
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

inp=json.loads(INPUT.read_text())
need(inp['reference']==[2,7,3,4] and inp['split_later_primes']==[7],'scope')
ids=inp['indices'];need(len(ids)==len(set(ids))==12705 and ids==sorted(ids),'support IDs')
need(all(isinstance(i,int) and 0<=i<len(rows) for i in ids),'valid support IDs')
S=set(ids);support=[rows[i] for i in ids]
middle=sum((weights[i] for i in ids),F());total=middle+overflow
for key,val in [('middle_mass',middle),('overflow39',overflow),('total_mass',total),('m7',M7),('excess',total-M7)]:need(F(inp[key])==val,'independent fraction '+key)
need(total>M7,'strict method barrier')

# Immediate covers generate the whole fixed-3/5 paired partial order.
finite_covers=0;overflow_covers=0
for s in support:
 children=[]
 for j in range(2,7):
  opts=(2,-2) if j==2 and s[j]==0 else ((s[j]+(1 if s[j]>0 else -1),) if j==2 else (s[j]+1,))
  for z in opts:children.append(s[:j]+(z,)+s[j+1:])
 for child in children:
  if load(child)>=39:overflow_covers+=1
  else:
   need(index[child] in S,'support not upward at '+str(s)+' -> '+str(child));finite_covers+=1

# Prove the coefficient identity pointwise for all16 membership patterns.
for a,b,c,d in product((0,1),repeat=4):
 rhs=(a+b-a*b)+(c+d-c*d)-a*d-b*c+a*b*c+a*b*d+a*c*d+b*c*d-2*a*b*c*d
 need(rhs==max(a+c,b+d),'universal literal selector identity')
# For these split/common boxes, every triple/quad intersection is the same
# common-coordinate box. Thus the exact coefficient identity gives the N
# used below: Qx+Qy-cross1-cross2+2*common. No graph data is consumed.
@lru_cache(None)
def literal_inventory(s):
 a,b=boxes(s)
 return set(product(*(range(f) for f in a))),set(product(*(range(f) for f in b)))

# For every pair of load classes find the least literal N over ALL support
# pairs (including diagonals). Feasible zero witnesses at these minima cover
# larger N without asserting optimum or graph completeness from a producer.
groups=defaultdict(list)
for i,s in zip(ids,support):groups[load(s)].append((i,s))
mins=[];ordered_pairs=0
for q in sorted(groups):
 for r in sorted(groups):
  if r<q:continue
  gx,gy=groups[q],groups[r];Y=np.asarray([s for _,s in gy],dtype=np.int64)
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
   need(np.all(nn>=max(q,r)+1) and np.all(nn<=q+r),'literal pair capacity interval')
   mn=int(nn.min());ordered_pairs+=nn.size
   if mn<best:
    ii,jj=np.unravel_index(int(nn.argmin()),nn.shape);best=mn;arg=(part[ii][0],gy[jj][0])
  ai,bi=literal_inventory(rows[arg[0]]);aj,bj=literal_inventory(rows[arg[1]])
  literalN=sum(max(int(d in ai)+int(d in aj),int(d in bi)+int(d in bj)) for d in ai|bi|aj|bj)
  need(literalN==best,'literal sets at minimizing pair')
  mins.append((q,r,best,arg))

# Only find and verify feasible witnesses; no minimax theorem or optimizer.
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

witnesses=[{'q':q,'r':r,'minimum_N':n,'representative_indices':list(arg),'zero_witness':zero_witness(q,r,n)} for q,r,n,arg in mins]
overflow_witness=zero_witness(20,39,40)
# In every profile Q>=20 the common unit label supplies two units; every
# other union label supplies >=1, so N>=max(Qx,Qy)+1. Any overflow pair
# therefore dominates(20,39,40), after swapping the two points if required.
out={'verified':True,'support_sha256':hashlib.sha256(INPUT.read_bytes()).hexdigest(),'algorithm':'Independent Cartesian profiles and literal shell law; full exact integer NumPy pair scan by load classes; direct set check at each capacity minimum; rational feasible zero witnesses without optimization or producer imports.','profiles_Q20_through38':len(rows),'safe_profiles':len(allrows)-len(rows),'support_vertices':len(ids),'unordered_distinct_support_pairs':len(ids)*(len(ids)-1)//2,'integer_pairs_scanned_including_equal_load_symmetry':ordered_pairs,'load_class_pairs':len(mins),'finite_immediate_order_covers':finite_covers,'overflow_immediate_order_covers':overflow_covers,'middle_mass':str(middle),'overflow39':str(overflow),'total_mass':str(total),'total_mass_float':float(total),'m7':str(M7),'excess':str(total-M7),'excess_float':float(total-M7),'witnesses':witnesses,'overflow_zero_witness':overflow_witness,'source_inputs':source_inputs,'integer_scan_dtype':'numpy.int64','integer_intermediate_bound':4*38**7+76,'Lean_rerun':False,'boundary':'An upward auxiliary comparison support of mass above m7 satisfying every pair-positive-K exclusion. No claim that this support is an actual source survivor set or original congruence cover. Ordinary full-history monotone comparison and literal-capacity relaxation remain the specified method; new Lean verification is absent.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({k:out[k] for k in ('support_vertices','unordered_distinct_support_pairs','total_mass_float','excess_float')},indent=2))
