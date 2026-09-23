"""Exact integer-cut upper bound for the fixed mixed comparison. Report496.
Reconstructs active pair/triple inventories, integer triangle cuts, upward
rows, all rational weights and the complete positive residual charge.
Standard library only; no producer graph or optimization result is trusted.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,combinations,permutations
from collections import defaultdict
from math import prod
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
INPUT=args.certificate or args.input_dir/'mixed_split_integer_cut_certificate.json' 
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

@lru_cache(None)
def minimum(q,r,n):
 ax,ay=min(q,22),min(r,22);bx,by=min(q,28),min(r,28);A=min(n,ax+ay);B=min(n,bx+by);tl,th=max(0,A-ay),min(ax,A);ul,uh=max(0,B-by),min(bx,B)
 def value(t,u):
  rx=(22-t)*(28-u);ry=(22-A+t)*(28-B+u)
  return (F(),F(rx-q),F(ry-r),F(rx+ry-n))
 vals=[]
 corners=((tl,ul),(th,ul),(th,uh),(tl,uh))
 for p0,p1 in zip(corners,corners[1:]+corners[:1]):
  v0=value(*p0);v1=value(*p1);zs={F(),F(1)}
  for a,b in combinations(range(4),2):
   intercept=v0[a]-v0[b];slope=(v1[a]-v0[a])-(v1[b]-v0[b])
   if slope:
    z=-intercept/slope
    if 0<=z<=1:zs.add(z)
  for z in zs:vals.append(max(a+z*(b-a) for a,b in zip(v0,v1)))
 return min(vals)

inp=json.loads(INPUT.read_text())
need(inp['reference']==[2,7,3,4] and inp['split_later_primes']==[7]
     and inp['common_later_primes']==[11,13,17,19] and F(inp['theta'])==F(1,3696),
     'fixed chart and threshold')
D=inp['denominator'];need(type(D) is int and D>0,'positive exact denominator')
for kind,size in (('pairs',2),('genuine_triples',3),('triangle_cliques',3),('order',2)):
 entries=inp[kind];need(type(entries) is list,'row collection')
 need(len({tuple(e[:-1]) for e in entries})==len(entries),'unique rows within kind')
 for e in entries:
  need(type(e) is list and len(e)==size+1 and all(type(x) is int for x in e),
       'strict integer row schema')
  ids,units=e[:-1],e[-1]
  need(len(set(ids))==size and all(0<=i<len(rows) for i in ids) and units>0,
       'distinct valid row indices and positive multiplier')
  if kind!='order':need(ids==sorted(ids),'sorted unordered row')

pair_edges={tuple(e[:2]) for e in inp['pairs']}
for a,b,c,units in inp['triangle_cliques']:
 pair_edges.update(combinations((a,b,c),2))
types={}
for i,j in sorted(pair_edges):
 q,r,n=literal_capacities((i,j));k=minimum(q,r,n)
 need(k>=F(1,3),'pair bound at the common threshold')
 types[(q,r,n)]=k
# Each genuine triple is checked anew using its seven literal capacities.
triples=[]
for a,b,c,units in inp['genuine_triples']:
 ids=(a,b,c);N=literal_capacities(ids);proof=triple_certificate(N)
 need(F(proof['K3'])>=F(1,2),'genuine triple bound at the common threshold')
 triples.append({'indices':list(ids),**proof})
for i,j,units in inp['order']:
 s,t=rows[i],rows[j];diff=[k for k in range(7) if s[k]!=t[k]]
 need(len(diff)==1 and diff[0]>=2,'one later-coordinate enlargement')
 k=diff[0]
 opts=(2,-2) if k==2 and s[k]==0 else ((s[k]+(1 if s[k]>0 else -1),) if k==2 else (s[k]+1,))
 need(t[k] in opts,'upward order direction')

# Integer column loads allow negative values from the -z_j order coefficient.
# Multipliers themselves must remain nonnegative. Pay every positive residual.
loads=[0]*len(rows);price=0
for kind,rhs in (('pairs',1),('genuine_triples',2),('triangle_cliques',1)):
 for *ids,units in inp[kind]:
  for i in ids:loads[i]+=units
  price+=rhs*units
for i,j,units in inp['order']:loads[i]+=units;loads[j]-=units
residuals=[max(w-F(u,D),F()) for w,u in zip(weights,loads)]
residual=sum(residuals,F());upper=overflow+F(price,D)+residual

# Pin the earlier fractional witness, and check that all true triples used
# here belong to precisely its declared constraint family. No optimality claim.
prior_path=args.input_dir/'mixed_split_fractional_support_barrier.json'
prior_raw=prior_path.read_bytes()
need(hashlib.sha256(prior_raw).hexdigest()=='3ddf4010edf231767de37317a3dc33847acf956c27f9240980ba27415a7a2cb8','prior result identity')
prior=json.loads(prior_raw)
need(F(prior['middle_mass'])==all_middle and F(prior['overflow_mass'])==overflow
     and F(prior['m7'])==M7,'same comparison weights and source')
hyperedges={tuple(e['indices']) for e in prior['hyperedges']}
need(all(tuple(e[:3]) in hyperedges for e in inp['genuine_triples']),'same declared triple system')
lower=F(prior['fractional_support_exact_mass'])
need(lower>upper>M7,'strict relaxation gap and still above target')
# One explicit triangle displays where the earlier fractional witness fails.
a,b,c,units=max(inp['triangle_cliques'],key=lambda e:e[-1])
example=[]
for i,j in combinations((a,b,c),2):
 q,r,n=literal_capacities((i,j))
 example.append({'indices':[i,j],'Qx':q,'Qy':r,'N':n,'K2':str(minimum(q,r,n))})
cover_path=args.input_dir/'mixed_split_fractional_support_certificate.json'
cover_raw=cover_path.read_bytes()
need(hashlib.sha256(cover_raw).hexdigest()==prior['certificate_sha256'],'prior witness identity')
cover=json.loads(cover_raw)['cover_doubled']
example_values=[F(2-cover[i],2) for i in (a,b,c)]
need(sum(example_values)>1,'explicit earlier fractional cut violation')

out={'verified':True,'certificate_sha256':hashlib.sha256(INPUT.read_bytes()).hexdigest(),
 'source_inputs':source_inputs,'prior_fractional_result_sha256':'3ddf4010edf231767de37317a3dc33847acf956c27f9240980ba27415a7a2cb8',
 'profile_count':len(rows),'all_active_pair_edges':len(pair_edges),
 'literal_pair_capacity_types':[{'Qx':q,'Qy':r,'N':n,'K2':str(k)}
                              for (q,r,n),k in sorted(types.items())],
 'minimum_active_K2':str(min(types.values())),
 'active_rows':{kind:len(inp[kind]) for kind in ('pairs','genuine_triples','triangle_cliques','order')},
 'triple_exact_vertex_certificates':triples,'row_price_units':price,'denominator':D,
 'positive_residual_columns':sum(r>0 for r in residuals),
 'negative_column_loads':sum(u<0 for u in loads),'exact_residual_charge':str(residual),
 'safe_mass':str(safe),'middle_mass':str(all_middle),'overflow_mass':str(overflow),
 'exact_upper':str(upper),'upper_float':float(upper),'m7':str(M7),
 'upper_excess_over_m7':str(upper-M7),'upper_excess_float':float(upper-M7),
 'prior_fractional_feasible_mass':str(lower),'relaxation_gap_lower':str(lower-upper),
 'relaxation_gap_lower_float':float(lower-upper),
 'example_triangle':{'indices':[a,b,c],'profiles':[list(rows[i]) for i in (a,b,c)],
    'pair_capacities':example,'multiplier_units':units,
    'prior_fractional_values':list(map(str,example_values))},
 'Lean_rerun':False,
 'scope':'Fixed six-anchor reference(2,7,3,4), split3/5/7, common11/13/17/19, theta1/3696. A universal upper bound on binary upward supports satisfying valid pair and the declared genuine triple constraints.',
 'boundary':'Exact positive-residual certificate, not solver optimality. The bound remains above m7 and gives no original noncoverage conclusion. Fractional optimum minus binary optimum is at least the displayed positive gap for the same report495 constraint system; neither optimum is asserted computed.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({k:out[k] for k in ('active_rows','upper_float','upper_excess_float',
                                  'relaxation_gap_lower_float')},indent=2))
