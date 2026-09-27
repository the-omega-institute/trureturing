"""Binary mass obstruction after all pairs and1608 genuine triple exclusions.
Rebuilds the entire profile chart and exact source weights. Standard library
only: split-signature capacity bounds and78 small common-box scans replace
the earlier138-million-pair NumPy audit. No solver or producer graph input.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,combinations,permutations
from collections import defaultdict,Counter
from math import prod
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--certificate',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
INPUT=args.certificate or args.input_dir/'mixed_split_binary_support_certificate.json'
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
 return None


inp=json.loads(INPUT.read_text())
need(inp['reference']==[2,7,3,4] and inp['split_later_primes']==[7]
     and inp['common_later_primes']==[11,13,17,19] and F(inp['theta'])==F(1,3696)
     and inp['include_all_Q_ge39'] is True,'fixed comparison and complete overflow')
excluded=inp['excluded_middle_indices']
need(len(excluded)==4277 and all(type(i) is int and 0<=i<len(rows) for i in excluded)
     and excluded==sorted(set(excluded)),'unique complement indices')
E=set(excluded);support=set(range(len(rows)))-E
need(len(support)==15799,'binary support size')
total=overflow+sum((weights[i] for i in support),F())
need(total>M7 and total==F(inp['expected_mass']) and total-M7==F(inp['expected_excess']),
     'exact positive mass excess')

# Immediate arrows generate the fixed3/5 order, including zero-mass points.
finite_arrows=0;overflow_arrows=0
for i,s in enumerate(rows):
 for j in range(2,7):
  opts=(2,-2) if j==2 and s[j]==0 else ((s[j]+(1 if s[j]>0 else -1),) if j==2 else (s[j]+1,))
  for v in opts:
   child=s[:j]+(v,)+s[j+1:]
   if load(child)>=39:overflow_arrows+=1
   else:
    need(child in index,'finite order domain')
    need(i not in support or index[child] in support,'binary upward order')
    finite_arrows+=1
need((finite_arrows,overflow_arrows)==(16858,88764),'complete order census')

# Boolean expansion of the literal two-point selector inventory. Every
# triple/quad intersection has split factors1 and common factor I, hence
# N=q+r-I*(crossA+crossB-2). The common unit label also gives N>=max(q,r)+1.
for a,b,c,d in product((0,1),repeat=4):
 rhs=(a+b-a*b)+(c+d-c*d)-a*d-b*c+a*b*c+a*b*d+a*c*d+b*c*d-2*a*b*c*d
 need(rhs==max(a+c,b+d),'all16 selector patterns')
G=defaultdict(lambda:defaultdict(set));load_counts=Counter()
for i in sorted(support):
 s=rows[i];q=load(s);key=tuple(max(1,x) for x in s[:3])+tuple(max(1,-x) for x in s[:3])
 G[q][key].add(s[3:]);load_counts[q]+=1
# At fixed q and split signature, every common box has the same product.
groups={}
for q,block in G.items():
 groups[q]=[]
 for key,common in sorted(block.items()):
  common=tuple(sorted(common));size=prod(common[0])
  need(all(prod(c)==size for c in common),'constant common product')
  groups[q].append((key,common,size))
need(sorted(groups)==list(range(20,39)),'all19 load classes represented')
common_pair_checks=0
@lru_cache(None)
def max_common_intersection(A,B):
 global common_pair_checks
 common_pair_checks+=len(A)*len(B)
 return max(prod(min(x,y) for x,y in zip(a,b)) for a in A for b in B)

# A sufficient capacity is found by verifying a rational zero witness; no
# claim that the first found capacity is the true optimum is needed.
pair_proofs=[];universal_classes=0;group_checks=0;coarse_checks=0;refined_checks=0
for q in sorted(groups):
 for r in sorted(groups):
  if r<q:continue
  chosen_n=None;witness=None
  for n in range(r+1,q+r+1):
   candidate=zero_witness(q,r,n)
   if candidate is not None:chosen_n=n;witness=candidate;break
  need(chosen_n is not None,'found explicitly verified sufficient pair capacity')
  if chosen_n==r+1:universal_classes+=1
  else:
   for a,AC,ap in groups[q]:
    for b,BC,bp in groups[r]:
     group_checks+=1
     cross=prod(min(a[j],b[j+3]) for j in range(3))+prod(min(a[j+3],b[j]) for j in range(3))-2
     need(cross>=0,'nonnegative opposite-box correction')
     # I<=min(ap,bp) gives a LOWER bound for N because cross>=0.
     if q+r-min(ap,bp)*cross>=chosen_n:coarse_checks+=1;continue
     refined_checks+=1
     I=max_common_intersection(*sorted((AC,BC)))
     need(q+r-I*cross>=chosen_n,'all actual common-box pair capacities are sufficient')
  pair_proofs.append({'q':q,'r':r,'certified_capacity_lower':chosen_n,
                     'zero_witness':witness,'method':'unit-label' if chosen_n==r+1 else 'split-signature'})
need(len(pair_proofs)==190 and universal_classes==144,'all190 class-pair proofs')
need((group_checks,coarse_checks,refined_checks,common_pair_checks)==(335592,335186,406,2175),
     'exact compressed pair-check census')
need(max_common_intersection.cache_info().misses==78,'distinct common-box scans')
finite_pairs=sum(load_counts[q]*load_counts[r] if q<r else load_counts[q]*(load_counts[q]-1)//2
                 for q in groups for r in groups if q<=r)
need(finite_pairs==len(support)*(len(support)-1)//2==124796301,'all finite distinct pairs covered')
overflow_zero=zero_witness(20,39,40)
need(overflow_zero is not None,'all overflow pairs dominate a verified zero witness')

# Recheck the old seed bounds and the24 canonical499 weighted bounds using
# exact vertices. Only parameters/results are read; no script is imported.
weighted_inputs={
 'mixed_split_weighted_mixed_certificate.json':'a250bb1150187f0cc8aed43961af3b336a66e17c0cc56b21240538d6b52693c1',
 'mixed_split_weighted_mixed_bound.json':'8ea93224863f320b1e9385d52c8792e1dcd20e03ebf9e8d74fecf54a56711113'}
weighted_data={}
for name,digest in weighted_inputs.items():
 raw=(args.input_dir/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'canonical499 input '+name)
 weighted_data[name]=json.loads(raw)
wc=weighted_data['mixed_split_weighted_mixed_certificate.json'];wr=weighted_data['mixed_split_weighted_mixed_bound.json']
need(wc['new_primes']==[23,29] and wc['old_primes']==[3,5,7,11,13,17,19]
     and wc['split_positions']==[0,1,2] and wc['common_positions']==[3,4,5,6]
     and F(wc['theta'])==F(1,3696),'canonical499 same chart')
need(wr['certificate_sha256']==weighted_inputs['mixed_split_weighted_mixed_certificate.json']
     and len(wc['seeds'])==len(wr['seeds'])==24,'canonical499 certificate binding')
@lru_cache(None)
def patterns(ids):
 ab=[literal_inventory(rows[i]) for i in ids];labels=set().union(*(a|b for a,b in ab))
 return Counter(tuple(sorted((sum(1<<j for j,(a,b) in enumerate(ab) if d in a),
                               sum(1<<j for j,(a,b) in enumerate(ab) if d in b)))) for d in labels)
def weighted_capacity(pat,w):
 val=lambda mask:sum(w[j] for j in range(3) if mask>>j&1)
 return sum(n*max(val(a),val(b)) for (a,b),n in pat.items())
prior_fractional_input={'mixed_split_fractional_support_certificate.json':'6d7555cc5496dffb2a058adf192fe49ac84064767b97fae586a5c273f6e59c28'}
for name,digest in prior_fractional_input.items():
 raw=(args.input_dir/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'canonical495 certificate')
 prior=json.loads(raw)
need(prior['reference']==[2,7,3,4] and prior['split_later_primes']==[7]
     and prior['common_later_primes']==[11,13,17,19] and F(prior['theta'])==F(1,3696),'same fractional chart')
oldseeds=prior['seed_indices'];need(len(oldseeds)==9,'old declared nine seeds')
prior_cover=prior['cover_doubled']
need(len(prior_cover)==len(rows) and all(type(c) is int and c in (0,1,2) for c in prior_cover),
     'pinned fractional witness schema')
seed_proofs=[]
for kind,seeds in (('old',[{'indices':ids,'weight':[1,1,1]} for ids in oldseeds]),('weighted',wc['seeds'])):
 for si,seed in enumerate(seeds):
  ids=tuple(seed['indices']);w=tuple(seed['weight'])
  need(len(ids)==3 and len(set(ids))==3 and all(type(i) is int and 0<=i<len(rows) for i in ids),'valid seed indices')
  need(len(w)==3 and all(type(x) is int and x>0 for x in w),'positive seed weights')
  N=literal_capacities(ids);C=weighted_capacity(patterns(ids),w)
  V=poly_vertices(N,22);U=poly_vertices(N,28);need(V and U,'full-dimensional seed polytopes')
  value=min(sum(a*(22-t)*(28-u) for a,t,u in zip(w,v,z))-C for v in V for z in U)
  need(value>=F(sum(w),6),'positive seed exclusion at common theta1/3696')
  if kind=='weighted':
   retained=wr['seeds'][si]
   need(seed['profiles']==[list(rows[i]) for i in ids] and retained['indices']==list(ids)
        and retained['weight']==list(w) and retained['subset_capacities']==list(N)
        and retained['weighted_capacity']==C and F(retained['weighted_minimum'])==value,
        'reconstructed exact canonical499 bound')
  seed_proofs.append({'kind':kind,'indices':list(ids),'weight':list(w),'subset_capacities':list(N),
                      'weighted_capacity':C,'minimum_numerator':str(value),'vertex_counts':[len(V),len(U)]})

# The same bijection of old cofactor exponent tuples transports every
# selector budget. Point weights remain attached to the tested points.
edge_sets={'old':set(),'weighted':set()};edge_records={};valid=Counter();zero_s3=Counter()
for si,seed in enumerate(seed_proofs):
 ids=tuple(seed['indices']);kind=seed['kind'];pat=patterns(ids)
 for a,b,flip in product(permutations(range(3)),permutations(range(3,7)),(-1,1)):
  transformed=[tuple(flip*rows[i][j] for j in a)+tuple(rows[i][j] for j in b) for i in ids]
  if any(s[0]==0 for s in transformed):zero_s3[kind]+=1;continue
  need(all(s in index for s in transformed),'legal orbit chart')
  image=tuple(index[s] for s in transformed);edge=tuple(sorted(image));valid[kind]+=1
  need(patterns(image)==pat,'literal selector-pattern preservation')
  need(not all(i in support for i in edge),'binary support satisfies every orbit edge')
  edge_sets[kind].add(edge)
  if edge not in edge_records:
   edge_records[edge]={'indices':list(edge),'seed':si,'ordered_image':list(image),
                      'split_permutation':list(a),'common_permutation':list(b),'global_flip':flip}
need(len(edge_sets['old'])==432 and len(edge_sets['weighted'])==1176
     and not(edge_sets['old']&edge_sets['weighted']) and len(edge_records)==1608,'complete disjoint orbit union')
need(dict(valid)=={'old':1632,'weighted':4896} and dict(zero_s3)=={'old':960,'weighted':2016},'orbit transformation census')

# This only checks the new finite family against the already pinned495
# fractional witness; it does not rerun or re-claim its old pair audit.
prior_sum_counts=Counter()
for edge in edge_sets['weighted']:
 c=sum(prior_cover[i] for i in edge)
 need(c>=2,'prior495 fractional witness satisfies the1176 weighted edges')
 prior_sum_counts[c]+=1
need(prior_sum_counts==Counter({2:456,3:528,4:180,5:12}),'exact fractional edge census')


out={'verified':True,'certificate_sha256':hashlib.sha256(INPUT.read_bytes()).hexdigest(),
 'source_inputs':source_inputs,'weighted_inputs':weighted_inputs,'prior_fractional_input':prior_fractional_input,
 'profile_count':len(rows),'safe_profile_count':len(allrows)-len(rows),'support_vertices':len(support),
 'excluded_middle_vertices':len(E),'all_Q_le19_support_value':0,'all_Q_ge39_support_value':1,
 'safe_mass':str(safe),'middle_mass':str(all_middle),'overflow_mass':str(overflow),
 'support_exact_mass':str(total),'support_mass_float':float(total),'m7':str(M7),
 'support_excess':str(total-M7),'support_excess_float':float(total-M7),
 'finite_order_arrows_checked':finite_arrows,'overflow_order_arrows_checked':overflow_arrows,
 'finite_distinct_pairs_covered':finite_pairs,'load_class_pairs':len(pair_proofs),
 'universal_load_pairs':universal_classes,'split_signature_pair_checks':group_checks,
 'coarse_pair_checks':coarse_checks,'refined_pair_checks':refined_checks,
 'distinct_common_box_scans':max_common_intersection.cache_info().misses,'common_box_pair_checks':common_pair_checks,
 'pair_capacity_certificates':pair_proofs,'overflow_zero_witness':overflow_zero,
 'seed_count':len(seed_proofs),'seed_exact_certificates':seed_proofs,
 'old_hyperedges':432,'new_weighted_hyperedges':1176,'hyperedges_checked':len(edge_records),
 'prior495_new_edges_checked':1176,'prior495_cover_sum_counts':{str(c):prior_sum_counts[c] for c in range(7)},
 'hyperedges':[edge_records[e] for e in sorted(edge_records)],'Lean_rerun':False,
 'scope':'Binary auxiliary support at the fixed six-anchor chart and reference(2,7,3,4), all positive theoretical pair exclusions,432 old and1176 canonical499 weighted-mixed triple edges, and the full fixed3/5 later-factor order with all infinite overflow.',
 'boundary':'Its exact auxiliary mass exceeds m7. The specified pair/order/1608-triple system therefore cannot force binary mass below m7. No claim is made about any subsequently added triple or other constraint. This is not an actual original-source realization or covering counterexample. Other multi-point constraints and simultaneous phase realization remain separate obligations. No solver or new Lean claim.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({k:out[k] for k in ('support_vertices','finite_distinct_pairs_covered','split_signature_pair_checks',
 'common_box_pair_checks','hyperedges_checked','support_mass_float','support_excess_float')},indent=2))
