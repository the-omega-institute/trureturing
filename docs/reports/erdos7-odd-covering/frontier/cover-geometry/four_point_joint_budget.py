"""Independent exact verification of the fourpoint rational-box certificate.
No NumPy/SciPy, proposer import, solver status, or cached capacities used.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations,permutations
from collections import Counter
from functools import lru_cache
from math import gcd,prod
import argparse,json,hashlib
pa=argparse.ArgumentParser(description=__doc__)
pa.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
pa.add_argument('--certificate',type=Path)
pa.add_argument('--output',type=Path)
args=pa.parse_args();BASE=args.input_dir
CERT=args.certificate or BASE/'four_point_joint_budget_certificate.json'
CS=BASE/'integer_selector_tail_interface_certificate.json'
RS=BASE/'integer_selector_tail_interface.json'
def need(t,m):
 if not t:raise ValueError(m)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def det3(M):return M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])+M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])
need(hashlib.sha256(CS.read_bytes()).hexdigest()=='66f155d2d9f65b044017e0c033c1d3e8f9999cea100eabce1b8aa049810ecb5a','canonical503 certificate');need(hashlib.sha256(RS.read_bytes()).hexdigest()=='4681c5b6da42138625dfa6c21e680522edf60ed400a3ae83c817d94bfcf9e4f4','canonical503 arithmetic');source=json.loads(CS.read_text());real=json.loads(RS.read_text())['axis_realizations'][1];case=source['cases'][1];P=((3,2,2,1,2,1,1),(3,2,2,2,1,1,1),(-3,-2,2,2,2,1,1),(-3,0,-2,2,2,1,1));need(tuple(map(tuple,case['profiles']))==tuple(map(tuple,real['profiles']))==P,'samefixedfourprofiles');oldprimes=source['old_primes'];D=sorted({prod(p**e for p,e in zip(oldprimes,row['exponents'])) for row in case['axes'][0]['labels']});need(len(D)==45,'45 distinct literaloldlabels');M=real['old_carrier'];points=real['old_points'];centres=real['old_centres'];need(all(M%d==0 for d in D),'oldfibres stable on eachlabel')
# Build Boolean masks by literal original congruences.
AB=[tuple(tuple(int(x%d==c%d) for x in points) for c in centres) for d in D]
# Also regenerate their inventory from the signed-depth boxes.
boxpairs=[tuple(set(product(*(range(v) for v in z))) for z in (tuple(max(1,x) for x in s[:3])+s[3:],tuple(max(1,-x) for x in s[:3])+s[3:])) for s in P];explabels=set().union(*(a|b for a,b in boxpairs));need({prod(p**e for p,e in zip(oldprimes,label)) for label in explabels}==set(D),'full literal inventory equals all profile labels')
for label in explabels:
 d=prod(p**e for p,e in zip(oldprimes,label));masks=tuple(tuple(int(label in pair[side]) for pair in boxpairs) for side in (0,1));need(masks==AB[D.index(d)],'same-centre profile masks')
normals=[n for n in product((-1,0,1),repeat=4) if next((x for x in n if x),0)==1];rays=set()
for rows in combinations(normals,3):
 v=tuple((-1)**j*det3([[row[i] for i in range(4) if i!=j] for row in rows]) for j in range(4))
 if not any(v):continue
 if all(x<=0 for x in v):v=tuple(-x for x in v)
 if any(x<0 for x in v):continue
 g=gcd(*v);rays.add(tuple(x//g for x in v))
W=sorted(rays);need(len(W)==101,'independent101directions');N=[sum(max(dot(w,a),dot(w,b)) for a,b in AB) for w in W]
UA=[tuple(map(F,w)) for w in W]+[tuple(F(-int(i==j)) for i in range(4)) for j in range(4)];UB=[F(min(28,n) if sum(w)==1 else n) for w,n in zip(W,N)]+[F(0)]*4

def vector(x,name):
 need(isinstance(x,list) and len(x)==4 and all(isinstance(a,str) for a in x),name+' exactrational4tuple');return tuple(map(F,x))
def verify(c):
 need(tuple(map(tuple,c['profiles']))==P and list(map(tuple,c['directions']))==W and c['capacities']==N,'independentprofiles andall101capacities');need(F(c['theta'])==F(1,3696),'theta1/3696');nodes=c['nodes'];need(nodes,'nonemptytree');stack=[(0,(F(0),)*4,(F(22),)*4,0)];visited=set();farkas=[];empty=0;splits=0;trimmed=0;maxdepth=0;maxden=1;nonbinary=0
 while stack:
  index,expectedlo,expectedhi,depth=stack.pop();need(type(index)is int and 0<=index<len(nodes) and index not in visited,'uniqueacycliccoveredtree index');visited.add(index);node=nodes[index];lo=vector(node['lo'],'lo');hi=vector(node['hi'],'hi');need(lo==expectedlo and hi==expectedhi,'exactparentchildboxcoverage');need(all(0<=l<=h<=22 for l,h in zip(lo,hi)),'validrootboundedbox');maxdepth=max(maxdepth,depth)
  for v in lo+hi:
   maxden=max(maxden,v.denominator);nonbinary+=int(v.denominator&(v.denominator-1)!=0)
  if node['kind']=='empty_t':
   j=node['row'];need(type(j)is int and 0<=j<101 and dot(W[j],lo)>N[j],'t-onlymonotone emptybox');empty+=1;continue
  need(all(dot(w,lo)<=n for w,n in zip(W,N)),'unrejectedlowercorner satisfiesaxisbudgets')
  tight=tuple(min([hi[i]]+[F(n-dot(w,lo)+w[i]*lo[i],w[i]) for w,n in zip(W,N) if w[i]>0]) for i in range(4));need(vector(node['tight_hi'],'tight_hi')==tight and all(l<=h<=u for l,h,u in zip(lo,tight,hi)),'exactbudget-deriveduppertrim');trimmed+=tight!=hi
  # For any feasible t>=lo, each row bounds its i-th coordinate by the above
  # value. Thus discarded portions of the original box miss the t polytope.
  if node['kind']=='split':
   j=node['coordinate'];cut=F(node['cut']);need(type(j)is int and 0<=j<4 and lo[j]<cut<tight[j] and cut==(lo[j]+tight[j])/2,'exactnondegeneratemidpoint split');left_hi=list(tight);left_hi[j]=cut;right_lo=list(lo);right_lo[j]=cut;need('left'in node and 'right'in node,'bothsplit childrenpresent');stack.extend([(node['right'],tuple(right_lo),tight,depth+1),(node['left'],lo,tuple(left_hi),depth+1)]);splits+=1;continue
  need(node['kind']=='farkas','everyotherleaf isexactfarkas');x=tuple(22-h for h in tight);A=UA+[tuple(-wi*xi for wi,xi in zip(w,x)) for w in W];b=UB+[F(n)+F(sum(w),6)-28*dot(w,x) for w,n in zip(W,N)];multipliers=node['multipliers'];need(isinstance(multipliers,list) and multipliers,'nonemptydual');used=set();lam=[]
  for j,v in multipliers:
   need(type(j)is int and 0<=j<len(A) and j not in used and isinstance(v,str),'uniquerowindex exactdual');used.add(j);v=F(v);need(v>=0,'nonnegativedual');lam.append((j,v))
  cancellation=tuple(sum(v*A[j][i] for j,v in lam) for i in range(4));rhs=sum(v*b[j] for j,v in lam);need(cancellation==(0,0,0,0),'exactdual rowcancellation');need(rhs<0,'strictnegativeexactdualrhs');farkas.append({'node':index,'nonzero_multipliers':len(lam),'rhs':str(rhs)})
 need(visited==set(range(len(nodes))),'allnodescoveredandnounreachabledata');need(len(nodes)==splits+len(farkas)+empty and len(farkas)+empty==splits+1,'fullbinarytree census')
 return {'nodes':len(nodes),'branches':splits,'farkas_leaves':len(farkas),'empty_t_leaves':empty,'trimmed_nodes':trimmed,'maximum_depth':maxdepth,'maximum_box_denominator':maxden,'non_dyadic_bound_occurrences':nonbinary,'least_negative_farkas_rhs':str(max(F(e['rhs']) for e in farkas)),'all_leaf_certificates':farkas}
raw=CERT.read_bytes();certificate=json.loads(raw)
for name,digest in certificate['inputs'].items():
 need(hashlib.sha256((BASE/name).read_bytes()).hexdigest()==digest,'pinned input '+name)
result=verify(certificate)
# Two feasible axis pairs whose residual mean lies in the complete mixed budget.
# Completeness of the regenerated rays then handles every real nonnegative w.
pairs=certificate['fixed_weight_counterexample'];need(len(pairs)==2,'two counterexample pairs')
mean=[F(0)]*4;total=F(0);counterexample=[]
for pair in pairs:
 t=vector(pair['t'],'counterexample t');u=vector(pair['u'],'counterexample u')
 lam=F(pair['lambda']);need(lam>0,'positive mixture weight');total+=lam
 for v,axis in ((t,22),(u,28)):
  need(all(0<=x<=axis for x in v),'axis cap')
  need(all(dot(w,v)<=n for w,n in zip(W,N)),'all counterexample axis budgets')
 residual=tuple((22-x)*(28-y) for x,y in zip(t,u))
 need(residual==vector(pair['R'],'counterexample R'),'actual residual products')
 mean=[x+lam*y for x,y in zip(mean,residual)]
 counterexample.append({'lambda':str(lam),'t':list(map(str,t)),
                        'u':list(map(str,u)),'R':list(map(str,residual))})
need(total==1 and all(dot(w,mean)<=n for w,n in zip(W,N)),
     'convex residual mean satisfies all mixed budgets')
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

# Reconstruct the declared chart and its permitted order independently.
def profile_load(s):
 return (prod(max(1,x) for x in s[:3])+prod(max(1,-x) for x in s[:3])-1)*prod(s[3:])
rows=[]
def fill(s):
 if len(s)==7:
  if profile_load(s)>=20:rows.append(s)
  return
 for x in range(1,39):
  child=s+(x,)
  if profile_load(child)>38:break
  fill(child)
sp=list(range(2,39))+list(range(-2,-39,-1))
for a in sp:
 for b in sp+[0]:
  for c in [0]+sp:
   if profile_load((a,b,c))<=38:fill((a,b,c))
index={s:i for i,s in enumerate(rows)}
need(len(rows)==20076 and tuple(index[s] for s in P)==(2782,2784,13607,14355),
     'complete chart and four seed indices')
def boxes(s):
 return tuple(set(product(*(range(v) for v in z))) for z in
              (tuple(max(1,x) for x in s[:3])+s[3:],
               tuple(max(1,-x) for x in s[:3])+s[3:]))
def pattern(profiles):
 ab=list(map(boxes,profiles));labels=set().union(*(a|b for a,b in ab))
 return Counter(tuple(sorted((tuple(int(d in a) for a,b in ab),
                              tuple(int(d in b) for a,b in ab)))) for d in labels)
seedpattern=pattern(P);edges={};eligible=0
for a,b,flip in product(permutations(range(3)),permutations(range(3,7)),(-1,1)):
 image=[tuple(flip*s[j] for j in a)+tuple(s[j] for j in b) for s in P]
 if any(s not in index for s in image):continue
 eligible+=1;ids=tuple(index[s] for s in image);edge=tuple(sorted(ids))
 need(pattern(image)==seedpattern,'literal orbit membership patterns')
 edges.setdefault(edge,{'indices':edge,'ordered_image':ids,'split_permutation':a,
                        'common_permutation':b,'global_flip':flip})
need(eligible==192 and len(edges)==48,'eligible orbit census')
def pinned(name,digest):
 raw=(BASE/name).read_bytes()
 need(hashlib.sha256(raw).hexdigest()==digest,'prerequisite '+name)
 return json.loads(raw)
c501=pinned('mixed_split_complete_weighted_boundary_certificate.json',
            certificate['inputs']['mixed_split_complete_weighted_boundary_certificate.json'])
r501=pinned('mixed_split_complete_weighted_boundary.json',
            certificate['inputs']['mixed_split_complete_weighted_boundary.json'])
need(r501['certificate_sha256']==certificate['inputs']['mixed_split_complete_weighted_boundary_certificate.json'],
     'report501 result binding')
c500=pinned(c501['support_file'],c501['support_sha256'])
r500=pinned(c501['base_result_file'],c501['base_result_sha256'])
need(r500['certificate_sha256']==c501['support_sha256'],'report500 support binding')
support=set(range(len(rows)))-set(c500['excluded_middle_indices'])-set(c501['remove_indices'])
need(c501['remove_indices']==[4405,4407] and len(support)==15797,'fixed report501 support')
oldedges={tuple(e['indices']) for e in r500['hyperedges']}|{
 tuple(e['indices']) for e in r501['orbit_and_subset_repair']['hyperedges']}
need(len(oldedges)==1656 and all(not set(e)<=support for e in oldedges),'old triples inherited')
violations=sorted(e for e in edges if set(e)<=support)
need(len(violations)==7,'new edge violations of fixed support')
half=pinned(c501['fractional_file'],c501['fractional_sha256'])['cover_doubled']
need(len(half)==20076 and all(type(x)is int and x in(0,1,2) for x in half),'fractional witness')
cover_counts=Counter(sum(half[i] for i in e) for e in edges)
need(cover_counts=={2:6,3:18,4:18,5:6},'fractional witness survives new edges')
pred=[[] for _ in rows];arrows=[];overflow=0
for i,s in enumerate(rows):
 for j in range(2,7):
  values=(2,-2) if j==2 and s[j]==0 else ((s[j]+(1 if s[j]>0 else -1),) if j==2 else (s[j]+1,))
  for v in values:
   child=s[:j]+(v,)+s[j+1:]
   if profile_load(child)>=39:overflow+=1;continue
   need(child in index,'order child in chart');k=index[child]
   pred[k].append(i);arrows.append((i,k))
need(len(arrows)==16858 and overflow==88764,'complete order census')
need(all(i not in support or j in support for i,j in arrows),'baseline upward support')
@lru_cache(None)
def ancestors(i):
 out={i}
 for j in pred[i]:out.update(ancestors(j))
 return frozenset(out)
@lru_cache(None)
def removal(i):return ancestors(i)&support
@lru_cache(None)
def removal_cost(U):return sum((weight(rows[i]) for i in U),F())
minimum=None;winners=set();unions=set();choices=0
for endpoints in product(*violations):
 removed=frozenset().union(*(removal(i) for i in endpoints));cost=removal_cost(removed)
 choices+=1;unions.add(removed)
 if minimum is None or cost<minimum:minimum=cost;winners={removed}
 elif cost==minimum:winners.add(removed)
removed=min(winners,key=lambda u:tuple(sorted(u)));remaining=support-removed
need(choices==4**7 and len(unions)==14100,'complete endpoint-choice enumeration')
need(minimum==F(1223226848,13067220291125),'minimum exact deletion-only loss')
need(all(i not in remaining or j in remaining for i,j in arrows),'repaired upward order')
need(all(not set(e)<=remaining for e in oldedges|set(edges)),'all old and new edges after repair')
M7=F(7235955529,450000000000)
base_mass=F(r501['orbit_and_subset_repair']['repaired_mass'])
need(sum((weight(rows[i]) for i in support),F())+F(r500['overflow_mass'])==base_mass,
     'literal baseline mass from same source shells')
mass=base_mass-minimum
need(mass<M7,'fixed-support deletion-only maximum below m7')
orbit={'eligible_transformations':eligible,'new_edges':len(edges),
 'edges':[edges[e] for e in sorted(edges)],'violated_by_report501':violations,
 'fractional_cover_sums_doubled':{str(k):v for k,v in sorted(cover_counts.items())},
 'old_triples_checked':len(oldedges),'middle_order_arrows':len(arrows),
 'overflow_order_arrows':overflow,'endpoint_choices':choices,'distinct_removal_unions':len(unions),
 'minimum_removals':[sorted(u) for u in sorted(winners,key=lambda u:tuple(sorted(u)))],
 'endpoint_ancestor_closures':[{'index':i,'selected_ancestors':sorted(removal(i))}
                              for i in sorted(set().union(*map(set,violations)))],
 'minimum_deletion_only_loss':str(minimum),'baseline_mass':str(base_mass),
 'remaining_middle_count':len(remaining),'include_all_Q_ge39':True,
 'maximum_repaired_mass':str(mass),'maximum_repaired_mass_float':float(mass),
 'm7':str(M7),'excess_over_m7':str(mass-M7),'excess_over_m7_float':float(mass-M7),
 'scope':'Optimal only over upward subsets of the fixed report501 support. The old pair constraints are inherited under deletion. No global upper bound or actual-source realization.'}

out={'certificate_sha256':hashlib.sha256(raw).hexdigest(),
 'inputs':certificate['inputs'],'profiles':P,'label_count':len(D),
 'direction_count':len(W),'directions':W,'capacities':N,'theta':'1/3696',
 'tree':result,'orbit_and_fixed_support_repair':orbit,'fixed_weight_counterexample':counterexample,
 'residual_mean':list(map(str,mean)),
 'minimum_mean_budget_slack':str(min(F(n)-dot(w,mean) for w,n in zip(W,N))),
 'scope':'Exact four-point necessary-budget infeasibility and a counterexample to every fixed-weight positive separation. Original-family transfer requires the stated common-centre masks and uniform new-coordinate fibres. No source-mass bound, unrestricted noncoverage, or Lean verification.'}
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({'label_count':len(D),'direction_count':len(W),
 'tree':{k:v for k,v in result.items() if k!='all_leaf_certificates'},
 'residual_mean':out['residual_mean'],'new_edges':len(edges),
 'fixed_support_maximum_mass':float(mass),'excess_over_m7':float(mass-M7)},indent=2))
