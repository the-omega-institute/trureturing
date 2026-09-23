"""Independent integer-cut upper bound audit, standard library only.
Literal active rows, fresh exact pair/triple minima, signed order loads and
all20076 Fraction box residuals. No graph, solver, NumPy or producer import.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,combinations,permutations
from collections import defaultdict
from math import prod
import hashlib,json,argparse
pa=argparse.ArgumentParser(description=__doc__)
pa.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
pa.add_argument('--certificate',type=Path)
pa.add_argument('--output',type=Path)
args=pa.parse_args();BASE=args.input_dir
INPUT=args.certificate or BASE/'mixed_split_four_point_bound_certificate.json'
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
def need(x,msg):
 if not x:raise ValueError(msg)
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

@lru_cache(None)
def triple_certificate(N):
 V,W=poly_vertices(N,22),poly_vertices(N,28);need(V and W,'seed polytope nonempty')
 k,i,j=min((sum((22-a)*(28-b) for a,b in zip(t,u))-N[-1],i,j) for i,t in enumerate(V) for j,u in enumerate(W))
 return {'capacity':list(N),'K3':str(k),'axis23_vertices':[[str(x) for x in v] for v in V],'axis29_vertices':[[str(x) for x in v] for v in W],'minimum_at':[i,j]}

@lru_cache(None)
def pair_minimum(q,r,N):
 a1,a2=min(22,q),min(22,r);b1,b2=min(28,q),min(28,r)
 A=min(N,a1+a2);B=min(N,b1+b2)
 tl,th=max(0,A-a2),min(A,a1);ul,uh=max(0,B-b2),min(B,b1)
 corners=((tl,ul),(th,ul),(th,uh),(tl,uh));certs=[]
 def fs(t,u):
  rx=(22-t)*(28-u);ry=(22-A+t)*(28-B+u)
  return (0,rx-q,ry-r,rx+ry-N)
 for start,end in zip(corners,corners[1:]+corners[:1]):
  v0,v1=fs(*start),fs(*end)
  # Variables are lambda,h. lambda in[0,1] and h>=all four lines.
  cons=[((-1,0),F(0)),((1,0),F(1))]
  cons += [((F(y-x),F(-1)),F(-x)) for x,y in zip(v0,v1)]
  feasible=[]
  for i,j in combinations(range(6),2):
   (a,b),v=cons[i];(c,d),w=cons[j];de=a*d-b*c
   if not de:continue
   lam=F(v*d-b*w,de);h=F(a*w-v*c,de)
   if all(aa*lam+bb*h<=rhs for (aa,bb),rhs in cons):feasible.append((h,lam,i,j))
  need(feasible,'edge epigraph vertex exists')
  h,lam,i,j=min(feasible)
  need(h==max(F(x)+lam*(y-x) for x,y in zip(v0,v1)),'tight edge epigraph vertex')
  certs.append({'endpoints':[list(start),list(end)],'minimum':str(h),'lambda':str(lam),'active_rows':[i,j]})
 k=min(F(c['minimum']) for c in certs)
 need(k>=F(1,3),'used pair has sufficient same-threshold numerator')
 return {'Q1':q,'Q2':r,'N':N,'K2':str(k),'edge_epigraph_certificates':certs}

from collections import Counter
sourcebase=BASE
sourcepins={'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d','common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}
for name,digest in sourcepins.items():need(hashlib.sha256((sourcebase/name).read_bytes()).hexdigest()==digest,'source identity '+name)
com=json.loads((sourcebase/'common_law_mass_tail.json').read_text())['common_seven_core_law']
need(F(com['unnormalized_mass_lower'])==M7 and F(com['unnormalized_joint_density_cap'])==F(27,2),'same source mass/density')
need(tuple(map(F,com['conditional_caps']))==tuple(c for p,c in CAPS),'same conditional caps')
raw=INPUT.read_bytes();inp=json.loads(raw);D=inp['denominator'];need(D==10**13,'multiplier denominator')
for name,digest in inp['inputs'].items():need(hashlib.sha256((BASE/name).read_bytes()).hexdigest()==digest,'pinned prerequisite '+name)
need(inp['theta']=='1/3696' and inp['reference']==[2,7,3,4] and inp['old_primes']==[3,5,7,11,13,17,19] and inp['new_primes']==[23,29],'same declared chart')
need(not inp['zero_pairs'],'qualitative rows have zero price, so certificate remains theta valid')
need(F(inp['overflow'])==overflow,'literal overflow agreement')
for kind,arity in [('pairs',2),('genuine_triples',3),('triangle_cliques',3),('quads',4),('order',2)]:
 for e in inp[kind]:need(len(e)==arity+1 and all(type(x)is int for x in e) and e[-1]>0 and len(set(e[:-1]))==arity and all(0<=i<len(rows) for i in e[:-1]),'valid '+kind+' schema')
usedpairs={tuple(sorted(e[:2])) for e in inp['pairs']}
for *ids,u in inp['triangle_cliques']:usedpairs.update(tuple(sorted(e)) for e in combinations(ids,2))
pairtypes={};literalpairs=[]
for i,j in sorted(usedpairs):
 qi,qj,n=literal_capacities((i,j));q,r=sorted((qi,qj));key=(q,r,n)
 if key not in pairtypes:pairtypes[key]=pair_minimum(*key)
 literalpairs.append([i,j,qi,qj,n,pairtypes[key]['K2']])
@lru_cache(None)
def pattern(ids):
 ab=[literal_inventory(rows[i]) for i in ids];labels=set().union(*(a|b for a,b in ab))
 return Counter(tuple(sorted((sum(1<<j for j,(a,b) in enumerate(ab) if d in a),sum(1<<j for j,(a,b) in enumerate(ab) if d in b)))) for d in labels)
def wcap(pat,w):
 val=lambda mask:sum(w[j] for j in range(len(w)) if mask>>j&1)
 return sum(n*max(val(a),val(b)) for (a,b),n in pat.items())
def vertices10(ids,axis):
 dirs=tuple(tuple((mask>>j)&1 for j in range(3)) for mask in range(1,8))+tuple(sorted(set(permutations((1,1,2)))))
 pat=pattern(ids);cons=[(tuple(-int(j==i) for j in range(3)),0) for i in range(3)]
 cons +=[(w,min(axis,wcap(pat,w)) if sum(w)==1 else wcap(pat,w)) for w in dirs]
 out=set()
 for ix in combinations(range(len(cons)),3):
  v=solve(tuple(cons[i][0] for i in ix),tuple(cons[i][1] for i in ix))
  if v is not None and all(sum(a*b for a,b in zip(c,v))<=b for c,b in cons):out.add(v)
 return sorted(out)
b500=json.loads((sourcebase/'mixed_split_binary_support_barrier.json').read_text())
b501=json.loads((sourcebase/'mixed_split_complete_weighted_boundary.json').read_text())
e500={tuple(e['indices']):e for e in b500['hyperedges']};e501={tuple(e['indices']):e for e in b501['orbit_and_subset_repair']['hyperedges']}
seedproof={};triplerows=[]
for *ids,u in inp['genuine_triples']:
 edge=tuple(sorted(ids));need(edge in e500 or edge in e501,'declared actual triple')
 if edge in e500:
  rec=e500[edge];sk=('subset',rec['seed']);seed=b500['seed_exact_certificates'][rec['seed']];sid=tuple(seed['indices']);w=tuple(seed['weight'])
 else:
  rec=e501[edge];sk=('complete10',0);sid=tuple(b501['indices']);w=tuple(b501['weight'])
 image=tuple(rec['ordered_image']);need(set(image)==set(ids) and pattern(image)==pattern(sid),'same complete literal selector patterns')
 need(all(rows[i]==tuple(rec['global_flip']*rows[j][k] for k in rec['split_permutation'])+tuple(rows[j][k] for k in rec['common_permutation']) for i,j in zip(image,sid)),'declared transformation really yields indices')
 if sk not in seedproof:
  pat=pattern(sid);cap=wcap(pat,w);caps3=literal_capacities(sid)
  V=vertices10(sid,22) if sk[0]=='complete10' else poly_vertices(caps3,22)
  U=vertices10(sid,28) if sk[0]=='complete10' else poly_vertices(caps3,28)
  mn=min(sum(ww*(22-a)*(28-b) for ww,a,b in zip(w,t,u))-cap for t in V for u in U)
  need(mn>=F(sum(w),6),'same theta actual triple proof')
  seedproof[sk]={'indices':sid,'weight':w,'capacity':cap,'subset_capacities':caps3,'vertices':[len(V),len(U)],'minimum':str(mn)}
 triplerows.append({'indices':ids,'source_seed':list(sk),'ordered_image':image})
# The preceding canonical four-point proof is replayed only at its rational
# branch tree. No support enumeration or optimization is an input here.
qraw=(BASE/'four_point_joint_budget_certificate.json').read_bytes()
qcert=json.loads(qraw);qresult=json.loads((BASE/'four_point_joint_budget.json').read_text())
need(qresult['certificate_sha256']==hashlib.sha256(qraw).hexdigest(),'canonical four-point binding')
P=tuple(map(tuple,qcert['profiles']));W=list(map(tuple,qcert['directions']))
need(P==tuple(map(tuple,qresult['profiles'])) and W==list(map(tuple,qresult['directions'])) and len(W)==101 and all(len(w)==4 and all(type(x)is int and x>=0 for x in w) and sum(w)>0 for w in W),'valid four-point directions')
sid=tuple(index[s] for s in P);qpattern=pattern(sid)
N=[wcap(qpattern,w) for w in W]
need(N==qcert['capacities']==qresult['capacities'],'literal four-point capacities')
def dot(a,b):return sum(x*y for x,y in zip(a,b))
UA=[tuple(map(F,w)) for w in W]+[tuple(F(-int(i==j)) for i in range(4)) for j in range(4)]
UB=[F(min(28,n) if sum(w)==1 else n) for w,n in zip(W,N)]+[F(0)]*4
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
qtree=verify(qcert)
need(qtree==qresult['tree'],'same exact canonical branch proof')
qo={tuple(e['indices']):e for e in qresult['orbit_and_fixed_support_repair']['edges']};quadrows=[]
for *ids,u in inp['quads']:
 rec=qo[tuple(sorted(ids))];image=tuple(rec['ordered_image'])
 need(set(image)==set(ids) and pattern(image)==qpattern,'quad complete literal selector pattern transport')
 need(all(rows[i]==tuple(rec['global_flip']*rows[j][k] for k in rec['split_permutation'])+tuple(rows[j][k] for k in rec['common_permutation']) for i,j in zip(image,sid)),'quad actual coordinate transform')
 quadrows.append({'indices':ids,'ordered_image':image})
for i,j,u in inp['order']:
 s,t=rows[i],rows[j];changed=[k for k in range(7) if s[k]!=t[k]]
 need(len(changed)==1 and changed[0]>=2 and s[:2]==t[:2],'order support')
 k=changed[0]
 if k==2:need((s[k]==0 and t[k] in(-2,2)) or (s[k]>0 and t[k]==s[k]+1) or (s[k]<0 and t[k]==s[k]-1),'split order')
 else:need(t[k]==s[k]+1,'common order')
 aa,bb=boxes(s);cc,dd=boxes(t);need(all(a<=b for a,b in zip(aa,cc)) and all(a<=b for a,b in zip(bb,dd)),'actual inclusion')
loadunits=[0]*len(rows);price=0
for kind,rhs in [('pairs',1),('genuine_triples',2),('triangle_cliques',1),('quads',3)]:
 for *ids,u in inp[kind]:
  for i in ids:loadunits[i]+=u
  price+=rhs*u
for i,j,u in inp['order']:loadunits[i]+=u;loadunits[j]-=u
residuals=[max(w-F(a,D),F()) for w,a in zip(weights,loadunits)];residual=sum(residuals,F());upper=overflow+F(price,D)+residual
need(price==inp['row_price_units'] and residual==F(inp['exact_residual_charge']) and upper==F(inp['exact_upper']),'exact independent upper agreement')
old=json.loads((BASE/'mixed_split_integer_cut_bound.json').read_text());old_upper=F(old['exact_upper'])
out={'verified':True,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'valid_for_theta':'1/3696','qualitative_pair_multipliers_used':0,'source_pins':sourcepins,'profile_count':len(rows),'used_rows':{k:len(inp[k]) for k in ['pairs','genuine_triples','triangle_cliques','quads','order']},'unique_literal_pairs_checked':len(usedpairs),'pair_capacity_types':len(pairtypes),'least_pair_K2':str(min(F(c['K2']) for c in pairtypes.values())),'pair_type_certificates':list(pairtypes.values()),'pair_literal_capacities':literalpairs,'triple_seed_certificates':[{'key':list(k),**v} for k,v in seedproof.items()],'active_triple_rows':triplerows,'quad_branch_certificate_sha256':hashlib.sha256(qraw).hexdigest(),'quad_branch_independent_nodes':qtree['nodes'],'quad_rows':quadrows,'denominator':D,'row_price_units':price,'exact_residual_charge':str(residual),'exact_upper':str(upper),'upper_float':float(upper),'old_upper':str(old_upper),'improvement':str(old_upper-upper),'improvement_float':float(old_upper-upper),'m7':str(M7),'m7_minus_upper':str(M7-upper),'margin_float':float(M7-upper),'passes':upper<M7,'signed_load_units':loadunits,'box_residuals':list(map(str,residuals)),'scope':'Ordinary exact rational upper for the entire binary profile-support model with declared rows, all20076 finite profiles and exact overflow. No original-source realization and no full-system optimum claim. No qualitative zero-only row occurs in the positive-price certificate; the bound uses uniform theta throughout.'}
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained result differs')
print(json.dumps({k:v for k,v in out.items() if k not in ['pair_type_certificates','pair_literal_capacities','triple_seed_certificates','active_triple_rows','quad_rows','signed_load_units','box_residuals']},indent=2))
