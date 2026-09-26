#!/usr/bin/env python3
"""Independent exact upper bound for one priority field family across two layouts.
Reads canonical640/658 and the rational dual witness; reads/imports no producer.
Reconstructs menus, matching responses, group orbits and dual residuals.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,product
from hashlib import sha256
from math import prod
import json
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--witness',type=Path,default=None)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args();basepath=args.directory
sources=[basepath/'remaining33_global_root_exclusion_certificate.json',basepath/'joint_square_pair_225_star_certificate.json',args.witness or basepath/'leaf_pair_common_field_dual_certificate.json']
raw=[p.read_bytes() for p in sources];base,net,dual=map(json.loads,raw)
checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c:raise RuntimeError(k)
pins=['dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5','d408f1ba18b386085b00e7a9a88927ed84f6e59d33f45a4db36621750f197ebc']
for b,pin in zip(raw,pins):ck('pinned_input',sha256(b).hexdigest()==pin)
ck('two_literal_layouts',dual['layouts']==[[4]*10,[5]*10])
ck('candidate_dual_result_contract',dual['status']=='PASS' and dual['new_lean_verification'] is False)
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5)
cells=[(l,m) for l,m in product(I,J) if not(l<3 and m<5)]
points=[(i,j,l,m) for i,j in product(I,J) for l,m in cells]
ck('full_literal_variable_inventory',len(points)==7600)
keys=[tuple(row) for row in dual['orbit_keys']];keyidx={key:k for k,key in enumerate(keys)}
ck('distinct_one_hundred_eighty_keys',len(keys)==len(keyidx)==180)
def orbit(i,j,l,m):
 return ('r' if i<3 else str(i),('eq' if i==l else 'other') if i<3 and l<3 else 'r' if l<3 else str(l),j//5,m//5,j==m)
point_orbit={point:keyidx[orbit(*point)] for point in points}
ck('full_orbit_key_coverage',{orbit(*point) for point in points}==set(keys))
# Independently reconstruct actual group orbits using its17 adjacent transpositions.
idx={p:k for k,p in enumerate(points)};parent=list(range(len(points)))
def find(k):
 while parent[k]!=k:
  parent[k]=parent[parent[k]];k=parent[k]
 return k

def join(a,b):
 a,b=find(a),find(b)
 if a!=b:parent[b]=a

generators=[(3,0,1),(3,1,2)]
for block in ((0,1,2,3,4),(6,7,8,9),(10,11,12,13,14),(15,16,17,18,19)):
 generators.extend((5,a,b) for a,b in zip(block,block[1:]))
for axis,a,b in generators:
 def swap(x):return b if x==a else a if x==b else x
 def move(point):
  i,j,l,m=point
  return (swap(i),j,swap(l),m) if axis==3 else (i,swap(j),l,swap(m))
 moved=[move(p) for p in points]
 ck('generator_preserves_literal_variables',set(moved)==set(points))
 ck('generator_preserves_claimed_orbit_key',all(orbit(*p)==orbit(*q) for p,q in zip(points,moved)))
 for p,q in zip(points,moved):join(idx[p],idx[q])
 ck('both_response_layouts_preserved',all((int(l//3==1),int(m//5==2),int(l==5),int(l==4))==(int(move((0,0,l,m))[2]//3==1),int(move((0,0,l,m))[3]//5==2),int(move((0,0,l,m))[2]==5),int(move((0,0,l,m))[2]==4)) for l,m in cells))
components={}
for p in points:components.setdefault(find(idx[p]),set()).add(point_orbit[p])
ck('exact_group_orbits_not_coarser_relaxation',len(components)==180 and all(len(v)==1 for v in components.values()))
priority_edges=set()
for i,j,l,m in points:
 u=point_orbit[(i,j,l,m)]
 priority_edges.add((u,point_orbit[(l,j,l,m)]))
 priority_edges.add((u,point_orbit[(i,m,l,m)]))
Q=(7,11,13,17,19);edges=list(combinations(range(5),2))
r=[F(1,q-1) for q in Q];a=[F(1,q*(q-2)) for q in Q]
z=[F(5,6)]+[F(q-2,q-1)-2*a[k] for k,q in enumerate(Q) if k]
g=F(200163067,201247200)
C=[F(x) for x in base['combined512_coefficients']]
for k in range(1,5):C[9*32+(1<<k)]+=g*a[k]
ck('complete512_nonnegative',len(C)==512 and min(C)>=0)
# Cache by the actual central activation profile, separately for two layouts.
hprofiles={};Hs={}
for layout,activeleaf in enumerate((4,5)):
 Hs[layout]={}
 for l,m in cells:
  n=int(l//3==1)+int(m//5==2)+int(l==5);pair_on=int(l==activeleaf)
  profile=(n,pair_on)
  if profile not in hprofiles:
   zz=list(z);zz[0]-=F(n,35)
   beta=[a[i]*r[j]+r[i]*a[j]+r[i]*r[j]*pair_on for i,j in edges]
   p=[beta[e]/(zz[i]*zz[j]) for e,(i,j) in enumerate(edges)]
   for mask in range(1024):
    es=[e for e in range(10) if mask>>e&1]
    val=1-sum((p[e] for e in es),F(0))+sum((p[e]*p[f] for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])),F(0))
    ck('strict_induced_shearer_polynomial',val>0)
   table=[]
   for T in range(32):
    U=set(i for i in range(5) if not(T>>i&1));es=[e for e,ends in enumerate(edges) if set(ends)<=U]
    value=prod(zz[i] for i in U)-sum((beta[e]*prod(zz[i] for i in U-set(edges[e])) for e in es),F(0))+sum((beta[e]*beta[f]*prod(zz[i] for i in U-set(edges[e])-set(edges[f])) for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])),F(0))
    ck('valid_matching_response',0<value<=1);table.append(value)
   hprofiles[profile]=table
  Hs[layout][(l,m)]=hprofiles[profile]

# Menus constructed literally in the declared order, not read from the witness.
def menus(weights,p,live,deep):
 return [[weights],[[w if i//p==root else F(0) for i,w in enumerate(weights)] for root in range(len(weights)//p)],[[weights[k] if i==k else F(0) for i in range(len(weights))] for k in live],[[deep if i==k else F(0) for i in range(len(weights))] for k in live]]
D=dual['normalizer'];ck('exact_positive_normalizer',D==2**40)
ck('convex_cut_weights',len(dual['cut_terms'])==13 and sum(row['numerator'] for row in dual['cut_terms'])==D and all(isinstance(row['numerator'],int) and row['numerator']>=0 for row in dual['cut_terms']))
residual=[F(0)]*180;cuts=[]
for row in dual['cut_terms']:
 layout,i,j=row['case'];ck('legal_layout_corner_case',layout in (0,1) and i in I and j in J)
 ck('one_selector_for_every_fee',len(row['selectors'])==512)
 w=[F(0) if l==3 else F(1,9) if l==i else F(2,9) for l in range(6)]
 v=[F(0) if m==5 else F(3,75) if m==j else F(4,75) for m in range(20)]
 mx=menus(w,3,I,F(1));my=menus(v,5,J,F(4,5))
 f=[F(0)]*180
 for l,m in cells:f[point_orbit[(i,j,l,m)]]+=g*w[l]*v[m]*Hs[layout][(l,m)][0]
 for fee,index in enumerate(row['selectors']):
  mode,T=divmod(fee,32);xs,ys=mx[mode//4],my[mode%4]
  ck('selected_menu_index_is_legal',isinstance(index,int) and 0<=index<len(xs)*len(ys))
  ix,iy=divmod(index,len(ys));x,y=xs[ix],ys[iy]
  for l,m in cells:
   if x[l] and y[m]:f[point_orbit[(i,j,l,m)]]-=C[fee]*x[l]*y[m]*Hs[layout][(l,m)][T]
 mu=F(row['numerator'],D)
 for k,x in enumerate(f):residual[k]+=mu*x
 cuts.append(dict(case=row['case'],weight=str(mu),coefficient_sha256=sha256(json.dumps(list(map(str,f))).encode()).hexdigest()))
for row in dual['priority_terms']:
 u,v,n=row['lower'],row['upper'],row['numerator']
 ck('legal_orbit_priority_inequality',(u,v) in priority_edges and u!=v)
 ck('nonnegative_priority_multiplier',isinstance(n,int) and n>=0)
 # theta_u-theta_v<=0. Subtracting its nonnegative multiple gives a majorant.
 residual[u]-=F(n,D);residual[v]+=F(n,D)
upper=sum((max(F(0),x) for x in residual),F(0))
ck('exact_box_residual_upper_matches',upper==F(dual['dual_upper']))
ck('all_candidate_residual_coefficients_match',list(map(F,dual['orbit_coefficients']))==residual)
ck('strict_common_field_upper',upper<F(17,10000))
fees=[]
for row in net['policies']:
 fee=F(net['fee_before_arbitrary'])+F(row['fee'])
 ck('each_complete_network_fee_exceeds_threshold',fee>F(17,10000))
 fees.append(dict(kind=row['kind'],K=row['K'],complete_fee=str(fee),complete_fee_decimal=float(fee),gap_over_dual_upper=str(fee-upper)))
ck('candidate_network_count',len(dual['network_comparisons'])==len(fees)==2)
for row,ref in zip(dual['network_comparisons'],fees):
 ck('candidate_network_identity',row['kind']==ref['kind'] and row['K']==ref['K'])
 ck('candidate_complete_fee',F(row['complete_fee'])==F(ref['complete_fee']))
 ck('candidate_gap_above_dual',F(row['gap_above_dual'])==F(ref['gap_over_dual_upper']))
result=dict(schema='common-layout-priority-dual-independent-v1',status='PASS',new_lean_verification=False,scope='One layout-independent priority-compatible95field family cannot pay both specified complete658 network budgets in this fixed envelope certificate. Layout-adapted families and improved envelopes are not excluded.',verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),input_files=[p.name for p in sources],input_sha256=list(map(lambda b:sha256(b).hexdigest(),raw)),literal_variable_count=len(points),group_generators=generators,orbit_count=len(components),legal_priority_edge_count=len(priority_edges),cut_summaries=cuts,dual_residual=list(map(str,residual)),positive_residual_coordinates=sum(x>0 for x in residual),exact_upper=str(upper),exact_upper_decimal=float(upper),threshold='17/10000',complete_network_fees=fees,check_count=sum(checks.values()),checks=checks)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','orbit_count','positive_residual_coordinates','exact_upper','exact_upper_decimal','check_count')}))
print(json.dumps(fees))
