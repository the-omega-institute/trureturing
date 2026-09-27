#!/usr/bin/env python3
"""Independent exact audit of the one-regular leaf-pair layout library.
Standard library only. Reads pinned mathematical inputs and field data, never
producer code. Reconstructs beta matching responses and literal selector maxima.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations, product
from hashlib import sha256
from math import prod, lcm
from time import monotonic
from collections import Counter
import json

parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--witness',type=Path,default=None)
parser.add_argument('--library',type=Path,default=None)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args(); started=monotonic(); checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c: raise RuntimeError(k)
paths=[args.directory/'remaining33_global_root_exclusion_certificate.json',args.directory/'joint_square_pair_225_star_certificate.json',args.witness or args.directory/'one_regular_leaf_pair_library_certificate.json',args.library or args.directory/'binary_leaf_pair_library_certificate.json']
raw=[p.read_bytes() for p in paths]; base,net,witness,library=map(json.loads,raw)
pins=['dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5','7e43a59edb6d358119e793099256af6e095bf0fbf22c3bb11ac9776ec410caa4','4f64080de7056488b7299992ce8da2b7615410e8ddccc597ade50b323bff470d']
for b,pin in zip(raw,pins): ck('pinned_input',sha256(b).hexdigest()==pin)
ck('same_entire_four_field_library',witness['families']==library['families'] and witness['orbit_keys']==library['orbit_keys'])
Q=(7,11,13,17,19); edges=list(combinations(range(5),2))
ck('binary_edge_order',witness['edges']==[[Q[i],Q[j]] for i,j in edges])
I=(0,1,2,4,5); J=tuple(m for m in range(20) if m!=5)
cells=[(l,m) for l,m in product(I,J) if not(l<3 and m<5)]
corners=list(product(I,J)); points=[(i,j,l,m) for i,j in corners for l,m in cells]
reps=list(product((0,1,4,5),(0,6,10,15)))
def corner_rep(i,j): return (1 if i in (1,2) else i,(0,6,10,15)[j//5])
mult=Counter(corner_rep(i,j) for i,j in corners)
ck('corner_coverage',len(corners)==95 and len(reps)==16 and sum(mult.values())==95 and set(mult)==set(reps))
ck('candidate_corner_representatives',witness['corner_representatives']==[list(p) for p in reps])
keys=[tuple(k) for k in witness['orbit_keys']]; ki={k:i for i,k in enumerate(keys)}
def orbit(i,j,l,m):
 return ('r' if i<3 else str(i),('eq' if i==l else 'other') if i<3 and l<3 else 'r' if l<3 else str(l),j//5,m//5,j==m)
ck('exact_key_inventory',len(keys)==len(ki)==180 and {orbit(*p) for p in points}==set(keys))
pointkey={p:ki[orbit(*p)] for p in points}; pointindex={p:i for i,p in enumerate(points)}
parent=list(range(len(points)))
def find(x):
 while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
 return x

def join(a,b):
 a,b=find(a),find(b)
 if a!=b: parent[b]=a

generators=[(3,1,2)]
for block in ((0,1,2,3,4),(6,7,8,9),(10,11,12,13,14),(15,16,17,18,19)):
 generators.extend((5,a,b) for a,b in zip(block,block[1:]))
# Actual 16 permutation generators certify the stabilizer orbits. They preserve
# Z, each individual edge activation, both weak weights, and every selector menu.
for axis,a,b in generators:
 def sw(x): return b if x==a else a if x==b else x
 def mv(p):
  i,j,l,m=p
  return (sw(i),j,sw(l),m) if axis==3 else (i,sw(j),l,sw(m))
 moved=[mv(p) for p in points]
 ck('generator_bijection',set(moved)==set(points))
 ck('generator_preserves_field_key',all(pointkey[p]==pointkey[q] for p,q in zip(points,moved)))
 for p,q in zip(points,moved): join(pointindex[p],pointindex[q])
 ck('generator_preserves_all_binary_local_profiles',all((int(l//3==1)+int(m//5==2)+int(l==5),l==0,l==4,l==5)==(int(mv((0,0,l,m))[2]//3==1)+int(mv((0,0,l,m))[3]//5==2)+int(mv((0,0,l,m))[2]==5),mv((0,0,l,m))[2]==0,mv((0,0,l,m))[2]==4,mv((0,0,l,m))[2]==5) for l,m in cells))
 ck('generator_preserves_weak_weights',all((i==l,j==m)==(ii==ll,jj==mm) for (i,j,l,m),(ii,jj,ll,mm) in zip(points,moved)))
 ck('generator_preserves_selector_blocks',all((l//3,m//5)==(ll//3,mm//5) for (_,_,l,m),(_,_,ll,mm) in zip(points,moved)))
 ck('generator_preserves_corner_orbit',all(corner_rep(i,j)==corner_rep(ii,jj) for (i,j,_,_),(ii,jj,_,_) in zip(points,moved)))
components={}
for p in points: components.setdefault(find(pointindex[p]),set()).add(pointkey[p])
ck('exact_actual_group_orbits',len(components)==295 and all(len(v)==1 for v in components.values()))
families=witness['families']; ck('four_families',len(families)==4)
fieldtables=[]
for fi,f in enumerate(families):
 den=f['denominator']; nums=f['numerators']
 ck('family_shape',isinstance(den,int) and den>0 and len(nums)==180)
 for n in nums: ck('field_box',isinstance(n,int) and 0<=n<=den)
 for i,j,l,m in points:
  v=nums[pointkey[i,j,l,m]]
  ck('ternary_priority',nums[pointkey[l,j,l,m]]>=v)
  ck('quinary_priority',nums[pointkey[i,m,l,m]]>=v)
 # Each family consists of one value on each independently verified actual orbit.
 ck('whole_family_equivariance',all(len({nums[k] for k in ks})==1 for ks in components.values()))
 fieldtables.append({(i,j):[[0 if (l,m) not in cells else nums[pointkey[i,j,l,m]] for m in J] for l in I] for i,j in reps})
selection=witness['selection']; ck('one_family_per_layout',len(selection)==10 and all(len(row)==512 and all(isinstance(x,int) and 0<=x<4 for x in row) for row in selection))
ck('all_candidate_layout_records',len(witness['layout_records'])==5120)
records={(x['fixed_edge_index'],x['binary_mask']):x for x in witness['layout_records']}
ck('unique_candidate_layouts',set(records)==set(product(range(10),range(512))))
g=F(200163067,201247200); C=[F(x) for x in base['combined512_coefficients']]
r=[F(1,q-1) for q in Q]; a=[F(1,q*(q-2)) for q in Q]
for k in range(1,5): C[9*32+(1<<k)]+=g*a[k]
ck('full_512_coefficients',len(C)==512 and min(C)>=0)
cden=lcm(g.denominator,*(c.denominator for c in C)); cnum=[int(c*cden) for c in C]; gnum=int(g*cden)
z0=[F(5,6)]+[F(q-2,q-1)-2*a[k] for k,q in enumerate(Q) if k]
baseline=[a[i]*r[j]+r[i]*a[j] for i,j in edges]; increment=[r[i]*r[j] for i,j in edges]
worstz=list(z0); worstz[0]-=F(3,35)
strictgap=1-sum((baseline[e]+increment[e])/(worstz[i]*worstz[j]) for e,(i,j) in enumerate(edges))
ck('uniform_all_induced_strictness',strictgap>0)
# Direct matching formula; no expansion in binary layout variables is used.
# On five vertices every matching has at most two edges.
terms={}
for n in range(4):
 zz=list(z0); zz[0]-=F(n,35); arr=[]
 for T in range(32):
  U=set(k for k in range(5) if not(T>>k&1)); es=[e for e,ends in enumerate(edges) if set(ends)<=U]
  singles=[(e,prod(zz[k] for k in U-set(edges[e]))) for e in es]
  doubles=[(e,f,prod(zz[k] for k in U-set(edges[e])-set(edges[f]))) for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])]
  arr.append((prod(zz[k] for k in U),singles,doubles))
 terms[n]=arr

def responses(n,active):
 beta=[baseline[e]+increment[e]*int(bool(active>>e&1)) for e in range(10)]
 vals=[]
 for zero,singles,doubles in terms[n]:
  value=zero-sum((beta[e]*v for e,v in singles),F(0))+sum((beta[e]*beta[f]*v for e,f,v in doubles),F(0))
  ck('direct_matching_responses',0<value<=zero)
  vals.append(value)
 return vals
regular={n:responses(n,0) for n in (0,1)}
# Literal maxima. The row identity M(c*x)=c*M(x) for c>=0 only shares
# arithmetic; all row/leaf/deep menu members are still included in the maxima.
blocks=[tuple(k for k,m in enumerate(J) if m//5==b) for b in range(4)]
weights={p:([1 if l==p[0] else 2 for l in I],[3 if m==p[1] else 4 for m in J]) for p in reps}
def qmax(row,v):
 weighted=[x*y for x,y in zip(row,v)]
 return (sum(weighted),max(sum(weighted[k] for k in b) for b in blocks),max(weighted),60*max(row))

def maxima(mat,w,v):
 rows=[qmax(row,v) for row in mat]
 whole=qmax([sum(w[k]*mat[k][m] for k in range(5)) for m in range(19)],v)
 byrow=[qmax([sum(w[k]*mat[k][m] for k in indices) for m in range(19)],v) for indices in ((0,1,2),(3,4))]
 grouped=[max(x,y) for x,y in zip(*byrow)]
 leaves=[max(w[k]*rows[k][j] for k in range(5)) for j in range(4)]
 deep=[9*max(rows[k][j] for k in range(5)) for j in range(4)]
 return list(whole)+grouped+leaves+deep

# Separate literal loop confirms the optimized arithmetic, before its use on
# all layouts. This is not used to import any candidate selector reductions.
def literal_maxima(mat,w,v):
 xmenus=[[w],[[w[k] if l//3==b else 0 for k,l in enumerate(I)] for b in range(2)],[[w[k] if k==t else 0 for k in range(5)] for t in range(5)],[[9 if k==t else 0 for k in range(5)] for t in range(5)]]
 ymenus=[[v],[[v[k] if m//5==b else 0 for k,m in enumerate(J)] for b in range(4)],[[v[k] if k==t else 0 for k in range(19)] for t in range(19)],[[60 if k==t else 0 for k in range(19)] for t in range(19)]]
 out=[]
 for xs in xmenus:
  cols=[[sum(x[k]*mat[k][m] for k in range(5)) for m in range(19)] for x in xs]
  for ys in ymenus:
   out.append(max(sum(c*y for c,y in zip(col,y)) for col in cols for y in ys))
 return out

# Covariance to either other regular leaf uses the full S3 symmetry of the
# unchanged field library. It moves the special activation, not the fixed edge.
for target in (1,2):
 def tr(x): return target if x==0 else 0 if x==target else x
 ck('regular_leaf_transport_field',all(orbit(i,j,l,m)==orbit(tr(i),j,tr(l),m) for i,j,l,m in points))
 ck('regular_leaf_transport_profile',all((int(l//3==1)+int(m//5==2)+int(l==5),l==0,l==4,l==5)==(int(tr(l)//3==1)+int(m//5==2)+int(tr(l)==5),tr(l)==target,tr(l)==4,tr(l)==5) for l,m in cells))
 ck('regular_leaf_transport_menus_and_weights',all((i==l,l//3)==(tr(i)==tr(l),tr(l)//3) for i in I for l in I))
minimum=None; minrows=[]; outrows=[]; screen_count=0
active_regular={(fixed,n):responses(n,1<<fixed) for fixed in range(10) for n in (0,1)}
for layout,(fixed,bmask) in enumerate(product(range(10),range(512))):
 others=[e for e in range(10) if e!=fixed]
 mask4=sum(1<<e for bit,e in enumerate(others) if bmask>>bit&1)
 mask5=(1023^(1<<fixed))^mask4
 ck('one_regular_and_nine_binary_edge_partition',(mask4&mask5)==0 and (mask4|mask5|(1<<fixed))==1023 and not((mask4|mask5)&(1<<fixed)))
 family=selection[fixed][bmask]; den=families[family]['denominator']; field=fieldtables[family]
 tables={(0,0):regular[0],(1,0):regular[1],(0,3):active_regular[fixed,0],(1,3):active_regular[fixed,1],(1,1):responses(1,mask4),(2,1):responses(2,mask4),(2,2):responses(2,mask5),(3,2):responses(3,mask5)}
 hden=lcm(*(v.denominator for table in tables.values() for v in table))
 tables={key:[int(v*hden) for v in vals] for key,vals in tables.items()}
 cellprof=[[(int(l//3==1)+int(m//5==2)+int(l==5),3 if l==0 else 1 if l==4 else 2 if l==5 else 0) if (l,m) in cells else None for m in J] for l in I]
 H=[[[0 if key is None else tables[key][T] for key in row] for row in cellprof] for T in range(32)]
 candidate=records[fixed,bmask]; ck('candidate_whole_layout_family',candidate['family']==family)
 cg={(x['weak3'],x['weak5']):x for x in candidate['corner_gates']}
 ck('candidate_exact_corner_set',len(candidate['corner_gates'])==16 and set(cg)==set(reps))
 layout_gates=[]
 for corner in reps:
  w,v=weights[corner]; theta=field[corner]; fee=0; mass=None
  for T in range(32):
   mat=[[x*y for x,y in zip(hrow,trow)] for hrow,trow in zip(H[T],theta)]
   screens=maxima(mat,w,v); screen_count+=16
   if layout in (0,1,1706,3413,5119) and T in (0,3,17,31):
    ck('literal_complete_menu_crosscheck',screens==literal_maxima(mat,w,v))
   ck('complete_16_selector_maxima_nonnegative',len(screens)==16 and min(screens)>=0)
   if T==0: mass=screens[0]
   fee+=sum(cnum[32*mode+T]*screens[mode] for mode in range(16))
  gate=F(gnum*mass-fee,cden*675*den*hden)
  ck('candidate_corner_gate_exact',gate==F(cg[corner]['gate']))
  ck('complete_corner_gate_positive',gate>0)
  if 'source_mass' in cg[corner]: ck('candidate_source_mass_exact',F(cg[corner]['source_mass'])==F(mass,675*den*hden))
  entry=dict(weak3=corner[0],weak5=corner[1],multiplicity=mult[corner],source_mass=str(F(mass,675*den*hden)),gate=str(gate))
  layout_gates.append(entry)
  key=dict(fixed_edge_index=fixed,binary_mask=bmask,family=family,weak3=corner[0],weak5=corner[1])
  if minimum is None or gate<minimum: minimum=gate; minrows=[key]
  elif gate==minimum: minrows.append(key)
 outrows.append(dict(fixed_edge_index=fixed,binary_mask=bmask,family=family,corner_gates=layout_gates))
 if layout%512==511: print(json.dumps(dict(progress_layouts=layout+1,elapsed_seconds=round(monotonic()-started,3))),flush=True)
ck('all_complete_screens',screen_count==5120*16*512==41943040)
ck('candidate_global_minimum',F(witness['minimum']['gate'])==minimum)
ck('candidate_minimum_location',{k:v for k,v in witness['minimum'].items() if k!='gate'} in minrows)
ck('one_regular_minimum_reconstructed',minimum==F(1851931013276210341843005889,931162766019912935308800000000))
policies=[]; ck('two_complete_policies',len(net['policies'])==len(witness['policies'])==2)
for policy,claim in zip(net['policies'],witness['policies']):
 fee=F(net['fee_before_arbitrary'])+F(policy['fee']); margin=minimum-fee; projected=F(net['projection_alpha'])*margin
 ck('positive_complete_network_margin',margin>0)
 ck('uniform_complete_density',projected>F(1,490000))
 ck('candidate_policy_identity',(claim['kind'],claim['K'])==(policy['kind'],policy['K']))
 ck('candidate_complete_fee',F(claim['complete_fee'])==fee)
 ck('candidate_projected_margin',F(claim['projected_margin'])==projected)
 ck('candidate_density_denominator',claim['density_denominator']==490000)
 policies.append(dict(kind=policy['kind'],K=policy['K'],complete_fee=str(fee),raw_margin=str(margin),projected_margin=str(projected),projected_margin_decimal=float(projected),density_denominator=490000))
result=dict(schema='one-regular-leaf-pair-library-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,scope='Fixed null3/5, fixed7squarestar roles(1,2,5), one named9qs edge in regularleaf0 with nine independent binaryleaf4/5 edges:5120layouts, transported to15360byregularleafchoice. One unchanged663library family chosen per entire layout, all95prioritycorners and full512queryfees, both complete658policies.',input_files=[p.name for p in paths],input_sha256=[sha256(b).hexdigest() for b in raw],verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),group_generators=generators,actual_stabilizer_orbit_count=len(components),field_parameter_count=180,canonical_layout_count=5120,transported_layout_count=15360,corner_representatives=[dict(weak3=i,weak5=j,multiplicity=mult[i,j]) for i,j in reps],field_family_denominators=[f['denominator'] for f in families],family_selection_counts=dict(Counter(x for row in selection for x in row)),uniform_all_induced_strictness_margin=str(strictgap),complete_screen_count=screen_count,minimum_gate=str(minimum),minimum_gate_decimal=float(minimum),minimizers=minrows,policies=policies,layout_records=outrows,checks=checks,check_count=sum(checks.values()))
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','complete_screen_count','minimum_gate','minimum_gate_decimal','check_count')}),flush=True)
print(json.dumps(dict(elapsed_seconds=round(monotonic()-started,3))),flush=True)
print(json.dumps(policies),flush=True)
