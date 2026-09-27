#!/usr/bin/env python3
"""Independent eight-central-label dual audit by dense reverse integer transport.
Reuses the canonical 696 independent source/token reconstruction; does not
import the new producer, optimizer, contraction, or declared numerical result.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from hashlib import sha256
from math import prod, lcm
import argparse,json,time
import numpy as np
ap=argparse.ArgumentParser()
ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('clustered109_central_block_fraction_witness.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=ap.parse_args();started=time.monotonic();checks=0

def ck(b,label):
 global checks
 checks+=1
 if not b:raise RuntimeError(label)

def unique_object(pairs):
 out={}
 for k,v in pairs:
  if k in out:raise RuntimeError('duplicate JSON key '+k)
  out[k]=v
 return out

witbytes=a.witness.read_bytes();W=json.loads(witbytes,object_pairs_hook=unique_object)
oldbytes=(a.base/'clustered_full5_allfield_dual.json').read_bytes()
OLD=json.loads(oldbytes,object_pairs_hook=unique_object)
ck(W['schema']=='clustered109-eight-central-block-dual-v1','new block witness schema')
ck(sha256(oldbytes).hexdigest()==W['old_witness_sha256'],'pinned old source witness identity')
ck(W['source_sha256']==OLD['source_sha256'],'all three source and original fee pins match')
labels=(3,5,9,15,25,45,75,225)
ck(W['central_labels']==list(labels),'all eight independently named numerical labels')
ck(set(labels)=={d for d in range(2,226) if 225%d==0},'complete nonunit divisor inventory of225')
modified=(32,64,128,160,192,256,288,320)
ck(W['query_modified_groups']==list(modified),'exact selected fee groups')
D=W['denominator'];BD=W['block_denominator']
ck(type(D) is int and type(BD) is int and D==BD==10**12,'common exact witness denominator')
block_rows=[];seen_centers=set();block_total=0
for row in W['centered_rows']:
 ck(len(row)==2 and all(type(v) is int for v in row),'integer complete-layout row')
 center,N=row
 ck(0<=center<225 and N>0,'valid centered layout and positive numerator')
 ck(center not in seen_centers,'no repeated centered layout');seen_centers.add(center)
 residues=tuple(center%d for d in labels)
 ck(all(0<=b<d for b,d in zip(residues,labels)),'center induces one legal residue at each independent label')
 block_rows.append((center,residues,N));block_total+=N
ck(len(block_rows)==225 and seen_centers==set(range(225)),'all225 centered rows present')
ck(block_total==BD,'new layout simplex spends exactly c')
block_eval={}
for x in range(225):
 total=0
 for center,residues,N in block_rows:
  ind=[int(x%d==b) for d,b in zip(labels,residues)]
  n=sum(ind);h=n*n+2*n
  ck(h==3*sum(ind)+2*sum(ind[i]*ind[j] for i,j in combinations(range(8),2)),'literal8-unary28-pair row coefficient')
  ck(h in (0,3,8,15,24,35,48,63,80),'full central row coefficient range')
  total+=N*h
 block_eval[x]=total
names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json')
data={}
for n in names:
 raw=(a.base/n).read_bytes();ck(sha256(raw).hexdigest()==W['source_sha256'][n],'source pin '+n);data[n]=json.loads(raw)
Q=(7,11,13,17,19);g=F(200163067,201247200);c=1-g
ck(c==F(W['block_budget'])==F(1084133,201247200),'unchanged head coefficient c')
orig=data[names[0]]['actual_originals'];added=data[names[1]]['first_tested_success']['added_higher_pure_originals'];allorig=orig+added
ck(len(allorig)==109 and len({o['modulus'] for o in allorig})==109,'109 distinct actual originals')
ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)},'higher pure exact labels')
def factor(n):
 f={}
 for p in (3,5)+Q:
  e=0
  while n%p==0:n//=p;e+=1
  if e:f[p]=e
 ck(n==1,'factorization support');return f
facts=[(o,factor(o['modulus'])) for o in allorig]
central={}
for p in (3,5):
 pure=[o for o,f in facts if set(f)=={p}];N=max(o['modulus'] for o in pure)
 alive=[x for x in range(N) if all(x%o['modulus']!=o['residue'] for o in pure)]
 cap={r:F(sum(x%(p*p)==r for x in alive),N) for r in range(p*p)}
 weak=4 if p==3 else 2;w0=F(1,p*p);strong=F(2) if p==3 else F(4,3)
 weights={r:(w0 if r==weak else strong/F(p*p)) for r,k in cap.items() if k}
 ck(cap[weak]==(F(41,729) if p==3 else F(469,15625)),'actual weak capacity')
 ck(w0/(strong*cap[weak])==(F(81,82) if p==3 else F(1875,1876)),'actual deep gamma')
 ck(sum(weights.values())==1,'central reference probability')
 central[p]={'cap':cap,'w':weights,'deep':{r:(weights[r]/cap[r])/(F(2) if p==3 else F(5,3)) for r in weights}}
cmix=[o for o,f in facts if set(f)=={3,5}]
def label(x):
 a3,a5=x%9,x%25
 return 3*(a3%3)+a3//3,5*(a5%5)+a5//5
xs=sorted([x for x in range(225) if central[3]['cap'][x%9] and central[5]['cap'][x%25] and all(x%o['modulus']!=o['residue'] for o in cmix)],key=label)
ck(len(xs)==80,'80 actual central cells')
for q in Q:
 pp=[o for o,f in facts if set(f)=={q}]
 ck(len(pp)==1 and (pp[0]['modulus'],pp[0]['residue'])==(q,0),'fixed outside Haar reference')
for p,q in combinations(Q,2):
 pair=[o for o,f in facts if set(f).intersection(Q)=={p,q}]
 ck(len(pair)==4,'four actual pair labels')
 ck(any(o['modulus']==p*q and o['residue']==1 for o in pair),'root1/root1 base event')
 for o in pair:ck(o['residue']%p==1 and o['residue']%q==1,'pair subevent relation')
# Categories are literal q² atom sets. Token matrices are reconstructed by intersections.
cats=[];U=[];counts=[]
qshape=(8,11,11,11,11);cshape=(7,10,10,10,10)
for iq,q in enumerate(Q):
 cat=[{1},{1+q*j for j in range(1,q)}]+[{r+q*j for j in range(q)} for r in range(2,min(9,q))]
 if q>9:cat.append({r+q*j for r in range(9,q) for j in range(q)})
 union=set().union(*cat)
 ck(union=={z for z in range(q*q) if z%q},'category union is complete reference support')
 ck(sum(map(len,cat))==len(union),'categories are disjoint')
 cats.append(cat);counts.append(np.array([len(s) for s in cat],dtype=np.int64))
 token_sets=[union]+[{z for z in union if z%q==r} for r in range(1,(7 if q==7 else 10))]+[{1}]
 normals=[F(1)]+[F(1,q-1)]*(len(token_sets)-2)+[F(1,q*(q-2))]
 rows=[]
 for S,u in zip(token_sets,normals):
  row=[]
  for B in cat:
   val=F(len(B.intersection(S)),q*(q-1))/u/F(len(B),q*(q-1))
   scaled=val*(5 if q==19 else 1)
   ck(scaled.denominator==1 and scaled>=0,'exact integral outside token')
   row.append(int(scaled))
  rows.append(row)
 mat=np.array(rows,dtype=object)
 ck(mat.shape==(qshape[iq],cshape[iq]),'outside matrix shape')
 ck(all(v==(5 if q==19 else 1) for v in mat[0]),'whole row uses the common19 scale')
 U.append(mat)
local={q:[] for q in Q}
for o,f in facts:
 outside=set(f).intersection(Q)
 if len(outside)==1 and len(f)>1:
  q=next(iter(outside));qp=q**f[q];cm=o['modulus']//qp
  ck(qp<=q*q and set(f)<={3,5,q},'actual unary prefix predicate')
  local[q].append((cm,o['residue']%cm,qp,o['residue']%qp))
cat_allowed={}
for x in xs:
 aa=[]
 for q,cat in zip(Q,cats):
  alive={z for z in range(q*q) if z%q and all(x%cm!=r or z%qp!=s for cm,r,qp,s in local[q])}
  allowed=[]
  for B in cat:
   n=len(B.intersection(alive));ck(n in (0,len(B)),'actual predicate constant on category');allowed.append(bool(n))
  aa.append(np.array(allowed,dtype=bool))
 cat_allowed[x]=aa
# Central selector IDs are GLOBAL mode-major, left-major, right-fastest.
lmenus=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))
rmenus=((0,),(0,1,2,3),tuple(i for i in range(20) if i!=5),tuple(i for i in range(20) if i!=5))
selectors=[];sid_lookup={}
for mode in range(16):
 e3,e5=divmod(mode,4)
 for l,r in product(lmenus[e3],rmenus[e5]):
  sid_lookup[mode,l,r]=len(selectors);selectors.append((mode,l,r))
ck(len(selectors)==559,'global selector ID contract')
Dc=82*469
central_active={}
for x in xs:
 l,r=label(x);w=central[3]['w'][x%9]*central[5]['w'][x%25]
 live=[]
 for mode in range(16):
  e3,e5=divmod(mode,4)
  left=0 if e3==0 else l//3 if e3==1 else l
  right=0 if e5==0 else r//5 if e5==1 else r
  sel3=central[3]['deep'][x%9] if e3==3 else central[3]['w'][x%9]
  sel5=central[5]['deep'][x%25] if e5==3 else central[5]['w'][x%25]
  val=Dc*sel3*sel5/w
  ck(val.denominator==1,'exact central multiplier')
  live.append((sid_lookup[mode,left,right],int(val)))
 central_active[x]=live
C0=list(map(F,data[names[2]]['combined512_coefficients']))
ck(len(C0)==512 and all(v>=0 for v in C0),'all original combined fees')
for i,q in enumerate(Q):
 if i:C0[256+(1<<i)]+=g/F(q*(q-2))
C=C0.copy();selected_weights={}
for d in labels:
 n=d;e3=e5=0
 while n%3==0:n//=3;e3+=1
 while n%5==0:n//=5;e5+=1
 ck(n==1 and 0<=e3<=2 and 0<=e5<=2,'literal central height pair')
 j=32*(4*e3+e5);weight=(2*e3+1)*(2*e5+1)
 ck(j in modified and j not in selected_weights,'unique selected screen identity')
 selected_weights[j]=weight;C[j]-=c*weight
ck(sorted(selected_weights)==list(modified),'exact complete squarefactor debit inventory')
ck(sum(selected_weights.values())==80,'complete eight-label coefficient sum')
ck(all(v>=0 for v in C),'nonnegative remaining original fees')
ck([F(v) for v in W['remaining_coefficients']]==C,'rebuild every remaining fee from original pinned data')
for j in modified:
 ck(C[j]==(g if j in (192,288,320) else 0),'retain all three original-loss g charges')
ck(sum(v>0 for v in C)==506 and sum(v==0 for v in C)==6,'506 positive original groups and6 zero groups')
feeDen=lcm(*(v.denominator for v in C),c.denominator)
feeNum=[int(v*feeDen) for v in C]
ck(all(F(n,feeDen)==v for n,v in zip(feeNum,C)),'exact complete integer fee conversion')
ck(feeDen==326858176472093392896000000,'independent common fee denominator')
ck((c*feeDen).denominator==1,'new layout budget in common denominator')

def support(column):
 rem=column;out=[0]*5
 for i in range(4,-1,-1):rem,out[i]=divmod(rem,qshape[i])
 ck(rem==0 and column>=0,'mixedradix global query domain')
 return sum(1<<i for i,k in enumerate(out) if k)
loads=[0]*512;grouped=[[] for _ in selectors];seen=set()
for row in W['rows']:
 ck(len(row)==5 and all(type(z) is int for z in row),'integer new-screen witness row')
 mode,T,sid,column,N=row
 ck(0<=mode<16 and 0<=T<32 and 0<=sid<559 and N>0,'new-screen witness row domains')
 ck(selectors[sid][0]==mode,'selector belongs to its fee mode')
 ck(support(column)==T,'one globally fixed query tuple has declared support')
 ck((sid,column) not in seen,'unique new globally fixed query row');seen.add((sid,column))
 j=32*mode+T
 ck(C[j]>0,'no row spends a zero remaining budget')
 loads[j]+=N;grouped[sid].append((column,N*feeNum[j]))
for j,n in enumerate(loads):
 ck(n==(D if C[j]>0 else 0),'exact remaining simplex budget '+str(j))
ck(sum(n>0 for n in loads)==506,'every remaining fee group has a fixed mixture')
# All output addresses, then exact actual support; no response matrix is materialized.
base_n=counts[0]
for v in counts[1:]:base_n=np.multiply.outer(base_n,v)
root1_count=np.zeros(cshape,dtype=np.int8)
for i,n in enumerate(cshape):
 shape=[1]*5;shape[i]=n
 root1_count+=(np.arange(n)<2).reshape(shape)
pair_ok=root1_count<=1
# Construct the branch identity from literal physical residue sets. In each
# surviving address, at most one axis has root1. Do not use token IDs.
branch_id=np.zeros(cshape,dtype=np.int8)
branch_count=np.zeros(cshape,dtype=np.int8)
for axis,(q,cat) in enumerate(zip(Q,cats)):
 ids=[]
 for B in cat:
  roots={v%q for v in B}
  ck(1 not in roots or roots=={1},'one root1 truth value per literal category')
  if roots!={1}:ids.append(0)
  elif B=={1}:ids.append(1+2*axis)
  else:
   ck(1 not in B,'other-root1 category excludes its distinguished child')
   ids.append(2+2*axis)
 dims=[1]*5;dims[axis]=len(cat)
 ids=np.array(ids,dtype=np.int8).reshape(dims)
 branch_id+=ids
 branch_count+=(ids>0).astype(np.int8)
ck(np.all(branch_count==root1_count),'literal root branch count agrees with support predicate')
ck(np.all((branch_id[pair_ok]>=0)&(branch_id[pair_ok]<=10)),'all actual addresses have exactly one of11 branches')
branch_num=[0]*11;branch_positive=[0]*11;branch_states=[0]*11
cellwise_num=[F(0)]*11;central_cap_rows=[]
M0=675*prod(q*(q-1) for q in Q);dDen=D*feeDen*Dc*5
reward_num=g.numerator*dDen
upper_num=0;states=0;source_num=0;positive_states=0;cell_results=[]
for ci,x in enumerate(xs):
 initial=np.zeros(prod(qshape),dtype=object)
 for sid,central_num in central_active[x]:
  for column,value in grouped[sid]:initial[column]+=value*central_num
 tensor=initial.reshape(qshape)
 for axis in (4,3,2,1,0):
  tensor=np.moveaxis(np.tensordot(U[axis].T,tensor,axes=([1],[axis])),0,axis)
 ck(tensor.shape==cshape and tensor.dtype==object,'complete reverse dense arbitrary-integer transport')
 mask=pair_ok.copy()
 for axis,allowed in enumerate(cat_allowed[x]):
  shape=[1]*5;shape[axis]=len(allowed);mask &= allowed.reshape(shape)
 idx=np.flatnonzero(mask.ravel())
 l,r=label(x);central_mass_num=675*central[3]['w'][x%9]*central[5]['w'][x%25]
 ck(central_mass_num.denominator==1,'literal source central integer mass')
 nv=base_n.ravel()[idx]*int(central_mass_num)
 debit=tensor.ravel()[idx]
 replacement=int(c*feeDen)*block_eval[x]*Dc*5
 ck(type(replacement) is int and replacement>=0,'literal physical mod225 central-layout debit')
 cell_upper=0;positive=0;cell_branch_num=[0]*11
 for address,n,d in zip(idx,nv,debit):
  branch=int(branch_id.ravel()[address]);branch_states[branch]+=1
  ck(type(d) is int and d>=0,'exact nonnegative remaining-budget debit')
  dfull=d+replacement
  ck(type(dfull) is int and dfull>=d,'complete central-block debit is a nonnegative integer')
  rr=reward_num-g.denominator*dfull
  if rr>0:
   weighted=int(n)*rr;cell_upper+=weighted;positive+=1
   branch_num[branch]+=weighted;branch_positive[branch]+=1;cell_branch_num[branch]+=weighted
 cell_source=int(nv.sum())
 rc=F(8,3)*central[3]['cap'][x%9]*central[5]['cap'][x%25]/(central[3]['w'][x%9]*central[5]['w'][x%25])
 ck(1<=rc<=F(153832,151875),'local joint central cap lies within scalarR')
 ck(sum(cell_branch_num)==cell_upper,'local residual branch partition')
 for j in range(11):cellwise_num[j]+=rc*cell_branch_num[j]
 central_cap_rows.append({'cell':[l,r],'physical_mod225':x,'cap_ratio':str(rc),'branch_numerators':list(map(str,cell_branch_num))})
 upper_num+=cell_upper;states+=len(idx);source_num+=cell_source;positive_states+=positive
 cell_results.append({'cell':[l,r],'physical_mod225':x,'states':len(idx),'source_numerator':cell_source,'positive_residual_states':positive,'upper_numerator':cell_upper})
 if (ci+1)%20==0:print(json.dumps({'completed_cells':ci+1,'actual_states':states}),flush=True)
upper_den=M0*g.denominator*dDen;upper=F(upper_num,upper_den);source=F(source_num,M0)
ck(states==OLD['expected']['active_states']==2125830,'all2125830 actual states included')
ck(source==F(OLD['expected']['source_mass'])==F(305684996597,646498195200),'exact independently reconstructed source mass')
R=F(153832,151875);target=F(W['target'])
ck(target==F(193,100000),'unchanged method threshold')
lifted=R*upper
ck(0<upper<target,'fixed-source full-field upper below target')
ck(lifted<target,'uniform joint-central cap upper below target')
coeff=[F(n,upper_den) for n in branch_num]
ck(sum(coeff,F(0))==upper,'eleven branches reproduce fixed-source bound')
ck(sum(branch_positive)==positive_states and sum(branch_states)==states,'every positive residual and actual state in exactly one branch')
slopes=[coeff[1+2*i]-coeff[2+2*i]/(q-1) for i,q in enumerate(Q)]
ck(all(v<0 for v in slopes),'all five new outside branch slopes negative')
corner_families={}
for kind in ('capped','root_balanced'):
 corners=[]
 for bits in product((0,1),repeat=5):
  value=coeff[0];parameters=[]
  for i,(q,bit) in enumerate(zip(Q,bits)):
   t=F(q*bit) if kind=='root_balanced' else F((q-1)*bit,q-2)
   u=F(q-t,q-1)
   ck(0<=t<=q and 0<=u<=q and t+(q-1)*u==q,'one common allowed outside-root mass choice')
   value+=coeff[1+2*i]*t+coeff[2+2*i]*u;parameters.append(str(t))
  corners.append({'bits':list(bits),'parameters':parameters,'value':str(value)})
 maximum=max(F(row['value']) for row in corners)
 zero=next(F(row['value']) for row in corners if row['bits']==[0]*5)
 ck(maximum==zero,'negative slopes give simultaneously realizable zero-special maximum')
 corner_families[kind]={'maximum':str(maximum),'corners':corners}
V=F(corner_families['root_balanced']['maximum'])
ck(V==F(corner_families['capped']['maximum']),'both outside classes have identical residual envelope')
ck(V>=upper,'fixed outside reference is included')
cw=[v/upper_den for v in cellwise_num]
fixed_cw=sum(cw,F(0))
ck(upper<=fixed_cw<=lifted,'fixed-outside cellwise central cap between base and scalar lift')
cwslopes=[cw[1+2*i]-cw[2+2*i]/(q-1) for i,q in enumerate(Q)]
cw_corners=[]
for bits in product((0,1),repeat=5):
 value=cw[0]
 for i,(q,bit) in enumerate(zip(Q,bits)):
  t=F(q*bit);u=(q-t)/(q-1)
  value+=cw[1+2*i]*t+cw[2+2*i]*u
 cw_corners.append({'bits':list(bits),'value':str(value)})
cwV=max(F(row['value']) for row in cw_corners)
ck(cwV<=R*V,'cellwise envelope is no worse than uniform lift')
result={'status':'PASS','checks':checks,'new_lean_verification':False,'optimizer_used':False,
 'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'witness_sha256':sha256(witbytes).hexdigest(),'old_witness_sha256':sha256(oldbytes).hexdigest(),
 'source_sha256':W['source_sha256'],'all_actual_states':states,'source_mass':str(source),
 'positive_residual_states':positive_states,'upper':str(upper),'upper_decimal':float(upper),
 'joint_central_factor':str(R),'joint_central_upper':str(lifted),'joint_central_upper_decimal':float(lifted),
 'fixed_outside_cellwise_upper':str(fixed_cw),'fixed_outside_cellwise_upper_decimal':float(fixed_cw),
 'fixed_outside_cellwise_margin':str(target-fixed_cw),'fixed_outside_cellwise_below_target':fixed_cw<target,
 'target':str(target),'target_margin':str(target-upper),'lifted_target_margin':str(target-lifted),
 'remaining_rows':len(W['rows']),'remaining_groups':506,'remaining_zero_groups':6,
 'remaining_coefficients':list(map(str,C)),'remaining_weight_sums':loads,
 'block_labels':list(labels),'block_rows':len(block_rows),'block_weight_denominator':BD,
 'block_weight_sum':block_total,'block_budget':str(c),'selected_W_coefficients':{str(k):v for k,v in sorted(selected_weights.items())},
 'debit_denominator':dDen,'cell_results':cell_results,'branch_coefficients':list(map(str,coeff)),
 'branch_positive_states':branch_positive,'branch_states':branch_states,'branch_slopes':list(map(str,slopes)),
 'outside_envelope':str(V),'outside_envelope_decimal':float(V),'outside_margin':str(target-V),
 'outside_below_target':V<target,'lifted_outside_envelope':str(R*V),
 'lifted_outside_envelope_decimal':float(R*V),'lifted_outside_margin':str(target-R*V),
 'lifted_outside_below_target':R*V<target,'outside_corner_families':corner_families,
 'cellwise_coefficients':list(map(str,cw)),'cellwise_slopes':list(map(str,cwslopes)),
 'cellwise_upper':str(cwV),'cellwise_upper_decimal':float(cwV),
 'cellwise_margin':str(target-cwV),'cellwise_below_target':cwV<target,
 'cellwise_corners':cw_corners,'central_cap_rows':central_cap_rows,
 'scope':'One feasible dual for the independent eight-central-label query replacement on the unchanged actual109 all-measurable retention interface. Complete centered layouts are a legal dual subset only, not an equality reduction for the layout maximum. All remaining506 old fee budgets and all original-loss terms are reconstructed from the new witness, not frozen old weights. Dense reverse arbitrary-integer transport checks every actual category state. Eleven-branch and cellwise envelopes require the existing ordinary same-measure root-balanced transport argument; a bound above target is certificate failure only, not a feasible gate. No optimizer, exact optimum, new Lean, or unrestricted covering conclusion.'}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':checks,'upper':str(upper),'lifted':str(lifted),
 'fixed_outside_cellwise':str(fixed_cw),'outside':str(V),'cellwise':str(cwV),
 'outside_below':V<target,'cellwise_below':cwV<target,'states':states,
 'output':str(a.output),'elapsed_seconds':time.monotonic()-started}),flush=True)
