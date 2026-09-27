#!/usr/bin/env python3
"""Independent triangle residual and root-balanced 11-branch envelope, dense reverse transport."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from hashlib import sha256
from math import prod, lcm
import argparse,json,time
import numpy as np
ap=argparse.ArgumentParser()
ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
ap.add_argument('--witness',type=Path)
ap.add_argument('--triangle-witness',type=Path,default=Path(__file__).with_name('clustered109_triangle_replacement_witness.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=ap.parse_args();started=time.monotonic();checks=0
if a.witness is None:a.witness=a.base/'clustered_full5_allfield_dual.json'

def ck(b,label):
 global checks
 checks+=1
 if not b:raise RuntimeError(label)

witbytes=a.witness.read_bytes();W=json.loads(witbytes)
tri_bytes=a.triangle_witness.read_bytes();TW=json.loads(tri_bytes)
ck(TW['schema']=='clustered109-triangle-replacement-dual-v1','triangle witness schema')
ck(sha256(witbytes).hexdigest()==TW['old_witness_sha256'],'same frozen old witness')
ck(TW['source_sha256']==W['source_sha256'],'same three actual source and fee pins')
ck(TW['removed_groups']==[32,128,160],'exactly three original query-only groups replaced')
ck(TW['triangle_row_schema']==['b3','b5','b15','numerator'] and TW['triangle_domain']==[3,5,15],'literal triangle row format')
triangle_D=TW['triangle_denominator'];ck(type(triangle_D) is int and triangle_D==10**12,'exact triangle denominator')
triangle_rows=[];triangle_seen=set();triangle_total=0
for row in TW['triangle_rows']:
 ck(len(row)==4 and all(type(v) is int for v in row),'integer triangle row')
 b3,b5,b15,N=row
 ck(0<=b3<3 and 0<=b5<5 and 0<=b15<15 and N>0,'each row is one valid independent-label layout')
 ck((b3,b5,b15) not in triangle_seen,'no duplicate triangle layout')
 triangle_seen.add((b3,b5,b15));triangle_total+=N;triangle_rows.append(tuple(row))
ck(triangle_total==triangle_D,'triangle group spends exactly its c budget')
triangle_eval={}
for x15 in range(15):
 score=0
 for b3,b5,b15,N in triangle_rows:
  ind=[int(x15%3==b3),int(x15%5==b5),int(x15==b15)]
  n=sum(ind);h=n*n+2*n
  ck(h==3*sum(ind)+2*sum(ind[i]*ind[j] for i,j in combinations(range(3),2)),'literal six-factor coefficient')
  ck(h in (0,3,8,15),'triangle row coefficient range')
  score+=N*h
 triangle_eval[x15]=score
ck(W['row_columns']==['mode','support','central_selector','outside_column','numerator'],'literal witness row schema')
names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json')
data={}
for n in names:
 raw=(a.base/n).read_bytes();ck(sha256(raw).hexdigest()==W['source_sha256'][n],'source pin '+n);data[n]=json.loads(raw)
Q=(7,11,13,17,19);g=F(200163067,201247200);c=1-g
ck(c==F(TW['triangle_budget'])==F(1084133,201247200),'unchanged head coefficient c')
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
C=list(map(F,data[names[2]]['combined512_coefficients']))
ck(len(C)==512 and all(c>=0 for c in C),'complete fees')
for i,q in enumerate(Q):
 if i:C[256+(1<<i)]+=g/F(q*(q-2))
feeDen=lcm(*(c.denominator for c in C));feeNum=[int(c*feeDen) for c in C]
ck(feeDen==326858176472093392896000000,'fullmode8 fee denominator')
D=W['denominator'];ck(type(D) is int and D==triangle_D,'old and replacement denominator coincide')
ck(C[32]==3*c and C[128]==3*c and C[160]==9*c,'removed groups contain only their exact original square factors')
ck((c*feeDen).denominator==1,'triangle budget represented by old common fee denominator')
# Independently decode each global outside column and check its support.
def support(column):
 rem=column;out=[0]*5
 for i in range(4,-1,-1):rem,out[i]=divmod(rem,qshape[i])
 ck(rem==0 and column>=0,'query column in declared mixedradix grid')
 return sum(1<<i for i,k in enumerate(out) if k)
loads=[0]*512;grouped=[[] for _ in selectors];seen=set();removed_rows=[]
for row in W['rows']:
 ck(len(row)==5 and all(type(z) is int for z in row),'integer witness row')
 mode,T,sid,column,N=row
 ck(0<=mode<16 and 0<=T<32 and 0<=sid<559 and N>0,'witness domain')
 ck(selectors[sid][0]==mode,'central selector belongs to fee mode')
 ck(support(column)==T,'one global query with declared support')
 ck((sid,column) not in seen,'unique merged query row');seen.add((sid,column))
 j=32*mode+T;loads[j]+=N;grouped[sid].append((column,N*feeNum[j]))
 if j in (32,128,160):
  ck(T==0 and column==0,'removed row has no outside query')
  removed_rows.append((j,sid,N))
for j,n in enumerate(loads):ck(n<=D,'exact group budget '+str(j))
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
new_upper_num=0;new_positive_states=0;root_corrections={}
for ci,x in enumerate(xs):
 initial=np.zeros(prod(qshape),dtype=object)
 for sid,central_num in central_active[x]:
  for column,value in grouped[sid]:initial[column]+=value*central_num
 tensor=initial.reshape(qshape)
 # Deliberately dense arbitrary-integer contraction in reverse axis order.
 for axis in (4,3,2,1,0):
  tensor=np.moveaxis(np.tensordot(U[axis].T,tensor,axes=([1],[axis])),0,axis)
 ck(tensor.shape==cshape and tensor.dtype==object,'complete exact tensor result')
 mask=pair_ok.copy()
 for axis,allowed in enumerate(cat_allowed[x]):
  shape=[1]*5;shape[axis]=len(allowed);mask &= allowed.reshape(shape)
 idx=np.flatnonzero(mask.ravel())
 l,r=label(x);central_mass_num=675*central[3]['w'][x%9]*central[5]['w'][x%25]
 ck(central_mass_num.denominator==1,'base central integer mass')
 nv=base_n.ravel()[idx]*int(central_mass_num)
 debit=tensor.ravel()[idx]
 # Reconstruct deleted root-query density directly from physical residues,
 # independently of the tensor's central-selector multiplication.
 deleted=0
 for j,sid,N in removed_rows:
  mode,left,right=selectors[sid]
  active=(x%5==right) if j==32 else (x%3==left) if j==128 else (x%3==left and x%5==right)
  if active:deleted+=N*feeNum[j]*Dc*5
 replacement=int(c*feeDen)*triangle_eval[x%15]*Dc*5
 delta=replacement-deleted
 root=(x%3,x%5)
 if root in root_corrections:ck(root_corrections[root]==delta,'one common correction per physical central root category')
 else:root_corrections[root]=delta
 cell_upper=0;positive=0;cell_new_upper=0;new_positive=0
 cell_branch_num=[0]*11
 for address,n,d in zip(idx,nv,debit):
  j=int(branch_id.ravel()[address]);branch_states[j]+=1
  ck(type(d) is int and d>=0,'exact nonnegative actual-state debit')
  rr=reward_num-g.denominator*d
  if rr>0:cell_upper+=int(n)*rr;positive+=1
  ck(d>=deleted,'old debit contains every removed nonnegative term')
  dnew=d+delta
  ck(type(dnew) is int and dnew>=0,'remaining509 plus triangle debit is exact nonnegative integer')
  rrnew=reward_num-g.denominator*dnew
  if rrnew>0:
   cell_new_upper+=int(n)*rrnew;new_positive+=1
   branch_num[j]+=int(n)*rrnew;branch_positive[j]+=1;cell_branch_num[j]+=int(n)*rrnew
 cell_source=int(nv.sum())
 rc=F(8,3)*central[3]['cap'][x%9]*central[5]['cap'][x%25]/(central[3]['w'][x%9]*central[5]['w'][x%25])
 ck(1<=rc<=F(153832,151875),'exact local central cap bounded by old uniform scalar')
 ck(sum(cell_branch_num)==cell_new_upper,'local new branch partition')
 for j in range(11):cellwise_num[j]+=rc*cell_branch_num[j]
 central_cap_rows.append({'cell':[l,r],'cap_ratio':str(rc),'branch_numerators':list(map(str,cell_branch_num))})
 new_upper_num+=cell_new_upper;new_positive_states+=new_positive
 upper_num+=cell_upper;states+=len(idx);source_num+=cell_source;positive_states+=positive
 cell_results.append({'cell':[l,r],'states':len(idx),'source_numerator':cell_source,'positive_residual_states':positive,'upper_numerator':cell_upper,'triangle_upper_numerator':cell_new_upper,'triangle_positive_residual_states':new_positive})
 if (ci+1)%20==0:print(json.dumps({'completed_cells':ci+1,'actual_states':states}),flush=True)
upper_den=M0*g.denominator*dDen
upper=F(upper_num,upper_den)
source=F(source_num,M0)
ck(states==W['expected']['active_states']==2125830,'every actual full5 state included')
ck(source==F(W['expected']['source_mass'])==F(305684996597,646498195200),'exact total common source')
ck(upper==F(W['expected']['upper']),'exact full-state upper matches candidate')
ck(all(n==W['expected']['weight_sum_numerator'] for n in loads),'merged common schedule weight')
R=F(153832,151875);target=F(193,100000)
lifted=R*upper
ck(F(0)<upper<target,'positive exact upper below original target')
ck(lifted<target,'joint central density cap reuse remains below original target')
new_upper=F(new_upper_num,upper_den)
new_lifted=R*new_upper
ck(len(root_corrections)==7,'all seven physical central root categories')
ck(len(removed_rows)==6 and len(W['rows'])-len(removed_rows)==157335,'exact unchanged old row inventory')
ck(F(0)<=new_upper<F(TW['target'])==target,'triangle gate all-field threshold exclusion')
ck(new_lifted<target,'same joint central cap extension remains below threshold')
coeff=[F(n,upper_den) for n in branch_num]
ck(sum(coeff,F(0))==new_upper,'eleven new branches reproduce the independently computed triangle upper')
ck(sum(branch_positive)==new_positive_states and sum(branch_states)==states,'complete new branch state partition')
slopes=[coeff[1+2*i]-coeff[2+2*i]/(q-1) for i,q in enumerate(Q)]
ck(all(v<0 for v in slopes),'all five new affine slopes strictly negative')
corner_families={}
for kind in ('capped','root_balanced'):
 corners=[]
 for bits in product((0,1),repeat=5):
  value=coeff[0];parameters=[]
  for i,(q,bit) in enumerate(zip(Q,bits)):
   t=F(q*bit) if kind=='root_balanced' else F((q-1)*bit,q-2)
   u=F(q-t,q-1)
   ck(0<=t<=q and 0<=u<=q,'nonnegative global root-balanced category law')
   ck(t+(q-1)*u==q,'one common root mass constraint')
   value+=coeff[1+2*i]*t+coeff[2+2*i]*u;parameters.append(str(t))
  corners.append({'bits':list(bits),'parameters':parameters,'value':str(value)})
 maximum=max(F(row['value']) for row in corners)
 zero=next(F(row['value']) for row in corners if row['bits']==[0]*5)
 ck(maximum==zero,'simultaneously realizable zero-special maximum')
 corner_families[kind]={'maximum':str(maximum),'corners':corners}
V=F(corner_families['root_balanced']['maximum'])
ck(V==F(corner_families['capped']['maximum']),'both outside-reference classes have same residual envelope')
ck(V>=new_upper,'old outside reference included in envelope')
cw=[v/upper_den for v in cellwise_num]
cwslopes=[cw[1+2*i]-cw[2+2*i]/(q-1) for i,q in enumerate(Q)]
cw_corners=[]
for bits in product((0,1),repeat=5):
 value=cw[0]
 for i,(q,bit) in enumerate(zip(Q,bits)):
  t=F(q*bit);u=(q-t)/(q-1)
  value+=cw[1+2*i]*t+cw[2+2*i]*u
 cw_corners.append({'bits':list(bits),'value':str(value)})
cwV=max(F(row['value']) for row in cw_corners)
ck(cwV<=R*V,'cellwise bound no worse than scalar lift')
result={'status':'PASS'  ,'checks':checks,'new_lean_verification':False,'optimizer_used':False,
 'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'old_witness_sha256':sha256(witbytes).hexdigest(),'triangle_witness_sha256':sha256(tri_bytes).hexdigest(),
 'source_sha256':W['source_sha256'],'all_actual_states':states,'source_mass':str(source),
 'old_positive_residual_states':positive_states,'new_positive_residual_states':new_positive_states,
 'old_upper':str(upper),'triangle_upper':str(new_upper),'triangle_upper_decimal':float(new_upper),
 'joint_central_factor':str(R),'joint_central_triangle_upper':str(new_lifted),
 'joint_central_triangle_upper_decimal':float(new_lifted),'target':str(target),
 'target_margin':str(target-new_upper),'lifted_target_margin':str(target-new_lifted),
 'old_rows':len(W['rows']),'removed_rows':len(removed_rows),'retained_rows':len(W['rows'])-len(removed_rows),
 'retained_groups':509,'triangle_rows':len(triangle_rows),'triangle_weight_denominator':triangle_D,
 'triangle_weight_sum':triangle_total,'triangle_budget':str(c),'debit_denominator':dDen,
 'root_corrections':[{'physical_roots':list(k),'replacement_minus_deleted_density':str(F(v,dDen))} for k,v in sorted(root_corrections.items())],
 'cell_results':cell_results,
 'branch_coefficients':[str(v) for v in coeff],'branch_positive_states':branch_positive,
 'branch_states':branch_states,'branch_slopes':[str(v) for v in slopes],
 'outside_envelope':str(V),'outside_envelope_decimal':float(V),
 'lifted_outside_envelope':str(R*V),'lifted_outside_envelope_decimal':float(R*V),
 'outside_margin':str(target-V),'lifted_outside_margin':str(target-R*V),
 'outside_below_target':V<target,'lifted_outside_below_target':R*V<target,
 'outside_corner_families':corner_families,
 'cellwise_coefficients':list(map(str,cw)),'cellwise_slopes':list(map(str,cwslopes)),
 'cellwise_upper':str(cwV),'cellwise_upper_decimal':float(cwV),
 'cellwise_margin':str(target-cwV),'cellwise_below_target':cwV<target,
 'cellwise_corners':cw_corners,'central_cap_rows':central_cap_rows,

 'scope':'One exact feasible triangle-replacement dual for the same actual109 all-field source and complete remaining509 fee groups including fullmode8. New triangle group has budgetc and valid independent-label layout rows. All actual states recomputed by dense reverse integer transport. New eleven-branch sums and both global-corner envelopes independently computed. The ordinary measure-level argument from693, with the new mod15 fee preserved, is required for arbitrary root-balanced outside product references. A false below-target field reports only failure of this certificate, never an achievable gate. No exact optimum, further cluster, or unrestricted covering claim.'}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':checks,'upper':str(new_upper),'lifted':str(new_lifted),'outside':str(V),'lifted_outside':str(R*V),'outside_below':V<target,'lifted_outside_below':R*V<target,'cellwise_upper':str(cwV),'cellwise_decimal':float(cwV),'cellwise_below':cwV<target,'states':states,'output':str(a.output),'elapsed_seconds':time.monotonic()-started}),flush=True)
