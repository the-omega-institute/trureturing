#!/usr/bin/env python3
"""Independent full-support replay via dense object matrices, reverse axis order."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from hashlib import sha256
from math import prod, lcm
import argparse,json,time
import numpy as np
ap=argparse.ArgumentParser()
ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
ap.add_argument('--witness',type=Path,default=(Path(__file__).parent / '../clustered_full5_allfield_dual.json'))
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=ap.parse_args();started=time.monotonic();checks=0

def ck(b,label):
 global checks
 checks+=1
 if not b:raise RuntimeError(label)

witbytes=a.witness.read_bytes();W=json.loads(witbytes)
ck(W['row_columns']==['mode','support','central_selector','outside_column','numerator'],'literal witness row schema')
names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json')
data={}
for n in names:
 raw=(a.base/n).read_bytes();ck(sha256(raw).hexdigest()==W['source_sha256'][n],'source pin '+n);data[n]=json.loads(raw)
Q=(7,11,13,17,19);g=F(200163067,201247200)
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
D=W['denominator'];ck(type(D) is int and D>0,'integer mixture denominator')
# Independently decode each global outside column and check its support.
def support(column):
 rem=column;out=[0]*5
 for i in range(4,-1,-1):rem,out[i]=divmod(rem,qshape[i])
 ck(rem==0 and column>=0,'query column in declared mixedradix grid')
 return sum(1<<i for i,k in enumerate(out) if k)
loads=[0]*512;grouped=[[] for _ in selectors];seen=set()
for row in W['rows']:
 ck(len(row)==5 and all(type(z) is int for z in row),'integer witness row')
 mode,T,sid,column,N=row
 ck(0<=mode<16 and 0<=T<32 and 0<=sid<559 and N>0,'witness domain')
 ck(selectors[sid][0]==mode,'central selector belongs to fee mode')
 ck(support(column)==T,'one global query with declared support')
 ck((sid,column) not in seen,'unique merged query row');seen.add((sid,column))
 j=32*mode+T;loads[j]+=N;grouped[sid].append((column,N*feeNum[j]))
for j,n in enumerate(loads):ck(n<=D,'exact group budget '+str(j))
# All output addresses, then exact actual support; no response matrix is materialized.
base_n=counts[0]
for v in counts[1:]:base_n=np.multiply.outer(base_n,v)
root1_count=np.zeros(cshape,dtype=np.int8)
for i,n in enumerate(cshape):
 shape=[1]*5;shape[i]=n
 root1_count+=(np.arange(n)<2).reshape(shape)
pair_ok=root1_count<=1
M0=675*prod(q*(q-1) for q in Q);dDen=D*feeDen*Dc*5
reward_num=g.numerator*dDen
upper_num=0;states=0;source_num=0;positive_states=0;cell_results=[]
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
 cell_upper=0;positive=0
 for n,d in zip(nv,debit):
  ck(type(d) is int and d>=0,'exact nonnegative actual-state debit')
  rr=reward_num-g.denominator*d
  if rr>0:cell_upper+=int(n)*rr;positive+=1
 cell_source=int(nv.sum())
 upper_num+=cell_upper;states+=len(idx);source_num+=cell_source;positive_states+=positive
 cell_results.append({'cell':[l,r],'states':len(idx),'source_numerator':cell_source,'positive_residual_states':positive,'upper_numerator':cell_upper})
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
result={'status':'PASS','checks':checks,'new_lean_verification':False,'optimizer_used':False,'witness_sha256':sha256(witbytes).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':W['source_sha256'],'all_actual_states':states,'raw_category_states_per_cell':prod(cshape),'merged_rows':len(seen),'fee_groups':512,'weight_denominator':D,'group_weight_numerator':loads[0],'fee_denominator':feeDen,'central_denominator':Dc,'outside_common_scale':5,'source_mass':str(source),'positive_residual_states':positive_states,'upper':str(upper),'joint_central_domination_factor':str(R),'joint_central_cap_upper':str(lifted),'target':str(target),'target_margin':str(target-upper),'lifted_target_margin':str(target-lifted),'cell_results':cell_results,'scope':'One exact feasible merged-query dual on the fixed109 full-five category source and complete allheight512 gate. Every actual state replayed with dense NumPy object matrices in reverse axis order. The same-source joint central density extension uses682/689/690; no gate nonpositivity, exact optimum, changed outside reference or covering-resolution claim.'}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':checks,'upper':str(upper),'states':states,'output':str(a.output),'elapsed_seconds':time.monotonic()-started}),flush=True)
