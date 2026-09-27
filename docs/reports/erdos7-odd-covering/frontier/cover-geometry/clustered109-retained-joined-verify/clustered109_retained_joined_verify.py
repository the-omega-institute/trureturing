#!/usr/bin/env python3
"""Explicit retained fields and same-source exact interfaces for a joined oracle.

Sign uses the exact698 rational residual. The smooth field is defined by the
supplied NPZ integer numerators; it was proposed by binary64 sigmoid evaluation
and dyadic rounding. No error against the exact real sigmoid is certified.
The single-field route accepts any explicit integer NPZ table with its stored
positive denominator, without importing the sign/smooth proposal metadata.
All source projections and original screen maxima are exact for the supplied
fields on the original fixed actual109 source. No joined33 gate is evaluated.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from hashlib import sha256
import importlib.util,json,time,argparse,base64,io
import numpy as np
CHECKS=0

def ck(x,msg):
 global CHECKS
 CHECKS+=1
 if not x:raise ArithmeticError(msg)


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--base',type=Path,required=True)
 parser.add_argument('--witness',type=Path)
 parser.add_argument('--sign-field',type=Path)
 parser.add_argument('--smooth-field',type=Path)
 parser.add_argument('--field',type=Path,help='Evaluate only this explicit NPZ or base64 NPZ, using its stored positive denominator')
 parser.add_argument('--field-name',default='explicit_rational_field')
 parser.add_argument('--field-definition',default='explicit supplied integer NPZ table divided by its stored denominator')
 parser.add_argument('--output-prefix',type=Path,required=True)
 args=parser.parse_args();BASE=args.base
 ck(args.field is None or (args.sign_field is None and args.smooth_field is None and args.witness is None),'generic field cannot borrow sign/smooth metadata')
 ck(args.field is not None or all(x is not None for x in (args.witness,args.sign_field,args.smooth_field)),'three-field route requires all declared inputs')
 WP=args.witness if args.field is None else BASE/'clustered_full5_allfield_dual.json'
 started=time.perf_counter();w=json.loads(WP.read_text())
 if args.field is not None:w['rows']=[];w['denominator']=1
 spec=importlib.util.spec_from_file_location('source692',BASE/'clustered_full5_allfield_verify.py');core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
 class NewRows:
  def read_text(self):return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':w['source_sha256'],'denominator':w['denominator'],'rows':w['rows'],'expected':{}})
 p=core.prepare(BASE,NewRows(),w['denominator']);M=core.G.denominator*p['debitDen'];c=1-core.G
 # Same definitions as the pinned helper's internal C and selectors. The
 # helper does not export them; no separate numerical source model is used.
 fees_exact=list(map(F,json.loads((BASE/'remaining33_global_root_exclusion_certificate.json').read_text())['combined512_coefficients']))
 for iq,q in enumerate(core.Q):
  if q>7:fees_exact[256+(1<<iq)]+=core.G/F(q*(q-2))
 selectors=[]
 for mode in range(16):
  ex,ey=divmod(mode,4)
  xm=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[ex]
  ym=((0,),(0,1,2,3),tuple(m for m in range(20) if m!=5),tuple(m for m in range(20) if m!=5))[ey]
  for left,right in product(xm,ym):
   ids=[ci for ci,(l,m) in enumerate(p['cells']) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))]
   mult=F(1)
   if ex==3:mult*=(F(81,82) if left==4 else F(1))/F(2-(left==4),9)
   if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else F(1))/F(4-(right==10),75)
   selectors.append({'mode':mode,'indices':np.array(ids,dtype=np.intp),'exact_multiplier':mult})
 ck(len(selectors)==559 and len(fees_exact)==512,'literal original query families')
 support=np.zeros(p['token_shape'],dtype=np.uint8)
 for axis,size in enumerate(p['token_shape']):
  dims=[1]*5;dims[axis]=size
  support|=((np.arange(size)>0).astype(np.uint8)*(1<<axis)).reshape(dims)
 group_columns=[np.flatnonzero(support.ravel()==T) for T in range(32)]
 ck(sum(map(len,group_columns))==117128,'outside query partition')
 changed={32:F(3),64:F(5),128:F(3),160:F(9),192:F(15),256:F(5),288:F(15),320:F(25)}
 correction=[F(0)]*80
 for mode,T,sid,col,num in w['rows']:
  j=32*mode+T
  if j in changed:
   ck(T==col==0,'shallow correction only')
   for ci in selectors[sid]['indices']:correction[int(ci)]+=c*changed[j]*F(num,w['denominator'])
 shape=p['category_shape'];fullshape=(80,)+shape
 rootcount=np.zeros(shape,dtype=np.uint8)
 for k,size in enumerate(shape):
  dims=[1]*5;dims[k]=size;rootcount+=(np.arange(size)<2).astype(np.uint8).reshape(dims)
 good=rootcount<=1
 source_num=np.zeros(fullshape,dtype=np.int64);sign=np.zeros(fullshape,dtype=np.uint32)
 points=[];residues=[];Qf=2**20;active_count=0
 for ci,(l,m) in enumerate(p['cells']):
  x=(100*(3*(l%3)+l//3)+126*(5*(m%5)+m//5))%225;points.append([x%9,x%25]);residues.append(x)
  count=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64)
  for axis,row in enumerate(p['counts'][ci]):
   dims=[1]*5;dims[axis]=len(row);count*=np.array(row,dtype=np.int64).reshape(dims)
  count*=good;source_num[ci]=count;mask=count>0;active_count+=int(mask.sum())
  if args.field is not None or not np.any(mask):continue
  sparse=np.zeros(p['token_shape'],dtype=object)
  for col,z in p['scatter'][ci].items():sparse.flat[col]=z
  debit=core.transform(sparse,p['matrices'])
  hnum=0
  for center,num in w['centered_rows']:
   n=sum((x-center)%d==0 for d in w['central_labels']);hnum+=num*(n*n+2*n)
  addback=M*correction[ci];new=M*c*F(hnum,w['block_denominator'])
  ck(addback.denominator==new.denominator==1,'exact residual normalization')
  residual=core.G.numerator*p['debitDen']-core.G.denominator*debit+int(addback)-int(new)
  sign[ci][mask]=(residual[mask]>0).astype(np.uint32)
 ck(active_count==2125830 and int(source_num.sum())==int(F(305684996597,646498195200)*p['M0']),'complete common source')
 if args.field is not None:
  raw=args.field.read_bytes()
  if args.field.suffix=='.b64':raw=base64.b64decode(raw,validate=True)
  with np.load(io.BytesIO(raw),allow_pickle=False) as data:
   explicit_num=data['numerators'].copy();stored_den=data['denominator'];stored_residues=data['central_residues']
   ck(explicit_num.shape==fullshape and explicit_num.dtype.kind in 'iu','explicit integer field table')
   ck(stored_den.shape==(1,) and stored_den.dtype.kind in 'iu' and int(stored_den[0])>0,'stored positive integer field denominator')
   explicit_den=int(stored_den[0])
   ck(np.array_equal(stored_residues,residues),'field coordinate order')
   ck(np.all(explicit_num>=0) and np.all(explicit_num<=explicit_den),'retention in unit interval')
   ck(np.all(explicit_num[source_num==0]==0),'zero outside actual source')
  jobs=[(args.field_name,explicit_num,explicit_den)]
 else:
  saved=[]
  for path,den in ((args.sign_field,1),(args.smooth_field,Qf)):
   raw=path.read_bytes()
   if path.suffix=='.b64':raw=base64.b64decode(raw,validate=True)
   with np.load(io.BytesIO(raw),allow_pickle=False) as data:
    arr=data['numerators'];stored_den=data['denominator'];stored_residues=data['central_residues']
    ck(arr.shape==fullshape and arr.dtype.kind in 'iu','explicit integer field table')
    ck(stored_den.shape==(1,) and int(stored_den[0])==den,'field denominator')
    ck(np.array_equal(stored_residues,residues),'field coordinate order')
    ck(np.all(arr>=0) and np.all(arr<=den),'retention in unit interval')
    ck(np.all(arr[source_num==0]==0),'zero outside actual source')
    saved.append(arr.copy())
  ck(np.array_equal(sign,saved[0]),'saved sign equals exact rational residual sign')
  sign,smooth=saved
  jobs=[('allone',(source_num>0).astype(np.uint32),1),('sign',sign,1),('smooth20',smooth,Qf)]
 # Exact forward query matrices are transposes of the pinned debit matrices.
 # The sole common outside denominator5 comes from the q19 free-root token.
 forward=[]
 for axis,matrix in enumerate(p['matrices']):
  rows=[]
  for token in range(p['token_shape'][axis]):
   rows.append([(cat,coef) for cat,terms in enumerate(matrix) for t,coef in terms if t==token])
  ck(all(rows),'every outside token has a literal support');forward.append(rows)
 prime=(3,5)+core.Q;rootsets=[]
 for q,cats in zip(core.Q,p['cats']):
  rootsets.append([tuple(sorted({z%q for z in cat})) for cat in cats])
 # All phases in each free-root category are equidistributed conditional on it.
 # Same-prime event intersections are Kronecker, never products of two averages.
 for q,cats,sets in zip(core.Q,p['cats'],rootsets):
  for cat,roots in zip(cats,sets):
   hist=[sum(z%q==r for z in cat) for r in roots]
   ck(len(set(hist))==1,'literal uniform roots inside one pooled category')
   for a,b in combinations(roots,2):ck(not any(z%q==a and z%q==b for z in cat),'distinct roots of one prime have empty intersection')
 fields=[]
 for name,fnum,fden in jobs:
  tic=time.perf_counter();field_path=args.field if args.field is not None else None if name=='allone' else args.sign_field if name=='sign' else args.smooth_field
  mass=source_num.astype(object)*fnum.astype(object);den=p['M0']*fden
  central=np.array([int(mass[i].sum()) for i in range(80)],dtype=object)
  unary=[np.zeros(q,dtype=object) for q in prime]
  pairs={(i,j):np.zeros((prime[i],prime[j]),dtype=object) for i,j in combinations(range(7),2)}
  # Each projection is derived from this same complete mass tensor.
  for ci,x in enumerate(residues):
   nn=int(central[ci]);unary[0][x%3]+=nn;unary[1][x%5]+=nn;pairs[0,1][x%3,x%5]+=nn
   for iq,q in enumerate(core.Q):
    table=mass[ci].sum(axis=tuple(axis for axis in range(5) if axis!=iq))
    for k,n in enumerate(table):
     roots=rootsets[iq][k];ck(int(n)%len(roots)==0,'exact unary free-root distribution');each=int(n)//len(roots)
     for root in roots:
      unary[iq+2][root]+=each;pairs[0,iq+2][x%3,root]+=each;pairs[1,iq+2][x%5,root]+=each
  for iq,jq in combinations(range(5),2):
   table=mass.sum(axis=tuple(axis for axis in range(6) if axis not in (iq+1,jq+1)))
   for ki,kj in product(range(shape[iq]),range(shape[jq])):
    ri,rj=rootsets[iq][ki],rootsets[jq][kj];n=int(table[ki,kj]);ck(n%(len(ri)*len(rj))==0,'exact distinct-prime free-root joint distribution');each=n//(len(ri)*len(rj))
    for a,b in product(ri,rj):pairs[iq+2,jq+2][a,b]+=each
  total=int(central.sum())
  for row in unary:ck(int(row.sum())==total,'common unary total')
  for (i,j),table in pairs.items():
   ck(all(int(x)==int(y) for x,y in zip(table.sum(axis=1),unary[i])),'pair first marginal')
   ck(all(int(x)==int(y) for x,y in zip(table.sum(axis=0),unary[j])),'pair second marginal')
  transformed=np.empty((80,prod(p['token_shape'])),dtype=object)
  for ci in range(80):transformed[ci]=core.transform(mass[ci],forward).reshape(-1)
  maxima=[0]*512;winning=[None]*512
  for sid,selector in enumerate(selectors):
   ids=selector['indices']
   if not len(ids):continue
   mult=selector['exact_multiplier']*p['Dc'];ck(mult.denominator==1,'integer central normalizer')
   row=np.sum(transformed[ids],axis=0)*int(mult)
   mode=selector['mode']
   for T,columns in enumerate(group_columns):
    local=row[columns];arg=int(np.argmax(local));value=int(local[arg]);j=32*mode+T
    if winning[j] is None or value>maxima[j]:maxima[j]=value;winning[j]=[sid,int(columns[arg])]
  S=[F(z,5*p['Dc']*den) for z in maxima]
  mass_exact=F(total,den);original_fee=sum(C*Sj for C,Sj in zip(fees_exact,S));old_gate=core.G*mass_exact-original_fee
  # Joined ownership: complete central block plus the five extra prime unaries
  # and20 noncentral prime-pair triangles. Each selected factor is charged once.
  selected={j:W for j,W in changed.items()};ledger=[]
  for iq,q in enumerate(core.Q):
   selected[1<<iq]=F(3,q-1)
   selected[128+(1<<iq)]=F(9,q-1);selected[32+(1<<iq)]=F(9,q-1)
  for iq,jq in combinations(range(5),2):selected[(1<<iq)+(1<<jq)]=F(9,(core.Q[iq]-1)*(core.Q[jq]-1))
  ck(len(selected)==33,'33 distinct selected screen coefficients')
  Wfull=[]
  for j in range(512):
   mode,T=divmod(j,32);e3,e5=divmod(mode,4)
   W=(F(1),F(3),F(5),F(8,9))[e3]*(F(1),F(3),F(5),F(1,8))[e5]
   for iq,q in enumerate(core.Q):
    if T&(1<<iq):W*=F(3,q-1)+F(5*q-3,(q-2)*(q-1)**2)
   if j==0:W=F(0)
   pick=selected.get(j,F(0));loss=fees_exact[j]-c*W;remaining=fees_exact[j]-c*pick
   ck(loss>=0 and W>=pick and remaining==loss+c*(W-pick),'retain original loss and all unselected query charges')
   Wfull.append(W)
   if pick:ledger.append({'screen':j,'selected_W':str(pick),'original_W':str(W),'original_loss':str(loss),'original_C':str(fees_exact[j]),'remaining_C':str(remaining),'same_measure_screen':str(S[j]),'selected_linear_fee':str(pick*S[j])})
  selected_fee=sum(pick*S[j] for j,pick in selected.items())
  payload={'schema':'clustered109-retained-joined-input-v1','scope':'One explicit rational retained field on the original fixed actual109 source. Exact same-source projections and original screens only; joined oracle not yet applied.','field':name,'field_definition':args.field_definition if args.field is not None else 'unit retention on the actual source' if name=='allone' else 'exact sign of698 rational residual' if name=='sign' else 'explicit NPZ integer field divided by 2^20, originally proposed using binary64 sigmoid(tau=.0003) then rounding; no exact-real sigmoid approximation bound certified','field_denominator':fden,'tau':'.0003' if args.field is None and name=='smooth20' else None,'exact_real_sigmoid_error_bound':None,'field_file':field_path.name if field_path else None,'field_sha256':sha256(field_path.read_bytes()).hexdigest() if field_path else None,'dual_witness_sha256':None if args.field is not None else sha256(WP.read_bytes()).hexdigest(),'source_sha256':p['pins'],'denominator':den,'source_mass':str(mass_exact),'central':{'points':points,'residues_mod225':residues,'weights':list(map(int,central))},'unary':{str(q):list(map(int,unary[i])) for i,q in enumerate(prime)},'pairs':{f'{prime[i]},{prime[j]}':[[int(z) for z in row] for row in table] for (i,j),table in pairs.items()},'same_prime_intersection_rule':'1_[a]_q*1_[b]_q=0 for a!=b and=1_[a]_q for a=b; never multiply separate pooled means','original_screen_values':list(map(str,S)),'original_screen_winners':winning,'original_coefficients':list(map(str,fees_exact)),'original_fee':str(original_fee),'old_gate':str(old_gate),'old_gate_decimal':float(old_gate),'selected_joined_screen_fee':str(selected_fee),'selected_joined_screen_fee_decimal':float(selected_fee),'selected_fee_ledger':ledger,'joined_gate':None,'exact_checks':CHECKS+core.CHECKS,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':time.perf_counter()-tic}
  path=Path(str(args.output_prefix)+'_'+name+'_joined_input.json');path.write_text(json.dumps(payload,indent=2)+'\n')
  fields.append({'field':name,'input':str(path),'sha256':sha256(path.read_bytes()).hexdigest(),'old_gate':str(old_gate),'source_mass':str(mass_exact),'selected_fee':str(selected_fee),'seconds':time.perf_counter()-tic})
  print(json.dumps(fields[-1]),flush=True)
 summary={'status':'PASS','scope':'Exact retained-field source interfaces, not a33-gate or positive primal conclusion.','fields':fields,'exact_source_states':active_count,'checks':CHECKS+core.CHECKS,'seconds':time.perf_counter()-started,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'peak_rss_bytes':core.rss()}
 Path(str(args.output_prefix)+'_retained_interfaces.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
