#!/usr/bin/env python3
"""Exact central retention against all loss screens and a coherent Haar-tail family.

The only imported project program is the existing canonical exact source engine.
No optimizer, floating-point decision, or unrestricted Gamma maximum is used.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod,lcm
from hashlib import sha256
import importlib.util,argparse,json,time,resource,platform
import numpy as np
P=(3,5,7,11,13,17,19);Q=P[2:];LS=(0,1,2,4,5);MS=tuple(m for m in range(20) if m!=5)
CHECKS=0
def ck(x,label):
 global CHECKS
 CHECKS+=1
 if not x:raise ArithmeticError(label)
def prepare_source(base):
 path=base/'clustered_full5_allfield_verify.py';ck(sha256(path.read_bytes()).hexdigest()=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56','pinned source engine');sp=importlib.util.spec_from_file_location('canonical_exact_source',path);core=importlib.util.module_from_spec(sp);sp.loader.exec_module(core)
 names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json');pins={name:sha256((base/name).read_bytes()).hexdigest() for name in names}
 class Empty:
  def read_text(self):return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':pins,'denominator':1,'rows':[],'expected':{}})
 return core,core.prepare(base,Empty(),1),pins

def literal_selectors(p):
 result=[]
 for mode in range(16):
  ex,ey=divmod(mode,4);xs=((0,),(0,1),LS,LS)[ex];ys=((0,),(0,1,2,3),MS,MS)[ey]
  for left,right in product(xs,ys):
   ids=[i for i,(l,m) in enumerate(p['cells']) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))]
   mult=F(1)
   if ex==3:mult*=(F(81,82) if left==4 else 1)/F(2-(left==4),9)
   if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else 1)/F(4-(right==10),75)
   result.append((mode,left,right,ids,mult))
 ck(len(result)==559 and sum(bool(s[3]) for s in result)==482,'all literal central selectors')
 return result

def source_weights(p,ci):
 shape=p['category_shape'];l,m=p['cells'][ci];a=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64);roots=np.zeros(shape,dtype=np.uint8)
 for axis,row in enumerate(p['counts'][ci]):
  dims=[1]*5;dims[axis]=len(row);a*=np.array(row,dtype=np.int64).reshape(dims);roots+=(np.arange(len(row))<2).reshape(dims)
 return a*(roots<=1)

def forward_integer(value,matrices):
 for axis in range(4,-1,-1):
  view=np.moveaxis(value,axis,0);rows=matrices[axis];nt=max(token for row in rows for token,coef in row)+1;out=np.zeros((nt,)+view.shape[1:],dtype=object)
  for k,row in enumerate(rows):
   for token,coef in row:out[token]+=view[k] if coef==1 else coef*view[k]
  value=np.moveaxis(out,0,axis)
 return value

def collapse(value):
 for axis in range(5):
  view=np.moveaxis(value,axis,0);value=np.moveaxis(np.concatenate(((view[0]+view[1])[None,...],view[2:]),axis=0),0,axis)
 return value

def independent_row_numerator(p,ci,col):
 toks=np.unravel_index(col,p['token_shape']);aa=[];bb=[]
 for q,row,matrix,tok in zip(Q,p['counts'][ci],p['matrices'],toks):
  a=b=0
  for k,(count,entries) in enumerate(zip(row,matrix)):
   z=count*dict(entries).get(int(tok),0)
   if k<2:b+=z
   else:a+=z
  aa.append(a);bb.append(b)
 x=prod(aa)+sum(bb[i]*prod(aa[j] for j in range(5) if j!=i) for i in range(5));l,m=p['cells'][ci]
 return (2-(l==4))*(4-(m==10))*x

def match_factor(p,h,E):
 if E is None:return F((h+1)**2)+F(2*(h+1),p-1)+F(p+1,(p-1)**2)
 ck(E>=h,'declared inventory resolves shallow centre')
 return F((h+1)**2)+sum((F(2*(h+k)+1,p**k) for k in range(1,E-h+1)),F(0))

def centre_integer_transform(value,exponents):
 scale=1;times=[];physical=([3*(l%3)+l//3 for l in LS],[5*(m%5)+m//5 for m in MS]);roots=[tuple(range(1,min(q,9)))+((9,) if q>9 else ()) for q in Q]
 for axis,p in enumerate(P):
  start=time.perf_counter();h=2 if axis<2 else 1;match=match_factor(p,h,None if exponents is None else exponents[axis]);view=np.moveaxis(value,axis,0);total=np.sum(view,axis=0);out=np.empty_like(view)
  if axis<2:
   D=match.denominator;groups={r:[i for i,x in enumerate(physical[axis]) if x%p==r] for r in {x%p for x in physical[axis]}};partial={r:np.sum(view[ids],axis=0) for r,ids in groups.items()};excess=int((match-4)*D)
   for i,x in enumerate(physical[axis]):out[i]=D*total+3*D*partial[x%p]+excess*view[i]
  else:
   diag=[(match-1)/F(p-9 if r==9 else 1) for r in roots[axis-2]];D=lcm(*(z.denominator for z in diag))
   for i,z in enumerate(diag):out[i]=D*total+int(z*D)*view[i]
  value=np.moveaxis(out,0,axis);scale*=D;times.append(time.perf_counter()-start)
 return value,scale,times

def independent_centre(p,ci,centre,exponents):
 l,m=p['cells'][ci];physical=(3*(l%3)+l//3,5*(m%5)+m//5);central=F(1)
 for i,(prime,x,a) in enumerate(zip(P[:2],physical,centre[:2])):
  d=(x-a)%(prime**2);r=0
  while r<2 and d%(prime**(r+1))==0:r+=1
  central*=F((r+1)**2) if r<2 else match_factor(prime,2,None if exponents is None else exponents[i])
 aa=[];bb=[]
 for i,(q,row,cats,a) in enumerate(zip(Q,p['counts'][ci],p['cats'],centre[2:])):
  excess=match_factor(q,1,None if exponents is None else exponents[2+i])-1;u=v=F(0)
  for k,(n,cat) in enumerate(zip(row,cats)):
   roots={x%q for x in cat};factor=1+excess*F(sum(r==a for r in roots),len(roots))
   if k<2:v+=n*factor
   else:u+=n*factor
  aa.append(u);bb.append(v)
 x=prod(aa)+sum(bb[i]*prod(aa[j] for j in range(5) if j!=i) for i in range(5));prefactor=(2-(l==4))*(4-(m==10))
 return central*prefactor*x

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent);ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('joined33_coherent_central_field_witness.json'));ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--metrics',type=Path);a=ap.parse_args();started=time.perf_counter();w=json.loads(a.witness.read_text());core,p,pins=prepare_source(a.base);ck(w['schema']=='actual109-central-coherent-haar-tail-field-v1','field witness schema');ck(w['source_sha256']==pins,'exact canonical source identities');ck(w['source_engine_sha256']==sha256((a.base/'clustered_full5_allfield_verify.py').read_bytes()).hexdigest(),'witness source engine identity');D=w['denominator'];nums=w['retention_numerators'];ck(type(D) is int and D>0 and len(nums)==80 and all(type(n) is int and 0<=n<=D for n in nums),'80 rational retention bounds');ck(w['central_cells']==[list(x) for x in p['cells']],'same original central cells');exponents=w['exponents'];ck(exponents==[6,6,2,2,2,2,2],'declared finite Q0 inventory');selectors=literal_selectors(p);c=1-core.G
 C=list(map(F,json.loads((a.base/'remaining33_global_root_exclusion_certificate.json').read_text())['combined512_coefficients']))
 for i,q in enumerate(Q):
  if i:C[256+(1<<i)]+=core.G/F(q*(q-2))
 W=[]
 for j in range(512):
  mode,T=divmod(j,32);ex,ey=divmod(mode,4);v=(F(1),F(3),F(5),F(8,9))[ex]*(F(1),F(3),F(5),F(1,8))[ey]
  for i,q in enumerate(Q):
   if T>>i&1:v*=F(3,q-1)+F(5*q-3,(q-2)*(q-1)**2)
  W.append(v if j else F(0))
 A=[x-c*y for x,y in zip(C,W)];ck(min(A)>=0 and sum(x>0 for x in A)==499,'all original loss and fullmode8 fees retained')
 support=np.zeros(p['token_shape'],dtype=np.uint8)
 for axis,n in enumerate(p['token_shape']):
  sh=[1]*5;sh[axis]=n;support|=((np.arange(n)>0)*(1<<axis)).astype(np.uint8).reshape(sh)
 columns=[np.flatnonzero(support.ravel()==T) for T in range(32)];ck(sum(map(len,columns))==117128,'all outside query tuples')
 query=np.zeros((80,117128),dtype=object);shape=(5,19,6,9,9,9,9);centre=np.zeros(shape,dtype=object);ck(prod(shape)==3739770,'full compact cartesian centre domain');source_num=0;original_num=0;states=0;live=0;li={x:i for i,x in enumerate(LS)};mi={x:i for i,x in enumerate(MS)};percell=[]
 tick=time.perf_counter()
 for ci,(l,m) in enumerate(p['cells']):
  ww=source_weights(p,ci);original_num+=int(ww.sum());states+=int(np.count_nonzero(ww));live+=bool(np.any(ww));integer=ww.astype(object)*nums[ci];source_num+=int(integer.sum());t=time.perf_counter();query[ci]=forward_integer(integer,p['matrices']).ravel();percell.append(time.perf_counter()-t);centre[li[l],mi[m]]=collapse(integer)
  for col in (0,117127,(ci*1319)%117128):ck(query[ci,col]==nums[ci]*independent_row_numerator(p,ci,col),'independent source/query contraction')

 query_build=time.perf_counter()-tick;ck(states==2125830 and live==79 and F(original_num,p['M0'])==F(305684996597,646498195200),'all actual source categories and exact source mass');ck(int(centre.sum())==source_num,'collapse preserves full joint mass');print(json.dumps({'stage':'source_query_integer_transform','seconds':query_build,'max_cell_seconds':max(percell),'source_states':states}),flush=True)
 Dc=82*469;maxima=[0]*512;winners=[None]*512;raw=0;nonzero=0;tick=time.perf_counter()
 for sid,(mode,left,right,ids,mult) in enumerate(selectors):
  k=mult*Dc;ck(k.denominator==1,'exact selector normalization');scores=np.sum(query[ids],axis=0)*int(k) if ids else np.zeros(117128,dtype=object)
  for T,cols in enumerate(columns):
   gid=32*mode+T
   if not A[gid]:continue
   values=scores[cols];raw+=len(cols);nonzero+=int(np.count_nonzero(values));ix=int(np.argmax(values));value=int(values[ix])
   if winners[gid] is None or value>maxima[gid]:maxima[gid]=value;winners[gid]=(sid,int(cols[ix]))
 query_max_seconds=time.perf_counter()-tick;ck(raw==65474442,'every current positive-fee literal query row visited');den=p['M0']*D*5*Dc;fee=sum((A[j]*F(maxima[j],den) for j in range(512)),F(0))
 for j,win in enumerate(winners):
  if win is None:continue
  sid,col=win;_,_,_,ids,mult=selectors[sid];independent=sum(nums[ci]*independent_row_numerator(p,ci,col) for ci in ids)*mult*Dc;ck(independent==maxima[j],'every winning query independently contracted')
 del query
 print(json.dumps({'stage':'complete_query_maxima','seconds':query_max_seconds,'raw_rows':raw,'positive_values':nonzero,'fee_decimal':float(fee)}),flush=True)
 tick=time.perf_counter();centres,scale,axis_times=centre_integer_transform(centre,exponents);idx=tuple(map(int,np.unravel_index(int(np.argmax(centres)),shape)));top=int(centres[idx]);centre_max=F(top-source_num*scale,p['M0']*D*scale);mass=F(source_num,p['M0']*D);rootlabels=[tuple(range(1,min(q,9)))+((9,) if q>9 else ()) for q in Q];physical=[3*(LS[idx[0]]%3)+LS[idx[0]]//3,5*(MS[idx[1]]%5)+MS[idx[1]]//5]+[rootlabels[i][idx[2+i]] for i in range(5)]
 controls=[(0,0,0,0,0,0,0),idx,(4,18,0,0,0,0,0),(2,7,5,8,8,8,8)]
 for ciidx in controls:
  aa=[3*(LS[ciidx[0]]%3)+LS[ciidx[0]]//3,5*(MS[ciidx[1]]%5)+MS[ciidx[1]]//5]+[rootlabels[i][ciidx[2+i]] for i in range(5)];check=sum((nums[ci]*independent_centre(p,ci,aa,exponents) for ci in range(80)),F(0));ck(check*scale==int(centres[ciidx]),'independent complete centre contraction including multiple root1')
 result=core.G*mass-fee-c*centre_max;target=F(193,100000);ck(result>target,'exact relaxed central field exceeds continuation target');out={'status':'PASS','exact':True,'scope':'The rational central-only field exceeds target after all499 loss-screen maxima and the exact maximum over every shallow centre prefix with independently Haar deeper centre digits. This refutes target-excluding duals restricted to this centre family at the declared inventory. It is not a positive full independent-layout Gamma gate and not a general covering conclusion.','inventory':w['inventory'],'exponents':exponents,'shallow_depths':[2,2,1,1,1,1,1],'mass':str(mass),'query_fee':str(fee),'centre_maximum':str(centre_max),'centre_fee':str(c*centre_max),'relaxed_gate':str(result),'relaxed_gate_decimal':float(result),'target':str(target),'margin':str(result-target),'margin_decimal':float(result-target),'query_groups':499,'raw_query_rows':raw,'nonzero_query_values':nonzero,'centre_prefixes':prod(shape),'multi_root1_centre_prefixes':432250,'centre_maximizer':physical,'source_states':states,'live_central_cells':live,'query_maxima':list(map(str,[F(v,den) for v in maxima])),'query_winners':winners,'loss_coefficients':list(map(str,A)),'source_sha256':pins,'witness_sha256':sha256(a.witness.read_bytes()).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'canonical_source_engine_sha256':sha256((a.base/'clustered_full5_allfield_verify.py').read_bytes()).hexdigest(),'checks':CHECKS+core.CHECKS};
 if a.metrics:
  peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
  a.metrics.write_text(json.dumps({'query_transform_seconds':query_build,'query_max_seconds':query_max_seconds,'centre_axis_seconds':axis_times,'centre_total_seconds':time.perf_counter()-tick,'total_seconds':time.perf_counter()-started,'peak_rss_bytes':peak if platform.system()=='Darwin' else 1024*peak},indent=2)+'\n')
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('query_maxima','query_winners','loss_coefficients')},indent=2),flush=True)
if __name__=='__main__':main()
