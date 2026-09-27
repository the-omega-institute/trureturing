#!/usr/bin/env python3
"""Fixed Report706 field: exact maximum over every common centre at Q0.
Only the pinned canonical source engine is imported. No optimizer or new field.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod,lcm
from hashlib import sha256
import importlib.util,argparse,json,time,resource,platform
import numpy as np


_DEFAULT_INPUT_PATHS = {'clustered_full5_allfield_verify.py': '../clustered_full5_allfield_verify.py', 'clustered_global_phase_fixture.json': '../clustered_global_phase_fixture.json', 'clustered_higher_pure_capacity_obstruction.json': '../clustered_higher_pure_capacity_obstruction.json', 'remaining33_global_root_exclusion_certificate.json': '../remaining33_global_root_exclusion_certificate.json'}

def _resolve_input_path(directory, name):
    if directory is not None:
        return directory / name
    return Path(__file__).resolve().parent / _DEFAULT_INPUT_PATHS.get(name, name)
P=(3,5,7,11,13,17,19);Q=P[2:];LS=(0,1,2,4,5);MS=tuple(m for m in range(20) if m!=5)
CHECKS=0
def ck(x,label):
 global CHECKS
 CHECKS+=1
 if not x: raise ArithmeticError(label)
def prepare(base,w):
 path=_resolve_input_path(base, 'clustered_full5_allfield_verify.py')
 ck(sha256(path.read_bytes()).hexdigest()==w['source_engine_sha256']=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56','source engine pin')
 sp=importlib.util.spec_from_file_location('canonical_exact_source',path);core=importlib.util.module_from_spec(sp);sp.loader.exec_module(core)
 class Empty:
  def read_text(self):return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':w['source_sha256'],'denominator':1,'rows':[],'expected':{}})
 p=core.prepare(path.parent,Empty(),1)
 ck(w['central_cells']==[list(x) for x in p['cells']],'same central cells')
 for ci in range(80):
  for qi in range(5):
   for n,cat in zip(p['counts'][ci][qi],p['cats'][qi]):ck(n in (0,len(cat)),'full-or-empty source category')
 return core,p

def weights(p,ci):
 l,m=p['cells'][ci];shape=p['category_shape'];a=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64);root1=np.zeros(shape,dtype=np.uint8)
 for axis,row in enumerate(p['counts'][ci]):
  dims=[1]*5;dims[axis]=len(row);a*=np.array(row,dtype=np.int64).reshape(dims);root1+=(np.arange(len(row))<2).reshape(dims)
 return a*(root1<=1)

CENTRAL={};CENTRAL_REPS={};CENTRAL_LOCAL={};CENTRAL_SUPPORT={}
def central_match(q,leaf):return CENTRAL[q][leaf]
def prepare_central(base):
 originals=json.loads((_resolve_input_path(base, 'clustered_global_phase_fixture.json')).read_text())['actual_originals']+json.loads((_resolve_input_path(base, 'clustered_higher_pure_capacity_obstruction.json')).read_text())['first_tested_success']['added_higher_pure_originals']
 ck(len(originals)==len({v['modulus'] for v in originals})==109,'same109 distinct original labels')
 for q,indexed,weak,want,branch in ((3,LS,4,F(685,41),22),(5,MS,2,F(5389,469),52)):
  physical=[q*(i%q)+i//q for i in indexed];pure=[]
  for v in originals:
   d=v['modulus'];h=0
   while d%q==0:d//=q;h+=1
   ck(d==1 or h<=2,'mixed original central valuation at most2')
   if d==1:pure.append((v['modulus'],v['residue']))
  raw=[];maxima={};reps={};populations={};survivors={};aall=np.arange(q**6,dtype='int64')
  for leaf in physical:
   surviving=[x for x in range(leaf,q**6,q*q) if all(x%d!=b for d,b in pure)]
   survivors[leaf]=surviving;N=len(surviving);populations[leaf]=N;ck(N==(41 if q==3 else 469) if leaf==weak else N==q**4,'actual pure surviving child population')
   numer=np.full(q**6,N,dtype='int64')
   for h in range(1,7):
    counts=np.bincount(np.array(surviving,dtype='int64')%(q**h),minlength=q**h)
    numer+=(2*h+1)*counts[aall%(q**h)]
   ck(all(int(numer[a])==N*(4 if (a-leaf)%q==0 else 1) for a in range(q**6) if a%(q*q)!=leaf),'nonmatching leaf only shallow dependent')
   ids=np.arange(leaf,q**6,q*q);rep=int(ids[np.argmax(numer[ids])]);value=F(int(numer[rep]),N)
   upper=F(9)+sum((F((2*h+1)*q**(6-h),N) for h in range(3,7)),F(0))
   ck(value==upper,'all level population upper bounds simultaneously attained')
   ck(value==(want if leaf==weak else F(9)+sum((F(5+2*j,q**j) for j in range(1,5)),F(0))),'exact local maximum formula')
   if leaf==weak:ck(all(x in surviving for x in range(branch,q**6,q**3)),'intact weak depth3 subtree')
   raw.append(numer);maxima[leaf]=value;reps[leaf]=rep
  def shallow_representative(a):
   leaf=a%(q*q)
   if leaf in reps:return leaf
   if leaf==1:return 4 if q==3 else 6
   ck(leaf%q==q-1,'only missing pure-root leaves remain')
   return 0
  amap=np.array([reps[shallow_representative(a)] for a in range(q**6)],dtype='int64')
  for numer in raw:ck(bool(np.all(numer<=numer[amap])),'every literal central centre row dominated by its representative')
  CENTRAL[q]=maxima;CENTRAL_REPS[q]=reps;CENTRAL_SUPPORT[q]=survivors;CENTRAL_LOCAL[q]={'source_leaves':physical,'surviving_populations':populations,'maxima':{str(k):str(v) for k,v in maxima.items()},'deep_representatives':reps,'literal_centre_residues_checked':q**6}

def labels(q):return (1,1+q)+tuple(range(2,min(q,9)))+((9,) if q>9 else ())
def local_factor(q,source,centre):
 if (source-centre)%q: return 1
 return 9 if (source-centre)%(q*q)==0 else 4

def outside_matrix(q,cats):
 reps=labels(q);mat=[]
 for a in reps:mat.append([sum((F(local_factor(q,x,a)) for x in cat),F(0))/len(cat) for cat in cats])
 # Independent closed form, including one representative of a free-root orbit.
 for i,row in enumerate(mat):
  for k,z in enumerate(row):
   want=F(1)
   if i<2 and k<2:want=F(9) if i==k==0 else F(4)+ (F(5,q-1) if i==k==1 else 0)
   elif i==k:want=1+F(3*q+5,q*(q-9 if i==len(cats)-1 and q>9 else 1))
   ck(z==want,'literal child enumeration equals closed matrix')
 # Every q^2 centre is dominated by or has the same vector as a representative.
 for a in range(q*q):
  row=[sum((F(local_factor(q,x,a)) for x in cat),F(0))/len(cat) for cat in cats]
  ck(any(all(x<=y for x,y in zip(row,rr)) for rr in mat),'all actual centre residues dominated by declared representative')
 return mat

def transform_outside(value,matrices):
 scale=1;times=[]
 for local,q in enumerate(Q):
  axis=value.ndim-5+local;tick=time.perf_counter();view=np.moveaxis(value,axis,0);total=np.sum(view,axis=0);mat=matrices[local];den=lcm(*(x.denominator for row in mat for x in row));out=np.empty_like(view)
  for i,row in enumerate(mat):
   out[i]=den*total
   for k,z in enumerate(row):
    coeff=int((z-1)*den)
    if coeff:out[i]+=coeff*view[k]
  value=np.moveaxis(out,0,axis);scale*=den;times.append(time.perf_counter()-tick)
 return value,scale,times

def transform_central(value):
 scale=1;times=[];physical=([3*(l%3)+l//3 for l in LS],[5*(m%5)+m//5 for m in MS])
 for axis,q in enumerate(P[:2]):
  tick=time.perf_counter();view=np.moveaxis(value,axis,0);total=np.sum(view,axis=0);out=np.empty_like(view);den=lcm(*(central_match(q,x).denominator for x in physical[axis]));groups={r:[i for i,x in enumerate(physical[axis]) if x%q==r] for r in {x%q for x in physical[axis]}};partial={r:np.sum(view[ids],axis=0) for r,ids in groups.items()}
  for i,x in enumerate(physical[axis]):out[i]=den*total+3*den*partial[x%q]+int((central_match(q,x)-4)*den)*view[i]
  value=np.moveaxis(out,0,axis);scale*=den;times.append(time.perf_counter()-tick)
 return value,scale,times

def independent_centre(p,nums,centre):
 total=F(0)
 for ci,(l,m) in enumerate(p['cells']):
  central=F(1)
  for q,x,a in zip(P[:2],(3*(l%3)+l//3,5*(m%5)+m//5),centre[:2]):
   aa=CENTRAL_REPS[q][a];v=0
   for xx in CENTRAL_SUPPORT[q][x]:
    depth=0
    while depth<6 and (xx-aa)%(q**(depth+1))==0:depth+=1
    v+=(depth+1)**2
   central*=F(v,len(CENTRAL_SUPPORT[q][x]))
  U=[];V=[]
  for q,counts,cats,a in zip(Q,p['counts'][ci],p['cats'],centre[2:]):
   vals=[F(n)*sum((F(local_factor(q,x,a)) for x in cat),F(0))/len(cat) for n,cat in zip(counts,cats)]
   V.append(sum(vals[:2],F(0)));U.append(sum(vals[2:],F(0)))
  total+=nums[ci]*(2-(l==4))*(4-(m==10))*central*(prod(U)+sum((V[i]*prod(U[j] for j in range(5) if j!=i) for i in range(5)),F(0)))
 return total

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,default=None);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--metrics',type=Path);a=ap.parse_args();start=time.perf_counter();wp=_resolve_input_path(a.base, 'joined33_coherent_central_field_witness.json');w=json.loads(wp.read_text());oldp=_resolve_input_path(a.base, 'joined33_coherent_central_field_verify.json');old=json.loads(oldp.read_text());ck(sha256(oldp.read_bytes()).hexdigest()=='b3f65df4353ef6251f986b3f32fad7a4c053d8654829745f1d15f29dd92f8897','audited complete-loss result pin');ck(old['program_sha256']==sha256((_resolve_input_path(a.base, 'joined33_coherent_central_field_verify.py')).read_bytes()).hexdigest()=='f30e60ae5fa31ca7b2b463ff640b2b955a20cbb2ce444435792effa3b38ced73','audited complete-loss verifier pin');ck(old['status']=='PASS' and old['exact'],'reused finite certificate');ck(old['witness_sha256']==sha256(wp.read_bytes()).hexdigest(),'reused finite result same field');ck(w['exponents']==[6,6,2,2,2,2,2],'fixed E0');D=w['denominator'];nums=w['retention_numerators'];ck(type(D) is int and D>0 and len(nums)==80 and all(type(n) is int and 0<=n<=D for n in nums),'rational field');core,p=prepare(a.base,w);prepare_central(a.base);matrices=[outside_matrix(q,cats) for q,cats in zip(Q,p['cats'])];shape=(5,19,*p['category_shape']);ck(shape==(5,19,7,10,10,10,10),'expanded complete centre shape')

 tensor=np.zeros(shape,dtype=object);li={x:i for i,x in enumerate(LS)};mi={x:i for i,x in enumerate(MS)};source_num=original_num=states=live=0;tick=time.perf_counter()
 for ci,(l,m) in enumerate(p['cells']):
  ww=weights(p,ci);original_num+=int(ww.sum());states+=int(np.count_nonzero(ww));live+=bool(np.any(ww));v=ww.astype(object)*nums[ci];tensor[li[l],mi[m]]=v;source_num+=int(v.sum())
 ck(states==2125830 and live==79,'same actual source support');ck(F(original_num,p['M0'])==F(305684996597,646498195200),'source mass');mass=F(source_num,p['M0']*D);ck(mass==F(old['mass']),'fixed retained mass');buildsecs=time.perf_counter()-tick
 print(json.dumps({'stage':'source-built','entries':prod(shape),'seconds':buildsecs}),flush=True)
 centres,oscale,otimes=transform_outside(tensor,matrices);del tensor;centres,cscale,ctimes=transform_central(centres);scale=oscale*cscale;idx=tuple(map(int,np.unravel_index(int(np.argmax(centres)),shape)));top=int(centres[idx]);cm=F(top-source_num*scale,p['M0']*D*scale)
 phys=lambda ix:[3*(LS[ix[0]]%3)+LS[ix[0]]//3,5*(MS[ix[1]]%5)+MS[ix[1]]//5]+[labels(q)[ix[i+2]] for i,q in enumerate(Q)]
 controls=[idx,(0,0,0,0,0,0,0),(4,18,1,1,1,1,1),(2,7,6,9,9,9,9),(3,9,1,0,1,0,1)]
 for ix in controls:ck(independent_centre(p,nums,phys(ix))*scale==int(centres[ix]),'independent whole-centre contraction')
 c=1-core.G;fee=F(old['query_fee']);oldcm=F(old['centre_maximum']);target=F(193,100000);oldgate=F(old['relaxed_gate']);ck(core.G*mass-fee-c*oldcm==oldgate,'reused exact fee/gate arithmetic');gate=core.G*mass-fee-c*cm;gain=cm-oldcm;ck(gain>=0,'complete common-centre family contains old Haar family by averaging');margin=oldgate-target;threshold=margin/c;ck(oldgate-gate==c*gain,'exact charge difference')
 peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
 out={'status':'PASS','exact':True,'scope':'Fixed Report706 rational central-only field and unchanged actual109 source, with all unchanged loss-screen maxima. Exact complete maximum over every common centre moduloQ0: all central depth6 and exterior depth2 residues are dominated by or equal to the retained representatives. This is not the arbitrary independent-label Gamma maximum and not an all-field result.','decision':'complete coherent gate at or below target' if gate<=target else 'complete coherent gate above target','source_states':states,'live_central_cells':live,'source_cells':80,'independent_literal_centre_controls':[[CENTRAL_REPS[3][phys(ix)[0]],CENTRAL_REPS[5][phys(ix)[1]],*phys(ix)[2:]] for ix in controls],'centre_shape':shape,'centre_count':prod(shape),'central_local':CENTRAL_LOCAL,'centre_maximizer_shallow':phys(idx),'centre_maximizer':[CENTRAL_REPS[3][phys(idx)[0]],CENTRAL_REPS[5][phys(idx)[1]],*phys(idx)[2:]],'centre_maximizer_index':idx,'mass':str(mass),'query_fee':str(fee),'old_centre_maximum':str(oldcm),'new_centre_maximum':str(cm),'charge_gain':str(gain),'charge_gain_decimal':float(gain),'required_charge_gain':str(threshold),'required_charge_gain_decimal':float(threshold),'old_relaxed_gate':str(oldgate),'new_relaxed_gate':str(gate),'new_relaxed_gate_decimal':float(gate),'target':str(target),'below_target':gate<=target,'target_margin':str(target-gate),'source_engine_sha256':w['source_engine_sha256'],'source_sha256':w['source_sha256'],'field_witness_sha256':sha256(wp.read_bytes()).hexdigest(),'reused_finite_result_sha256':sha256(oldp.read_bytes()).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'checks':CHECKS+core.CHECKS,'outside_matrices':[[[str(x) for x in row] for row in mat] for mat in matrices]}
 if a.metrics:a.metrics.write_text(json.dumps({'source_seconds':buildsecs,'outside_axis_seconds':otimes,'central_axis_seconds':ctimes,'total_seconds':time.perf_counter()-start,'peak_rss_bytes':peak if platform.system()=='Darwin' else peak*1024},indent=2)+'\n')
 a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='outside_matrices'},indent=2),flush=True)
if __name__=='__main__':main()
