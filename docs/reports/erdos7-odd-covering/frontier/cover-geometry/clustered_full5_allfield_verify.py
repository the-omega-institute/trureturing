#!/usr/bin/env python3
"""Exact full-five dual evaluation using per-cell native-Python-integer tensors.

NumPy object operations transport Python integers; no floating arithmetic enters
source masses, rational weights, budget checks, dual coefficients or upper bound.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from hashlib import sha256
import argparse,json,time,resource,platform
import numpy as np
Q=(7,11,13,17,19);G=F(200163067,201247200)
CHECKS=0
def ck(x):
 global CHECKS
 CHECKS+=1
 if not x:raise ValueError('check '+str(CHECKS))
def rss():
 n=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
 return n if platform.system()=='Darwin' else n*1024

def prepare(base,candidate,D):
 names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json')
 pins={n:sha256((base/n).read_bytes()).hexdigest() for n in names};js=[json.loads((base/n).read_text()) for n in names]
 ck(pins[names[0]]=='4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6');ck(pins[names[2]]=='36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4')
 orig=js[0]['actual_originals'];high=js[1]['first_tested_success'];added=high['added_higher_pure_originals']
 ck(len(orig+added)==len({o['modulus'] for o in orig+added})==109)
 ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)})
 for p,weak,w,ref,cap,gamma in ((3,4,F(1,9),F(2),F(41,729),F(81,82)),(5,2,F(1,25),F(4,3),F(469,15625),F(1875,1876))):
  pp=[(o['modulus'],o['residue']) for o in added if o['modulus']%p==0];depth=max(x[0] for x in pp)
  actual=F(sum(all(x%m!=r for m,r in pp) for x in range(weak,depth,p*p)),depth)
  ck(actual==cap and w/(ref*actual)==gamma and F(high['gamma'+str(p)])==gamma)
 local=[[] for q in Q]
 for o in orig:
  c=o['modulus'];b=o['residue'];qq=[]
  for i,q in enumerate(Q):
   if c%q==0:
    power=1
    while c%q==0:c//=q;power*=q
    qq.append((i,power))
  if len(qq)==1 and c>1:
   i,d=qq[0];local[i].append((c,b%c,d,b%d))
  if len(qq)==2:ck(all(b%Q[i]==1 for i,d in qq))
 for i,j in combinations(range(5),2):ck(any(o['modulus']==Q[i]*Q[j] and o['residue']==1 for o in orig))
 cells=[(l,m) for l in (0,1,2,4,5) for m in range(20) if m!=5 and not(l<3 and m<5)]
 cats=[]
 for q in Q:
  cat=[[1],[1+q*k for k in range(1,q)]]+[[r+q*k for k in range(q)] for r in range(2,min(q,9))]
  if q>9:cat.append([r+q*k for r in range(9,q) for k in range(q)])
  cats.append(cat)
 counts=[]
 for l,m in cells:
  c=(100*(3*(l%3)+l//3)+126*(5*(m%5)+m//5))%225;cc=[]
  for i,(q,cat) in enumerate(zip(Q,cats)):
   row=[]
   for atoms in cat:
    flags=[all(c%cm!=cr or z%qm!=qr for cm,cr,qm,qr in local[i]) for z in atoms]
    ck(all(flags) or not any(flags));row.append(len(atoms) if all(flags) else 0)
   cc.append(row)
  counts.append(cc)
 C=list(map(F,js[2]['combined512_coefficients']))
 for i,q in enumerate(Q):
  if i:C[256+(1<<i)]+=G/F(q*(q-2))
 ck(len(C)==512 and min(C)>=0)
 L=lcm(*(c.denominator for c in C));Dc=82*469;debitDen=5*D*L*Dc;M0=675*prod(q*(q-1) for q in Q)
 selectors=[]
 for mode in range(16):
  ex,ey=divmod(mode,4)
  xm=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[ex];ym=((0,),(0,1,2,3),tuple(m for m in range(20) if m!=5),tuple(m for m in range(20) if m!=5))[ey]
  for left,right in product(xm,ym):
   ids=[ci for ci,(l,m) in enumerate(cells) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))]
   mult=F(1)
   if ex==3:mult*=(F(81,82) if left==4 else F(1))/F(2-(left==4),9)
   if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else F(1))/F(4-(right==10),75)
   ck((mult*Dc).denominator==1 and 0<mult<=180);selectors.append((mode,left,right,ids,int(mult*Dc)))
 ck(len(selectors)==559)
 cj=json.loads(candidate.read_text());ck(cj['schema']=='clustered109-full5-rational-dual-v1')
 for name,digest in pins.items():ck(cj['source_sha256'][name]==digest)
 ck(cj['denominator']==D and D>0)
 token_shape=(8,11,11,11,11);N=prod(token_shape);scatter=[{} for c in cells];logical_rows=0;loads=[0]*512;seen=set()
 for mode,T,sid,column,Nw in cj['rows']:
  ck(all(type(x) is int for x in (mode,T,sid,column,Nw)))
  ck(0<=mode<16 and 0<=T<32 and 0<=sid<len(selectors) and 0<=column<N and Nw>0)
  key=(mode,T,sid,column);ck(key not in seen);seen.add(key)
  smode,left,right,ids,mult=selectors[sid];ck(smode==mode)
  coords=[];remainder=column
  for d in reversed(token_shape):coords.append(remainder%d);remainder//=d
  coords.reverse();ck(sum(1<<i for i,x in enumerate(coords) if x)==T);ck(bool(ids))
  loads[32*mode+T]+=Nw;coef=int(C[32*mode+T]*L)*Nw*mult
  for ci in ids:scatter[ci][column]=scatter[ci].get(column,0)+coef
  logical_rows+=1
 for n in loads:ck(0<=n<=D)
 matrices=[]
 for q,cat in zip(Q,cats):
  scale=5 if q==19 else 1;rows=[]
  for k in range(len(cat)):
   row=[(0,scale)]
   if k<2:row.append((1,scale*(q-1)))
   elif q!=7 and k==9:row.append((9,int(F(scale*(q-1),q-9))))
   else:row.append((k,scale*(q-1)))
   if k==0:row.append((len(cat),scale*q*(q-2)))
   rows.append(row)
  matrices.append(rows)
 Kmax=prod(q*(q-2) for q in Q);debit_bound=debitDen*sum(C,F(0))*180*Kmax
 ck(debit_bound.denominator==1);debit_bound=int(debit_bound)
 ck(debit_bound.bit_length()<=191 and (G.denominator*debit_bound).bit_length()<=219)
 result=dict(pins=pins,cells=cells,counts=counts,cats=cats,scatter=scatter,matrices=matrices,token_shape=token_shape,category_shape=tuple(map(len,cats)),D=D,L=L,Dc=Dc,debitDen=debitDen,M0=M0,debit_bound=debit_bound,loads=loads,logical_rows=logical_rows,expected=cj['expected'])
 return result

def transform(tensor,matrices):
 dims=list(tensor.shape);value=tensor
 for axis,rows in enumerate(matrices):
  outer=prod(dims[:axis]);inner=prod(dims[axis+1:]);view=value.reshape(outer,dims[axis],inner)
  out=np.empty((outer,len(rows),inner),dtype=object)
  for k,terms in enumerate(rows):
   token,coef=terms[0];v=view[:,token,:] if coef==1 else view[:,token,:]*coef
   for token,coef in terms[1:]:v=v+view[:,token,:]*coef
   out[:,k,:]=v
  dims[axis]=len(rows);value=out.reshape(dims)
 return value

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('clustered_full5_allfield_dual.json'));ap.add_argument('--cells',type=int,default=0);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--metrics',type=Path);a=ap.parse_args();t0=time.perf_counter();witness=json.loads(a.witness.read_text());D=witness['denominator'];p=prepare(a.base,a.witness,D);tprep=time.perf_counter()-t0
 ck(8*prod(q*(q-1) for q in Q)<2**63);ck(p['M0']<2**63)
 shape=p['category_shape'];rootcount=np.zeros(shape,dtype=np.uint8)
 for axis,size in enumerate(shape):
  sh=[1]*5;sh[axis]=size;rootcount+=(np.arange(size)<2).astype(np.uint8).reshape(sh)
 pairgood=rootcount<=1;source_num=0;sum_positive=0;actual_count=0;reports=[];selected=[]
 for ci,(l,m) in enumerate(p['cells']):
  base_num=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64)
  for axis,row in enumerate(p['counts'][ci]):
   sh=[1]*5;sh[axis]=len(row);base_num*=np.array(row,dtype=np.int64).reshape(sh)
  base_num*=pairgood
  if not np.any(base_num):continue
  selected.append(ci)
  if a.cells and len(selected)>a.cells:break
  tic=time.perf_counter();sparse=np.zeros(p['token_shape'],dtype=object);flat=sparse.reshape(-1)
  for column,val in p['scatter'][ci].items():flat[column]=val
  debit=transform(sparse,p['matrices']);mask=base_num>0;d=debit[mask];b=base_num[mask]
  # All object scalars in d are builtin arbitrary-precision int.
  ck(all(type(x) is int and 0<=x<=p['debit_bound'] for x in d))
  # Independent scalar contraction of selected output coordinates against the literal sparse input.
  flat_ids=np.flatnonzero(mask);strides=[prod(p['token_shape'][k+1:]) for k in range(5)]
  for pos in sorted({0,len(flat_ids)//2,len(flat_ids)-1}):
   oid=int(flat_ids[pos]);cats=[];rem=oid
   for size in reversed(shape):cats.append(rem%size);rem//=size
   cats.reverse();maps=[dict(p['matrices'][k][cats[k]]) for k in range(5)];direct=0
   for column,coef in p['scatter'][ci].items():
    term=coef
    for k in range(5):
     term*=maps[k].get((column//strides[k])%p['token_shape'][k],0)
     if not term:break
    direct+=term
   ck(d[pos]==direct)
  scaled=G.numerator*p['debitDen']-G.denominator*d
  positive=np.maximum(scaled,0);weighted=positive*b;ck(all(type(x) is int for x in weighted));total=int(np.sum(weighted));src=int(np.sum(b));count=len(d)
  source_num+=src;sum_positive+=total;actual_count+=count
  reports.append(dict(cell=[l,m],index=ci,seconds=time.perf_counter()-tic,source_num=src,actual_states=count,positive_numerator=str(total),max_debit_bits=max(x.bit_length() for x in d),positive_states=int(np.count_nonzero(positive))))
  print(json.dumps(reports[-1]),flush=True)
 upper=F(sum_positive,p['M0']*G.denominator*p['debitDen'])
 result=dict(status='PASS',exact=True,scope='Exact fixed109 full-five/allheight512 fullmode8 dual. Base and joint-central-cap-lifted uppers are below193/100000. No exactzero optimum, arbitraryoutside-source or unrestrictedcovering claim. Partial benchmark unless complete.',complete=(a.cells==0 or a.cells>=79),source_sha256=p['pins'],witness_sha256=sha256(a.witness.read_bytes()).hexdigest(),program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),numpy_version=np.__version__,grid_denominator=D,dual_rows=p['logical_rows'],group_numerator_sums=p['loads'],fee_lcm=str(p['L']),fee_lcm_bits=p['L'].bit_length(),central_denominator=p['Dc'],debit_denominator=str(p['debitDen']),debit_denominator_bits=p['debitDen'].bit_length(),proven_debit_bound=str(p['debit_bound']),proven_debit_bound_bits=p['debit_bound'].bit_length(),source_denominator=p['M0'],partial_source_num=source_num,actual_states=actual_count,upper=str(upper),upper_decimal=float(upper),checks=CHECKS,per_cell=[{k:v for k,v in r.items() if k!='seconds'} for r in reports])
 if result['complete']:
  ck(actual_count==2125830);ck(F(source_num,p['M0'])==F(305684996597,646498195200));ck(source_num<=p['M0']);ck(sum_positive<=p['M0']*G.numerator*p['debitDen']);ck(upper==F(p['expected']['upper']));ck(F(0)<=upper<F(p['expected']['target'])==F(193,100000));R=F(1)/(F(81,82)*F(1875,1876));ck(R==F(p['expected']['domination_factor'])==F(153832,151875));lifted=R*upper;ck(lifted==F(p['expected']['lifted_upper']) and lifted<F(193,100000));result['joint_central_density_cap']='8/3';result['domination_factor']=str(R);result['lifted_upper']=str(lifted);result['lifted_margin']=str(F(193,100000)-lifted);result['checks']=CHECKS
 if a.metrics:
  metrics=dict(program_sha256=result['program_sha256'],witness_sha256=result['witness_sha256'],complete=result['complete'],preparation_seconds=tprep,total_seconds=time.perf_counter()-t0,peak_rss_bytes=rss(),numpy_version=np.__version__,cell_seconds=[r['seconds'] for r in reports])
  a.metrics.write_text(json.dumps(metrics,indent=2)+'\n')
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('per_cell','group_numerator_sums','source_sha256')},indent=2),flush=True)
if __name__=='__main__':main()
