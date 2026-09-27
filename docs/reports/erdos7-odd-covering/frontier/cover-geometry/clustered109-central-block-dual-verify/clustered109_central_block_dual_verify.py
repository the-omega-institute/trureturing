#!/usr/bin/env python3
"""Optimizer-free exact dual check for the changed full central eight-label gate.

The full independent-layout maximum is bounded below by the supplied probability
mixture of complete centered layouts. This is not an equality reduction.
Every remaining old fee budget and every actual source state is checked.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
import argparse,importlib.util,json,time
import numpy as np
CHECKS=0

def ck(x,label):
 global CHECKS
 CHECKS+=1
 if not x:raise ArithmeticError(label)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
 ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('clustered109_central_block_fraction_witness.json'))
 ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 ap.add_argument('--metrics',type=Path)
 a=ap.parse_args();start=time.perf_counter()
 helper=a.base/'clustered_full5_allfield_verify.py'
 ck(sha256(helper.read_bytes()).hexdigest()=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56','pinned exact engine')
 spec=importlib.util.spec_from_file_location('exact_source',helper);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 w=json.loads(a.witness.read_text())
 ck(w['schema']=='clustered109-eight-central-block-dual-v1','new witness schema')
 D=w['denominator'];c=F(w['block_budget']);target=F(w['target'])
 ck(c==1-v.G==F(1084133,201247200),'fixed head budget')
 ck(target==F(193,100000),'same target')
 labels=(3,5,9,15,25,45,75,225)
 ck(tuple(w['central_labels'])==labels,'whole eight-label block')
 changed=[32,64,128,160,192,256,288,320]
 ck(w['query_modified_groups']==changed,'exact query group removal')
 W=dict(zip(changed,map(F,[3,5,3,9,15,5,15,25])))
 ck(sum(W.values())==80,'unit-inclusive nine-label square minus unit')
 C=list(map(F,json.loads((a.base/'remaining33_global_root_exclusion_certificate.json').read_text())['combined512_coefficients']))
 for i,q in enumerate(v.Q):
  if i:C[256+(1<<i)]+=v.G/F(q*(q-2))
 remaining=C.copy()
 for j in changed:remaining[j]-=c*W[j]
 ck(all(x>=0 for x in remaining),'nonnegative remaining fees')
 ck([remaining[j] for j in changed]==[F(0),F(0),F(0),F(0),v.G,F(0),v.G,v.G],'loss on75,45,225 kept')
 ck(list(map(F,w['remaining_coefficients']))==remaining,'all512 budgets faithful')
 # Reuse the old interface validator and exact full transport with the new row
 # fractions. Its original fees are corrected below only on shallow columns.
 class InputRows:
  def read_text(self):
   return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':w['source_sha256'],'denominator':D,'rows':w['rows'],'expected':{}})
 p=v.prepare(a.base,InputRows(),D)
 ck(all(load==(D if remaining[j]>0 else 0) for j,load in enumerate(p['loads'])),'all506 positive old budgets full; all zero budgets empty')
 ck(type(w['block_denominator']) is int and w['block_denominator']>0,'positive new denominator')
 blockD=w['block_denominator'];seen=set()
 for b,num in w['centered_rows']:
  ck(type(b) is int and 0<=b<225 and type(num) is int and num>0,'legal centered complete layout')
  ck(b not in seen,'distinct centered row');seen.add(b)
 ck(sum(num for b,num in w['centered_rows'])==blockD,'new block mixture full budget')
 selectors=[]
 for mode in range(16):
  ex,ey=divmod(mode,4)
  xs=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[ex]
  ys=((0,),(0,1,2,3),tuple(m for m in range(20) if m!=5),tuple(m for m in range(20) if m!=5))[ey]
  selectors.extend((mode,l,m) for l,m in product(xs,ys))
 ck(len(selectors)==559,'selector order')
 correction=[F(0)]*len(p['cells'])
 for mode,T,sid,column,num in w['rows']:
  j=32*mode+T
  ck(remaining[j]>0,'no row hidden in zero-budget group')
  if j not in changed:continue
  ck(T==column==0 and selectors[sid][0]==mode,'pure shallow row')
  ex,ey=divmod(mode,4);_,x,y=selectors[sid]
  for ci,(l,m) in enumerate(p['cells']):
   if (ex==0 or (l//3==x if ex==1 else l==x)) and (ey==0 or (m//5==y if ey==1 else m==y)):
    correction[ci]+=c*W[j]*F(num,D)
 shape=p['category_shape'];rootcount=np.zeros(shape,dtype=np.uint8)
 for axis,size in enumerate(shape):
  dims=[1]*5;dims[axis]=size
  rootcount+=(np.arange(size)<2).astype(np.uint8).reshape(dims)
 good=rootcount<=1;M=v.G.denominator*p['debitDen']
 ck(8*prod(q*(q-1) for q in v.Q)<2**63 and p['M0']<2**63,'safe source integer bound')
 # The eleven branches are formed from literal residue classes.
 branch_masks=[rootcount==0]
 for axis,(q,cats) in enumerate(zip(v.Q,p['cats'])):
  sp=[all(z==1 for z in cat) for cat in cats]
  ot=[all(z%q==1 and z!=1 for z in cat) for cat in cats]
  dims=[1]*5;dims[axis]=len(cats)
  branch_masks.extend([np.broadcast_to(np.array(sp).reshape(dims),shape)&good,np.broadcast_to(np.array(ot).reshape(dims),shape)&good])
 partition=sum(x.astype(np.uint8) for x in branch_masks)
 ck(np.all(partition[good]==1) and np.all(partition[~good]==0),'eleven complete literal branches')
 branch_num=[0]*11;branch_positive=[0]*11;cellwise_num=[F(0)]*11
 states=source_num=positive_num=positive_states=0
 strides=[prod(p['token_shape'][k+1:]) for k in range(5)]
 cells=[]
 for ci,(l,m) in enumerate(p['cells']):
  masses=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64)
  for axis,row in enumerate(p['counts'][ci]):
   dims=[1]*5;dims[axis]=len(row);masses*=np.array(row,dtype=np.int64).reshape(dims)
  masses*=good;mask=masses>0
  if not np.any(mask):continue
  x=(100*(3*(l%3)+l//3)+126*(5*(m%5)+m//5))%225
  hnum=0
  for b,num in w['centered_rows']:
   n=sum((x-b)%d==0 for d in labels);ck(0<=n<=8,'indicator count')
   hnum+=num*(n*n+2*n)
  addback=M*correction[ci];new=M*c*F(hnum,blockD)
  ck(addback.denominator==new.denominator==1,'exact scaled correction')
  sparse=np.zeros(p['token_shape'],dtype=object)
  for column,value in p['scatter'][ci].items():sparse.flat[column]=value
  debit=v.transform(sparse,p['matrices'])[mask];weights=masses[mask]
  ck(all(type(q) is int and 0<=q<=p['debit_bound'] for q in debit),'exact debit all positive source states')
  ck(np.all(v.G.denominator*debit>=int(addback)),'nonnegative remaining old debit')
  ids=np.flatnonzero(mask);pos=len(ids)//2;rem=int(ids[pos]);cats=[]
  for size in reversed(shape):cats.append(rem%size);rem//=size
  cats.reverse();maps=[dict(p['matrices'][k][cats[k]]) for k in range(5)];direct=0
  for column,value in p['scatter'][ci].items():
   term=value
   for k in range(5):
    term*=maps[k].get((column//strides[k])%p['token_shape'][k],0)
    if not term:break
   direct+=term
  ck(debit[pos]==direct,'literal scalar contraction')
  residual=v.G.numerator*p['debitDen']-v.G.denominator*debit+int(addback)-int(new)
  positive=np.maximum(residual,0);cellnum=int(np.sum(positive*weights));count=len(debit)
  parts=[]
  gamma3=F(81,82) if l==4 else F(1);gamma5=F(1875,1876) if m==10 else F(1);Rc=1/(gamma3*gamma5)
  for j,bm in enumerate(branch_masks):
   selected=bm[mask];bn=int(np.sum((positive*weights)[selected]));parts.append(bn)
   branch_num[j]+=bn;cellwise_num[j]+=Rc*bn;branch_positive[j]+=int(np.count_nonzero(positive[selected]))
  ck(sum(parts)==cellnum,'every positive residual counted in one branch')
  positive_num+=cellnum;states+=count;source_num+=int(weights.sum());positive_states+=int(np.count_nonzero(positive))
  cells.append({'cell':[l,m],'actual_states':count,'source_numerator':int(weights.sum()),'positive_numerator':str(cellnum),'removed_query_debit':str(correction[ci]),'block_debit':str(c*F(hnum,blockD))})
 ck(states==2125830 and len(cells)==79,'complete source state pass')
 ck(F(source_num,p['M0'])==F(305684996597,646498195200),'same source total')
 upper=F(positive_num,M*p['M0']);R=F(153832,151875)
 total_den=M*p['M0'];coeff=[F(n,total_den) for n in branch_num];ccoeff=[n/total_den for n in cellwise_num]
 ck(sum(coeff,F(0))==upper,'unmodified reference equals branch sum')
 slopes=[coeff[1+2*i]-coeff[2+2*i]/(q-1) for i,q in enumerate(v.Q)]
 cslopes=[ccoeff[1+2*i]-ccoeff[2+2*i]/(q-1) for i,q in enumerate(v.Q)]
 corners=[]
 for bits in product((0,1),repeat=5):
  value=coeff[0];cvalue=ccoeff[0]
  for i,(q,bit) in enumerate(zip(v.Q,bits)):
   t=F(q*bit);other=(q-t)/(q-1);ck(t/q+(q-1)*other/q==1,'one shared root-balanced reference')
   value+=coeff[1+2*i]*t+coeff[2+2*i]*other;cvalue+=ccoeff[1+2*i]*t+ccoeff[2+2*i]*other
  corners.append({'bits':list(bits),'outside_upper':str(value),'cellwise_upper':str(cvalue)})
 outside=max(F(row['outside_upper']) for row in corners);cellwise=max(F(row['cellwise_upper']) for row in corners)
 ck(upper<=outside and cellwise<=R*outside,'reference envelope and cellwise domination')
 result={'status':'PASS','complete':True,'exact':True,'scope':'A feasible rational dual upper for the changed eight-label independent-layout gate, retaining all original loss charges. Centered rows are only a legal dual family. No optimum or primal conclusion. All-measurable/allheight scope requires the unchanged source averaging and category proof, which preserves the central mod225 block.','actual_states':states,'positive_residual_states':positive_states,'source_mass':str(F(source_num,p['M0'])),'upper':str(upper),'upper_decimal':float(upper),'target':str(target),'below_target':upper<target,'joint_central_factor':str(R),'lifted_upper':str(R*upper),'lifted_upper_decimal':float(R*upper),'lifted_below_target':R*upper<target,'margin':str(target-upper),'source_sha256':p['pins'],'witness_sha256':sha256(a.witness.read_bytes()).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'helper_sha256':sha256(helper.read_bytes()).hexdigest(),'denominator':D,'old_group_rows':len(w['rows']),'centered_layout_rows':len(w['centered_rows']),'remaining_fees':list(map(str,remaining)),'group_loads':p['loads'],'reused_checks':v.CHECKS,'new_checks':CHECKS,'checks':v.CHECKS+CHECKS,'branch_coefficients':list(map(str,coeff)),'branch_positive_states':branch_positive,'outside_slopes':list(map(str,slopes)),'outside_upper':str(outside),'outside_upper_decimal':float(outside),'outside_below_target':outside<target,'outside_uniform_lift':str(R*outside),'outside_uniform_lift_decimal':float(R*outside),'outside_uniform_lift_below_target':R*outside<target,'cellwise_coefficients':list(map(str,ccoeff)),'cellwise_slopes':list(map(str,cslopes)),'cellwise_upper':str(cellwise),'cellwise_upper_decimal':float(cellwise),'cellwise_below_target':cellwise<target,'fixed_outside_cellwise_upper':str(sum(ccoeff,F(0))),'outside_32_corners':corners,'per_cell':cells}
 a.output.write_text(json.dumps(result,indent=2)+'\n')
 if a.metrics:a.metrics.write_text(json.dumps({'seconds':time.perf_counter()-start,'rss_bytes':v.rss()},indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ('status','upper','upper_decimal','below_target','lifted_upper','lifted_below_target','checks','actual_states')},indent=2),flush=True)
if __name__=='__main__':main()
