#!/usr/bin/env python3
"""Exact residual-only star cuts for the fixed Report706 measure.

Only the canonical exact source engine is imported. All certificate decisions
use rational or integer arithmetic. Existing screen maxima are reused only
under fixed result/program/witness pins; the thirteen missing zero-loss
screens are reconstructed directly. No optimization is performed.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import prod
from hashlib import sha256
import importlib.util,argparse,json,time
import numpy as np


_DEFAULT_INPUT_PATHS = {'clustered_full5_allfield_verify.py': '../clustered_full5_allfield_verify.py', 'clustered_global_phase_fixture.json': '../clustered_global_phase_fixture.json', 'clustered_higher_pure_capacity_obstruction.json': '../clustered_higher_pure_capacity_obstruction.json', 'remaining33_global_root_exclusion_certificate.json': '../remaining33_global_root_exclusion_certificate.json'}

def _resolve_input_path(directory, name):
    if directory is not None:
        return directory / name
    return Path(__file__).resolve().parent / _DEFAULT_INPUT_PATHS.get(name, name)
P=(3,5,7,11,13,17,19);Q=P[2:];LS=(0,1,2,4,5);MS=tuple(m for m in range(20) if m!=5)
LABELS=tuple(sorted({3,5,9,15,25,45,75,225}|set(Q)|{p*q for p,q in combinations(P,2) if (p,q)!=(3,5)}))
CHECKS=0

def ck(value,label):
 global CHECKS
 CHECKS+=1
 if not value:raise ArithmeticError(label)

def prepare(base):
 wp=_resolve_input_path(base, 'joined33_coherent_central_field_witness.json');rp=_resolve_input_path(base, 'joined33_coherent_central_field_verify.json');vp=_resolve_input_path(base, 'joined33_coherent_central_field_verify.py');ep=_resolve_input_path(base, 'clustered_full5_allfield_verify.py')
 ck(sha256(wp.read_bytes()).hexdigest()=='ccdf8b7bb7fd25bb8e111143cbb3905dec451ddf5a533b350d0706dd053bdf2a','fixed rational field witness pin')
 ck(sha256(rp.read_bytes()).hexdigest()=='b3f65df4353ef6251f986b3f32fad7a4c053d8654829745f1d15f29dd92f8897','complete-loss result pin')
 ck(sha256(vp.read_bytes()).hexdigest()=='f30e60ae5fa31ca7b2b463ff640b2b955a20cbb2ce444435792effa3b38ced73','complete-loss program pin')
 w=json.loads(wp.read_text());old=json.loads(rp.read_text());engine_hash=sha256(ep.read_bytes()).hexdigest()
 ck(engine_hash==w['source_engine_sha256']=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56','canonical source engine pin')
 ck(old['status']=='PASS' and old['exact'] and old['witness_sha256']==sha256(wp.read_bytes()).hexdigest() and old['program_sha256']==sha256(vp.read_bytes()).hexdigest(),'same verified complete-loss certificate')
 for name,digest in w['source_sha256'].items():ck(sha256((_resolve_input_path(base, name)).read_bytes()).hexdigest()==digest,'same original source input')
 sp=importlib.util.spec_from_file_location('canonical_source_engine',ep);core=importlib.util.module_from_spec(sp);sp.loader.exec_module(core)
 class Empty:
  def read_text(self):return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':w['source_sha256'],'denominator':1,'rows':[],'expected':{}})
 p=core.prepare(ep.parent,Empty(),1);D=w['denominator'];nums=w['retention_numerators']
 ck(w['central_cells']==[list(x) for x in p['cells']] and len(nums)==80,'same80 indexed central cells')
 ck(type(D) is int and D>0 and all(type(n) is int and 0<=n<=D for n in nums),'rational retention bounds')
 ck(w['exponents']==[6,6,2,2,2,2,2],'fixed resolving inventory')
 return core,p,w,old

def source_weights(p,ci):
 l,m=p['cells'][ci];value=np.full(p['category_shape'],(2-(l==4))*(4-(m==10)),dtype=np.int64);root1=np.zeros(p['category_shape'],dtype=np.uint8)
 for axis,row in enumerate(p['counts'][ci]):
  sh=[1]*5;sh[axis]=len(row);value*=np.array(row,dtype=np.int64).reshape(sh);root1+=(np.arange(len(row))<2).reshape(sh)
 return value*(root1<=1)

def recurrence(u,v):return prod(u)+sum(v[i]*prod(u[j] for j in range(5) if j!=i) for i in range(5))

def read_cylinder(p,nums,d,b):
 dc=d
 for q in Q:
  while dc%q==0:dc//=q
 total=0
 for ci,(l,m) in enumerate(p['cells']):
  x3=3*(l%3)+l//3;x5=5*(m%5)+m//5;x=(100*x3+126*x5)%225
  if x%dc!=b%dc:continue
  u=[];v=[]
  for q,counts in zip(Q,p['counts'][ci]):
   if d%q:uu=sum(counts[2:]);vv=sum(counts[:2])
   else:
    r=b%q
    if r==0:uu=vv=0
    elif r==1:uu=0;vv=sum(counts[:2])
    else:
     k=r if r<9 else 9;size=q-9 if r>=9 else 1;ck(counts[k]%size==0,'exact literal free-root cylinder');uu=counts[k]//size;vv=0
   u.append(uu);v.append(vv)
  total+=nums[ci]*(2-(l==4))*(4-(m==10))*recurrence(u,v)
 return total

def query_weights(exponents=None):
 # Report592 ordered-pair multiplicities (2e+1), applied to the fixed
 # central and exterior screen normalizers of Reports689/695/705.
 if exponents is None:
  left=(F(1),F(3),F(5),F(8,9));right=(F(1),F(3),F(5),F(1,8));outside=[F(3,q-1)+F(5*q-3,(q-2)*(q-1)**2) for q in Q]
 else:
  left=(F(1),F(3),F(5),sum((F(2*(2*e+1),3**e) for e in range(3,exponents[0]+1)),F(0)))
  right=(F(1),F(3),F(5),sum((F(2*e+1,3*5**(e-1)) for e in range(3,exponents[1]+1)),F(0)))
  outside=[F(3,q-1)+sum((F(2*e+1,(q-2)*q**(e-1)) for e in range(2,E+1)),F(0)) for q,E in zip(Q,exponents[2:])]
 return [F(0) if j==0 else left[j//128]*right[(j//32)%4]*prod(outside[i] for i in range(5) if j%32>>i&1) for j in range(512)]

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,default=None);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--metrics',type=Path);a=ap.parse_args();start=time.perf_counter();core,p,w,old=prepare(a.base);nums=w['retention_numerators'];den=p['M0']*w['denominator'];c=1-core.G
 ck(len(LABELS)==33,'selected33 numerical labels')
 inventory=prod(q**E for q,E in zip(P,w['exponents']));stars=[];spent=set();total=F(0)
 for d in (9,25):
  profiles={}
  for q in Q:
   e=d*q;pair=(d,e);ck(d in LABELS and e not in LABELS,'spent pair is outside selected33 square');ck(inventory%e==0,'spent pair is present in finite Q0');ck(pair not in spent,'one owner per spent unordered pair');spent.add(pair)
   vals=[F(read_cylinder(p,nums,e,b),den) for b in range(e)];profiles[e]=[max(vals[b::d]) for b in range(d)]
  separate=sum((max(v) for v in profiles.values()),F(0));jointvals=[sum((v[b] for v in profiles.values()),F(0)) for b in range(d)];joint=max(jointvals);gap=2*(separate-joint);ck(gap>=0,'nonnegative joint conflict gap');total+=gap
  stars.append({'centre':d,'neighbours':list(profiles),'profiles':{str(k):list(map(str,v)) for k,v in profiles.items()},'neighbour_maximizing_centre_residues':{str(k):[b for b,z in enumerate(v) if z==max(v)] for k,v in profiles.items()},'separate_mass_sum':str(separate),'joint_star_mass_sum':str(joint),'best_centre_residues':[b for b,v in enumerate(jointvals) if v==joint],'gap':str(gap),'gap_decimal':float(gap)})
 # Independent source-tensor marginals, preserving the actual root1 mask.
 marg={d:{q:[[0]*q for b in range(d)] for q in Q} for d in (9,25)};cellnums=[];catnums=[[0]*len(cats) for cats in p['cats']];original_num=0
 for ci,(l,m) in enumerate(p['cells']):
  raw=source_weights(p,ci);original_num+=int(raw.sum());cellnums.append(int(raw.sum())*nums[ci]);x3=3*(l%3)+l//3;x5=5*(m%5)+m//5
  for qi,q in enumerate(Q):
   row=raw.sum(axis=tuple(j for j in range(5) if j!=qi));rootcounts=[0]*q
   for k,(n,cat) in enumerate(zip(row,p['cats'][qi])):
    catnums[qi][k]+=int(n)*nums[ci];roots=[r%q for r in cat]
    for r in set(roots):
     z=F(int(n)*roots.count(r),len(roots));ck(z.denominator==1,'exact independent category split');rootcounts[r]+=int(z)
   for d,b in ((9,x3),(25,x5)):
    for r,n in enumerate(rootcounts):marg[d][q][b][r]+=n*nums[ci]
 independent_checks=0
 for row in stars:
  d=row['centre'];joint=[F(0)]*d;separate=F(0)
  for q in Q:
   values=[F(max(v),den) for v in marg[d][q]];expected=list(map(F,row['profiles'][str(d*q)]))
   for z,e in zip(values,expected):ck(z==e,'independent complete profile entry');independent_checks+=1
   separate+=max(values);joint=[u+v for u,v in zip(joint,values)]
  ck(2*(separate-max(joint))==F(row['gap']),'independent exact joint mass gap');independent_checks+=1
 ck(independent_checks==172,'all independent profile and gap checks');ck(total==F(22213436809,874800000000000),'strict measured residual-only correction')
 mass=F(sum(cellnums),den);ck(mass==F(old['mass']),'same retained source mass');ck(F(original_num,p['M0'])==F(305684996597,646498195200),'same original source mass')
 # The finite field certificate stored all499 positive-loss screens. Fill
 # only its13 zero-loss groups, which comprise five single-axis screens
 # and eight unqueried-exterior central screens (including group0).
 A=list(map(F,old['loss_coefficients']));screens=list(map(F,old['query_maxima']));missing=[j for j,z in enumerate(A) if not z];ck(missing==[0,1,2,4,8,16,32,64,96,128,160,256,384],'exact missing screen set')
 for j in missing:
  mode,T=divmod(j,32)
  if T:
   ck(mode==0 and T&(T-1)==0,'one exterior axis only');qi=T.bit_length()-1;q=Q[qi];row=catnums[qi];vals=[F(q-1)*F(row[0]+row[1],den),F(q*(q-2))*F(row[0],den)]
   vals.extend(F(q-1,q-9 if k==9 and q>9 else 1)*F(row[k],den) for k in range(2,len(row)));screens[j]=max(vals)
   # Check the compact single-axis menu against EVERY nonzero source
   # matrix token, including the scaled19 coefficients. Token0 belongs
   # to the unqueried group, not this screen.
   exact_tokens={};scale=5 if q==19 else 1
   for count,entries in zip(row,p['matrices'][qi]):
    for token,coef in entries:
     if token:exact_tokens[token]=exact_tokens.get(token,F(0))+F(count*coef,den*scale)
   ck(screens[j]==max(exact_tokens.values()),'complete single-axis screen agrees with every canonical token')
  else:
   ex,ey=divmod(mode,4);xs=((0,),(0,1),LS,LS)[ex];ys=((0,),(0,1,2,3),MS,MS)[ey];vals=[]
   for left in xs:
    for right in ys:
     mult=F(1)
     if ex==3:mult*=(F(81,82) if left==4 else 1)/F(2-(left==4),9)
     if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else 1)/F(4-(right==10),75)
     vals.append(mult*F(sum(cellnums[ci] for ci,(l,m) in enumerate(p['cells']) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))),den))
   screens[j]=max(vals)
 fee=sum((aa*z for aa,z in zip(A,screens)),F(0));ck(fee==F(old['query_fee']),'unchanged complete original-loss fee')
 allW=query_weights();finiteW=query_weights(w['exponents']);ck(all(x>=y>=0 for x,y in zip(allW,finiteW)),'finite inventory lies within all-height pair envelope');bounds=[];target=F(193,100000)
 fs_path=_resolve_input_path(a.base, 'joined33_full_square_verify.json');fs=json.loads(fs_path.read_text())
 ck(sha256(fs_path.read_bytes()).hexdigest()=='8081db5db397568ea569842d706fd6428fe16c5fa964b3b1e529e648e57e389f','Report705 all-retention upper certificate pin')
 ck(fs['status']=='PASS' and fs['exact'] and fs['source_sha256']==w['source_sha256'],'Report705 identical actual source')
 ck(fs['program_sha256']==sha256((_resolve_input_path(a.base, 'joined33_full_dual_verify.py')).read_bytes()).hexdigest()=='a2680cf4da113106b29877f63bd5b725a54d9a5226749cb6ea71faf22fc0025c','Report705 verifier program pin')
 ck(fs['witness_sha256']==sha256((_resolve_input_path(a.base, 'joined33_full_square_witness.json')).read_bytes()).hexdigest()=='92949c0c415bc6a7e435ae422d8607bdbebb841ce24f7b66c8b2a2eed30c7f69','Report705 witness pin')
 residual=[(F(r)-aa)/c for r,aa in zip(fs['remaining_coefficients'],A)]
 for row in stars:
  d=row['centre'];mode=8 if d==9 else 2
  for qi,q in enumerate(Q):
   j=32*mode+(1<<qi);coef=F(2,q-1);ck(residual[j]>=coef,'spent pair retains its full unused coefficient outside33')
   raw_max=max(map(F,row['profiles'][str(d*q)]));ck(raw_max<=screens[j]/(q-1),'literal pair maximum bounded by its declared complete screen')
 updated_upper=F(fs['upper'])+c*total;ck(updated_upper<target,'this cut alone cannot meet target under Report705')
 old_square_cut={'definition':'G_star(mu)=G_full(mu)+c*kappa(mu), retaining all unspent all-height residual coefficients and exact K33.','report705_gate_upper':fs['upper'],'fixed_field_G_star_upper':str(updated_upper),'fixed_field_G_star_upper_decimal':float(updated_upper),'gap_below_target':str(target-updated_upper),'gap_below_target_decimal':float(target-updated_upper),'scope':'This is an upper bound on the improved33-block criterion at this fixed field, obtained from Report705. It is not an upper bound on the true full independent-label gate.'}

 for name,W in (('all_height',allW),('finite_Q0',finiteW)):
  debit=sum((v*z for v,z in zip(W,screens)),F(0));lower=core.G*mass-fee-c*debit;improved=lower+c*total
  bounds.append({'inventory':name,'independent_pair_charge_upper':str(debit),'gamma_upper_with_stars':str(mass+debit-total),'gate_lower_before_stars':str(lower),'gate_lower_before_stars_decimal':float(lower),'gate_lower_after_stars':str(improved),'gate_lower_after_stars_decimal':float(improved),'gap_to_target_after_stars':str(target-improved),'gap_to_target_after_stars_decimal':float(target-improved),'certifies_target':improved>target})
 out={'status':'PASS','exact':True,'scope':'Upper bound on independent-label Gamma for one fixed actual109 rational retention. The two residual-only stars respect every shared numerical-label phase and are disjoint from the selected33 internal square. Their formula is valid for arbitrary finite query phases and heights containing the spent labels; the positive numerical gap is for this fixed field only. The evaluated gate lower bounds use the coarser complete independent-pair envelope, not an unproved upper for the exact33 maximum. No positive gate or all-family result is claimed.','stars':stars,'spent_pairs':[list(z) for z in sorted(spent)],'charge_upper_improvement':str(total),'charge_upper_improvement_decimal':float(total),'gate_lower_improvement':str(c*total),'gate_lower_improvement_decimal':float(c*total),'independent_category_checks':independent_checks,'mass':str(mass),'query_fee':str(fee),'missing_screens_reconstructed':{str(j):str(screens[j]) for j in missing},'evaluated_envelope_bounds':bounds,'report705_cut_consumer':old_square_cut,'target':str(target),'source_sha256':w['source_sha256'],'source_engine_sha256':w['source_engine_sha256'],'field_witness_sha256':sha256((_resolve_input_path(a.base, 'joined33_coherent_central_field_witness.json')).read_bytes()).hexdigest(),'reused_finite_result_sha256':sha256((_resolve_input_path(a.base, 'joined33_coherent_central_field_verify.json')).read_bytes()).hexdigest(),'reused_report705_result_sha256':sha256(fs_path.read_bytes()).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'checks':CHECKS+core.CHECKS}
 a.output.write_text(json.dumps(out,indent=2)+'\n')
 if a.metrics:a.metrics.write_text(json.dumps({'seconds':time.perf_counter()-start},indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k not in ('stars','missing_screens_reconstructed')},indent=2))
if __name__=='__main__':main()
