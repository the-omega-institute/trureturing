#!/usr/bin/env python3
"""Exact fixed-source duals from query and whole-layout simplexes.

Existing source reconstruction/integer transform is reused. Complete layout
atoms are compiled independently by generalized CRT. No numerical search is
imported. Source-envelope coefficients use the same exact residual. Their measure-level
scope is supplied by Reports704/705, not inferred from finite enumeration.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm,gcd
from hashlib import sha256
import argparse,importlib.util,json
import numpy as np


_DEFAULT_INPUT_PATHS = {'clustered_full5_allfield_verify.py': '../clustered_full5_allfield_verify.py', 'clustered_global_phase_fixture.json': '../clustered_global_phase_fixture.json', 'clustered_higher_pure_capacity_obstruction.json': '../clustered_higher_pure_capacity_obstruction.json', 'joined33_full_dual_witness.json': '../joined33-full-dual-witness/joined33_full_dual_witness.json', 'remaining33_global_root_exclusion_certificate.json': '../remaining33_global_root_exclusion_certificate.json'}

def _resolve_input_path(directory, name):
    if directory is not None:
        return directory / name
    return Path(__file__).resolve().parent / _DEFAULT_INPUT_PATHS.get(name, name)
P=(3,5,7,11,13,17,19);Q=P[2:];D0=(3,5,9,15,25,45,75,225)
EDGES=tuple(z for z in combinations(P,2) if z!=(3,5));LABELS=tuple(sorted(set(D0)|set(Q)|{p*q for p,q in EDGES}))
PAIRS=tuple(combinations(D0,2))+tuple(z for p,q in EDGES for z in ((p,q),(p,p*q),(q,p*q)))
FULL_PAIRS=tuple(combinations(LABELS,2))
CHECKS=0
def ck(x,label):
 global CHECKS
 CHECKS+=1
 if not x:raise ArithmeticError(label)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
def compile_layout(layout,selector_index,token_shape,pairs=PAIRS):
 ck(set(layout)==set(LABELS) and all(type(a) is int and 0<=a<d for d,a in layout.items()),'complete legal33-label layout')
 atoms=[(d,layout[d],F(3)) for d in LABELS]
 for d,e in pairs:
  a,b=layout[d],layout[e];g=gcd(d,e)
  if (b-a)%g:continue
  n=e//g;modulus=lcm(d,e);phase=(a+d*(((b-a)//g*pow(d//g,-1,n))%n))%modulus
  atoms.append((modulus,phase,F(2)))
 result={}
 for modulus,phase,coef in atoms:
  n=modulus;e3=e5=0
  while n%3==0:n//=3;e3+=1
  while n%5==0:n//=5;e5+=1
  left=0 if not e3 else phase%3 if e3==1 else 3*(phase%3)+(phase%9)//3
  right=0 if not e5 else phase%5 if e5==1 else 5*(phase%5)+(phase%25)//5
  sid=selector_index.get((4*e3+e5,left,right))
  if sid is None:continue
  toks=[];den=1;dead=False
  for q in Q:
   if n%q:toks.append(0);continue
   n//=q;r=phase%q
   if r==0:dead=True;break
   toks.append(9 if r>=9 else r);den*=q-1
  if dead:continue
  ck(n==1,'all selected atom prime coordinates represented')
  col=int(np.ravel_multi_index(tuple(toks),token_shape));key=(sid,col);result[key]=result.get(key,F(0))+coef/den
 return result
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,default=None);ap.add_argument('--block',choices=('joined','full-square'),default='joined');ap.add_argument('--witness',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args()
 full=a.block=='full-square';pairs=FULL_PAIRS if full else PAIRS
 stem='joined33_full_square' if full else 'joined33_full_dual'
 if a.witness is None:a.witness=_resolve_input_path(a.base, stem+'_witness.json')
 if a.output is None:a.output=(a.base if a.base is not None else Path(__file__).resolve().parent) / (stem+'_verify.json')
 schema='actual109-full33-square-dual-candidate-v1' if full else 'actual109-joined33-full-dual-v1'
 w=json.loads(a.witness.read_text());ck(w['schema']==schema,'declared block matches candidate schema');D=w['denominator'];ck(type(D) is int and D>0,'positive common probability denominator')
 helper=_resolve_input_path(a.base, 'clustered_full5_allfield_verify.py')
 ck(sha256(helper.read_bytes()).hexdigest()=='edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56','pinned exact source engine')
 core=load('exact_source',helper)
 ck(len(LABELS)==33 and len(pairs)==(528 if full else 88) and 3*len(LABELS)+2*len(pairs)==(1155 if full else 275),'complete selected atom ownership')
 class EmptyRows:
  def read_text(self):return json.dumps({'schema':'clustered109-full5-rational-dual-v1','source_sha256':w['source_sha256'],'denominator':D,'rows':[],'expected':{}})
 p=core.prepare(helper.parent,EmptyRows(),D);c=1-core.G;ck(F(w['block_budget'])==c,'same selected budgetc')
 coeff=list(map(F,json.loads((_resolve_input_path(a.base, 'remaining33_global_root_exclusion_certificate.json')).read_text())['combined512_coefficients']))
 for i,q in enumerate(Q):
  if i:coeff[256+(1<<i)]+=core.G/F(q*(q-2))
 selected=[F(0)]*512
 for d,k in [(d,3) for d in LABELS]+[(lcm(d,e),2) for d,e in pairs]:
  n=d;ex=ey=T=0;norm=1
  while n%3==0:n//=3;ex+=1
  while n%5==0:n//=5;ey+=1
  for i,q in enumerate(Q):
   if n%q==0:n//=q;T|=1<<i;norm*=q-1
  ck(n==1,'literal selected ownership factorization');selected[32*(4*ex+ey)+T]+=F(k,norm)
 remaining=[x-c*v for x,v in zip(coeff,selected)];ck(remaining==list(map(F,w['remaining_coefficients'])) and min(remaining)>=0,'all original loss/fullmode8/query remainders unchanged')
 if full:
  for j,(fee,v) in enumerate(zip(coeff,selected)):
   mode,T=divmod(j,32);ex,ey=divmod(mode,4)
   W=(F(1),F(3),F(5),F(8,9))[ex]*(F(1),F(3),F(5),F(1,8))[ey]
   for i,q in enumerate(Q):
    if T>>i&1:W*=F(3,q-1)+F(5*q-3,(q-2)*(q-1)**2)
   if j==0:W=F(0)
   ck(fee-c*W>=0 and W-v>=0 and remaining[j]==(fee-c*W)+c*(W-v),'full square preserves original losses and every unselected all-height query budget')
 selectors=[]
 for mode in range(16):
  ex,ey=divmod(mode,4);xm=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[ex];ym=((0,),(0,1,2,3),tuple(m for m in range(20) if m!=5),tuple(m for m in range(20) if m!=5))[ey]
  for left,right in product(xm,ym):
   ids=[ci for ci,(l,m) in enumerate(p['cells']) if (ex==0 or (l//3==left if ex==1 else l==left)) and (ey==0 or (m//5==right if ey==1 else m==right))]
   mult=F(1)
   if ex==3:mult*=(F(81,82) if left==4 else 1)/F(2-(left==4),9)
   if ey==3:mult*=F(4,5)*(F(1875,1876) if right==10 else 1)/F(4-(right==10),75)
   selectors.append((mode,left,right,ids,mult))
 ck(len(selectors)==559,'complete central selector interface')
 sidmap={(mode,l,m):i for i,(mode,l,m,ids,mult) in enumerate(selectors)}
 layout_maps=[compile_layout({int(d):phase for d,phase in lo.items()},sidmap,p['token_shape'],pairs) for lo in w['layouts']]
 loads=[0]*512;seen=set();layout_load=0;layout_nums={}
 for li,num in w['layout_rows']:
  ck(type(li) is int and 0<=li<len(layout_maps) and li not in layout_nums and type(num) is int and num>0,'one nonnegative complete-layout probability');layout_nums[li]=num;layout_load+=num
 ck(layout_load==D,'whole-layout mixture has exactly budgetc')
 L=lcm(core.G.denominator,*(r.denominator for r in remaining),*((c*coef).denominator for li in layout_nums for coef in layout_maps[li].values()))
 Dc=82*469;debitDen=5*D*L*Dc;rewardnum=core.G*debitDen;ck(rewardnum.denominator==1,'exact reward scaling');rewardnum=int(rewardnum)
 scatter=[{} for _ in p['cells']]
 def add(sid,col,coefficient):
  mode,left,right,ids,mult=selectors[sid];value=coefficient*L*mult*Dc;ck(value.denominator==1 and value>=0,'exact nonnegative integer query/layout debit')
  value=int(value)
  for ci in ids:scatter[ci][col]=scatter[ci].get(col,0)+value
 for mode,T,sid,col,num in w['rows']:
  ck(all(type(z) is int for z in (mode,T,sid,col,num)) and 0<=mode<16 and 0<=T<32 and 0<=sid<len(selectors) and 0<=col<prod(p['token_shape']) and num>0,'legal old-query row probability')
  key=(mode,T,sid,col);ck(key not in seen,'distinct old-query row');seen.add(key);j=32*mode+T
  ck(selectors[sid][0]==mode and remaining[j]>0,'row in its positive new fee group')
  coords=np.unravel_index(col,p['token_shape']);ck(sum(1<<i for i,tok in enumerate(coords) if tok)==T,'literal outside support')
  ck(bool(selectors[sid][3]),'query selector meets actual central support')
  loads[j]+=num;add(sid,col,remaining[j]*num)
 ck(all(n==(D if remaining[j]>0 else 0) for j,n in enumerate(loads)),'every506 positive new budget filled; zero budgets empty')
 for li,num in layout_nums.items():
  for (sid,col),coef in layout_maps[li].items():add(sid,col,c*num*coef)
 ck(8*prod(q*(q-1) for q in Q)<2**63 and p['M0']<2**63,'source counts fit signed64 arithmetic')
 shape=p['category_shape'];rootcount=np.zeros(shape,dtype=np.uint8)
 for axis,size in enumerate(shape):
  dims=[1]*5;dims[axis]=size;rootcount+=(np.arange(size)<2).astype(np.uint8).reshape(dims)
 good=rootcount<=1;branches=[rootcount==0]
 for axis,(q,cats) in enumerate(zip(Q,p['cats'])):
  dims=[1]*5;dims[axis]=len(cats);sp=[all(z==1 for z in cat) for cat in cats];other=[all(z%q==1 and z!=1 for z in cat) for cat in cats]
  branches.extend([np.broadcast_to(np.array(sp).reshape(dims),shape)&good,np.broadcast_to(np.array(other).reshape(dims),shape)&good])
 partition=sum(mask.astype(np.uint8) for mask in branches);ck(np.all(partition[good]==1),'eleven actual source branches partition')
 total=source_num=states=positive_states=0;branch_num=[0]*11;cellwise=[F(0)]*11
 for ci,(l,m) in enumerate(p['cells']):
  weights=np.full(shape,(2-(l==4))*(4-(m==10)),dtype=np.int64)
  for axis,row in enumerate(p['counts'][ci]):
   dims=[1]*5;dims[axis]=len(row);weights*=np.array(row,dtype=np.int64).reshape(dims)
  weights*=good;mask=weights>0
  if not np.any(mask):continue
  sparse=np.zeros(p['token_shape'],dtype=object)
  for col,num in scatter[ci].items():sparse.flat[col]=num
  debit=core.transform(sparse,p['matrices'])[mask];ck(all(type(v) is int and v>=0 for v in debit),'exact whole mixed debit on positive source states')
  residual=rewardnum-debit;positive=np.maximum(residual,0);weighted=positive*weights[mask];celltotal=int(np.sum(weighted));total+=celltotal;source_num+=int(weights.sum());states+=len(debit);positive_states+=int(np.count_nonzero(positive))
  Rc=(F(82,81) if l==4 else 1)*(F(1876,1875) if m==10 else 1)
  parts=[int(np.sum(weighted[bm[mask]])) for bm in branches];ck(sum(parts)==celltotal,'branch totals reproduce whole residual')
  for i,num in enumerate(parts):branch_num[i]+=num;cellwise[i]+=Rc*num
 ck(states==2125830 and F(source_num,p['M0'])==F(305684996597,646498195200),'same entire actual109 source')
 denominator=p['M0']*debitDen;upper=F(total,denominator);target=F(193,100000);branchesF=[F(z,denominator) for z in branch_num];cellF=[z/denominator for z in cellwise]
 slopes=[branchesF[1+2*i]-branchesF[2+2*i]/(q-1) for i,q in enumerate(Q)];cell_slopes=[cellF[1+2*i]-cellF[2+2*i]/(q-1) for i,q in enumerate(Q)]
 outside=branchesF[0]+sum(max(q*branchesF[1+2*i],F(q,q-1)*branchesF[2+2*i]) for i,q in enumerate(Q))
 celloutside=cellF[0]+sum(max(q*cellF[1+2*i],F(q,q-1)*cellF[2+2*i]) for i,q in enumerate(Q))
 ck(0<=upper<=outside<=celloutside,'ordered nonnegative common-source arithmetic envelopes')
 if not full:
  ck(upper<target,'strict complete699 fixed-source dual obstruction')
  for slope in slopes+cell_slopes:ck(slope<0,'shared outside endpoint maximizes the affine residual envelope')
  ck(celloutside<target,'complete699 common-source arithmetic envelopes below target')
 result={'status':'PASS','exact':True,'block':a.block,'selected_pairs':len(pairs),'selected_atomic_weight':3*len(LABELS)+2*len(pairs),'scope':'Exact feasible dual for the declared block with all512 remaining fees and one law on complete33-label layouts. Reports704/705 supply the arbitrary-depth and common-source redistribution proofs. PASS certifies the rational bound; below_target separately records whether the target is excluded. No optimum or positive primal is claimed.',
 'source_sha256':p['pins'],'witness_sha256':sha256(a.witness.read_bytes()).hexdigest(),'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'source_helper_sha256':sha256((_resolve_input_path(a.base, 'clustered_full5_allfield_verify.py')).read_bytes()).hexdigest(),
 'upper':str(upper),'upper_decimal':float(upper),'target':str(target),'below_target':upper<target,'margin':str(target-upper),'actual_states':states,'positive_residual_states':positive_states,'source_mass':str(F(source_num,p['M0'])),'old_query_rows':len(w['rows']),'layout_columns':len(layout_maps),'positive_layout_probabilities':len(layout_nums),'budget_denominator':D,'remaining_coefficients':list(map(str,remaining)),'group_loads':loads,'layout_budget_load':layout_load,'new_checks':CHECKS,'source_checks':core.CHECKS,'checks':CHECKS+core.CHECKS,
 'branch_coefficients':list(map(str,branchesF)),'outside_slopes':list(map(str,slopes)),'outside_arithmetic_envelope':str(outside),'outside_arithmetic_envelope_decimal':float(outside),'cellwise_coefficients':list(map(str,cellF)),'cellwise_slopes':list(map(str,cell_slopes)),'cellwise_arithmetic_envelope':str(celloutside),'cellwise_arithmetic_envelope_decimal':float(celloutside),'source_extension_requires_measure_proof':True}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('remaining_coefficients','group_loads','source_sha256','branch_coefficients','outside_slopes','cellwise_coefficients','cellwise_slopes')},indent=2),flush=True)
if __name__=='__main__':main()
