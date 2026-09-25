#!/usr/bin/env python3
"""Common conditional pair law: all eighty outside square-pair labels.

Ordinary Scott--Sokal query ratios and one Z-thinned actual survivor law.
The complete five-star comparison scan retains every old/query height.
No Lean verification and no unrestricted Erdos7 resolution are claimed.
"""
import argparse,hashlib,importlib.util,itertools,json,shutil,subprocess,tempfile
from fractions import Fraction as F
from math import ceil,floor,prod
from pathlib import Path
TAIL=F(1084133,201247200)
SCALE=10**9
CD=1<<30
EXPECTED=F(548601319573,131072000000000)
EXPECTED_HAAR=F(1466411327218629,18129879040000000000)


def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def encode(v):
 if isinstance(v,F):return str(v)
 if isinstance(v,dict):return {str(k):encode(x) for k,x in v.items()}
 if isinstance(v,(list,tuple)):return [encode(x) for x in v]
 return v


def main():
 p=argparse.ArgumentParser(description=__doc__.splitlines()[0]);base=Path(__file__).parent
 p.add_argument('--source-profile',type=Path,default=base/'two_centre_star_profile.py')
 p.add_argument('--boundary-profile',type=Path,default=base/'multi_joint_square_profile.py')
 p.add_argument('--inventory-profile',type=Path,default=base/'outside_square_pair_core_profile.py')
 p.add_argument('--engine',type=Path,default=base/'outside_pair_shearer_scan.cpp')
 p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 p.add_argument('--cxx',default=shutil.which('clang++') or shutil.which('g++'));args=p.parse_args()
 if not args.cxx:p.error('C++17 compiler required')
 s=vars(load(args.source_profile,'source'));b=load(args.boundary_profile,'boundary');inv=load(args.inventory_profile,'inventory')
 checks={}
 def require(name,predicate):
  if not predicate:raise ArithmeticError('certificate failed: '+name)
  checks[name]=True
 Q=s['Q'];edges=list(itertools.combinations(range(5),2));masks=[(1<<i)|(1<<j) for i,j in edges]
 matchings=[(i,j,next(iter(set(range(5))-set(edges[i])-set(edges[j])))) for i,j in itertools.combinations(range(10),2) if not set(edges[i])&set(edges[j])]
 kappa=[F(1,(Q[i]-1)*(Q[j]-1))+F(1,Q[i]*(Q[i]-2)*(Q[j]-1))+F(1,Q[j]*(Q[j]-2)*(Q[i]-1)) for i,j in edges]
 cross=[F()]*5
 for i,j,left in matchings:cross[left]+=kappa[i]*kappa[j]
 require('matching_inventory',len(edges)==10 and len(matchings)==15)
 bmin=[1-3*F(1,q-1)-2*F(1,q*(q-2)) for q in Q]
 pmax=[4*kappa[j]/(bmin[i]*bmin[k]) for j,(i,k) in enumerate(edges)]
 allZ=[1-sum((pmax[i] for i in range(10) if mask>>i&1),F())+sum((pmax[i]*pmax[j] for i,j,_ in matchings if mask>>i&1 and mask>>j&1),F()) for mask in range(1024)]
 disjoint=[sum((pmax[j] for j in range(10) if not set(edges[i])&set(edges[j])),F()) for i in range(10)]
 require('strict_shearer_box',min(allZ)==F(851826382717,13419739162053) and min(allZ)>F(3,50))
 require('strict_coordinate_monotonicity',max(disjoint)==F(45428404,79049907) and max(disjoint)<F(3,5))
 _,groups=inv.inventory(Q);extra=inv.enumerate_coefficients(groups['extra']+groups['pair_core']);old,query,W=b.coefficients(s)
 remaining=[x+y for x,y in zip(old,extra)];pair=[F()]*192
 for mask,k in zip(masks,kappa):
  for mode in(0,1,2,4):pair[32*mode+mask]+=k/(4 if mode in(1,4) else 1)
 remaining=[x-y for x,y in zip(remaining,pair)]
 labels=[];enumerated=[F()]*192;sf=[F()]*192
 for i,j in edges:
  q,r=Q[i],Q[j];mask=(1<<i)|(1<<j)
  for hq,hr in((1,1),(2,1),(1,2)):
   cq=F(1,q-1) if hq==1 else F(1,q*(q-2));cr=F(1,r-1) if hr==1 else F(1,r*(r-2))
   for h3,h5 in itertools.product(range(2),repeat=2):
    mode={(0,0):0,(0,1):1,(1,0):2,(1,1):4}[h3,h5];v=cq*cr/(4 if h5 else 1)
    enumerated[32*mode+mask]+=v
    if hq==hr==1:sf[32*mode+mask]+=v
    labels.append(3**h3*5**h5*q**hq*r**hr)
 require('pair_120_distinct_labels',len(labels)==len(set(labels))==120)
 require('pair_coefficient_enumeration',enumerated==pair)
 only749=inv.enumerate_coefficients(groups['extra'])
 require('old594_plus_full829_inventory',remaining==[x+y-z for x,y,z in zip(old,only749,sf)])
 require('all_queries_unchanged',len(W)==192 and all(w>=0 for w in W))
 require('residual_losses_nonnegative',all(x>=0 for x in remaining))
 gain=1-TAIL;new=[gain*l+TAIL*w for l,w in zip(remaining,W)]
 rg=floor(gain*SCALE);op=[ceil(gain*x*SCALE) for x in pair];np=[ceil(x*SCALE) for x in new];cg=[floor(gain*x*SCALE) for x in cross]
 kl=[floor(x*CD) for x in kappa];ch=[ceil(x*CD) for x in cross]
 require('directed_coefficients',F(rg,SCALE)<=gain and all(F(v,SCALE)>=gain*x for v,x in zip(op,pair)) and all(F(v,SCALE)>=x for v,x in zip(np,new)) and all(F(v,SCALE)<=gain*x for v,x in zip(cg,cross)))
 require('directed_matching_weights',all(F(v,CD)<=x for v,x in zip(kl,kappa)) and all(F(v,CD)>=x for v,x in zip(ch,cross)))
 bound=(rg+sum(op)+sum(np)+sum(cg))*b.SCREEN_DENOMINATOR
 require('signed_integer_accumulation',bound<2**63-1 and SCALE*b.SCREEN_DENOMINATOR<2**63-1)
 require('matching_product_accumulation',max(kl+ch)*b.D+CD-1<2**63-1)
 templates=[b.templates(q) for q in Q]
 require('factor_intervals',all(F(lo,b.D)<=v<=F(hi,b.D) and hi-lo<=1 for ts in templates for row in ts for lo,v,hi in zip(row['lower'],row['factor'],row['upper'])))
 require('factor_strict_region',all(v>=bmin[q] for q,ts in enumerate(templates) for row in ts for v in row['factor']))
 colcounts=b.canonical_columns();expected_cases=sum(colcounts)*4**5*2
 require('orbit_count',colcounts==[1,1023,28501,145750] and expected_cases==358963200)
 text=[f'{SCALE} {rg}',' '.join(map(str,op)),' '.join(map(str,np)),' '.join(map(str,cg)),' '.join(map(str,kl)),' '.join(map(str,ch))]
 for ts in templates:
  for row in ts:text.append(' '.join(f'{l} {h}' for l,h in zip(row['lower'],row['upper'])))
 input_text='\n'.join(text)+'\n'
 with tempfile.TemporaryDirectory(prefix='outside-pair-shearer-') as td:
  d=Path(td);inp=d/'input.txt';exe=d/'scan';inp.write_text(input_text)
  subprocess.run([args.cxx,'-std=c++17','-O3',str(args.engine),'-o',str(exe)],check=True,capture_output=True,text=True)
  output=subprocess.run([str(exe),str(inp)],check=True,capture_output=True,text=True).stdout
 fields=list(map(int,output.split()));require('engine_row',len(fields)==9)
 cases,num,den,ti,*codes=fields;t=F(ti,3)
 require('complete_coverage',cases==expected_cases and den==SCALE*b.SCREEN_DENOMINATOR and ti in(1,2) and len(codes)==5 and all(0<=v<64 for v in codes))
 raw=F(num,den);oldex,oldlo,oldhi=b.witness_screens(templates,codes,t)
 exG=[];loG=[];hiG=[]
 for mask in range(32):
  ev=[];lv=[];hv=[]
  for cell in range(8):
   x=F(int(cell!=0));l=h=b.D if cell else 0
   for q in range(5):
    if mask>>q&1:continue
    row=templates[q][codes[q]];x*=row['factor'][cell];l=l*row['lower'][cell]//b.D;h=(h*row['upper'][cell]+b.D-1)//b.D
   ev.append(x);lv.append(l);hv.append(h)
  exG.append(ev);loG.append(lv);hiG.append(hv)
 newex=[F()]*192;newhi=[F()]*192;querygrids=[]
 for mask in range(32):
  eg=[];hg=[]
  for cell in range(8):
   x=exG[mask][cell];h=hiG[mask][cell]
   for j,m in enumerate(masks):
    if not m&mask:x-=kappa[j]*exG[mask|m][cell];h-=kl[j]*loG[mask|m][cell]//CD
   for q in range(5):
    m=31^(1<<q)
    if not m&mask:x+=cross[q]*exG[mask|m][cell];h+=(ch[q]*hiG[mask|m][cell]+CD-1)//CD
   require(f'query_upper_{mask}_{cell}',0<=x<=min(F(h,b.D),F(hiG[mask][cell],b.D)))
   eg.append(x);hg.append(min(F(h,b.D),F(hiG[mask][cell],b.D)))
  querygrids.append({'exact':eg,'upper':hg})
  for mode,x in enumerate(b.screen_values(eg,t)):newex[32*mode+mask]=x
  for mode,x in enumerate(b.screen_values(hg,t)):newhi[32*mode+mask]=x
 rounded=F(rg,SCALE)*oldlo[0]+sum((F(cg[q],SCALE)*oldlo[31^(1<<q)] for q in range(5)),F())-sum((F(v,SCALE)*x for v,x in zip(op,oldhi)),F())-sum((F(v,SCALE)*x for v,x in zip(np,newhi)),F())
 mass=oldex[0]-sum((v*x for v,x in zip(pair,oldex)),F())+sum((cross[q]*oldex[31^(1<<q)] for q in range(5)),F())-sum((v*x for v,x in zip(remaining,newex)),F())
 weighted=sum((v*x for v,x in zip(W,newex)),F());exact=gain*mass-TAIL*weighted
 require('integer_witness_reconstruction',rounded==raw)
 require('exact_witness_outward',raw<=exact)
 require('positive_uniform_potential',raw==EXPECTED and raw>0)
 haar=raw/(s['DENSITY']*F(200,33));require('positive_haar',haar==EXPECTED_HAAR and haar>F(1,12500))
 paths=(Path(__file__),args.engine,args.source_profile,args.boundary_profile,args.inventory_profile)
 result={'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'input_sha256':hashlib.sha256(input_text.encode()).hexdigest(),'inventory':{'pair_labels':sorted(labels),'pair_count':120,'existing_sf_count':40,'new_square_pair_count':80,'remaining_extra749':len(groups['extra'])},'shearer':{'bmin':bmin,'kappa':kappa,'cross_by_leftover':cross,'pmax':pmax,'all_induced_count':len(allZ),'minimum_induced':min(allZ),'maximum_disjoint_sum':max(disjoint)},'factor_denominator':b.D,'matching_denominator':CD,'coefficient_scale':SCALE,'signed_accumulation_bound':bound,'bound_bits':bound.bit_length(),'column_orbit_counts':colcounts,'cases':cases,'raw_tail_lower':raw,'haar_lower':haar,'witness':{'codes':codes,'t':t,'raw_mass_lower':mass,'weighted_query_upper':weighted,'exact_raw_tail':exact,'rounding_gap':exact-raw,'query_grids':querygrids},'coefficients':[{'remaining_loss':l,'pair_charge':v,'weighted_query':w,'combined':n,'old_rounded':o,'new_rounded':r} for l,v,w,n,o,r in zip(remaining,pair,W,new,op,np)],'checks':checks}
 args.output.write_text(json.dumps(encode(result),indent=2)+'\n');print(json.dumps({'checks':len(checks),'cases':cases,'raw_tail_lower':str(raw),'haar_lower':str(haar),'codes':codes,'t':str(t)}))

if __name__=='__main__':main()
