#!/usr/bin/env python3
"""Conditional exact reuse of Report392 RT11--RT12; no optimizer.
Weights are nonnegative integers with a caller-supplied common denominator.
The returned score excludes the divisor-one mass: it is the eight-label
3*sum(I)+2*sum(I_i I_j) block, with the two root labels fixed independently.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product,islice
from math import gcd,prod,lcm
import importlib.util,json,argparse,time,sys
import numpy as np
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('existing_height_two',BASE/'height_two_layout_second_moment.py')
existing=importlib.util.module_from_spec(spec);sys.modules[spec.name]=existing;spec.loader.exec_module(existing)

class ConditionalHeightTwoOracle(existing.HeightTwoLayoutOracle):
 def separate_conditioned(self,weights,a,b,denominator=1,chunk_size=256):
  weights=tuple(weights)
  existing.check(len(weights)==len(self.points),'one integer weight per point')
  existing.check(all(type(w) is int and w>=0 for w in weights),'nonnegative integer weights')
  existing.check(type(a) is int and 0<=a<self.p and type(b) is int and 0<=b<self.q,'both literal fixed roots')
  existing.check(type(denominator) is int and denominator>0,'positive common measure denominator')
  existing.check(type(chunk_size) is int and chunk_size>0,'positive chunk size')
  total=sum(weights);dtype=np.int64 if 81*total<=existing.INT64_MAX else object
  w=np.array(weights,dtype=dtype)
  free=(self.p2,self.q2,self.p*self.q)
  baseline_count=prod(len(self.residues[d]) for d in free)
  fixed=1+(self.point_residues[self.p]==a).astype(np.int64)+(self.point_residues[self.q]==b).astype(np.int64)
  choices=product(*(range(len(self.residues[d])) for d in free))
  best=-1;best_ids=None;examined=0
  while True:
   block=list(islice(choices,chunk_size))
   if not block:break
   ids=np.array(block,dtype=np.int64);examined+=len(block)
   v=np.broadcast_to(fixed,(len(block),len(self.points))).copy()
   for j,d in enumerate(free):v+=(self.point_residues[d][None,:]==self.residues[d][ids[:,j]][:,None])
   baseline=(v*v*w).sum(axis=1);h=(2*v+1)*w
   gb=np.column_stack([h[:,group].sum(axis=1) for group in self.b_groups])
   gc=np.column_stack([h[:,group].sum(axis=1) for group in self.c_groups])
   boosted=h+2*w
   hb=np.column_stack([boosted[:,group].max(axis=1) for group in self.b_groups])
   hc=np.column_stack([boosted[:,group].max(axis=1) for group in self.c_groups])
   h0=h.max(axis=1);gb0=gb.max(axis=1);gc0=gc.max(axis=1)
   m0=gb0+gc0+h0;mb=(gb+hb).max(axis=1)+gc0;mc=gb0+(gc+hc).max(axis=1)
   intersection=gb[:,self.b_index]+gc[:,self.c_index]+2*w
   point_term=np.maximum(np.maximum(h0[:,None],hb[:,self.b_index]),np.maximum(hc[:,self.c_index],h+4*w))
   mi=(intersection+point_term).max(axis=1)
   totals=baseline+np.maximum(np.maximum(m0,mb),np.maximum(mc,mi))
   j=int(totals.argmax())
   if int(totals[j])>best:best=int(totals[j]);best_ids=tuple(map(int,ids[j]))
  existing.check(examined==baseline_count,'all three-label baselines examined')
  layout={1:0,self.p:a,self.q:b,**{d:int(self.residues[d][j]) for d,j in zip(free,best_ids)}}
  v=fixed.copy()
  for d in free:v+=(self.point_residues[d]==layout[d])
  # Direct cylinder-pair scan only at the winning baseline. This independently
  # reconstructs a witness rather than trusting the compressed case selection.
  direct_best=-1;winner=None;pair_count=0
  for ib,ic in product(range(len(self.b_groups)),range(len(self.c_groups))):
   pair_count+=1
   u=v+(self.b_index==ib)+(self.c_index==ic)
   gains=(2*u+1)*w;iz=int(gains.argmax())
   value=int(np.dot(u*u,w))+int(gains[iz])
   if value>direct_best:direct_best=value;winner=(ib,ic,iz)
  existing.check(direct_best==best,'compressed optimum matches direct final-pair reconstruction')
  ib,ic,iz=winner
  layout.update({self.b_modulus:int(self.residues[self.b_modulus][ib]),self.c_modulus:int(self.residues[self.c_modulus][ic]),self.carrier:int(self.values[iz])})
  literal=self.layout_costs(layout)-1
  score=int(np.dot(literal,w))
  existing.check(score==best-total,'literal eight-label row matches conditional optimum')
  existing.check(layout[self.p]==a and layout[self.q]==b,'literal witness preserves fixed root choices')
  existing.check(all(0<=r<d for d,r in layout.items()),'every independent numerical label has a legal residue')
  return {'fixed_roots':[a,b],'score_numerator':score,'measure_denominator':denominator,
   'conditional_value':str(Fraction(score,denominator)),'source_mass':str(Fraction(total,denominator)),
   'full_square_numerator':best,'layout':{str(d):r for d,r in sorted(layout.items())},
   'point_costs':list(map(int,literal)),'baseline_choices':examined,'reconstruction_pairs':pair_count,
   'arithmetic':'int64_guarded' if dtype is np.int64 else 'arbitrary_integer'}

 def brute_conditioned(self,weights,a,b):
  free=[d for d in self.moduli if d not in (1,self.p,self.q)]
  best=-1;count=0
  for values in product(*(self.residues[d] for d in free)):
   layout={1:0,self.p:a,self.q:b,**dict(zip(free,map(int,values)))}
   score=sum(int(z)*w for z,w in zip(self.layout_costs(layout)-1,weights))
   best=max(best,score);count+=1
  return best,count

def central_conditional_table(points,weights):
 """Return (C[3,5], layouts[(a,b)]) for unnormalized integer masses.

 C contains exactly the NONUNIT selected-square numerator. No normalization
 occurs; callers divide by their one common measure denominator. Layouts use
 integer keys for the eight original moduli and preserve even zero-mass fixed
 root choices. The complete pair of tables is a fresh function of weights.
 """
 weights=tuple(weights)
 oracle=ConditionalHeightTwoOracle(3,5,points)
 existing.check(len(weights)==len(oracle.points) and all(type(w) is int and w>=0 for w in weights),'nonnegative joint integer field')
 dtype=np.int64 if 81*sum(weights)<=existing.INT64_MAX else object
 values=np.empty((3,5),dtype=dtype);layouts={}
 if sum(weights)==0:
  for a,b in product(range(3),range(5)):
   values[a,b]=0;layouts[a,b]={3:a,5:b,9:0,15:0,25:0,45:0,75:0,225:0}
  return values,layouts
 for a,b in product(range(3),range(5)):
  result=oracle.separate_conditioned(weights,a,b)
  values[a,b]=result['score_numerator']
  layouts[a,b]={int(d):v for d,v in result['layout'].items() if int(d)!=1}
 return values,layouts

def controls():
 cases=[([(1,1),(4,6),(2,12)],[2,3,5]), ([(1,1),(4,1),(1,6)],[0,7,4]), ([(0,0),(8,24),(3,10)],[7,2,11])]
 out=[]
 for points,weights in cases:
  oracle=ConditionalHeightTwoOracle(3,5,points);rows=[]
  for a,b in product(range(3),range(5)):
   r=oracle.separate_conditioned(weights,a,b);direct,n=oracle.brute_conditioned(weights,a,b)
   existing.check(r['score_numerator']==direct,'small-source six-free-label exhaustive control')
   rows.append({'roots':[a,b],'value':direct,'brute_layouts':n})
  out.append({'points':points,'weights':weights,'conditions':rows})
 # Same complete data above but beyond machine-integer range: scale homogeneity
 # checks every path through the arbitrary-integer fallback without new sampling.
 points,weights=cases[0];oracle=ConditionalHeightTwoOracle(3,5,points)
 scale=10**30
 a,b=0,4;r=oracle.separate_conditioned(weights,a,b);large=oracle.separate_conditioned([scale*w for w in weights],a,b)
 existing.check(large['score_numerator']==scale*r['score_numerator'] and large['arithmetic']=='arbitrary_integer','arbitrary-integer fallback homogeneous')
 # Zero retention is a legitimate field, including roots absent from support.
 zero=oracle.separate_conditioned([0]*len(points),0,4)
 existing.check(zero['score_numerator']==0,'zero measure conditional value')
 return out

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--actual-source',type=Path)
 args=ap.parse_args();started=time.monotonic();result={'status':'PASS','controls':controls(),'new_lean_verification':False,'optimizer_used':False,'prior_result':'Report392 RT11--RT12; existing height_two_layout_second_moment.py'}
 if args.actual_source:
  data=json.loads(args.actual_source.read_text());cells=data['cell_results']
  points=[(row['physical_mod225']%9,row['physical_mod225']%25) for row in cells]
  weights=[row['source_numerator'] for row in cells]
  den=Fraction(sum(weights),1)/Fraction(data['source_mass'])
  existing.check(den.denominator==1,'recover exact actual-source mass denominator')
  oracle=ConditionalHeightTwoOracle(3,5,points)
  table=[oracle.separate_conditioned(weights,a,b,int(den)) for a,b in product(range(3),range(5))]
  result['actual_source']={'input':str(args.actual_source),'source_mass':data['source_mass'],'points':len(points),'weight_denominator':int(den),'free_baselines_per_condition':table[0]['baseline_choices'],'conditional_table':table,'unconditional_central_maximum':str(max(Fraction(r['conditional_value']) for r in table))}
 result['elapsed_seconds']=time.monotonic()-started
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'output':str(args.output),'elapsed_seconds':result['elapsed_seconds'],'actual_max':result.get('actual_source',{}).get('unconditional_central_maximum')}))
