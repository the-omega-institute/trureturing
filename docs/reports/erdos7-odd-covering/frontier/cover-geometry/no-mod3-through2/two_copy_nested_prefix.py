#!/usr/bin/env python3
"""New exact depth-two 5-adic comparison budgets, consuming the retained PA schedule.
Only low product atoms 1,2,3 are convolved. Infinite tails enter full means.
No old producer, cap grid, original-family scan, or Lean invocation is run.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input',type=Path,default=Path(__file__).with_name('two_copy_pure_anchor.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
raw=args.input.read_bytes()
PIN='45939ae4a727d63d0e91d836b8519eea84482f8c06cfe46eb96cb082a2f78a53'
if hashlib.sha256(raw).hexdigest()!=PIN: raise ValueError('retained PA pin mismatch')
data=json.loads(raw)
checks={}
def req(name,value):
 checks[name]=bool(value)
 if not value: raise ValueError(name)
def pair(x): return F(*x)
def enc(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [enc(v) for v in x]
 return x

def add(x,y):return tuple(a+b for a,b in zip(x,y))
def scale(c,x):return tuple(c*a for a in x)
def ev(x,q):return sum((a*b for a,b in zip(x,(F(1),)+tuple(q))),F())

req('reference_primes',data['reference_primes']==[5,7,11,13,17,19])
req('stage_thresholds',data['stage_thresholds']==[2,2,4,4])
req('final_query_threshold',data['query_threshold']==3)
stored=data['corners'][0]['stages']
schedule=[(row['prime'],row['threshold'],pair(row['cap'])) for row in stored]
for p,t,c in schedule:req('cap_contract_'+str(p),c==F(p-1,p-1-2*t))

# Shared remaining-coordinate distribution. All moments of N5 below are affine
# in (q1,q2,K), so this one convolution provides all candidate ledgers.
rest_mean=F(5,4)
rest_low={1:F(11,14),2:F(9,49),3:F(9,343)}
mean5=(F(1),F(1),F(1),F(1,100))
atom5={1:(F(1),F(-1),F(0),F(0)),
       2:(F(0),F(1),F(-1),F(0)),
       3:(F(0),F(0),F(1),F(-1,125))}

def hinge5(t,rm,rl):
 h=add(scale(rm,mean5),(-F(t),F(0),F(0),F(0)))
 for n,a in atom5.items():
  for m,w in rl.items():
   if n*m<t:h=add(h,scale(F(t-n*m)*w,a))
 return h

seed=(F(1),F(-1,2),F(-1,2),F(-1,200))
alpha=seed
stage_coefficients=[]
for p,t,c in schedule:
 hinge=hinge5(t,rest_mean,rest_low)
 loss=scale(F(2,p-1-2*t),hinge)
 alpha=add(alpha,scale(F(-1),loss))
 stage_coefficients.append({'prime':p,'threshold':t,'cap':c,'old_rest_mean':rest_mean,'old_rest_low':rest_low.copy(),'hinge':hinge,'loss':loss,'mass_after':alpha})
 atoms={1:1-c/p,2:c*F(p-1,p**2),3:c*F(p-1,p**3)}
 nxt={}
 for n,w in rest_low.items():
  for m,v in atoms.items():
   if n*m<4:nxt[n*m]=nxt.get(n*m,F())+w*v
 rest_low=nxt
 rest_mean*=1+c/F(p-1)
phi=hinge5(3,rest_mean,rest_low)
T=F(257,51)
gap=add(scale(T-2,alpha),scale(F(-1),phi))

s=F(7,50)
candidates={
 'root_balanced_split25':(F(1,3),1/(75*s),1/(3*s)),
 'split125_cells':(F(40,103),F(8,103),F(250,103)),
 'common125_outside25_root':(F(14,37),F(3,37),F(100,37)),
}
rows={}
for name,q in candidates.items():
 q1,q2,K=q
 req(name+'_nonnegative_atoms',0<=K/125<=q2<=q1<=1)
 # The complete n>=4 mass is K/125, and its first moment is 17K/500.
 tail_mass=K/125
 tail_first_moment=F(17,500)*K
 req(name+'_normalization',(1-q1)+(q1-q2)+(q2-K/125)+tail_mass==1)
 req(name+'_full_mean',(1-q1)+2*(q1-q2)+3*(q2-K/125)+tail_first_moment==ev(mean5,q))
 a=ev(alpha,q); ph=ev(phi,q); g=ev(gap,q)
 req(name+'_positive_mass',a>0)
 req(name+'_positive_hinge',ph>=0)
 req(name+'_crosses_target',g>0)
 req(name+'_paired_identity',g==(T-2)*a-ph)
 stage_rows=[]
 for row in stage_coefficients:
  h=ev(row['hinge'],q);loss=ev(row['loss'],q)
  req(name+'_stage_nonnegative_'+str(row['prime']),h>=0 and loss>=0)
  stage_rows.append({'prime':row['prime'],'threshold':row['threshold'],'cap':row['cap'],'hinge':h,'loss':loss,'mass_after':ev(row['mass_after'],q)})
 rows[name]={'caps':q,'R5_upper':q1+q2+K/100,'seed_mass':ev(seed,q),'stages':stage_rows,'alpha':a,'Phi':ph,'paired_gap':g,'query_upper':2+ph/a,'target_margin':g/a,'density_upper':F(27,2)*K/a}

# The root-balanced family is affine in x=1/s; reconstruct the threshold
# from the general coefficients without the oracle's damaged fractions.
def specialize_root(coeff):
 return coeff[0]+coeff[1]/3, coeff[2]/75+coeff[3]/3
root_a=specialize_root(alpha);root_phi=specialize_root(phi);root_gap=specialize_root(gap)
root_s_threshold=-root_gap[1]/root_gap[0]
req('root_balanced_threshold_positive',root_s_threshold>0)
req('root_balanced_min_geometry_crosses',F(7,50)>root_s_threshold)
req('root_geometry_survivor_lower',F(1,5)-F(1,25)-F(2,125)-F(1,250)==F(7,50))
req('split125_clipped_mass',13*F(4,125)-F(1,250)==F(103,250))
req('split125_root_cap',5*F(4,125)/F(103,250)==F(40,103))
req('split125_cell_cap',F(4,125)/F(103,250)==F(8,103))
req('outside_special_cell_mass',F(1,25)-F(2,125)-F(1,250)==F(1,50))
req('outside_other_cell_mass',F(1,25)-F(1,250)==F(9,250))
req('outside_weight_total',2*F(14,37)+F(9,37)==1)
req('outside_density_special',F(2,37)/F(1,50)==F(100,37))
req('outside_density_others',F(3,37)/F(9,250)<F(100,37))
req('nested_poor_root_mass_lower',F(1,5)-F(2,25)-F(2,125)-F(1,250)==F(1,10))
req('nested_poor_root_mass_upper',F(1,5)-F(2,25)-F(2,125)==F(13,125))
req('nested_rich_root_mass_lower',F(1,5)-F(1,250)==F(49,250))

# Additional fixed depth-four packing arithmetic; geometry is an ordinary proof.
packing_raw=F(1,12)*(1-F(1,5**4))*(1-F(1,7**4))
w5=(1+F(1,5**4))/2
w7=(2+F(1,7**4))/3
packing_product=packing_raw/(w5*w7)
req('packing_raw_depth4',packing_raw==F(4992,60025))
req('packing_normalized_depth4',packing_product==F(124800,501113))
# Test this new finite packing against the retained PA joint NC region.
u=1-w5;v=1-w7
packing_NC_gap=F()
for corner in data['corners']:
 cu,cv=map(pair,corner['pure_removed_masses'])
 weight=(2*u if cu else 1-2*u)*(3*v if cv else 1-3*v)
 packing_NC_gap+=weight*((T-2)*pair(corner['mass_lower'])-pair(corner['query_hinge']))
req('packing_in_retained_joint_NC_region',packing_NC_gap<0)
terminal=data['corners'][-1]
pa_alpha=pair(terminal['mass_lower']);pa_phi=pair(terminal['query_hinge'])
raw_saving=(pa_phi-(T-2)*pa_alpha)/(T-2)
req('terminal_ledger_reconstruction',2+ev(phi,(F(2,5),F(2,25),F(2)))/ev(alpha,(F(2,5),F(2,25),F(2)))==pair(terminal['query_upper']))
req('raw_mixed_saving_positive',raw_saving>0)

result={'input_name':args.input.name,'input_sha256':PIN,'scope':'three fixed new depth-two geometry candidates; one shared later-coordinate low-atom convolution, exact full tails via means',
 'coefficient_order':['constant','q1','q2','K'],'alpha_coefficients':alpha,'Phi_coefficients':phi,'gap_coefficients':gap,'shared_stage_coefficients':stage_coefficients,
 'target':T,'candidates':rows,'root_balanced':{'alpha_coefficients_in_1_over_s':root_a,'Phi_coefficients_in_1_over_s':root_phi,'gap_coefficients_in_1_over_s':root_gap,'s_threshold':root_s_threshold},
 'packing_depth4':{'raw_union':packing_raw,'pure5_mass':w5,'pure7_mass':w7,'normalized_union':packing_product,'joint_NC_gap':packing_NC_gap,'pure5_deficit':F(1,2)-sum((F(2,5**e) for e in range(1,5)),F()),'pure7_deficit':F(1,3)-sum((F(2,7**e) for e in range(1,5)),F())},
 'raw_mixed_saving_needed_with_unchanged_PA_later_ledger':raw_saving,'checks':checks,'passed_count':len(checks)}
args.output.write_text(json.dumps(enc(result),indent=2)+'\n')
print(json.dumps(enc({'passed_count':len(checks),'candidates':{name:{'alpha':r['alpha'],'Phi':r['Phi'],'paired_gap':r['paired_gap'],'query_upper':r['query_upper'],'query_decimal':float(r['query_upper']),'margin_decimal':float(r['target_margin'])} for name,r in rows.items()},'root_threshold':root_s_threshold,'raw_saving':raw_saving,'result':str(args.output)}),indent=2))
