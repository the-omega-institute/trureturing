#!/usr/bin/env python3
"""Exact pure-union savings for two fixed PA orders, with realizable pure data.
No cap/order grid, original-family enumeration, repository imports or Lean.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse,json,hashlib

P=(11,13,17,19)
PARAM={11:(2,F(5,3),F(1,3)),13:(2,F(3,2),F(1,4)),17:(4,F(2),F(1,4)),19:(4,F(9,5),F(1,5))}
OLD=P;NEW=(13,11,19,17);T=F(257,51)
checks={}
def require(name,test):
 checks[name]=bool(test)
 if not test:raise ValueError(name)

def hinge(coords,t):
 # Only t=2,3,4 is needed: subthreshold products are1,2,3.
 if t not in (2,3,4):raise ValueError('unsupported threshold')
 mass=prod(w for p,w,c in coords)
 mean=prod(w+c/(p-1) for p,w,c in coords)
 atoms=[(w-c/p,c*(p-1)/p**2,c*(p-1)/p**3) for p,w,c in coords]
 p1=prod(v[0] for v in atoms)
 p2=sum((v[1]*prod(w[0] for j,w in enumerate(atoms) if j!=i) for i,v in enumerate(atoms)),F())
 p3=sum((v[2]*prod(w[0] for j,w in enumerate(atoms) if j!=i) for i,v in enumerate(atoms)),F())
 return mean-t*mass+sum(F(t-n)*z for n,z in enumerate((p1,p2,p3),1) if n<t)

def ledger(order,x,y):
 cs=[(5,x,F(1)),(7,y,F(1))];fs={};charges={}
 for q in order:
  t,c,a=PARAM[q];fs[q]=hinge(cs,t);charges[q]=a*fs[q];cs.append((q,F(1),c))
 alpha=x*y-F(1,12)-sum(charges.values(),F());phi=hinge(cs,3)
 return {'F':fs,'alpha':alpha,'Phi':phi,'G':(T-2)*alpha-phi}

def saving(q,f,theta):
 a=PARAM[q][2];delta=1-theta
 return a*a*f*delta/(1+a*delta)

res={}
for name,order in (('old',OLD),('new',NEW)):
 base=ledger(order,F(1,2),F(2,3));k=-base['G']/(T-2)
 corners={(x,y):ledger(order,x,y) for x,y in product((F(1,2),F(1)),(F(2,3),F(1)))}
 g=base['G'];A5=2*(corners[F(1),F(2,3)]['G']-g);A7=3*(corners[F(1,2),F(1)]['G']-g)
 A57=6*(corners[F(1),F(1)]['G']-g-A5/2-A7/3)
 require(name+'_all_NC4_coefficients_positive',all(v>0 for v in (A5,A7,A57)))
 roots={};single_cut={}
 for q in P:
  rho=F(q+1,2*q);s=saving(q,base['F'][q],rho)
  roots[q]={'theta_upper':rho,'saving_lower':s,'excess':s-k,'sufficient':s>k,'raw_margin_query_upper_when_sufficient':T-(T-2)*(s-k) if s>k else None,'comparison_query_upper':2+base['Phi']/(base['alpha']+s)}
  a=PARAM[q][2];single_cut[q]=1-k/(a*(a*base['F'][q]-k)) if a*base['F'][q]>k else None
 res[name]={'order':order,'F':base['F'],'alpha':base['alpha'],'Phi':base['Phi'],'kreq':k,'c0':-base['G'],'A5':A5,'A7':A7,'A57':A57,'root_at_most_one':roots,'single_row_theta_strict_cutoff':single_cut,'corners':[{'x':x,'y':y,**r} for (x,y),r in corners.items()]}
require('old_kreq',res['old']['kreq']==F(6168733163201163811,1650097635185615616000))
require('new_F13',res['new']['F'][13]==F(97,840))
require('new_F11',res['new']['F'][11]==F(15329,87360))
require('new_F19',res['new']['F'][19]==F(202266823897,1875745872000))
require('new_F17',res['new']['F'][17]==F(19655687364626449,128657409360480000))
require('new_alpha',res['new']['alpha']==F(52945498078747367,514629637441920000))
require('same_Phi',res['old']['Phi']==res['new']['Phi']==F(22496082952171,69510823782400))
require('new_kreq_smaller',0<res['new']['kreq']<res['old']['kreq'])
require('new_kreq_shift_by_mass_gain',res['old']['kreq']-res['new']['kreq']==res['new']['alpha']-res['old']['alpha'])
require('old_single_root_sufficiency',tuple(q for q in P if res['old']['root_at_most_one'][q]['sufficient'])==(11,13))
require('new_single_root_sufficiency',tuple(q for q in P if res['new']['root_at_most_one'][q]['sufficient'])==(11,17))
for name in res:
 for q in P:
  row=res[name]['root_at_most_one'][q]
  require(name+'_query_threshold_equivalence_'+str(q),(row['comparison_query_upper']<T)==row['sufficient'])

# Fixed actual pure originals: j*q^(e-1) modulo q^e for j=1,2 and
# e=1,...,4, except omit j=2 at e=1 for one designated prime.
# All cylinders are disjoint; other original labels may be arbitrary.
witness={}
for omitted_root in (17,13):
 theta={q:1-F(1,q**4)-(F(q-1,2*q) if q==omitted_root else 0) for q in P}
 gamma={name:sum((saving(q,r['F'][q],theta[q]) for q in P),F()) for name,r in res.items()}
 margin={name:gamma[name]-res[name]['kreq'] for name in res}
 require(str(omitted_root)+'_theta_admissible',all(0<=v<=1 for v in theta.values()))
 require(str(omitted_root)+'_opposite_regions',margin['new']>0>margin['old'] if omitted_root==17 else margin['old']>0>margin['new'])
 witness[omitted_root]={'pure_height':4,'omitted_second_root_at':omitted_root,'theta':theta,'Gamma':gamma,'margin_to_own_threshold':margin}
result={'scope':'Two fixed actual PA orders, each with its own kernels and own telescoping savings; bounds from separate orders are alternatives, never summed. Ordinary mathematical proof required; no Lean.','orders':res,'realizable_pure_data_witnesses':witness,'checks':checks,'passed_count':len(checks)}
def encode(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x).__name__)
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=parser.parse_args();args.output.write_text(json.dumps(result,indent=2,default=encode)+'\n')
print(json.dumps({'passed_count':len(checks),'new':res['new'],'witnesses':witness,'data_sha256':hashlib.sha256(args.output.read_bytes()).hexdigest()},indent=2,default=encode))
