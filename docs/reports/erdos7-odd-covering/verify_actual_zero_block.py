#!/usr/bin/env python3
"""Exact actual-AP13 fixture: physical global max and killed full-test bounds.

All finite state sums are exact. Global optimality and complete-domain
upper bounds use the ordinary pair-cap and tensor proof in marked_head_profile.md (ZB1--ZB8).
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from math import prod,gcd
from hashlib import sha256
from pathlib import Path
import argparse,json

HERE=Path(__file__).resolve().parent
Q=3**8*5*7*11*13
OTHER=(5,7,11,13)
P=[F(1,2)]+[F(1,3**j) for j in range(1,8)]+[F(1,2*3**7)]

def need(ok,message):
 if not ok:raise ArithmeticError(message)

def divisors():return sorted(3**a*prod(q**b for q,b in zip(OTHER,bits)) for a in range(9) for bits in product((0,1),repeat=4))

def literal(d,p,old,root):
 residue=(old+d*((root-old)*pow(d,-1,p)%p))%(d*p)
 need(residue%d==old%d and residue%p==root%p,'literal CRT class')
 return (d*p,residue)

def digest(value):return sha256(json.dumps(value,separators=(',',':')).encode()).hexdigest()

def compute():
 ds=divisors();need(len(ds)==144 and len(set(ds))==144 and ds[-1]==Q,'full old labels')
 unit_count=2*3**7*prod(q-1 for q in OTHER)
 density=F(Q,unit_count);S=prod(1+F(3,q-1) for q in OTHER)
 G3=sum(P[j]*(j+1)**2 for j in range(9));G=S*G3
 need(sum(P)==1 and density==F(1001,384) and S==F(273,64) and G==F(795613,46656),'exact actual source')
 other_states=[]
 for bits in product((0,1),repeat=4):
  probability=prod(F(1,q-1) if bit else 1-F(1,q-1) for q,bit in zip(OTHER,bits))
  other_states.append((2**sum(bits),probability))
 source_T81=sum(pr*ps*max(F(((j+1)*v)**2-81),F(0)) for j,pr in enumerate(P) for v,ps in other_states)
 pins={'certificates/shared_square_continuation_certificate.json':'529f2cf3470505f0b37b2c36d6aca5333f93dffa841bb305c6d4f2d3e6b1235d','certificates/shared_cell_square_certificate.json':'26530cd48f6244cd8622efdaed09f5af77375b6e4152e122dec2ebf798d61925'}
 sources={}
 for name,pin in pins.items():
  raw=read_artifact_bytes(HERE/name);need(sha256(raw).hexdigest()==pin,'source SHA-256: '+name)
  sources[name]=json.loads(raw,object_pairs_hook=unique)
 obs=sources['certificates/shared_square_continuation_certificate.json']['source'];checks=[]
 M=F(obs['mean']);need(M>0 and G<M*M,'uniform complete mean via Cauchy-Schwarz')
 checks.append({'observation':'mean','square_upper':G,'upper_squared':M*M,'squared_slack':M*M-G})
 def check(name,value,upper):
  upper=F(upper);need(value<upper,'strict source bound: '+name)
  checks.append({'observation':name,'derived_upper':value,'published_upper':upper,'slack':upper-value})
 check('square',G,obs['Gamma13'])
 need(set(obs['hinges'])=={str(h) for h in range(1,18)},'all seventeen hinges')
 for h in range(1,18):check('H'+str(h),G/(4*h),obs['hinges'][str(h)])
 targets=sources['certificates/shared_cell_square_certificate.json']['targets']
 need(len(targets)==2 and {row['tau'] for row in targets}=={16,81},'two square-hinge targets')
 for row in targets:check('T'+str(row['tau']),G,row['supported_hinge'])
 need(len(checks)==21,'all twenty-one source observations')
 rows=[]
 for p in (17,19):
  delta=F(7,p-2);g=[1/(1-min(F(j,p-1),delta)) for j in range(9)]
  beta=[max(F(j,p-1)-delta,F(0))/(1-delta) for j in range(9)]
  t=[v/(p-1) for v in g];q=[1-v for v in beta]
  need(all(g[j]>=g[j-1] for j in range(1,9)) and beta[:8]==[F(0)]*8 and beta[8]==F(1,p-1),'nested current weights and charge')
  for j in range(9):
   bad_density=beta[j]/j if j else F(0)
   masses=[F(0)]+[bad_density if 1<=y<=j else t[j] for y in range(1,p)]
   need(sum(masses)==1 and sum(masses[1:j+1])==beta[j] and masses[p-1]==t[j],'actual row kernel and clean root')
  b=sum(P[j]*beta[j] for j in range(9));Jt=sum(P[j]*t[j]*(j+1)**2 for j in range(9))
  physical=S*(G3+3*Jt)
  w=[qj+tj for qj,tj in zip(q,t)]
  caps=[sum(P[j]*w[j] for j in range(9))];choices=[]
  for a in range(1,9):
   off=F(1,2*3**(a-1))*w[a-1]
   spine=sum(P[j]*w[j] for j in range(a,9))
   caps.append(max(off,spine));choices.append('spine' if spine>=off else 'off')
  Bw=sum((2*a+1)*cap for a,cap in enumerate(caps))
  upper=S*(Bw+2*Jt)
  wt=[qj+3*tj for qj,tj in zip(q,t)]
  center=S*sum(P[j]*wt[j]*(j+1)**2 for j in range(9))
  lower=S*(sum(P[j]*wt[j]*(j+1)**2 for j in range(7))+P[8]*(wt[7]*(81+64)+wt[8]*64))
  need(center<lower<=upper<physical-b,'strict killed improvement and global extra loss')
  mixed=[literal(3**j,p,1,j) for j in range(1,9)]
  forbidden=[(d,0) for d in ds if d>1]+[(p,0)]+mixed
  need(len(forbidden)==152 and len({m for m,r in forbidden})==152,'distinct original forbidden moduli')
  tests=[]
  for old in (1,1+Q//3):
   current=[(d,old%d) for d in ds]+[literal(d,p,old,p-1) for d in ds]
   need(len(current)==288 and len({m for m,r in current})==288,'full independent-label test domain')
   tests.append(digest(current))
  pure_saving=[F(p-1,p-2)*v-F(p,p-1)*v for v in g]
  need(all(v>0 for v in pure_saving),'positive actual pure-density cap saving')
  rows.append({'prime':p,'full_period':Q*p,'forbidden_count':len(forbidden),'test_label_count':288,
    'mixed_literal_classes':mixed,'forbidden_sha256':digest(forbidden),'physical_center_test_sha256':tests[0],'killed_spur_test_sha256':tests[1],
    'row_good_density':g,'row_charge':beta,'assigned_bad_mass':b,'physical_global_square':physical,
    'killed_square_lower':lower,'killed_square_upper':upper,'killed_interval_width':upper-lower,
    'physical_maximizer_killed_square':center,'spur_killed_improvement':lower-center,
    'physical_minus_killed_max_lower':physical-upper,'max_loss_over_bad_mass_lower':(physical-upper)/b,
    'weighted_pair_cap_choices':choices,'positive_current_frontier_exact':3*S*Jt,'F403_exact':403*b+3*S*Jt,
    'actual_pure_cap_saving_by_row':pure_saving})
 need(rows[0]['max_loss_over_bad_mass_lower']==F(49231,192) and rows[1]['max_loss_over_bad_mass_lower']==F(1716897,7040),'exact nontrivial full-test loss factors')
 base19=rows[1];factor=F(19,16);ds17=sorted(ds+[17*d for d in ds])
 history_forbidden=[(d,0) for d in ds17 if d>1]+[(19,0)]+base19['mixed_literal_classes']
 need(len(ds17)==288 and len(history_forbidden)==296 and len({m for m,r in history_forbidden})==296,'explicit17 history original labels')
 embedding={'full_period':Q*17*19,'incoming17_Haar_density':density*F(17,16),'incoming17_complete_square':G*factor,
   'physical17_charge':F(0),'assigned19_bad_mass':base19['assigned_bad_mass'],'test_label_count':576,'forbidden_count':296,
   'forbidden_sha256':digest(history_forbidden),'factor':factor,
   'F19_403_exact':403*base19['assigned_bad_mass']+factor*base19['positive_current_frontier_exact']}
 for name in ('physical_global_square','killed_square_lower','killed_square_upper','killed_interval_width','physical_minus_killed_max_lower','max_loss_over_bad_mass_lower','positive_current_frontier_exact'):
  embedding[name]=factor*base19[name]
 return {'schema':'actual-ap13-zero-block-boundary-v1','source_sha256':pins,'source_observation_checks':checks,'source':{'period':Q,'uniform_survivor_count':unit_count,'Haar_density':density,'complete_square_exact':G,'centered_test_square_hinge81':source_T81,'other_prime_square_factor':S},'rows':rows,'p19_with_explicit_physical17_history':embedding,
   'scope':'One genuine actual AP13 family for each p17/19. Direct cases have288 original labels; p19 also has an explicit physical17 extension with576 labels and zero17 mixed charge. Physical maximum proved, killed full-test maximum bracketed. Zero-block physical anchoring can have equality with positive charge. Positive killed savings remain; no generic AP13 frontier inequality or unrestricted claim.'}

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [encode(v) for v in x]
 return x

def unique(pairs):
 out={}
 for k,v in pairs:need(k not in out,'duplicate JSON key');out[k]=v
 return out

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');parser.add_argument('--certificate',type=Path,default=HERE/'certificates/actual_zero_block_certificate.json');args=parser.parse_args()
 result=encode(compute())
 if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
 else:need(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)==result,'complete certificate match')
 print('PASS actual AP13 source, all original labels, both global physical maxima and killed full-test brackets')
