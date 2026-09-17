#!/usr/bin/env python3
"""Exact killed-law core bounds, complete energy tails and finite frontier budgets.

All original prime heights are covered by the ordinary KC proof. This
standard-library verifier checks exact rational coefficients, twelve
actual-root branches, both complete cutoffs and every saved certificate
field. No numerical solver, finite-period enumeration or Lean claim.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from math import prod,isqrt
import json

HERE=Path(__file__).resolve().parent
PINS={
 'certificates/shared_cell_hinges_certificate.json':'e5661edc37f4c133dd72f1ba51563908e8f02cc9cefa1ca15d319188591fc6ae',
 'certificates/pure_root_profile_certificate.json':'64cca3231e75e3356eac5202196db65ecc03beca27bbe9d290d21c89b3960751',
 'certificates/ap_core_stability_certificate.json':'338f6868753a5b2c321e20ef34bdadb2c52a78550c14e5f59cbc28177bdc1b46',
}

def require(condition,message):
 if not condition:raise ArithmeticError(message)

def unique(pairs):
 d={}
 for k,v in pairs:
  require(k not in d,'duplicate JSON key: '+k);d[k]=v
 return d

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [encode(v) for v in x]
 return x

def phi(p,a):return F((a+1)**2)+F(2*(a+1),p-1)+F(p+1,(p-1)**2)
def sigma(p):return F(p*(p*p+4*p+1),(p-1)**3)
def t0(p,b):return F(1,(p-1)*p**b)
def t2(p,b):return F(1,p**b)*(F((b+2)**2,p-1)+F(4*b+7,(p-1)**2)+F(3*(p+1),(p-1)**3))
def factors(box,w):
 full=prod(sigma(p) if w else F(p,p-1) for p,b in box)
 head=prod((sigma(p)-t2(p,b)) if w else (F(p,p-1)-t0(p,b)) for p,b in box)
 unit=prod(phi(p,0) if w else F(1) for p,b in box)
 require(all((sigma(p)-t2(p,b) if w else F(p,p-1)-t0(p,b)) == sum((F(1,p**a)*(phi(p,a) if w else 1) for a in range(b+1)),F()) for p,b in box), 'complete tail vs literal finite head')
 return full-head,head-unit

def step(p,T,box,k,D,J,w):
 s=F(p-2,p-1);delta=F(T-1,p-2);C=1/(1-delta);lip=max(C*C,C/delta)
 old_tail,head=factors(box,w);z=phi(p,0) if w else F(1)
 pos=sigma(p)-z if w else F(1,p-1);tail=t2(p,k) if w else t0(p,k)
 old=D*old_tail*(C/s*pos+lip/s**2*z/F(p-1))
 mixed=D*head*(C/s*tail+lip/s**2*z*t0(p,k))
 pure=J*(C/s*tail+(lip+C)/s**2*z*t0(p,k))
 return old+mixed+pure

def incoming(box):
 b3=box[:3];b4=box[:4];p11,k11=box[3];p13,k13=box[4]
 e0w=D0*(G0*factors(b3,False)[0]+factors(b3,True)[0]);e0m=2*D0*factors(b3,False)[0]
 ew=F(55,36)*(F(23,15)*e0w+step(11,4,b3,k11,D0,G0,True))+step(13,6,b4,k13,F(5,3)*D0,F(23,15)*G0,True)
 em=e0m+step(11,4,b3,k11,D0,F(1),False)+step(13,6,b4,k13,F(5,3)*D0,F(1),False)
 return (ew+G*em)/rho,2*em/rho

def testtail(box):
 full=prod(F(p*(p+1),(p-1)**2) for p,k in box)
 head=prod(1+sum(F(2*a+1,p**a) for a in range(1,k+1)) for p,k in box)
 return F(18,5)*D*(full-head)

def evaluate(box,current=None):
 k17,k19=current or (box[5][1],box[6][1])
 a2=step(17,8,box[:5],k17,D,G,True);a0=step(17,8,box[:5],k17,D,F(1),False)
 b2=step(19,8,box[:6],k19,2*D,F(89,64)*G,True);b0=step(19,8,box[:6],k19,2*D,F(1),False)
 ew,em=incoming(box[:5]);test=testtail(box)
 mask=F(59,45)*a2+b2+483*(a0+b0)
 src=F(5251,2880)*ew+242*em
 total=mask+src+test
 return dict(box=box,current=(k17,k19),steps=[a2,a0,b2,b0],source=[ew,em],incoming_mass_coefficient=242,mask=mask,incoming=src,test=test,total=total,test_labels=prod(k+1 for p,k in box))

def cost(branch,tau,last=False):
 require(isinstance(tau,int) and tau>=1,'finite correction uses a positive integer square threshold')
 u=list(map(F,branch['reference_pure_masses']))
 scale=F(branch['uniform357_Haar_density_bound'])*prod(u)/rho
 caps=list(zip([3,5,7],[1/v for v in u]))+[(11,F(5,3)),(13,F(2))]+([(17,F(2))] if last else [])
 second=prod(1+c*F(3*p-1,(p-1)**2) for p,c in caps)
 N=isqrt(tau-1);probs={1:F(1)}
 for p,c in caps:
  nxt={}
  for n,w in probs.items():
   for k in range(1,N//n+1):
    v=(1-c/p if k==1 else c*F(p-1,p**k))
    nxt[n*k]=nxt.get(n*k,F(0))+w*v
  probs=nxt
 tail_mass=1-sum(probs.values(),F());tail_second=second-sum((n*n*w for n,w in probs.items()),F())
 require(tail_mass>=0 and tail_second>=(N+1)**2*tail_mass,'complete auxiliary probability and second-moment tail')
 return dict(bound=scale*(tail_second-tau*tail_mass),scale=scale,full_second=second,probabilities=probs,tail_mass=tail_mass,tail_second=tail_second)


def main():
 global G0,D0,G,D,rho
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/killed_core_continuity_certificate.json')
 parser.add_argument('--source-directory',type=Path,default=HERE)
 parser.add_argument('--write',action='store_true')
 args=parser.parse_args();src={}
 for n,pin in PINS.items():
  raw=read_artifact_bytes(args.source_directory/n);require(sha256(raw).hexdigest()==pin,'source SHA-256: '+n)
  src[n]=json.loads(raw,object_pairs_hook=unique)
 PR=src['certificates/pure_root_profile_certificate.json'];HC=src['certificates/shared_cell_hinges_certificate.json']['same_actual_AP13_consumer']
 G0,D0=F(3849,106),F(432,53)
 G,D,rho=map(F,[HC['supported_square'],HC['supported_Haar_density'],HC['survival_lower']])
 require((HC['T11'],HC['T13'])==(4,6),'same actual AP(4,6) construction')
 require(G0==F(PR['source_inputs']['G']) and D0==1/F(PR['source_inputs']['survivor_density_lower']),'same actual357 inputs')
 ps=[3,5,7,11,13,17,19]
 rows=[evaluate(list(zip(ps,[20]*7)),(8,8)),evaluate(list(zip(ps,[17,10,8,7,6,6,6])),(6,6))]
 safe=[F(667,1000000),F(263,1000)]
 APC=src['certificates/ap_core_stability_certificate.json']
 predecessor=next(r for r in APC['rows'] if r['box']==20)
 require(rows[0]['source']==[F(predecessor['normalized_weighted_error']),F(predecessor['normalized_L1_error'])], 'same AP incoming variation')
 require([rows[0]['steps'][0],rows[0]['steps'][2]]==list(map(F,APC['full_finite_reference']['mask_step_epsilons'])), 'same full weighted mask tails')
 for r,budget in zip(rows,safe):
  require(0<r['total']<budget,'strict complete killed-Q error budget')
  r['safe_allowance']=budget;r['safety_slack']=budget-r['total']
  r['Q_criterion']='For every retained original family pattern and every complete box test, integral (L_box^2-484) d eta_core <= -safe_allowance.'
  box=r['box'];cur=r['current'];P5=prod(k+1 for p,k in box[:5]);P6=prod(k+1 for p,k in box[:6])
  r['forbidden_label_count_upper']=[P5-1,cur[0]*P5,cur[1]*P6]
  r['common_period']=prod(p**max(k,cur[0] if p==17 else cur[1] if p==19 else k) for p,k in box)
 require(rows[1]['test_labels']==4889808 and sum(rows[1]['forbidden_label_count_upper'])==4889807,'complete unequal-box label counts')
 energy=[]
 require(len(PR['branches'])==12,'all original missing-class branches')
 for tau,last in [(81,False),(1024,False),(1024,True)]:
  branch_rows=[cost(b,tau,last) for b in PR['branches']]
  best=max(r['bound'] for r in branch_rows);i=next(i for i,r in enumerate(branch_rows) if r['bound']==best)
  require(i==11,'same effective9/allroots branch controls these three bounds')
  energy.append(dict(tau=tau,physical17=last,branches=branch_rows,maximum=best,maximizing_branch=i))
 T81=energy[0]['maximum']
 require(T81==F(27462732511027063792077002926276002,234516374824438312292389830652525),'full square hinge at81')
 clip=F(35,192)*energy[1]['maximum']+F(98,765)*energy[2]['maximum']
 require(clip<F(13607,1000),'actual-row1024 clip error below13.607')
 require(F(25,128)*1024*2==400 and F(14,81)*1024*F(9,5)==F(14336,45),'HK1024 convexity thresholds')
 for r,frontier_safe in zip(rows,[F(285895,1000),F(285633,1000)]):
  r['tau']=81;r['W']=403;r['source_square_hinge']=T81
  r['available_frontier_budget']=403-T81-r['safe_allowance']
  require(frontier_safe<r['available_frontier_budget'],'safe killed-frontier sufficient threshold')
  r['sufficient_frontier_bound']=frontier_safe
 result=encode(dict(schema='erdos7-killed-core-continuity-v1',source_sha256=PINS,
  source_inputs=dict(G357=G0,D357=D0,Gamma13=G,D13=D,rho13=rho),rows=rows,
  energy_tail_bounds=energy,actual_row_1024_clip_error=clip,
  clip_scope='Only the pointwise HK minus unclipped cap cost under the actual old input laws. It does not bound every subsequent auxiliary/Jensen/supremum relaxation loss.',
  scope='Same actual AP13 construction, normalized physical and killed17/8,19/8 kernels; full original residues/heights and all missing classes. Complete source-law, forbidden-mask and test tails. The new criterion concerns killed Q, not the APC physical-square-plus-assigned-charge functional.',
  open_mathematical_obligations='No maximum of either finite killed core or the two Xi frontiers is computed. Neither a Gamma19<484 theorem nor later-prime continuation or unrestricted Erdos7 resolution follows without that inequality. Ordinary proof and exact arithmetic, no Lean endpoint.'))
 if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
 else:require(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)==result,'entire certificate equality')
 print('PASS killed-Q full core errors '+str([float(r['total']) for r in rows])+'; unequal box labels '+str(rows[1]['test_labels'])+'; T13(81) '+str(float(T81))+'; actual-row clip error '+str(float(clip)))

if __name__=='__main__':main()
