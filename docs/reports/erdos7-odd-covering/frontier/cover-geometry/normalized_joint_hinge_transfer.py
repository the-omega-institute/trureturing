#!/usr/bin/env python3
"""Exact all-height normalized PA hinge transfer with joint loss/cap credit.

Low atoms of the anchor are exact and all geometric tails are analytic.
The program never constructs an alternative source between row updates.
It verifies the rational arithmetic of a uniform same-source contract;
the general convex comparison is the mathematical input, not a finite test.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

PIN_PATH='docs/reports/erdos7-odd-covering/profile-notes/321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md'
PIN_SHA='16808a0c59e964ddb42925f727eab9a7f80fa0a4b240e8b614de621ee88147e7'
CHECKS={}

def check(name,ok):
 if name in CHECKS or not ok:
  raise ValueError(name)
 CHECKS[name]=True

def coordinate(p,m,c,H):
 return m,m+c/(p-1),{n:(m-c/p if n==1 else c*F(p-1,p**n)) for n in range(1,H+1)}

def multiply(a,b,H):
 atoms={n:F() for n in range(1,H+1)}
 for i,w in a[2].items():
  for j,v in b[2].items():
   if i*j<=H:
    atoms[i*j]+=w*v
 return a[0]*b[0],a[1]*b[1],atoms

def hinge(law,h):
 return law[1]-h*law[0]+sum(((h-n)*w for n,w in law[2].items() if n<h),F())

def interpolate(theta,t):
 if t<=0:
  return theta[0]-t
 floor=t.numerator//t.denominator
 if t==floor:
  return theta[floor]
 return (floor+1-t)*theta[floor]+(t-floor)*theta[floor+1]

def mean_improvement(theta):
 candidate,j=min((F(j)+v,j) for j,v in enumerate(theta))
 result=theta[:]
 result[0]=candidate
 return result,j

def transfer(theta,q,t,stage):
 H=len(theta)
 C=F(q-1)/(q-1-2*t)
 check(f'cap-domain-{stage}',1<C<q)
 check(f'threshold-domain-{stage}',0<t<=H)
 check(f'integer-threshold-{stage}',t.denominator==1)
 r=int(t)
 a=2*C/(q-1)
 loss=a*interpolate(theta,t-1)
 check(f'loss-domain-{stage}',0<=loss<1)
 mass_lower=1-loss
 vals={n:(F(q-1,q-1-2*n)-C if n<r else F()) for n in range(1,r+2)}
 slopes={n:vals[n+1]-vals[n] for n in range(1,r+1)}
 corr=vals[1]+slopes[1]*theta[0]+sum(
     ((slopes[j+1]-slopes[j])*theta[j] for j in range(1,r)),F())
 out=[]
 moments=[]
 for h in range(1,H+1):
  partial=F()
  finite_mass=F()
  finite_mean=F()
  for n in range(1,h):
   probability=1-C/q if n==1 else C*F(q-1,q**n)
   value=n*interpolate(theta,F(h,n)-1)
   partial+=probability*value
   finite_mass+=probability
   finite_mean+=n*probability
  if h==1:
   tail_mass=F(1)
   tail_mean=1+C/(q-1)
  else:
   tail_mass=C/q**(h-1)
   tail_mean=tail_mass*(h+F(1,q-1))
  check(f'geometric-mass-{stage}-{h}',finite_mass+tail_mass==1)
  check(f'geometric-first-moment-{stage}-{h}',finite_mean+tail_mean==1+C/(q-1))
  tail=tail_mean*(1+theta[0])-h*tail_mass
  numerator=partial+tail
  eta=F(1,q**(h-1)*(q-1))
  value=(numerator+eta*corr)/mass_lower
  check(f'joint-lambda-condition-{stage}-{h}',value>=eta*C)
  coeff={j:eta*(slopes[j+1]-slopes[j])+(value*a if j==r-1 else 0)
         for j in range(1,r)}
  check(f'joint-all-coefficients-{stage}-{h}',eta*slopes[1]>=0 and all(c>=0 for c in coeff.values()))
  check(f'joint-identity-{stage}-{h}',value==numerator+value*loss+eta*corr)
  for n in range(31):
   direct=eta*(F(q-1,q-1-2*(n+1))-C) if n+1<r else value*a*(n+1-r)
   expanded=eta*vals[1]+eta*slopes[1]*n+sum((c*max(0,n-j) for j,c in coeff.items()),F())
   check(f'discrete-convex-expansion-{stage}-{h}-{n}',direct==expanded)
  check(f'positive-hinge-{stage}-{h}',value>=0)
  out.append(value)
  moments.append(dict(h=h,finite=partial,tail=tail,Psi=numerator,eta=eta,
                      corr=corr,combined_hinge_coefficients=coeff,Theta=value))
 out,mean_index=mean_improvement(out)
 check(f'mean-contract-{stage}',all(out[0]<=j+out[j] for j in range(H)))
 return out,dict(q=q,threshold=t,cap=C,a=a,loss_bound=loss,mass_lower=mass_lower,
                 mean_index=mean_index,moments=moments,Theta=out,
                 Theta_first4_decimal=[float(v) for v in out[:4]])

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parents[5])
 parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 args=parser.parse_args()
 check('pin-source',sha256((args.source_dir/PIN_PATH).read_bytes()).hexdigest()==PIN_SHA)
 H=4
 check('enough-hinges',H>=4)
 schedule=[(11,F(2)),(13,F(2)),(19,F(4)),(17,F(4))]
 check('four-distinct-primes',len(schedule)==4 and {q for q,t in schedule}=={11,13,17,19})
 anchors=[]
 for x,y in product((F(1,2),F(1)),(F(2,3),F(1))):
  law=multiply(coordinate(5,x,F(1),H),coordinate(7,y,F(1),H),H)
  lower=x*y-F(1,12)
  anchors.append(dict(x=x,y=y,mass_lower=lower,Theta=[hinge(law,t+1)/lower for t in range(H)]))
 theta=[max(row['Theta'][t] for row in anchors) for t in range(H)]
 for t in range(H):
  check('anchor-worst-'+str(t),theta[t]==anchors[0]['Theta'][t])
 theta,base_mean_index=mean_improvement(theta)
 base=theta[:]
 stages=[]
 for i,(q,t) in enumerate(schedule):
  theta,row=transfer(theta,q,t,i)
  stages.append(row)
 G=F(566,49)
 gate=G-1-2*theta[0]-(3*theta[2]-3+(G-3)*theta[3])/27
 check('strict-source-only-gate',gate>0)
 check('stage-mean-indices',[row['mean_index'] for row in stages]==[0,1,1,1])
 alpha=F(1,4)
 density=F(1)
 for row in stages:
  alpha*=row['mass_lower']
  density*=row['cap']
 haar=F(49,11088)*alpha*gate
 check('same-raw-density-cap',density==9)
 check('positive-raw-mass',alpha>0)
 check('positive-restricted-consumer-mass',haar>0)
 result=dict(scope='Arithmetic audit of a uniformly quantified normalized hinge contract on one actual PA source; arbitrary original phases and all finite heights under the two-copy rule. No Lean claim, no unrestricted Erdos7 conclusion.',
             source_pin={PIN_PATH:PIN_SHA},schedule=schedule,H=H,anchor_corners=anchors,
             anchor=base,anchor_mean_index=base_mean_index,stages=stages,
             B=theta[0],K2=theta[2],K3=theta[3],G=G,source_only_gate=gate,
             raw_Q_mass_lower=alpha,raw_Q_density_cap=density,
             normalized_Q_density_cap=density/alpha,
             restricted_nine_prime_haar_lower=haar,
             B_decimal=float(theta[0]),K2_decimal=float(theta[2]),K3_decimal=float(theta[3]),
             source_only_gate_decimal=float(gate),checks=CHECKS,check_count=len(CHECKS))
 args.output.write_text(json.dumps(result,default=str,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ('schedule','B','K2','K3','source_only_gate','B_decimal','K2_decimal','K3_decimal','source_only_gate_decimal','check_count')},default=str,indent=2))

if __name__=='__main__':
 main()
