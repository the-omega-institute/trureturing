#!/usr/bin/env python3
"""Exact actual-head distortion bridges and a shared-cap envelope obstruction."""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json

PRIMES=(11,13,17,19,23,29)
DELTAS=(F(7,22),F(5,14),F(23,60),F(17,40),F(25,54),F(1,2))
PURE=((3,0),(9,1),(5,0),(7,0))
FAMILIES=(PURE,
 PURE+((15,11),(45,2),(21,1),(63,58),(35,3),(105,74),(315,187)),
 PURE+((15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)))
SIZES=(120,75,85)
EXACT_MINIMA=(None,F(187297,166896),F(51419,45828))


def need(ok,message):
 if not ok:raise RuntimeError(message)


def cylinder_caps(atoms,moduli):
 return {m:max(sum((w for x,w in atoms.items() if x%m==a),F(0))
               for a in range(m)) for m in moduli}


def calculate(witness_path=None):
 if witness_path is None:
  witness_path=Path(__file__).resolve().with_name('fibre_credit_depth_two_distortion_witnesses.json')
 data=json.loads(witness_path.read_text())
 need(data['primes']==list(PRIMES),'same six outside primes')
 r={0:F(0)}
 for row in data['subset_lowers']:
  mask,value=row['mask'],F(row['lower'])
  need(mask not in r and 1<=mask<64 and value>0,'unique positive subset lower')
  r[mask]=value
 need(set(r)==set(range(64)),'every subset including empty')
 quadratics=0
 for mask in range(1,64):
  for i,q in enumerate(PRIMES):
   if not mask>>i&1:continue
   previous=r[mask^(1<<i)]
   a=F(3*q-1,(q-1)**2);b=F(1,4*(q-1)**2)
   A=r[mask]-previous;B=(1+a)*previous-r[mask]
   need(A>0 and B*B-4*A*b<=0,'quadratic bounds every scalar parameter for this next prime')
   quadratics+=1
 comparison=F(1,19)
 need(quadratics==192 and r[63]==F(105794741,2000000000)>comparison,
      'strict lower for all720 orders and all scalar parameters')
 factor,beta=F(1),F(0)
 steps=[]
 for q,delta in zip(PRIMES,DELTAS):
  loss=factor/F(4*delta*(1-delta)*(q-1)**2)
  beta+=loss
  factor*=1+F(3*q-1,(q-1)**2)/(1-delta)
  steps.append(dict(prime=q,delta=str(delta),loss_coefficient=str(loss),next_moment_factor=str(factor)))
 need(beta==F(571565231731969973,10805159902521600000),'declared constructive six-prime coefficient')
 C6=F(35,4)*beta
 need(C6==F(571565231731969973,1234875417431040000),'Haar-seed comparison value')
 inverse_density=prod((1-d for d in DELTAS),start=F(1))
 need(inverse_density==F(24679,591360),'pointwise kernel density conversion')
 modes={}
 for j,e,f in product(range(3),range(2),range(2)):
  if not j+e+f:continue
  m=3**j*5**e*7**f
  lift=(F(5,4) if e else 1)*(F(7,6) if f else 1)
  square=(2*j+1)*(F(35,8) if e else 1)*(F(35,9) if f else 1)
  modes[m]=(lift,square,lift-1+comparison*square)
 need(len(modes)==11 and len(data['cases'])==3,'complete nonunit first-mode menu and fixed cases')
 rows=[];bridges=[]
 for index,(family,size,case) in enumerate(zip(FAMILIES,SIZES,data['cases'])):
  need(case['originals']==[list(x) for x in family],'literal original numerical labels and phases')
  need(len({m for m,a in family})==len(family),'distinct originals')
  need(all(m>1 and m%2 and 315%m==0 and 0<=a<m for m,a in family),'odd normalized actual head originals')
  live=[x for x in range(315) if all(x%m!=a for m,a in family)]
  need(len(live)==size,'actual head survivors')
  p={int(x):F(w) for x,w in case['primal_atoms'].items()}
  need(p and set(p)<=set(live) and all(w>=0 for w in p.values()) and sum(p.values(),F(0))==1,
       'one supported common primal probability table')
  caps=cylinder_caps(p,modes)
  deep=sum(((modes[m][0]-1)*caps[m] for m in modes),F(0))
  gamma=1+sum((modes[m][1]*caps[m] for m in modes),F(0))
  upper=deep+comparison*gamma
  budgets={m:F(0) for m in modes};coverage={x:F(0) for x in live};seen=set()
  for term in case['dual_terms']:
   m,a,w=term['modulus'],term['phase'],F(term['weight'])
   need(m in modes and 0<=a<m and w>=0 and (m,a) not in seen,'nonnegative unique dual cylinder')
   seen.add((m,a));budgets[m]+=w
   for x in live:
    if x%m==a:coverage[x]+=w
  need(all(budgets[m]<=modes[m][2] for m in modes),'all eleven dual mode budgets')
  lower=comparison+min(coverage.values())
  need(lower<=upper,'exact weak duality including unit constant')
  if index:
   need(lower==upper==EXACT_MINIMA[index] and lower>1,'exact common-source envelope minimum exceeds one')
  else:
   need(upper<1,'lower-comparison-coefficient control is nonvacuous')
  rows.append(dict(name=case['name'],actual_survivors=size,primal_atoms=len(p),dual_terms=len(seen),
   dual_cell_checks=len(live),dual_budget_checks=len(modes),primal_deep_loss=str(deep),
   primal_second_moment_cap=str(gamma),lower=str(lower),upper=str(upper),exact_minimum=lower==upper,
   margin_above_one=str(lower-1),universal_envelope_obstruction=index>0))
  if index:
   uniform={x:F(1,size) for x in live}
   ucaps=cylinder_caps(uniform,modes)
   ugamma=1+sum((modes[m][1]*ucaps[m] for m in modes),F(0))
   expected=(F(23053,1350),F(21163,1224))[index-1]
   need(ugamma==expected,'uniform actual-head complete quadratic cylinder cap')
   reserve=1-beta*ugamma
   support=F(size,315)
   need(reserve>0 and support<C6,'positive arbitrary-outside bridge but Haar-domination shortcut impossible')
   density=reserve*support*inverse_density
   bridges.append(dict(name=case['name'],head_classes=11,head_survivors=size,head_Haar_mass=str(support),
    second_moment_cap=str(ugamma),survivor_mass_lower=str(reserve),Haar_density_lower=str(density),
    Haar_density_lower_decimal=float(density),scope='These eleven are the COMPLETE 3,5,7-only original subfamily. All further originals must involve at least one of the six outside primes; their phases and nonternary heights are arbitrary, whole-family v3<=2.'))
 return dict(scope='Finite distinct odd original moduli, support within3,5,7,11,13,17,19,23,29, whole-family v3<=2. Positive bridges forbid additional357-only originals. Negative certificates concern only the declared shared prefix-Haar source, complete deep union debit and separate-cylinder second-moment envelope.',
  parameter_scope='All720 orders of the six outside primes and one scalar delta per step in(0,1), jointly chosen with the source.',
  excluded_scope='Does not exclude first/second-moment hybrids, actual joint Gamma, sharper propagation, row-dependent parameters, other source classes or other distortion constructions.',
  all_order_beta_lower=str(r[63]),comparison_beta=str(comparison),quadratic_checks=quadratics,subset_states=64,
  constructive_beta=str(beta),Haar_seed_comparison=str(C6),inverse_kernel_density_cap=str(inverse_density),
  constructive_steps=steps,mode_fees={str(m):str(modes[m][2]) for m in sorted(modes)},
  exact_envelope_cases=rows,positive_bridges=bridges,
  evidence='Ordinary mathematical derivations and exact rational certificate verification, not new Lean verification or unrestricted Erdős#7 resolution.')


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate()))
 rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if args.output is None:
  retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
  need(retained==result,'retained distortion result agrees with exact replay')
  print(rendered,end='')
 else:
  args.output.write_text(rendered)


if __name__=='__main__':main()
