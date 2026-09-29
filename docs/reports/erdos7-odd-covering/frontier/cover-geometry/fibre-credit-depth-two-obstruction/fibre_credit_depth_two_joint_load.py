#!/usr/bin/env python3
"""Exact finite checks for prefix-Haar actual joint-load reduction."""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

HEADS={
 'opposite':[(3,0),(9,1),(5,0),(7,0),(15,11),(45,2),(21,1),(63,58),(35,3),(105,74),(315,187)],
 'same':[(3,0),(9,1),(5,0),(7,0),(15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)]}
ROWS={'opposite':[23,128,233,268],'same':[17,52,122,227]}

def crt(parts):
 m=prod(d for d,a in parts)
 return next(x for x in range(m) if all(x%d==a for d,a in parts))

def slots(E,Fh):
 return [(j,e,f,3**j*5**e*7**f,3**j*5**bool(e)*7**bool(f))
         for j,e,f in product(range(3),range(E+1),range(Fh+1))]

def zerolift(slot,alpha):
 j,e,f,d,flat=slot
 parts=[(3**j,alpha%3**j)]
 if e:parts.append((5**e,alpha%5))
 if f:parts.append((7**f,alpha%7))
 return crt(parts)

def direct(weights,sl,layout,E,Fh):
 Q=9*5**E*7**Fh
 numerator=sum(weights[x%315]*sum(x%s[3]==a for s,a in zip(sl,layout))**2 for x in range(Q))
 return F(numerator,sum(weights)*5**(E-1)*7**(Fh-1))

def pair_formula(weights,sl,alphas):
 total=F(0);den=sum(weights)
 for s,a in zip(sl,alphas):
  for t,b in zip(sl,alphas):
   coeff=F(1,5**max(0,max(s[1],t[1])-1)*7**max(0,max(s[2],t[2])-1))
   mass=sum(w for x,w in enumerate(weights) if x%s[4]==a and x%t[4]==b)
   total+=coeff*F(mass,den)
 return total

def calculate():
 out={'scope':'Exact ordinary finite checks; no new Lean verification.',
      'prefix_reduction_checks':[],'coherent_counterexamples':[]}
 for name,head in HEADS.items():
  live=[x for x in range(315) if all(x%m!=a for m,a in head)]
  need(len(live)=={'opposite':75,'same':85}[name],'actual complete legal head count')
  rows=ROWS[name]
  need(set(rows)<=set(live),'all four source rows avoid every actual original')
  need(len({x%5 for x in rows})==len({x%7 for x in rows})==1,'fixed nonternary roots')
  weights=[(37 if x%9==7 else 21) if x in rows else 0 for x in range(315)]
  need(sum(weights)==100,'one actual probability source')
  sl=slots(1,1);r5=rows[0]%5;r7=rows[0]%7
  witness=[]
  for j,e,f,d,flat in sl:
   parts=[(3**j,0 if j==0 else (2 if j==1 else 7))]
   if e:parts.append((5,r5))
   if f:parts.append((7,r7))
   witness.append(crt(parts))
  val=direct(weights,sl,witness,1,1)
  need(val==64,'incompatible ternary query layout has constant load eight')
  reduced={f'{a},{b}':sum(F(weights[x],100)*(4*(1+(x%3==a)+(x%9==b)))**2 for x in rows)
           for a in range(3) for b in range(9)}
  need(max(reduced.values())==64,'all 27 pure ternary pairs after Jensen reduction')
  coherent={a:direct(weights,sl,[a%s[3] for s in sl],1,1) for a in range(315)}
  need(max(coherent.values())==F(1584,25),'exhaust all coherent anchors')
  out['coherent_counterexamples'].append(dict(head=name,actual_originals=[{'m':m,'a':a} for m,a in head],
    legal_head_size=len(live),source=[{'row':x,'mass':str(F(weights[x],100))} for x in rows],
    maximizing_query_layout=[{'m':s[3],'a':a} for s,a in zip(sl,witness)],
    exact_Gamma='64',coherent_max='1584/25',gap='16/25',
    reduced_ternary_pair_values={k:str(v) for k,v in reduced.items()},
    coherent_anchors_checked=315))
  weights=[1+(29*x)%101 if x in live else 0 for x in range(315)]
  sl=slots(2,2)
  checks=[]
  for seed in range(8):
   alphas=[(13*k*k+17*k+19*seed+seed*k)%s[4] for k,s in enumerate(sl)]
   zero=[zerolift(s,a) for s,a in zip(sl,alphas)]
   arbitrary=[(a+s[4]*((seed+7*k*k+3*k)%max(1,s[3]//s[4])))%s[3]
              for k,(s,a) in enumerate(zip(sl,alphas))]
   need(all(a%s[4]==alpha for a,s,alpha in zip(arbitrary,sl,alphas)),'arbitrary layout has same first phases')
   upper=pair_formula(weights,sl,alphas)
   exact=direct(weights,sl,zero,2,2)
   other=direct(weights,sl,arbitrary,2,2)
   need(exact==upper and other<=exact,'all-pair upper attained by one zero lift')
   checks.append({'seed':seed,'zero_lift_and_pair_value':str(exact),'arbitrary_lift_value':str(other)})
  out['prefix_reduction_checks'].append({'head':name,'period':9*5**2*7**2,'numerical_divisor_slots':27,
    'full_live_source_weight':sum(weights),'nonproduct_source':'weight 1+(29*x)%101 on actual legal residues',
    'layouts':checks})
 for q in (5,7):
  limit=F(q*(3*q-1),(q-1)**2)
  for h in range(1,9):
   finite=sum(F(2*t+1,q**(t-1)) for t in range(1,h+1))
   tail=F(1,q**h)*(F((2*h+3)*q,q-1)+F(2*q,(q-1)**2))
   need(finite+tail==limit,'complete geometric tail identity')
 out['complete_geometric_tail_identity_checks']=16
 return out


def main():
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 result=json.loads(json.dumps(calculate()))
 rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if args.output is None:
  retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
  need(retained==result,'retained result agrees with exact reconstruction')
  print(rendered,end='')
 else:
  args.output.write_text(rendered)

if __name__=='__main__':main()
