#!/usr/bin/env python3
"""Finite diagnostics for a proved selector-envelope boundary.
No Lean; no claim that finite tests prove the arbitrary-N construction.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

checks=[]
def need(name,ok):
 if not ok:raise ValueError(name)
 checks.append(name)

def color(a):
 r=sum(i*x for i,x in enumerate(a))%7
 return 0 if r<2 else (1 if r<4 else 2)

# Each 6-term nonzero-step progression omits only one of seven residues.
# The three residue groups have sizes2,2,3.
line_tests=0
for start in range(7):
 for step in range(1,7):
  colors={0 if (start+k*step)%7<2 else (1 if (start+k*step)%7<4 else 2) for k in range(6)}
  if colors!={0,1,2}:raise ValueError('six-point root direction failed')
  line_tests+=1
need('all modular root direction tests',line_tests==42)

# Arbitrary colorings, not merely linear ones, on the N=1 simplex.
colorings=0
for c in product(range(3),repeat=6):
 counts=[c.count(j) for j in range(3)]
 j=min(range(3),key=lambda a:counts[a])
 subset=[i for i in range(6) if c[i]!=j]
 if len(subset)<4 or any(c[i]==j for i in subset):raise ValueError('arbitrary coloring lower bound failed')
 colorings+=1
need('every N1 coloring has a missing-color four-point slice',colorings==729)

B=F(432040125182653876501,86355045355449035400)
G=F(566,49)
threshold=27*(1-(1+B)/(G-B))
need('incidence gate permits exactly positive integers1 and2',2<threshold<3)
values={M:B+(1+B)/(1-F(M,27)) for M in [2,3,4]}
need('M2 passes but M3 andM4 fail the retained direct lift',values[2]<G<values[3]<values[4])
# H=4 pure comb has41 surviving depth4 cells. At least one has mass1/41;
# all deeper descendants force an extra half of that mass in complete tails.
Amin=F(31,32);theta_min=F(3,82)
relaxed_lower=B+Amin*(1+B)/(1-4*theta_min)
need('arbitrary pure source still fails the M4 cap envelope at H4',relaxed_lower>G)
need('exact H4 relaxed lower',relaxed_lower==F(380921733986167047569097,32239216932700973216000))

result={'scope':'Geometric selector and uniform-incidence complete-tail-cap certificate only; no obstruction to actual joint laws, weighted selectors or phase-sensitive estimates.',
 'checks':checks,'check_count':len(checks),'N1_colorings':colorings,'modular_progressions':line_tests,
 'explicit_uniform_upper':3125,'universal_uniform_lower':4,
 'incidence_threshold':str(threshold),'direct_lift_values':{str(m):str(x) for m,x in values.items()},
 'pure_H4_A_lower':str(Amin),'pure_H4_theta_lower':str(theta_min),'pure_H4_relaxed_certificate_lower':str(relaxed_lower)}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'check_count':len(checks),'N1_colorings':colorings,'modular_progressions':line_tests,'pure_H4_lower':str(relaxed_lower)}))
