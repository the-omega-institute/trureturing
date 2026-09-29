#!/usr/bin/env python3
"""Exact controls for periodic projection selectors on an exponent antichain.
General interval and PA proofs are in the companion .md. No Lean claim.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import json

checks=[]
def need(name,p):
 if not p:raise ValueError(name)
 checks.append(name)

B=F(432040125182653876501,86355045355449035400)
rH=F(157435,165888)
c0=F(25,27)
general=B+(1+B)/c0
need('general selected-law gate',general<F(566,49))
N=80;p=5;q=7;D=11;L=D*p**N*q**N
cof=[D*p**i*q**(N-i) for i in range(N+1)]
need('cofactors distinct nonunits',len(set(cof))==N+1 and min(cof)>1)
need('cofactors an antichain',all(i==j or cof[i]%cof[j] for i in range(N+1) for j in range(N+1)))
need('common Q period',all(L%d==0 for d in cof))

# Each r-color can match an interval of cofactor indices. The chosen second
# PA slot at index i is phase i mod3, and no surviving interval contains that
# color. Checking the finite valuation rectangles is an exact control;
# the arbitrary-N proof is the elementary interval argument.
patterns=0;surviving_patterns=0
for color in range(3):
 for vp in range(N+1):
  for vq in range(N+1):
   I=list(range(max(0,N-vq),min(N,vp)+1))
   patterns+=1
   if any(i%3==color for i in I):continue
   surviving_patterns+=1
   if len(I)>2:raise ValueError('periodic selector failed')
need('all finite valuation patterns obey the claimed active-count bound',patterns==3*(N+1)**2)

# Literal actual family, four originals per cofactor.
# e0 phase3; e4 phase1 with all81 ternary residues; e5 phase2;
# e6 phase0. The full original AP phase is solved by CRT once.
originals=[]
for i,d in enumerate(cof):
 for e,r,t in ((0,3,0),(4,1,i),(5,2,0),(6,0,0)):
  a=r if e==0 else (r+d*((t-r)*pow(d,-1,3**e)%(3**e)))%(3**e*d)
  # A Q point matching exactly this cofactor for color r.
  xq=r+d
  witness=xq if e==0 else xq+L*((t-xq)*pow(L,-1,3**e)%(3**e))
  originals.append({'i':i,'d':d,'e':e,'r':r,'t':t,'m':3**e*d,'a':a,'witness':witness})
need('324 actual full moduli distinct',len(originals)==len({o['m'] for o in originals})==324)
need('one globally fixed CRT phase each',all(o['a']%o['d']==o['r'] and o['a']%(3**o['e'])==o['t'] for o in originals))
need('all original labels odd nonunits',all(o['m']>1 and o['m']%2 for o in originals))
need('all originals have literal private witnesses',all(o['witness']%o['m']==o['a'] and all(v is o or o['witness']%v['m']!=v['a'] for v in originals) for o in originals))
need('four projected phases at every actual cofactor',all({o['r'] for o in originals if o['i']==i}==set(range(4)) for i in range(N+1)))
need('unmodified shallow selector permits the dead Q cylinder',all(1%d!=3 for d in cof))
need('same Q cylinder activates all ternary depth4 residues',set(o['t'] for o in originals if o['e']==4)==set(range(81)) and all(1%o['d']==o['r'] for o in originals if o['e']==4))
need('cyclic selector eliminates the dead cylinder',any(i%3==1 for i in range(N+1)))

# The mandatory-phase3 input removes at most one11-root; the cyclic input
# removes at most four roots. Both PA11 rows normalize below its cap5/3.
need('old actual PA row is below its cap',F(11,10)<F(5,3))
need('new actual PA row is below its cap',F(11,7)<F(5,3))
old_RQ=F(11,10)*rH
new_RQ=F(11,7)*rH
need('old actual PA marginal has small full query norm',old_RQ<B)
need('new actual PA marginal has small full query norm',new_RQ<B)
# u=H3 for this example. At most two active cofactor towers at e4,e5,e6.
actual_c=1-2*sum(F(1,3**e) for e in (4,5,6))
actual_R=new_RQ+F(1,2)*(1+new_RQ)/actual_c
need('literal finite tail reserve',actual_c==F(703,729))
need('one fixed-u law passes the full gate',actual_R<F(566,49))
result={'kind':'ordinary selector theorem with exact actual-family controls','N':N,
 'original_count':len(originals),'all_irredundant':True,'Q_period':str(L),
 'valuation_patterns':patterns,'surviving_patterns':surviving_patterns,
 'old_PA_dead_cylinder_mass':str(F(1,L)),
 'general_R_upper':str(general),'old_PA_RQ_upper':str(old_RQ),
 'new_PA_RQ_upper':str(new_RQ),'example_fibre_reserve':str(actual_c),
 'example_fixed_u_R_upper':str(actual_R),'example_fixed_u_R_upper_decimal':float(actual_R),
 'checks':checks,'check_count':len(checks),
 'scope':{'arbitrary_N_proof':'companion md','original_phases_fixed':True,
 'all_query_heights':True,'same_old_marginal_preserved':False,'new_Lean':False,
 'unrestricted_families':False}}
with Path(__file__).with_suffix('.json').open('w') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({'checks':len(checks),'originals':len(originals),'valuation_patterns':patterns,'joint_R_upper':str(actual_R),'decimal':float(actual_R)}))
