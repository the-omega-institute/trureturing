#!/usr/bin/env python3
"""Exact first-root marginal fibre counterexample on actual109.

Pinned raw originals only. Construct eight entire CRT cylinders, all disjoint
from every one of109 original classes. Compare even-parity retention with
one-half retention on the same eight cylinders. Both obey0<=f<=1 under the
same fixed reference; central and every unary/pair projection agree, but a
complete triple-root screen differs. No full-gate optimum or new separator.
"""
import json,argparse
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,gcd
from hashlib import sha256

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();BASE=args.base
PINS={'clustered_global_phase_fixture.json':'4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
      'clustered_higher_pure_capacity_obstruction.json':'bbf9d977613f469b387cf60b7024092a9903b17bbac4374316c87d87c442bb99'}
def read(name):
 raw=(BASE/name).read_bytes()
 if sha256(raw).hexdigest()!=PINS[name]:raise ValueError('pinned source mismatch: '+name)
 return json.loads(raw)

orig=read('clustered_global_phase_fixture.json')['actual_originals']
high=read('clustered_higher_pure_capacity_obstruction.json')['first_tested_success']
orig+=high['added_higher_pure_originals']
Q=(7,11,13,17,19);P=(3,5)+Q;mods=(9,25)+Q;period=prod(mods)
def crt(res):return sum(r*(period//d)*pow(period//d,-1,d) for r,d in zip(res,mods))%period
atoms=[];checks=0
def ck(cond,label):
 global checks
 checks+=1
 if not cond:raise AssertionError(label)

ck(len(orig)==len({o['modulus'] for o in orig})==109,'literal109 distinct numerical originals')
for bits in product((0,1),repeat=3):
 res=(0,3,2,9+bits[0],9+bits[1],9+bits[2],9)
 residue=crt(res)
 for o in orig:
  ck((residue-o['residue'])%gcd(period,o['modulus'])!=0,'whole cylinder avoids actual original, including all deeper descendants')
 atoms.append({'bits':bits,'residue':residue,'retention_even':F(sum(bits)%2==0),'retention_half':F(1,2)})
ck(len({a['residue'] for a in atoms})==8,'eight disjoint actual cylinders')
# These central leaves are nonweak occupied leaves; their actual source mass
# is the stated reference density times their complete Haar leaf capacity.
central_mass=F(1)
for p,residue in ((3,0),(5,3)):
 row=next(r for r in high['capacities'] if r['prime']==p)
 ck(residue!=row['weak_leaf_residue'],'nonweak central leaf')
 central_mass*=F(row['reference_density'])/p**2
unit=central_mass*prod(F(1,q-1) for q in Q)
def mass(kind,event):return sum((a['retention_'+kind]*unit for a in atoms if event(a['residue'])),F(0))
total=mass('even',lambda _:True)
ck(total==mass('half',lambda _:True),'same total')
for residue in range(225):
 ck(mass('even',lambda z:z%225==residue)==mass('half',lambda z:z%225==residue),'same full central mod225 marginal')
for p in P:
 for residue in range(p):
  ck(mass('even',lambda z:z%p==residue)==mass('half',lambda z:z%p==residue),'same first-root unary marginal')
for p,q in combinations(P,2):
 for a,b in product(range(p),range(q)):
  ck(mass('even',lambda z:z%p==a and z%q==b)==mass('half',lambda z:z%p==a and z%q==b),'same complete root pair table')
event=lambda z:z%11==9 and z%13==9 and z%17==9
left,right=mass('even',event),mass('half',event)
ck(left==unit and right==unit/2 and left!=right,'different actual unselected triple event')
# Report689(P2),(P4): for these whole first-root cylinders, source and field
# are uniform in ALL deeper digits. A height-e query in a selected root has
# mass equal to its first-root mass divided by q**(e-1). On normalizing by
# u_q(1)=1/(q-1), u_q(e)=1/((q-2)*q**(e-1)), its multiplier is q-1 at e=1
# and q-2 at EVERY e>=2. Thus the following8 root/deep patterns represent the
# full unbounded height supremum exactly, rather than truncate its height.
triples=(11,13,17);screens={};winning={}
for kind in ('even','half'):
 best=F(-1);winner=None
 for bits in product((0,1),repeat=3):
  first=mass(kind,lambda z:all(z%q==9+b for q,b in zip(triples,bits)))
  for deep in product((0,1),repeat=3):
   value=first*prod(q-1-flag for q,flag in zip(triples,deep))
   ck(value<=first*prod(q-1 for q in triples),'every deep normalized query is dominated by same first-root tuple')
   if value>best:best=value;winner={'bits':bits,'deep_flags':deep}
 screens[kind]=best;winning[kind]=winner
ck(screens['even']==F(2,18225) and screens['half']==F(1,18225),'exact complete mode0 support14 screens')
ck(screens['even']==2*screens['half'],'complete allheight screen factor2 separation')
out={'status':'PASS','checks':checks,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'source_sha256':PINS,
 'cylinder_period':period,'source_mass_per_cylinder':str(unit),'each_retained_mass':str(total),
 'central_mod225':153,'fixed_root7':2,'variable_roots':{'11':[9,10],'13':[9,10],'17':[9,10]},'fixed_root19':9,
 'same_observations':['central mod225 joint marginal','all7 first-root unary marginals','all21 first-root pair marginals'],
 'different_triple_event':{'moduli':[11,13,17],'residues':[9,9,9],'even_mass':str(left),'half_mass':str(right)},
 'complete_screen14':{'central_mode':0,'outside_support_mask':14,'outside_primes':list(triples),
                     'even':str(screens['even']),'half':str(screens['half']),'ratio':'2','winning_queries':winning,
                     'allheight_coverage':'Analytic cancellation reduces every e>=2 to multiplier q-2, strictly below the first-root q-1; no numerical height truncation.',
                     'definition_source':'Report689(P2),(P4), equivalent Report682 section2'},
 'selected_joined33_charge':'same by the already proved Report699 factorization; not recomputed',
 'conclusion':'The Report699 marginal boundary does not determine the complete remaining screen14, even on actual109. This is an exact full allheight-screen counterexample, not merely a differing named row. No full-gate maximum/obstruction asserted.',
 'no_lean':True}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
