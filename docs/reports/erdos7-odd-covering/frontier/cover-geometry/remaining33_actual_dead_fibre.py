#!/usr/bin/env python3
"""One actual empty central fibre, with an explicit global survivor.
Finite exact counterexample to preserving every old positive fibre.
Not a covering system or a universal remaining33 result.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from hashlib import sha256
checks={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 checks[k]=True
# Central leaf indices(1,11) give residues3mod9,7mod25, hence57mod225.
mods=[(3,2),(5,4),(7,0),(9,1),(25,1),(15,0),(45,0),(75,0),(225,0),
      (21,15),(35,2),(105,87),(315,102),(525,432),(1575,1182)]
ck('15_distinct_odd_numerical_moduli',len(mods)==len({m for m,a in mods})==15 and all(m>1 and m%2 and 0<=a<m for m,a in mods))
ck('central_leaf_and_crt',57%9==3 and 57%25==7)
for m,a in mods:
 if m%7:ck('central_cell_avoids_'+str(m),57%m!=a)
linear=[(m,a)for m,a in mods if m%7==0 and m!=7]
for i,(m,a)in enumerate(linear,1):
 d=m//7
 ck('global_central_projection_'+str(m),a%d==57%d)
 ck('distinct_live_root_'+str(m),a%7==i)
points=[x for x in range(225*7)if x%225==57]
ck('exact_seven_point_fibre',len(points)==7)
incidences=[]
for x in points:
 hits=[m for m,a in mods if x%m==a]
 ck('all_fibre_points_covered_'+str(x),len(hits)==1)
 incidences.append({'residue_mod1575':x,'root7':x%7,'covering_modulus':hits[0]})
ck('global_survivor3',all(3%m!=a for m,a in mods))
z=1-6*F(1,6)-3*F(1,35)
ck('new_fullslot_budget_negative',z==-F(3,35))
out={'schema':'remaining33-fixedstar-actual-dead-fibre-v1','status':'PASS','scope':'One actual15-original family with the fixed631 STAR central roles on present slots; three new linear stars from remaining33 make one old positive cell truly empty. Not a global cover and not a uniform33 certificate.',
 'central_cell':{'leaf_indices':[1,11],'residue_mod225':57,'old_theta':'1'},'originals':[{'modulus':m,'residue':a}for m,a in mods],
 'fibre':incidences,'global_uncovered_integer':3,'new_uniform_fullslot_Z7':str(z),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'checks':checks,'check_count':len(checks),'new_lean_verification':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
