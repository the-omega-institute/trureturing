"""Retained45/75 anchors do not remove the mixed pair-support obstruction.
Report493: exact standard-library reweighting of report492 support.
Reconstructs profile IDs and literal cell-conditional shell laws, no producer
or NPZ import. Checks all221 cell masses and all561 legal45/75 pairs.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from collections import defaultdict
from math import prod
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
SUPPORT=args.input_dir/'mixed_split_pair_support_certificate.json'
CANON=args.input_dir/'all_ternary_two_fibre.json'
SUPPORT_HASH='21835ce8429c77ff3a0debe4e3cfd9d85e807f78abf2dce54ecf9892e65cc449'
CANON_HASH='d9ea8b1d26e598bdf77a12b2465c16942a39e65680adf02a7a305478b0606323'
M7=F(7235955529,450000000000)
ANCHORS=((3,0),(5,0),(9,1),(15,2),(25,1),(27,4))
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
def need(test,msg):
 if not test:raise ValueError(msg)
need(hashlib.sha256(SUPPORT.read_bytes()).hexdigest()==SUPPORT_HASH,'audited support identity')
need(hashlib.sha256(CANON.read_bytes()).hexdigest()==CANON_HASH,'retained legal-phase source identity')
cert=json.loads(SUPPORT.read_text());retained=json.loads(CANON.read_text())
need(F(cert['m7'])==M7,'same support mass threshold')
source_name='common_law_mass_tail.json'
source_hash='3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'
source_raw=(args.input_dir/source_name).read_bytes()
need(hashlib.sha256(source_raw).hexdigest()==source_hash,'same complete source identity')
source=json.loads(source_raw)['common_seven_core_law']
need(F(source['unnormalized_mass_lower'])==M7,'same complete source mass')
need(tuple(map(F,source['conditional_caps']))==tuple(c for p,c in CAPS),'same conditional caps')

def load(s):
 a=prod(max(1,v) for v in s[:3]);b=prod(max(1,-v) for v in s[:3])
 return (a+b-1)*prod(s[3:])
allrows=[]
def complete(s):
 if len(s)==7:allrows.append(s);return
 for factor in range(1,39):
  t=s+(factor,)
  if load(t)>38:break
  complete(t)
factors=list(range(2,39))+list(range(-2,-39,-1))
for a,b,c in product(factors,factors+[0],[0]+factors):
 if load((a,b,c))<=38:complete((a,b,c))
need(len(allrows)==23408,'complete finite profile count')
rows=[s for s in allrows if load(s)>=20];need(len(rows)==20076,'middle profile count')
S={rows[i] for i in cert['indices']};need(len(S)==12705,'fixed support size')
@lru_cache(None)
def later(s):
 ans=F(1)
 for j,((p,C),z) in enumerate(zip(CAPS,s)):
  baseline=(z==0) if j==0 else (z==1)
  ans*=1-(2 if j==0 else 1)*C/p if baseline else C*F(p-1,p**abs(z))
 return ans
# U contains all Q>=39; its complement is therefore exactly these finite
# missing profiles. Retain only the probability of their last5 factors.
complement=defaultdict(F)
for s in allrows:
 if s not in S:complement[s[:2]]+=later(s[2:])
need(all(0<=v<=1 for v in complement.values()),'conditional later probabilities')

# Given ONE literal initial residue cell, calculate conditional shell laws.
# This is cell->profiles, independently of the producer's profiles->cells sum.
@lru_cache(None)
def conditional_shell(p,E,residue,ref):
 if residue!=ref:
  diff=residue-ref;v=0
  while diff%p==0:diff//=p;v+=1
  return ((v+1,F(1)),)
 return tuple((f,F((p-1)*p**E,p**f)) for f in range(E+1,39))

cells=[n for n in range(675) if all(n%m!=a for m,a in ANCHORS)]
need(len(cells)==221,'literal six-cylinder complement')
pay={}
for n in cells:
 x,y=n%27,n%25
 sign3=1 if x%3==2 else -1;ref3=2 if sign3==1 else 7
 sh3=tuple((sign3*f,w) for f,w in conditional_shell(3,3,x,ref3))
 if y%5 in (3,4):
  sign5=1 if y%5==3 else -1;ref5=3 if sign5==1 else 4
  sh5=tuple((sign5*f,w) for f,w in conditional_shell(5,2,y,ref5))
 else:sh5=((0,F(1)),)
 missed=sum((w3*w5*complement[s3,s5] for s3,w3 in sh3 for s5,w5 in sh5),F())
 need(0<=missed<=1,'literal cell complement probability')
 pay[n]=(1-missed)/675
total=sum(pay.values(),F());need(total==F(cert['total_mass']),'audited complete support mass')

# Selected source legality only prohibits overlap with selected proper
# divisors; incomparable45/75 may intersect. This is exactly483 AT2.
def legal(m):
 divisors=[(d,a) for d,a in ANCHORS if m%d==0 and d<m]
 return [r for r in range(m) if all(r%d!=a for d,a in divisors)]
legal45,legal75=legal(45),legal(75)
need(legal45==retained['legal45'] and len(legal45)==17,'all17 legal45 phases')
need(legal75==retained['legal75'] and len(legal75)==33,'all33 legal75 phases')
computed=[]
for r,s in product(legal45,legal75):
 # Use inclusion-exclusion on the actual retained221 cell payoffs.
 removed45=sum((pay[n] for n in cells if n%45==r),F())
 removed75=sum((pay[n] for n in cells if n%75==s),F())
 overlap=sum((pay[n] for n in cells if n%45==r and n%75==s),F())
 mass=total-removed45-removed75+overlap
 kept=sum(n%45!=r and n%75!=s for n in cells)
 computed.append({'r45':r,'r75':s,'retained_cells':kept,'support_mass':str(mass),'excess':str(mass-M7)})
maximum=max(computed,key=lambda r:F(r['support_mass']));minimum=min(computed,key=lambda r:F(r['support_mass']))
above=sum(F(r['support_mass'])>M7 for r in computed);equal=sum(F(r['support_mass'])==M7 for r in computed)
need(above==77 and equal==0 ,'exact77 strict surviving candidates')
need((maximum['r45'],maximum['r75'])==(31,16) and (minimum['r45'],minimum['r75'])==(38,53),'extreme phase identities')
out={'verified':True,'method':'Independent standard-library profile enumeration, cell-conditional shells and inclusion-exclusion over actual45/75 cells; no producer or NPZ imported.','support_sha256':SUPPORT_HASH,'legal_source_sha256':CANON_HASH,'source_inputs':{source_name:source_hash},'legal45':legal45,'legal75':legal75,'m7':str(M7),'six_anchor_mass':str(total),'support_vertices':len(S),'literal_initial_cells':len(cells),'phase_pairs':len(computed),'strictly_above_m7':above,'equal_m7':equal,'strictly_below_m7':len(computed)-above-equal,'maximum':{**maximum,'support_mass_float':float(F(maximum['support_mass'])),'excess_float':float(F(maximum['excess']))},'minimum':{**minimum,'support_mass_float':float(F(minimum['support_mass']))},'rows':computed,'cell_payoffs':[[n,str(pay[n])] for n in cells],'support_proof_rerun':False,'Lean_rerun':False,'boundary':'Keeps the same fixed upward support and complete worst-coarse source lower bound. Only the upper comparison retains45/75 exclusions. This support remains above m7 in77 charts; the484 other charts eliminate this support only, not all possible supports. Neither outcome constructs an actual congruence cover or settles the original remaining class. No new Lean verification.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'retained exact result differs')
print(json.dumps({k:out[k] for k in ('phase_pairs','strictly_above_m7','equal_m7','strictly_below_m7','maximum')},indent=2))
