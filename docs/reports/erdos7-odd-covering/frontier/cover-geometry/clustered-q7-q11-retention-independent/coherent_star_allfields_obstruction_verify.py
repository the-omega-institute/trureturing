"""Exact all-central-field obstruction for the coherent phase81 count envelope.

Reuse only the rational multipliers of Report682; all current coefficients,
selectors, responses and cell inequalities are reconstructed independently.
No optimizer or producer import is used in this verifier.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


_DEFAULT_INPUT_PATHS = {'clustered_global_phase_fixture.json': '../clustered_global_phase_fixture.json', 'remaining33_global_root_exclusion_certificate.json': '../remaining33_global_root_exclusion_certificate.json'}

def _resolve_input_path(directory, name):
    if directory is not None:
        return directory / name
    return Path(__file__).resolve().parent / _DEFAULT_INPUT_PATHS.get(name, name)

HERE=Path(__file__).resolve().parent
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=None)
parser.add_argument('--output',type=Path,default=HERE/'coherent_star_allfields_obstruction_verify.json')
args=parser.parse_args()
PINS={
 'remaining33_global_root_exclusion_certificate.json':'36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4',
 'clustered_global_phase_fixture.json':'4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
 'clustered_q7_q11_retention_obstruction.json':'89b89676db47826d4c647692527da0656a1f6784d6d38feaca7081f1ad61c028',
}
checks=Counter()
def ck(name,condition):
 checks[name]+=1
 if not condition:raise ArithmeticError(name)
inputs={}
for name,pin in PINS.items():
 raw=(_resolve_input_path(args.directory, name)).read_bytes()
 ck('input_digest',sha256(raw).hexdigest()==pin)
 inputs[name]=json.loads(raw)
C=[F(x) for x in inputs['remaining33_global_root_exclusion_certificate.json']['combined512_coefficients']]
ck('complete512_nonnegative',len(C)==512 and min(C)>=0)
originals=inputs['clustered_global_phase_fixture.json']['actual_originals']
original={x['modulus']:x['residue'] for x in originals}
ck('101_unique_originals',len(originals)==len(original)==101)
for m,residue in original.items():
 ck('odd_reduced_original',m>1 and m%2==1 and 0<=residue<m)
Q=(7,11,13,17,19)
D=(3,5,15,9,25,45,75,225)
g=F(200163067,201247200)
r=[F(1,q-1) for q in Q]
a=[F(1,q*(q-2)) for q in Q]
B=[1-r[i]-(3 if i==0 else 2)*a[i] for i in range(5)]
additions=[]
for i,q in enumerate(Q[1:],start=1):
 C[256+(1<<i)]+=g*a[i]
 additions.append({'mode':8,'support':1<<i,'original_modulus':9*q*q,'coefficient':str(g*a[i])})
for q,d in product(Q,D):
 ck('actual_star_phase81',original[q*d]%d==81%d)
for m,value in ((3,2),(9,1),(5,4),(25,1),(15,0)):
 ck('actual_central_geometry',original[m]==value)

# Physical residue coordinates, then root-major labels for literal selectors.
thirds=[x for x in range(9) if x%3!=2 and x!=1]
fifths=[y for y in range(25) if y%5!=4 and y!=1]
physical=[(x,y) for x,y in product(thirds,fifths) if not(x%3==0 and y%5==0)]
physical.sort(key=lambda c:(3*(c[0]%3)+c[0]//3,5*(c[1]%5)+c[1]//5))
cells=[(3*(x%3)+x//3,5*(y%5)+y//5) for x,y in physical]
crt={(x%9,x%25):x for x in range(225)}
ck('80_live_cells',len(cells)==80)
counts=[tuple(sum(crt[c]%d==original[q*d]%d for d in D) for q in Q) for c in physical]
beta={e:a[e[0]]*r[e[1]]+r[e[0]]*a[e[1]]+2*r[e[0]]*r[e[1]] for e in combinations(range(5),2)}
cache={}
for ns in sorted(set(counts)):
 Z=[max(F(),B[i]-r[i]*ns[i]) for i in range(5)]
 h=[]
 for T in range(32):
  U=set(i for i in range(5) if not(T>>i&1))
  edges=[e for e in beta if set(e)<=U]
  value=prod(Z[i] for i in U)
  value-=sum((beta[e]*prod(Z[i] for i in U-set(e)) for e in edges),F())
  value+=sum((beta[e]*beta[f]*prod(Z[i] for i in U-set(e)-set(f)) for e,f in combinations(edges,2) if not(set(e)&set(f))),F())
  h.append(value)
 cache[ns]=(Z,h)
H=[];valid=[]
for ns in counts:
 Z,h=cache[ns]
 good=all(z>0 for z in Z)
 valid.append(good)
 if good:
  for value in h:ck('all32_valid_cell_responses_positive',value>0)
  H.append(h)
 else:
  ck('invalid_cell_has_zero7_mass',Z[0]==0)
  H.append([F()]*32)
ck('74_admissible_cells',sum(valid)==74)
I=(0,1,2,4,5)
J=tuple(m for m in range(20) if m!=5)
w={l:F(1 if l==4 else 2,9) for l in I}
v={m:F(3 if m==10 else 4,75) for m in J}
source=[g*w[l]*v[m]*h[0] for (l,m),h in zip(cells,H)]

def axis(labels,weights,block,level,deep):
 if level==0:return [(0,weights)]
 if level==1:
  return [(root,{x:weights[x] if x//block==root else F() for x in labels}) for root in range(2 if block==3 else 4)]
 return [(leaf,{x:(weights[x] if level==2 else deep) if x==leaf else F() for x in labels}) for leaf in labels]

selectors={}
for mode in range(16):
 ex,ey=divmod(mode,4)
 for (left,x),(right,y) in product(axis(I,w,3,ex,F(1)),axis(J,v,5,ey,F(4,5))):
  selectors[mode,left,right]=[x[l]*y[m] for l,m in cells]
ck('559_literal_selectors',len(selectors)==559)

# These are reused NUMBERS. Old outside root labels are irrelevant here:
# collapsing them gives legal nonnegative weights on current central selectors.
old=inputs['clustered_q7_q11_retention_obstruction.json']
denominator=old['dual_denominator']
ck('positive_integer_dual_denominator',isinstance(denominator,int) and denominator>0)
dual=defaultdict(F)
for mode,T,q7,q11,left,right,numerator in old['dual_rows']:
 ck('inherited_nonnegative_multiplier',isinstance(numerator,int) and numerator>0)
 ck('literal_selector_address',(mode,left,right) in selectors and 0<=T<32)
 dual[mode,T,left,right]+=F(numerator,denominator)
ck('2568_input_dual_rows',len(old['dual_rows'])==2568)
ck('1733_collapsed_dual_rows',len(dual)==1733)
loads=[F()]*512
debit=[F()]*80
for (mode,T,left,right),lam in sorted(dual.items()):
 loads[32*mode+T]+=lam
 profile=selectors[mode,left,right]
 for j in range(80):
  debit[j]+=lam*profile[j]*H[j][T]
for index,(used,available) in enumerate(zip(loads,C)):
 ck('all512_exact_fee_budgets',0<=used<=available)
residual=[s-d for s,d in zip(source,debit)]
for j in range(80):
 ck('all80_source_dominated',residual[j]<=0)
 if valid[j]:ck('all74_strict_source_dominated',residual[j]<0 and source[j]>0)
 else:ck('all6_zero_cell_vectors',source[j]==debit[j]==0)
upper=sum((max(F(),t) for t in residual),F())
ck('universal_upper_zero',upper==0)
ratios=[(debit[j]/source[j],cells[j]) for j in range(80) if valid[j]]
minimum_ratio,ratio_cell=min(ratios)
ck('strict_minimum_ratio',minimum_ratio>1)
ck('exact_minimum_ratio',minimum_ratio==F(523631189695910122364169377659221,412988045678799323025011875000000))
ck('minimum_ratio_cell',ratio_cell==(5,14))
ck('quarter_source_deficit',minimum_ratio>F(5,4))

# A current-response regression also checks the exact full one field value.
fees=[]
for mode in range(16):
 candidates=[profile for key,profile in selectors.items() if key[0]==mode]
 fee=F()
 for T in range(32):
  screen=max(sum((profile[j]*H[j][T] for j in range(80)),F()) for profile in candidates)
  fee+=C[32*mode+T]*screen
 fees.append(fee)
one_gate=sum(source,F())-sum(fees,F())
ck('old_chi_exact_gate',one_gate==-F(34684038567037034905564050721,275900078820714943795200000000))

result={
 'schema':'coherent-star-allfields-count-envelope-obstruction-v1',
 'status':'PASS','optimizer_used':False,'new_lean_verification':False,
 'input_sha256':PINS,'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'check_count':sum(checks.values()),'checks':dict(sorted(checks.items())),
 'corner':[4,10],'central_nulls':[3,5],'field_coordinates':80,'effective_coordinates':74,
 'field_class':'theta(c) depends only on the central mod9/mod25 cell and is fixed for all query selectors; no outside-root or higher-digit dependence.',
 'count_distribution':[[list(ns),counts.count(ns)] for ns in sorted(set(counts))],
 'charge_additions':additions,'original_dual_rows':2568,'collapsed_dual_rows':len(dual),
 'dual_rows':[[*address,str(lam)] for address,lam in sorted(dual.items())],
 'fee_budgets':[{'index':j,'used':str(loads[j]),'available':str(C[j])} for j in range(512)],
 'cell_inequalities':[{'cell':list(cells[j]),'physical_cell':list(physical[j]),
                       'counts':list(counts[j]),'admissible':valid[j],
                       'source':str(source[j]),'dual_debit':str(debit[j]),
                       'residual':str(residual[j])} for j in range(80)],
 'minimum_debit_source_ratio':str(minimum_ratio),'minimum_ratio_cell':list(ratio_cell),
 'universal_gate_upper':str(upper),'maximum_gate':'0','attained_by':'zero field',
 'one_field_gate':str(one_gate),'one_field_mode_fees':list(map(str,fees)),
 'scope':('At fixed corner(4,10), every nonnegative central field in Report686\'s '
          'phase81 count-matching envelope has corrected full512 gate<=0; every '
          'field positive on an admissible cell has gate<0. The six zero-Z7 cells '
          'are discarded and have identically zero response. Generic deep caps '
          'and fullmode8 residual fees are retained. This is not an upper bound '
          'on outside-dependent retention fields, all actual source constructions '
          'or sharper query envelopes, and '
          'not a covering or nonexistence result.'),
}
args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','checks':result['check_count'],'upper':str(upper),
                  'min_ratio':str(minimum_ratio),'ratio_cell':list(ratio_cell),
                  'collapsed_rows':len(dual)},sort_keys=True))
