#!/usr/bin/env python3
"""One fixed actual head supports the complete three-parent network.
The rational cell selector is evaluated exactly against all512 query charges.
The raw-source omitted-coordinate factor replaces the smaller factor appropriate
to658's separately thinned source. All full-height/tail caps are inherited.
No uniform arbitrary-phase theorem or Lean verification is claimed.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
from hashlib import sha256
from argparse import ArgumentParser
import json
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
BASE=args.directory
paths=[BASE/'linear15_exact_boundary_obstruction.json',BASE/'joint_square_pair_225_star_certificate.json']
raw=[p.read_bytes() for p in paths]; old,net=map(json.loads,raw)
checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c: raise RuntimeError(k)
ck('canonical652_pass',old['status']=='PASS' and old['fixture_originals']==183)
ck('canonical658_pass',net['status']=='PASS' and net['branch_parameters']['parents']==[3,5,7])
ck('pinned652_exact_source',sha256(raw[0]).hexdigest()=='7645e344c353bcf2eedd4a903b0267db66e792f38e141f46b03cdc1b5bfe653d')
ck('pinned658_complete_schedule',sha256(raw[1]).hexdigest()=='cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5')
ck('fixed_actual_corner',old['corner']==[3,4,5,6])
D=10**6
# A fixed exact selector witness. No optimization or floating input is used.
numerators=[966039,918245,1000000,958417,986710,951684,933500,872698,954559,898451,689518,898451,898451,699130,1000000,1000000,1000000,1000000,848449,948053,858053,948053,895843,727672,904046,904046,883616,904046,966039,898451,1000000,898451,889158,822226,986710,954549,957429,898451,898451,689518,708741,888839,951118,951118,951118,951118,507006,951118,951118,951118,951118,1000000,853865,1000000,1000000,693681,771626,906039,840079,842616,951118,1000000,1000000,545602,1000000,1000000,1000000,1000000,1000000,1000000,923571,1000000,864708,867940,990133,1000000,604023,1000000,1000000,941579]
ck('fixed_admissible_rational_selector',all(isinstance(n,int) and 0<=n<=D for n in numerators))
theta=[F(n,D) for n in numerators]
w=[F(0) if l==3 else F(1,9) if l==4 else F(2,9) for l in range(6)]
v=[F(0) if m==5 else F(3,75) if m==6 else F(4,75) for m in range(20)]
cells=[(l,m) for l in range(6) for m in range(20) if w[l] and v[m] and not(l<3 and m<5)]
ck('complete_eighty_theta',len(theta)==len(cells)==80)
H=[[F(x) for x in row] for row in old['induced_responses']]
C=[F(x) for x in old['complete512_coefficients']]
def menus(weights,root,deep):
 out=[[weights],[[x if root(i)==a else F(0) for i,x in enumerate(weights)] for a in sorted({root(i) for i in range(len(weights))})],[],[]]
 for i,x in enumerate(weights):
  if x:
   out[2].append([x if j==i else F(0) for j in range(len(weights))])
   out[3].append([deep if j==i else F(0) for j in range(len(weights))])
 return out
sx=menus(w,lambda l:l//3,F(1)); sy=menus(v,lambda m:m//5,F(4,5))
g=F(200163067,201247200)
mass=g*sum(w[l]*v[m]*H[0][i]*theta[i] for i,(l,m) in enumerate(cells))
fees=[]
for j,c in enumerate(C):
 mode,T=divmod(j,32)
 responses=[]
 for x in sx[mode//4]:
  for y in sy[mode%4]:
   responses.append(sum((x[l]*y[m]*H[T][i]*theta[i] for i,(l,m) in enumerate(cells) if x[l] and y[m]),F(0)))
 best=max(responses)
 ck('nonnegative_complete_selector_max',best>=0 and c>=0)
 fees.append(c*best)
gate=mass-sum(fees,F(0)); perturb=F(old['central_capacity_perturbation']); robust=gate-perturb
ck('below_old_certified_dual_upper',gate<=F(old['exact_corner_gate_upper']))
# Raw652 unary source has no fixedD thinning. Atq>7 only removing the forced
# root1 uniformly givesD_raw=(q-2)/(q-1). Never use658's smallerD here.
Q=(7,11,13,17,19)
D_raw={q:F(q-2,q-1) for q in Q}
zeta_raw=prod(D_raw[q] for q in Q if q!=7)
zeta_old=F(net['branch_parameters']['factor'])
ratio=zeta_raw/zeta_old
ck('omitted_mass_factor_grows',ratio>1)
finite=F(net['finite_fee_upper'])*ratio
unchanged=F(net['complete_five_parent_tail'])+F(net['ordinary_typeI_fee'])
ck('reconstruct_old_prefee',F(net['finite_fee_upper'])+unchanged==F(net['fee_before_arbitrary']))
policies=[]
alpha=F(net['projection_alpha'])
for p in net['policies']:
 cost=finite+unchanged+F(p['fee'])
 margin=robust-cost
 ck('new_complete_network_comparison',margin>0)
 ck('uniform_central_capacity_density',alpha*margin>F(1,35000))
 policies.append(dict(kind=p['kind'],K=p['K'],new_complete_fee=str(cost),new_complete_fee_decimal=float(cost),raw_margin=str(margin),raw_margin_decimal=float(margin),projected_margin=str(alpha*margin),projected_margin_decimal=float(alpha*margin)))
result=dict(schema='fixed652-rational-thinning-complete-network-v1',status='PASS',scope='Fixed183 original layout and all admitted central laws within its existing capacity ball. No uniform arbitrary phase theorem. Ordinary-source/tail bridge must accompany arithmetic.',new_lean_verification=False,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),source_files=[p.name for p in paths],source_hashes=list(map(lambda r:sha256(r).hexdigest(),raw)),theta_denominator=D,theta_numerators=numerators,cells=cells,complete512_fees=list(map(str,fees)),exact_gate=str(gate),exact_gate_decimal=float(gate),uniform_capacity_perturbation=str(perturb),robust_gate_lower=str(robust),robust_gate_lower_decimal=float(robust),old_fixed_network_fee=old['r4_network_budget'],raw_omitted_mass_factor=str(zeta_raw),old_omitted_mass_factor=str(zeta_old),finite_fee_scale=str(ratio),finite_fee_upper=str(finite),finite_fee_upper_decimal=float(finite),policies=policies,checks=checks,check_count=sum(checks.values()))
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','exact_gate_decimal','robust_gate_lower_decimal','raw_omitted_mass_factor','finite_fee_upper_decimal','check_count')}))
for p in policies: print(json.dumps({k:v for k,v in p.items() if k.endswith('decimal') or k in ('kind','K')}))
