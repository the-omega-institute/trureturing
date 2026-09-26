#!/usr/bin/env python3
"""Independent rational selector-budget certificate for the free-qs response obstruction.
No optimizer or other implementation is imported. Matchings are enumerated directly.
"""
import argparse, hashlib, itertools, json
from fractions import Fraction as F
from math import prod
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--certificate',type=Path,default=Path(__file__).with_name('free_qs_matching_response_obstruction.json'))
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
p.add_argument('--phase-witness',type=Path,default=Path(__file__).with_name('free_qs_matching_response_obstruction_verification.json'))
a=p.parse_args();checks={}
def ck(label,truth):
 if not truth:raise ArithmeticError(label)
 checks[label]=checks.get(label,0)+1
raw=a.certificate.read_bytes();w=json.loads(raw)
ck('schema',w['schema']=='free-qs-matching-response-obstruction-v1')
source_raw=(a.directory/w['source640']['filename']).read_bytes()
ck('source_sha256',hashlib.sha256(source_raw).hexdigest()==w['source640']['sha256']=='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4')
source=json.loads(source_raw)
ck('copied_coefficients',w['source640_combined512_coefficients']==source['combined512_coefficients'])
ck('fixed_geometry',(w['nulls'],w['square7_role'],w['weak_corner'],w['primes'],w['alpha_by_lex_edge'])==([3,5],[0,2,4],[4,6],[7,11,13,17,19],[5]*10))
Q=tuple(w['primes']);edges=tuple(itertools.combinations(range(5),2));masks=tuple((1<<i)|(1<<j) for i,j in edges)
matchings=[()]+[(e,) for e in range(10)]+[(e,f) for e,f in itertools.combinations(range(10),2) if not(masks[e]&masks[f])]
ck('matching_inventory',len(matchings)==26)
r=[F(1,q-1) for q in Q];d=[F(1,q*(q-2)) for q in Q]
b=[d[i]*r[j]+r[i]*d[j]+r[i]*r[j] for i,j in edges]
def unary(n):return [F(5,6)-n*F(1,35)]+[F(q-2,q-1)-2*d[k] for k,q in enumerate(Q) if k]
zmin=unary(3)
strict=1-sum((b[e]+r[i]*r[j])/(zmin[i]*zmin[j]) for e,(i,j) in enumerate(edges))
ck('strict_region',strict>0 and str(strict)==w['expected']['strict_whole_box_margin'])
I=[0,1,2,4,5];J=[m for m in range(20) if m!=5]
cells=[(l,m) for l in I for m in J if not(l//3==0 and m//5==0)]
wx={l:F(1 if l==4 else 2,9) for l in I};wy={m:F(3 if m==6 else 4,75) for m in J}
ck('weak_weights',sum(wx.values())==sum(wy.values())==1)
responses=[]
for l,m in cells:
 z=unary(int(l//3==0)+int(m//5==2)+int(l==4))
 beta=[b[e]+r[i]*r[j]*int(l==5) for e,(i,j) in enumerate(edges)]
 h=[]
 for T in range(32):
  value=F(0)
  for matching in matchings:
   used=0
   for e in matching:used|=masks[e]
   if used&T:continue
   value+=(-1)**len(matching)*prod(beta[e] for e in matching)*prod(z[q] for q in range(5) if not((T|used)>>q&1))
  ck('induced_response_positive',0<value<=1);h.append(value)
 responses.append(h)
def selectors(labels,weights,block,root_count,deep):
 return [[dict(weights)], [{x:(weights[x] if x//block==root else F(0)) for x in labels} for root in range(root_count)], [{x:(weights[x] if x==leaf else F(0)) for x in labels} for leaf in labels], [{x:(deep if x==leaf else F(0)) for x in labels} for leaf in labels]]
xs=selectors(I,wx,3,2,F(1));ys=selectors(J,wy,5,4,F(4,5))
menus=[]
for xmode,ymode in itertools.product(range(4),repeat=2):
 menus.append([[x[l]*y[m] for l,m in cells] for x in xs[xmode] for y in ys[ymode]])
ck('literal_selector_inventory',sum(map(len,menus))==559)
g=F(source['constants']['g']);ck('source_coefficient',g==1-F(1084133,201247200))
fees=list(map(F,source['combined512_coefficients']))
for q in range(1,5):fees[9*32+(1<<q)]+=g*d[q]
ck('complete_fee_inventory',len(fees)==512 and min(fees)>=0)
mass=sum(wx[l]*wy[m]*responses[k][0] for k,(l,m) in enumerate(cells))
unit_fee=sum(fees[32*mode+T]*max(sum(vector[k]*responses[k][T] for k in range(len(cells))) for vector in menu) for mode,menu in enumerate(menus) for T in range(32))
unit_gate=g*mass-unit_fee
ck('unit_gate_agreement',str(unit_gate)==w['expected']['unit_gate'])
residual=[g*wx[l]*wy[m]*responses[k][0] for k,(l,m) in enumerate(cells)]
budgets=[F(0)]*512;seen=set();den=w['dual_denominator'];ck('denominator',isinstance(den,int) and den>0)
for mode,T,xindex,yindex,numerator in w['dual_rows']:
 ck('dual_row_in_domain',all(isinstance(v,int) for v in (mode,T,xindex,yindex,numerator)) and 0<=mode<16 and 0<=T<32 and numerator>0)
 xm,ym=divmod(mode,4);ck('selector_indices',0<=xindex<len(xs[xm]) and 0<=yindex<len(ys[ym]))
 key=(mode,T,xindex,yindex);ck('unique_dual_row',key not in seen);seen.add(key)
 lam=F(numerator,den);budgets[32*mode+T]+=lam
 for k,(l,m) in enumerate(cells):residual[k]-=lam*xs[xm][xindex][l]*ys[ym][yindex][m]*responses[k][T]
for total,cap in zip(budgets,fees):ck('selector_fee_budget',0<=total<=cap)
upper=sum(max(F(0),v) for v in residual)
ck('universal_upper_agreement',str(upper)==w['expected']['universal_field_upper'])
ck('strict_obstruction',upper<F(w['expected']['upper_ceiling'])<F(w['expected']['target']))
ck('complete_census',len(cells)==w['expected']['cell_count']==80 and len(seen)==w['expected']['dual_nonzero_count']==354)
phase_raw=a.phase_witness.read_bytes();phase_data=json.loads(phase_raw)
rows=phase_data['actual_phase_witness'];phases={x['modulus']:x['residue'] for x in rows}
ck('phase_labels_unique',len(rows)==len(phases)==105)
expected_labels={3,5,9,15,25}
for modulus,value in phases.items():ck('odd_original_phase',isinstance(modulus,int) and modulus>1 and modulus%2==1 and isinstance(value,int) and 0<=value<modulus)
for modulus,value in {3:2,9:1,5:4,25:1,15:0}.items():ck('central_original',phases[modulus]==value)
for q in Q:
 expected_labels.add(q);ck('outside_pure_original',phases[q]==0)
 for c in (3,5,15,9,25,45,75,225):
  expected_labels.add(c*q);ck('fixed_common_root_star',phases[c*q]%c==0 and phases[c*q]%q==1)
 for c,target in ((3,0),(5,2),(9,4)):
  expected_labels.add(c*q*q);ck('fixed_square_star_phase',phases[c*q*q]%c==target and phases[c*q*q]%(q*q)==2)
for q,s in itertools.combinations(Q,2):
 expected_labels.update((q*s,9*q*s,q*q*s,q*s*s))
 ck('free_qs_phase',phases[q*s]%q==phases[q*s]%s==2)
 ck('global_9qs_phase',phases[9*q*s]%9==7 and phases[9*q*s]%q==phases[9*q*s]%s==3)
 ck('first_square_pair_phase',phases[q*q*s]%(q*q)==4 and phases[q*q*s]%s==4)
 ck('second_square_pair_phase',phases[q*s*s]%q==5 and phases[q*s*s]%(s*s)==5)
 ck('four_edge_events_disjoint',len({(phases[m]%q,phases[m]%s) for m in (q*s,9*q*s,q*q*s,q*s*s)})==4)
ck('complete_phase_inventory',set(phases)==expected_labels)
for l in I:ck('realizable_ternary_leaf_density',0<9*wx[l]<=2 and (l//3+3*(l%3))%3!=2 and l//3+3*(l%3)!=1)
for m in J:ck('realizable_quinary_leaf_density',0<25*wy[m]<=F(4,3) and (m//5+5*(m%5))%5!=4 and m//5+5*(m%5)!=1)
out=dict(schema='free-qs-matching-response-obstruction-independent-v1',status='PASS',new_lean_verification=False,read_verifier_implementation=False,program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),certificate_sha256=hashlib.sha256(raw).hexdigest(),source_sha256=hashlib.sha256(source_raw).hexdigest(),phase_witness_sha256=hashlib.sha256(phase_raw).hexdigest(),actual_phase_witness_count=len(phases),matching_count=len(matchings),cell_count=len(cells),response_count=len(cells)*32,literal_selector_count=sum(map(len,menus)),fee_count=len(fees),dual_nonzero_count=len(seen),strict_matching_margin=str(strict),source_mass=str(mass),complete_unit_fee=str(unit_fee),unit_gate=str(unit_gate),universal_field_upper=str(upper),cell_residuals=[dict(cell=list(cell),coefficient=str(v)) for cell,v in zip(cells,residual)],checks=checks,check_count=sum(checks.values()),scope='All theta in [0,1] on the stated fixed 80-cell matching-response table and corner. This is a comparison-gate obstruction, not an upper bound for actual survivors or a covering example.')
a.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','check_count','unit_gate','universal_field_upper']}))
