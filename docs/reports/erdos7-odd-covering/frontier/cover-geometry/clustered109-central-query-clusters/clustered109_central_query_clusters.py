#!/usr/bin/env python3
"""Exact existing common-label cluster test on actual109 central marginals.

Success criterion fixed before evaluation: a strictly positive difference
between the independent six/three-factor envelope and the exact common-label
maximum is a valid strict correction on this SAME source. If all tested pairs
and triangles vanish, this finite cluster library gives no correction; no
global saturation or impossibility is inferred. No source/field optimization.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from math import lcm,prod
from hashlib import sha256
import argparse,json,numpy as np

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args()
BASE=args.base
checks=0
def ck(v):
 global checks
 checks+=1
 if not v: raise ArithmeticError(checks)
source_name='clustered_exact_actual_source.json'
field=json.loads((BASE/'clustered_actual_boundary_gate_witness.json').read_text())
raw=(BASE/source_name).read_bytes();ck(sha256(raw).hexdigest()==field['source_sha256'][source_name])
source=json.loads(raw);cells={tuple(x['cell']):F(x['H_by_support_and_root7'][0][0]) for x in source['cells']}
fixture_raw=(BASE/'clustered_global_phase_fixture.json').read_bytes()
ck(sha256(fixture_raw).hexdigest()=='4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6')
originals=json.loads(fixture_raw)['actual_originals'];outside=(7,11,13,17,19)
full_witness=json.loads((BASE/'clustered_full5_allfield_dual.json').read_text())
higher_name='clustered_higher_pure_capacity_obstruction.json'
higher_raw=(BASE/higher_name).read_bytes()
ck(sha256(higher_raw).hexdigest()==full_witness['source_sha256'][higher_name])
higher=json.loads(higher_raw)['first_tested_success'];added=higher['added_higher_pure_originals']
ck(len(originals+added)==len({o['modulus'] for o in originals+added})==109)
ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)})
for p,weak,w,ref,cap,gamma in ((3,4,F(1,9),F(2),F(41,729),F(81,82)),(5,2,F(1,25),F(4,3),F(469,15625),F(1875,1876))):
 pp=[(o['modulus'],o['residue']) for o in added if o['modulus']%p==0];depth=max(x[0] for x in pp)
 actual=F(sum(all(x%m!=r for m,r in pp) for x in range(weak,depth,p*p)),depth)
 ck(actual==cap and w/(ref*actual)==gamma==F(higher['gamma'+str(p)]))
local={q:[] for q in outside}
for o in originals:
 cm=o['modulus'];parts=[]
 for q in outside:
  power=1
  while cm%q==0:cm//=q;power*=q
  if power>1:parts.append((q,power))
 if len(parts)==1 and cm>1:
  q,power=parts[0];local[q].append((cm,o['residue']%cm,power,o['residue']%power))
 if len(parts)==2:ck(all(o['residue']%q==1 for q,power in parts))
for q,r in combinations(outside,2):ck(any(o['modulus']==q*r and o['residue']==1 for o in originals))
mass=[F(0)]*225
for (l,m),v in cells.items():
 a=3*(l%3)+l//3;b=5*(m%5)+m//5;x=(100*a+126*b)%225
 ck(x%9==a and x%25==b)
 aa=[];bb=[]
 for q in outside:
  alive=[r for r in range(q*q) if r%q!=0 and all(x%cm!=cr or r%qm!=qr for cm,cr,qm,qr in local[q])]
  aa.append(F(sum(r%q==1 for r in alive),q*(q-1)))
  bb.append(F(sum(r%q!=1 for r in alive),q*(q-1)))
 actual=prod(bb)+sum(aa[i]*prod(bb[j] for j in range(5) if j!=i) for i in range(5))
 ck(actual==v)
 mass[x]=F(2-(l==4),9)*F(4-(m==10),75)*v
ck(sum(mass,F(0))==F(305684996597,646498195200))
D=lcm(*(x.denominator for x in mass));nums=np.array([int(x*D) for x in mass],dtype=np.int64)
ck(15*int(sum(nums))<2**63)
labels=(3,5,9,15,25,45,75,225)
marg={d:np.array([sum(int(nums[x]) for x in range(a,225,d)) for a in range(d)],dtype=np.int64) for d in labels}
maximum={d:int(max(v)) for d,v in marg.items()};joint={}
for d,e in combinations(labels,2):
 table=np.zeros((d,e),dtype=np.int64)
 for x,n in enumerate(nums):table[x%d,x%e]+=n
 joint[d,e]=table
 ck(int(table.max())==maximum[lcm(d,e)])
pairs=[]
for d,e in combinations(labels,2):
 costs=3*marg[d][:,None]+3*marg[e][None,:]+2*joint[d,e]
 best=int(costs.max());ind=3*(maximum[d]+maximum[e])+2*maximum[lcm(d,e)]
 ck(best<=ind)
 a,b=map(int,np.unravel_index(int(costs.argmax()),costs.shape))
 pairs.append({'labels':[d,e],'independent':str(F(ind,D)),'joint_maximum':str(F(best,D)),'defect':str(F(ind-best,D)),'maximizing_phases':[a,b]})
triangles=[]
for d,e,f in combinations(labels,3):
 costs=(3*marg[d][:,None,None]+3*marg[e][None,:,None]+3*marg[f][None,None,:]
        +2*joint[d,e][:,:,None]+2*joint[d,f][:,None,:]+2*joint[e,f][None,:,:])
 best=int(costs.max());ind=3*(maximum[d]+maximum[e]+maximum[f])+2*(maximum[lcm(d,e)]+maximum[lcm(d,f)]+maximum[lcm(e,f)])
 ck(best<=ind)
 phases=list(map(int,np.unravel_index(int(costs.argmax()),costs.shape)))
 triangles.append({'labels':[d,e,f],'independent':str(F(ind,D)),'joint_maximum':str(F(best,D)),'defect':str(F(ind-best,D)),'maximizing_phases':phases,'maximizer_count':int(np.count_nonzero(costs==best))})
positive_pairs=[x for x in pairs if F(x['defect'])>0]
positive_triangles=[x for x in triangles if F(x['defect'])>0]
selected=(positive_pairs or positive_triangles or [None])[0]
if selected:
 ds=selected['labels'];best=-1;best_phase=None
 for phases in product(*(range(d) for d in ds)):
  value=0
  for x,n in enumerate(nums):
   count=sum(x%d==a for d,a in zip(ds,phases))
   value+=int(n)*(count*count+2*count)
  if value>best:best=value;best_phase=phases
 ck(F(best,D)==F(selected['joint_maximum']))
 selected=dict(selected,direct_maximizing_phases=list(best_phase))
oldraw=(BASE/'remaining33_global_root_exclusion_certificate.json').read_bytes()
ck(sha256(oldraw).hexdigest()=='36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4')
old=json.loads(oldraw);c=F(1084133,201247200);g=1-c
coeff=list(map(F,old['combined512_coefficients']))
for i,q in enumerate(outside):
 if i:coeff[256+(1<<i)]+=g/F(q*(q-2))
responses={tuple(x['cell']):[[F(z) for z in row] for row in x['H_by_support_and_root7']] for x in source['cells']}
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5)
menus3=((0,),(0,1),I,I);menus5=((0,),(0,1,2,3),J,J)
screens=[]
for ex,ey,T in product(range(4),range(4),range(32)):
 best=F(0)
 for left,right in product(menus3[ex],menus5[ey]):
  for k in (range(6) if T&1 else (0,)):
   value=F(0)
   for l,m in cells:
    sx=F(2-(l==4),9);sy=F(4-(m==10),75)
    if ex==1:sx*=int(l//3==left)
    if ex==2:sx*=int(l==left)
    if ex==3:sx=(F(81,82) if l==4 else F(1))*int(l==left)
    if ey==1:sy*=int(m//5==right)
    if ey==2:sy*=int(m==right)
    if ey==3:sy=F(4,5)*(F(1875,1876) if m==10 else F(1))*int(m==right)
    value+=sx*sy*responses[l,m][T][k]
   best=max(best,value)
 screens.append(best)
ck(len(screens)==512)
ck(screens[128]==F(maximum[3],D) and screens[32]==F(maximum[5],D) and screens[160]==F(maximum[15],D))
gate=g*sum(mass,F(0))-sum(a*b for a,b in zip(coeff,screens))
pair35=next(x for x in pairs if x['labels']==[3,5]);kappa=F(pair35['defect']);improvement=c*kappa
ck(improvement==F(7570500739,70420420224000))
triangle3515=next(x for x in triangles if x['labels']==[3,5,15])
delta=F(triangle3515['defect']);triangle_gain=c*delta
ck(delta==F(6983,77760) and triangle_gain==F(7570500739,15648982272000))
ck(triangle3515['maximizing_phases']==[1,3,13] and triangle3515['maximizer_count']==1)
f1={'fullmode8_complete_gate':str(gate),'gate_decimal':float(gate),'pair35_correction':str(kappa),'pair_head_gate_increment':str(improvement),'pair_corrected_gate':str(gate+improvement),'triangle3515_correction':str(delta),'triangle_head_gate_increment':str(triangle_gain),'triangle_increment_decimal':float(triangle_gain),'triangle_corrected_gate':str(gate+triangle_gain),'triangle_corrected_gate_decimal':float(gate+triangle_gain),'triangle_pays_193_over_100000':gate+triangle_gain>F(193,100000),'scope':'All-one retention of actual109 source, exact inherited full-height screens and fullmode8 fees. Uses680 outside root/deep domination; no field search. Pair and triangle are alternative corrections, never added.'}
result={'status':'PASS','scope':'Fixed actual109 unretained source central mod225 marginal; existing original-label cluster mechanism. No all-state field optimization, no positive gate or unrestricted covering assertion.','source_sha256':{source_name:sha256(raw).hexdigest(),'clustered_global_phase_fixture.json':sha256(fixture_raw).hexdigest(),higher_name:sha256(higher_raw).hexdigest(),'remaining33_global_root_exclusion_certificate.json':sha256(oldraw).hexdigest()},'source_mass':str(sum(mass,F(0))),'denominator':D,'central_mass_numerators':list(map(int,nums)),'marginal_maxima':{str(d):str(F(v,D)) for d,v in maximum.items()},'pairs':pairs,'triangles':triangles,'positive_pair_count':len(positive_pairs),'positive_triangle_count':len(positive_triangles),'selected_pair':selected,'selected_triangle':triangle3515,'all_one_gate':f1,'checks':checks,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('central_mass_numerators','pairs','triangles')},indent=2))
