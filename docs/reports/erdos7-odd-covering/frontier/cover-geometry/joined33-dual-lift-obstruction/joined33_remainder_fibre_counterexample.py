#!/usr/bin/env python3
"""Exact actual109 pair: equal joined33 responses, unequal complete fees.

Standard library only. Source and698 witness pins are explicit. This checks one
pair,512 scalar screen formulas and the stated proportional-row fibre condition;
it does not solve the whole-layout convex-hull membership problem.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from hashlib import sha256
import argparse,json


_DEFAULT_INPUT_PATHS = {'clustered_global_phase_fixture.json': '../clustered_global_phase_fixture.json', 'clustered_higher_pure_capacity_obstruction.json': '../clustered_higher_pure_capacity_obstruction.json', 'remaining33_global_root_exclusion_certificate.json': '../remaining33_global_root_exclusion_certificate.json', 'clustered109_central_block_outside_witness.json': 'clustered109_central_block_outside_witness.json'}

def _resolve_input_path(directory, name):
    if directory is not None:
        return directory / name
    return Path(__file__).resolve().parent / _DEFAULT_INPUT_PATHS.get(name, name)

P=(3,5,7,11,13,17,19);Q=P[2:];CENTRAL=(3,5,9,15,25,45,75,225)
COST=F(1084133,201247200);G=1-COST
PINS={
 'clustered_global_phase_fixture.json':'4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
 'clustered_higher_pure_capacity_obstruction.json':'bbf9d977613f469b387cf60b7024092a9903b17bbac4374316c87d87c442bb99',
 'remaining33_global_root_exclusion_certificate.json':'36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4',
 'clustered109_central_block_outside_witness.json':'bfac781f0630effacf47c097d2685c37fe0db80decec983390f36505c51ee620'}
CHECKS=0
def ck(condition,label):
 global CHECKS
 CHECKS+=1
 if not condition:raise ArithmeticError(label)
def selected(j):
 mode,T=divmod(j,32);e3,e5=divmod(mode,4)
 if T==0 and e3<=2 and e5<=2 and mode:
  return F((2*e3+1)*(2*e5+1))
 if T and e3<=1 and e5<=1 and e3+e5+T.bit_count()<=2:
  return F(3**(e3+e5+T.bit_count()))*prod(F(1,q-1) for i,q in enumerate(Q) if T&(1<<i))
 return F(0)
def prime_power(n,p):
 power=1
 while n%p==0:power*=p;n//=p
 return power
def crt_pair(a,m,b,n):return a+m*((b-a)*pow(m,-1,n)%n)
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--base',type=Path,default=None)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args();data={}
 for name,pin in PINS.items():
  content=(_resolve_input_path(args.base, name)).read_bytes();ck(sha256(content).hexdigest()==pin,'pinned source '+name);data[name]=json.loads(content)
 originals=data['clustered_global_phase_fixture.json']['actual_originals']+data['clustered_higher_pure_capacity_obstruction.json']['first_tested_success']['added_higher_pure_originals']
 ck(len(originals)==len({r['modulus'] for r in originals})==109,'109 distinct actual originals')
 ck(all(r['modulus']>1 and r['modulus']%2 for r in originals),'odd nonunit originals')
 # Literal central pure survivors, not an invented Cartesian choice.
 central_sets={}
 coordinate_period={3:729,5:15625,**{q:q*q for q in Q}}
 for p,period,shallow,residue in ((3,729,9,4),(5,15625,25,0)):
  pure=[r for r in originals if prime_power(r['modulus'],p)==r['modulus']]
  central_sets[p]=[x for x in range(residue,period,shallow) if all(x%r['modulus']!=r['residue']%r['modulus'] for r in pure)]
 ck(len(central_sets[3])==41 and len(central_sets[5])==625,'actual central cylinders have positive stated capacities')
 outside_A={7:[1],**{q:list(range(2,q*q,q)) for q in Q[1:]}}
 outside_B={7:list(range(8,49,7)),**{q:list(range(2,q*q,q)) for q in Q[1:]}}
 all_sets=[]
 for outside in (outside_A,outside_B):
  coordinates={**central_sets,**outside};all_sets.append(coordinates)
  for row in originals:
   modulus=row['modulus'];residue=row['residue'];powers={p:prime_power(modulus,p) for p in P}
   ck(prod(powers.values())==modulus,'all original prime coordinates included')
   ck(all(coordinate_period[p]%power==0 for p,power in powers.items()),'every original resolved by the full coordinate cylinder periods')
   # A whole rectangle avoids a class if one of its coordinate cylinders does.
   ck(any(power>1 and all(x%power!=residue%power for x in coordinates[p]) for p,power in powers.items()),'entire literal cylinder avoids original '+str(modulus))
 central=175;roots={3:central%3,5:central%5,7:1,11:2,13:2,17:2,19:2}
 for p,coords in all_sets[0].items():
  shallow=9 if p==3 else 25 if p==5 else p
  ck({x%shallow for x in coords}=={x%shallow for x in all_sets[1][p]},'identical shallow coordinate set')
  ck(len({x%shallow for x in coords})==1,'one common shallow coordinate')
 # The fixed699 reference gives central cell(l,m)=(4,0) weight1*4/675;
 # each outside literal q-square residue contributes1/[q(q-1)].
 denominator=675*prod(q*(q-1) for q in Q)
 massA=F(4*prod(len(outside_A[q]) for q in Q),denominator)
 massB=F(4*prod(len(outside_B[q]) for q in Q),denominator)
 alpha=min(massA,massB);rateA=alpha/massA;rateB=alpha/massB
 ck(massA==F(1,244944000) and massB==6*massA,'same699 category source masses')
 ck(rateA==1 and rateB==F(1,6),'two admissible equal-mass retained fields')
 # Every label residue is determined by the common shallow coordinates.
 layout={d:central%d for d in CENTRAL}
 layout.update({q:roots[q] for q in Q})
 for p,q in combinations(P,2):
  if (p,q)!=(3,5):layout[p*q]=crt_pair(roots[p],p,roots[q],q)
 tokens=[('unary',d,3,d) for d in layout]
 tokens.extend(('pair',(d,e),2,lcm(d,e)) for d,e in combinations(CENTRAL,2))
 for p,q in combinations(P,2):
  if (p,q)!=(3,5):tokens.extend(('pair',(d,e),2,lcm(d,e)) for d,e in ((p,q),(p,p*q),(q,p*q)))
 ck(len(layout)==33 and len(tokens)==121 and sum(t[2] for t in tokens)==275,'same selected33 block')
 for d,a in layout.items():
  for p in P:
   power=prime_power(d,p)
   if power>1:ck(all(x%power==a%power for coords in all_sets for x in coords[p]),'one layout hits every source point in both cylinders')
 K=275*alpha
 # The complete screen representation at this actual central cell has one
 # maximal central multiplier per mode: (729/82)^[e3=3]15^[e5=3].
 # Outside root2 cylinders have factor(q-1). At7 the special child is35,
 # whereas the other-child cylinder is6. These follow from all legal tokens:
 # shallow root normalized by(q-1), special root1 child normalized byq(q-2).
 coefficients=list(map(F,data['remaining33_global_root_exclusion_certificate.json']['combined512_coefficients']))
 for i,q in enumerate(Q):
  if i:coefficients[256+(1<<i)]+=G/F(q*(q-2))
 ck(len(coefficients)==512,'complete original coefficient table with fullmode8 additions')
 screensA=[];screensB=[];remainder=[];rows=[];difference_sum=F(0)
 for j in range(512):
  mode,T=divmod(j,32);e3,e5=divmod(mode,4)
  multiplier=(F(729,82) if e3==3 else F(1))*(F(15) if e5==3 else F(1))
  others=prod(q-1 for i,q in enumerate(Q) if i and T&(1<<i))
  factorA=35 if T&1 else 1;factorB=6 if T&1 else 1
  SA=alpha*multiplier*others*factorA;SB=alpha*multiplier*others*factorB
  remaining=coefficients[j]-COST*selected(j)
  ck(remaining>=0 and SA>=SB,'nonnegative unchanged fee and all-screen dominance')
  screensA.append(SA);screensB.append(SB);remainder.append(remaining)
  if T&1:difference_sum+=remaining*multiplier*others
  rows.append({'screen':j,'central_multiplier':str(multiplier),'other_root_factor':others,'remaining_coefficient':str(remaining),'A':str(SA),'B':str(SB)})
 gateA=G*alpha-sum(coef*S for coef,S in zip(remainder,screensA))-COST*K
 gateB=G*alpha-sum(coef*S for coef,S in zip(remainder,screensB))-COST*K
 delta=29*alpha*difference_sum
 ck(delta==gateB-gateA>0,'complete exact gate difference, not a single-term inference')
 ck(screensA[1]==35*alpha and screensB[1]==6*alpha,'literal complete screen1 values')
 ck(remainder[1]==F(1084133,1132015500)>0,'strict positive retained screen1 fee')
 # Independently recombine the old gate plus the selected query credit.
 for ss,gate in ((screensA,gateA),(screensB,gateB)):
  old=G*alpha-sum(coef*S for coef,S in zip(coefficients,ss))
  credit=COST*(sum(selected(j)*S for j,S in enumerate(ss))-K)
  ck(old+credit==gate,'old-gate difference agrees with direct complete gate')
 # Check the narrower proposed698 equality lift separately. Its292 exterior
 # selected rows all use shallow tokens, so this particular R has no child split.
 witness=data['clustered109_central_block_outside_witness.json'];D=witness['denominator'];selectors=[]
 ck(witness['source_sha256']=={name:PINS[name] for name in tuple(PINS)[:3]},'698 same-source pins')
 for mode in range(16):
  e3,e5=divmod(mode,4)
  xs=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[e3]
  ys=((0,),(0,1,2,3),tuple(i for i in range(20) if i!=5),tuple(i for i in range(20) if i!=5))[e5]
  selectors.extend((mode,left,right) for left,right in product(xs,ys))
 shape=(8,11,11,11,11);group_loads={};count=0;exterior_R=F(0)
 for mode,T,sid,column,num in witness['rows']:
  j=32*mode+T
  if T==0 or not selected(j):continue
  count+=1;group_loads[j]=group_loads.get(j,0)+num
  coords=[];rem=column
  for size in shape[::-1]:coords.append(rem%size);rem//=size
  coords=coords[::-1]
  ck(all(tok!=size-1 for tok,size in zip(coords,shape)),'no exterior selected row uses a deep child token')
  smode,left,right=selectors[sid];ck(smode==mode,'selected central mode')
  # At(l,m)=(4,0), shallow3 selector is1 and shallow5 selector is0.
  val=F(int((mode!=4 or left==1) and (mode!=1 or right==0)))
  for q,tok in zip(Q,coords):
   if not tok:continue
   allowed=range(9,q) if tok==9 and q>9 else (tok,)
   val*=F(q-1,len(allowed)) if roots[q] in allowed else 0
  exterior_R+=selected(j)*F(num,D)*val
 ck(count==292 and len(group_loads)==25 and all(n==D for n in group_loads.values()),'292 shallow rows fill all25 exterior selected groups')
 central_R=sum(F(num,witness['block_denominator'])*(sum((central-b)%d==0 for d in CENTRAL)**2+2*sum((central-b)%d==0 for d in CENTRAL)) for b,num in witness['centered_rows'])
 desired_R=central_R+exterior_R
 ck(desired_R==F(2792882767253,10**12),'specific698 desired density on either member')
 result={'status':'PASS','checks':CHECKS,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':PINS,
  'scope':'One actual109 same-source pair disproves sufficiency of selected33 responses for the full699 gate. The specific698 proportional-row desired density remains shallow-fibre constant; its whole-layout convex-hull membership is not decided.',
  'central_cell':[4,0],'central_mod225':175,'central_pure_survivor_counts':{str(p):len(v) for p,v in central_sets.items()},'outside_roots':[1,2,2,2,2],
  'A_categories':[0,2,2,2,2],'B_categories':[1,2,2,2,2],'A_source_mass':str(massA),'B_source_mass':str(massB),'A_retention':str(rateA),'B_retention':str(rateB),'equal_mass':str(alpha),
  'all_selected33_responses_equal':True,'K33_both':str(K),'common_attaining_layout':{str(d):a for d,a in sorted(layout.items())},
  'screen1_A':str(screensA[1]),'screen1_B':str(screensB[1]),'screen1_difference':str(screensA[1]-screensB[1]),'screen1_remaining_coefficient':str(remainder[1]),
  'screen1_deep_row':{'mode':0,'support':1,'selector':0,'token':7,'literal_modulus':49,'literal_residue':1,'normalizer':35},
  'weighted_remaining_sum':str(difference_sum),'gate_A':str(gateA),'gate_B':str(gateB),'gate_B_minus_gate_A':str(delta),
  'gate_A_decimal':float(gateA),'gate_B_decimal':float(gateB),'difference_decimal':float(delta),
  'specific698_exterior_rows':292,'specific698_exterior_groups':25,'specific698_deep_rows':0,'specific698_R_both':str(desired_R),'specific698_R_difference':'0','specific698_convex_hull_membership':'open','screens':rows}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('screens','common_attaining_layout')},indent=2))
if __name__=='__main__':main()
