#!/usr/bin/env python3
"""Exact actual109 separation of the proposed698 desired density from joined33.

The test measure is a product of a finite central mixture and uniform outside
roots2..q-1. Central descendants follow the SAME actual pure-survivor laws.
Every free central numerical label is independent. The full central maximum is
computed by direct enumeration, not by a centered-layout restriction or an
imported separator. Standard library only; no optimizer is imported.
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
PINS={
 'clustered_global_phase_fixture.json':'4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
 'clustered_higher_pure_capacity_obstruction.json':'bbf9d977613f469b387cf60b7024092a9903b17bbac4374316c87d87c442bb99',
 'remaining33_global_root_exclusion_certificate.json':'36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4',
 'clustered109_central_block_outside_witness.json':'bfac781f0630effacf47c097d2685c37fe0db80decec983390f36505c51ee620'}
CHECKS=0
def ck(x,why):
 global CHECKS
 CHECKS+=1
 if not x:raise ArithmeticError(why)
def ppower(n,p):
 r=1
 while n%p==0:n//=p;r*=p
 return r
def central_maxima(xs,weights):
 # A free label assigned a zero-support residue has no positive indicator;
 # replacing it by any supported residue cannot decrease the positive charge.
 # Keep both fixed root labels in their COMPLETE domains, including dead roots.
 domains={d:sorted({x%d for x in xs}) for d in CENTRAL}
 vectors={d:{r:tuple(int(x%d==r) for x in xs) for r in domains[d]} for d in CENTRAL}
 C=[];layouts=[];count=0
 for a,b in product(range(3),range(5)):
  fixed=tuple(int(x%3==a)+int(x%5==b) for x in xs);best=-1;winner=None
  for r9,r15,r25 in product(domains[9],domains[15],domains[25]):
   baseline=tuple(f+u+v+z for f,u,v,z in zip(fixed,vectors[9][r9],vectors[15][r15],vectors[25][r25]))
   for r45,r75 in product(domains[45],domains[75]):
    ns=tuple(f+u+v for f,u,v in zip(baseline,vectors[45][r45],vectors[75][r75]))
    base=sum(w*(n*n+2*n) for w,n in zip(weights,ns))
    #225 meets at most one of the distinct physical central points.
    gains=[w*(2*n+3) for w,n in zip(weights,ns)];mx=max(gains);value=base+mx;count+=1
    if value>best:
     best=value;winner={3:a,5:b,9:r9,15:r15,25:r25,45:r45,75:r75,225:xs[gains.index(mx)]}
  direct=sum(w*(sum((x-winner[d])%d==0 for d in CENTRAL)**2+2*sum((x-winner[d])%d==0 for d in CENTRAL)) for x,w in zip(xs,weights))
  ck(best==direct,'full independent central optimum attained literally')
  C.append(best);layouts.append(winner)
 ck(count==15*prod(len(domains[d]) for d in (9,15,25,45,75)),'every five-label baseline enumerated')
 return C,layouts,count,{str(d):len(domains[d]) for d in CENTRAL}
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--base',type=Path,default=None)
 ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('joined33_dual_lift_obstruction_witness.json'))
 ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--joined-input',type=Path,help='optionally export this same probability measure for the existing joined33 separator')
 a=ap.parse_args();data={}
 for name,pin in PINS.items():
  b=(_resolve_input_path(a.base, name)).read_bytes();ck(sha256(b).hexdigest()==pin,'pinned '+name);data[name]=json.loads(b)
 wr=json.loads(a.witness.read_text());ck(wr['schema']=='actual109-joined33-dual-lift-separator-v1','separator witness schema')
 cells=wr['central_weights'];xs=[r[0] for r in cells];weights=[r[1] for r in cells];Z=sum(weights)
 ck(len(xs)==len(set(xs))>0 and all(type(x) is int and 0<=x<225 for x in xs),'distinct literal central points')
 ck(all(type(w) is int and w>0 for w in weights),'positive integer central weights')
 roots={q:tuple(wr['outside_roots'][str(q)]) for q in Q}
 ck(all(roots[q]==tuple(range(2,q)) for q in Q),'same full nonzero nonroot1 sets')
 originals=data['clustered_global_phase_fixture.json']['actual_originals']+data['clustered_higher_pure_capacity_obstruction.json']['first_tested_success']['added_higher_pure_originals']
 ck(len(originals)==len({r['modulus'] for r in originals})==109,'109 actual numerical originals')
 periods={3:729,5:15625,**{q:q*q for q in Q}};pure={p:[r for r in originals if ppower(r['modulus'],p)==r['modulus']] for p in (3,5)}
 centralsets={p:{} for p in (3,5)}
 for p in (3,5):
  for residue in {x%(p*p) for x in xs}:
   centralsets[p][residue]=tuple(z for z in range(residue,periods[p],p*p) if all((z-r['residue'])%r['modulus'] for r in pure[p]))
   ck(bool(centralsets[p][residue]),'positive actual central pure survivor')
 outside={q:tuple(r+q*k for r in roots[q] for k in range(q)) for q in Q}
 source_mass=[]
 for x in xs:
  coords={3:centralsets[3][x%9],5:centralsets[5][x%25],**outside}
  for row in originals:
   d=row['modulus'];b=row['residue'];powers={p:ppower(d,p) for p in P}
   ck(prod(powers.values())==d,'complete original factorization')
   ck(all(periods[p]%power==0 for p,power in powers.items()),'original resolved by same coordinate periods')
   ck(any(power>1 and all((z-b)%power for z in coords[p]) for p,power in powers.items()),'whole actual survivor rectangle avoids original')
  w3=F(1 if x%9==4 else 2,9);w5=F(1,25) if x%25==2 else F(4,75)
  source_mass.append(w3*w5*prod(F(q-2,q-1) for q in Q))
 scale=min(m*Z/w for m,w in zip(source_mass,weights))
 rates=[scale*F(w,Z)/m for m,w in zip(source_mass,weights)]
 ck(scale>0 and all(0<f<=1 for f in rates),'one actual admissible scaled retention')
 witness=data['clustered109_central_block_outside_witness.json'];D=witness['denominator'];Db=witness['block_denominator']
 ck(witness['source_sha256']=={k:PINS[k] for k in tuple(PINS)[:3]},'same actual source for desired density')
 ck(tuple(witness['central_labels'])==CENTRAL,'all eight central numerical labels')
 ck(sum(n for _,n in witness['centered_rows'])==Db,'old central probability law')
 h=sum(F(w,Z)*F(n,Db)*(sum((x-b)%d==0 for d in CENTRAL)**2+2*sum((x-b)%d==0 for d in CENTRAL)) for x,w in cells for b,n in witness['centered_rows'])
 pm={p:{r:F(sum(w for x,w in cells if x%p==r),Z) for r in range(p)} for p in (3,5)}
 selectors=[]
 for mode in range(16):
  e3,e5=divmod(mode,4)
  xx=((0,),(0,1),(0,1,2,4,5),(0,1,2,4,5))[e3]
  yy=((0,),(0,1,2,3),tuple(i for i in range(20) if i!=5),tuple(i for i in range(20) if i!=5))[e5]
  selectors.extend((mode,l,m) for l,m in product(xx,yy))
 loads={};groups={};rows=0
 for mode,T,sid,column,num in witness['rows']:
  e3,e5=divmod(mode,4)
  if not(T and e3<=1 and e5<=1 and e3+e5+T.bit_count()<=2):continue
  rows+=1;j=32*mode+T;loads[j]=loads.get(j,0)+num
  smode,left,right=selectors[sid];ck(smode==mode,'literal selected central selector')
  coords=[];rem=column
  for size in (8,11,11,11,11)[::-1]:coords.append(rem%size);rem//=size
  coords=coords[::-1]
  ck(all(t!=(7 if q==7 else 10) for q,t in zip(Q,coords)),'selected exterior rows are shallow')
  ck(sum(1<<i for i,t in enumerate(coords) if t)==T,'same original query support')
  value=F(3**(e3+e5+T.bit_count()))
  if e3:value*=pm[3][left]
  if e5:value*=pm[5][right]
  for q,t in zip(Q,coords):
   if not t:continue
   choices=tuple(range(9,q)) if t==9 else (t,)
   value*=F(sum(r in roots[q] for r in choices),len(choices)*(q-2))
  groups[j]=groups.get(j,F(0))+F(num,D)*value
 ck(rows==292 and len(groups)==25 and all(n==D for n in loads.values()),'all25 probability budgets filled by292 rows')
 R=h+sum(groups.values(),F(0))
 C,central_layouts,enumerated,domains=central_maxima(xs,weights)
 L=sum(F(1,q-2) for q in Q);B=9*sum(F(1,(p-2)*(q-2)) for p,q in combinations(Q,2));constant=3*L+B
 # Product outside roots: a chosen live q-root has mass1/(q-2). All chosen
 # outside roots can be fixed to2 simultaneously. With central endpoint a,
 # eliminate an independent composite(pq) by maximizing its central root u:
 #   E_p(a)=2m_p(a)+max_u (5+2[u=a])m_p(u).
 # The outside-only triangles simultaneously contribute9/[(p-2)(q-2)].
 E={p:{a0:2*pm[p][a0]+max((5+2*int(u==a0))*pm[p][u] for u in range(p)) for a0 in range(p)} for p in (3,5)}
 values=[F(C[5*ap+bp],Z)+constant+L*(E[3][ap]+E[5][bp]) for ap,bp in product(range(3),range(5))]
 best=max(values);idx=values.index(best);ap,bp=divmod(idx,5);layout=central_layouts[idx]
 us={p:max(range(p),key=lambda u:(5+2*int(u==z))*pm[p][u]) for p,z in ((3,ap),(5,bp))}
 # A single full layout attains each upper component. This is not a sum of
 # independently unattainable branch maxima.
 joined=dict(layout);joined.update({q:2 for q in Q})
 def crt(a,p,b,q):return a+p*((b-a)*pow(p,-1,q)%q)
 for p,q in combinations(P,2):
  if (p,q)==(3,5):continue
  joined[p*q]=crt(us[p],p,2,q) if p in (3,5) else crt(2,p,2,q)
 ck(len(joined)==33,'one complete33 numerical-label layout')
 ck(all(0<=r<d for d,r in joined.items()),'all layout residues legal')
 # Independent literal evaluation from the121 actual selected atomic factors.
 def probability(requirements):
  for d,phase in requirements:
   if not 0<=phase<d:return F(0)
  prob=F(0)
  for x,w in cells:
   if any(any(d%p==0 and x%ppower(d,p)!=phase%ppower(d,p) for p in (3,5)) for d,phase in requirements):continue
   term=F(w,Z)
   for q in Q:
    requested={phase%q for d,phase in requirements if d%q==0}
    if len(requested)>1:term=F(0);break
    if requested:term*=F(int(next(iter(requested)) in roots[q]),q-2)
   prob+=term
  return prob
 factors=[(3,((d,joined[d]),)) for d in joined]
 factors.extend((2,((d,joined[d]),(e,joined[e]))) for d,e in combinations(CENTRAL,2))
 for p,q in combinations(P,2):
  if (p,q)!=(3,5):factors.extend((2,((d,joined[d]),(e,joined[e]))) for d,e in ((p,q),(p,p*q),(q,p*q)))
 ck(len(factors)==121 and sum(v for v,_ in factors)==275,'correct33-block ownership')
 literal=sum(coef*probability(req) for coef,req in factors)
 ck(literal==best,'one literal full33 layout attains complete upper')
 gap=R-best;ck(gap>0,'strict nonnegative-measure separation')
 # Evaluate this particular admissible scaled retention against the COMPLETE
 #699 gate. All exterior roots are uniform on2..q-1; the root response factor
 #(q-1)/(q-2) dominates every deeper response factor1. Central mode3 uses the
 #unchanged actual pure-survivor all-height reduction, including weak leaves.
 def central_factor(p,e,r,x):
  if e==0:return F(1)
  if e<3:return F(int(x%(p**e)==r))
  if x%(p*p)!=r:return F(0)
  if p==3:return F(729,82) if r==4 else F(9,2)
  return F(9375,469) if r==2 else F(15)
 central_screen=[]
 for e3,e5 in product(range(4),repeat=2):
  aa=(0,) if e3==0 else range(3) if e3==1 else range(9)
  bb=(0,) if e5==0 else range(5) if e5==1 else range(25)
  central_screen.append(max(sum(scale*F(w,Z)*central_factor(3,e3,ra,x)*central_factor(5,e5,rb,x) for x,w in cells) for ra,rb in product(aa,bb)))
 screens=[central_screen[mode]*prod(F(q-1,q-2) for i,q in enumerate(Q) if T>>i&1) for mode,T in product(range(16),range(32))]
 c=F(1084133,201247200);g=1-c
 fees=list(map(F,data['remaining33_global_root_exclusion_certificate.json']['combined512_coefficients']))
 for i,q in enumerate(Q):
  if q>7:fees[256+(1<<i)]+=g/F(q*(q-2))
 selected=[F(0)]*512
 for coefficient,requirements in factors:
  d=lcm(*(modulus for modulus,phase in requirements));n=d;exponents=[]
  for p in P:
   exponent=0
   while n%p==0:n//=p;exponent+=1
   exponents.append(exponent)
  ck(n==1 and max(exponents[2:])<=1,'selected fee has declared prime support')
  T=sum((1<<i)*e for i,e in enumerate(exponents[2:]));j=32*(4*exponents[0]+exponents[1])+T
  selected[j]+=coefficient*prod(F(1,q-1) for i,q in enumerate(Q) if T>>i&1)
 remaining=[fee-c*pick for fee,pick in zip(fees,selected)]
 for fee in remaining:ck(fee>=0,'full nonnegative remaining fee')
 old_gate=g*scale-sum(fee*S for fee,S in zip(fees,screens))
 scaled_K=scale*best;selected_fee=sum(pick*S for pick,S in zip(selected,screens))
 improvement=c*(selected_fee-scaled_K)
 full_gate=g*scale-sum(fee*S for fee,S in zip(remaining,screens))-c*scaled_K
 ck(old_gate+improvement==full_gate,'full original-loss and all-height gate recombination')
 ck(full_gate<0,'this separating retention is not a paying field')
 result={'status':'PASS','checks':CHECKS,'source_sha256':PINS,'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'witness_sha256':sha256(a.witness.read_bytes()).hexdigest(),
 'scope':'No probability distribution over arbitrary independent full33-label layouts can have expected charge H>=the specified698 desired density R on every positive actual-source category. This excludes that fixed-row dual lift, not every joined33 dual and not the primal gate.',
 'central_positive_points':len(cells),'central_weight_total':Z,'normalized_R_expectation':str(R),'normalized_K33':str(best),'strict_gap':str(gap),'strict_gap_decimal':float(gap),'retention_scale':str(scale),'retention_gap':str(scale*gap),
 'central_h698_expectation':str(h),'exterior_R_expectation':str(R-h),'conditional_C_numerators':[C[5*i:5*i+5] for i in range(3)],'conditional_C_denominator':Z,'central_supported_residue_counts':domains,'enumerated_five_free_label_baselines':enumerated,'conditional_joined_values':list(map(str,values)),
 'attaining_layout':{str(d):r for d,r in sorted(joined.items())},'root_marginals':{str(p):{str(r):str(v) for r,v in z.items()} for p,z in pm.items()},'central_retention_rates':[[x,str(f)] for x,f in zip(xs,rates)],'selected_rows':rows,'selected_groups':len(groups),'group_R':{str(j):str(v) for j,v in sorted(groups.items())}}
 result['complete_gate']={'scope':'Only this explicit admissible scaled separator retention; all512 screens, original losses and fullmode8 additions retained. No field optimization or all-field conclusion.',
  'mass':str(scale),'K33':str(scaled_K),'old_gate':str(old_gate),'selected_screen_fee':str(selected_fee),'joined_improvement':str(improvement),'full_joined_gate':str(full_gate),'full_joined_gate_decimal':float(full_gate),
  'central_maxima':list(map(str,central_screen)),'screens':list(map(str,screens))}
 if a.joined_input:
  outside_size=prod(q-2 for q in Q);common_den=Z*outside_size
  node_mass={p:[sum(w for x,w in cells if x%p==r) for r in range(p)] for p in (3,5)}
  unary={str(p):[n*outside_size for n in node_mass[p]] if p in node_mass else [Z*(outside_size//(p-2)) if r>=2 else 0 for r in range(p)] for p in P}
  pairs={}
  for p,q in combinations(P,2):
   table=[]
   for rp in range(p):
    row=[]
    for rq in range(q):
     if q==5:value=sum(w for x,w in cells if x%p==rp and x%q==rq)*outside_size
     elif p in node_mass:value=node_mass[p][rp]*(outside_size//(q-2)) if rq>=2 else 0
     else:value=Z*(outside_size//((p-2)*(q-2))) if rp>=2 and rq>=2 else 0
     row.append(value)
    table.append(row)
   pairs[f'{p},{q}']=table
  common={'schema':'joined33-common-field-input-v1','scope':'The verified actual-source product probability measure tau used to separate the specified698 R; no complete gate claim. Its scaled version is an admissible retention.',
   'source_sha256':{k:PINS[k] for k in tuple(PINS)[:3]},'separator_witness_sha256':result['witness_sha256'],'denominator':common_den,
   'central':{'points':[[x%9,x%25] for x in xs],'weights':[w*outside_size for w in weights],'residues_mod225':xs},'unary':unary,'pairs':pairs}
  a.joined_input.write_text(json.dumps(common,indent=2)+'\n')
 a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('source_sha256','attaining_layout','conditional_joined_values','root_marginals','central_retention_rates','group_R','complete_gate')},indent=2))
if __name__=='__main__':main()
