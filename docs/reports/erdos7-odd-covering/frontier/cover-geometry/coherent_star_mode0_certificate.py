#!/usr/bin/env python3
"""Coherent forty-star mode0 bound and a complete-gate policy counterexample.

Integer matching recurrence, exact rational phase support and literal selectors.
The common field chi=1[F>0] has a uniform mode0 lower bound, but fails the
complete corrected512 gate on the actual clustered global-phase fixture.
This does not exclude other fields or sources and is not Lean verification.
"""
from fractions import Fraction as F
from itertools import product
from math import prod,lcm
from pathlib import Path
from hashlib import sha256
import argparse,json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args();checks={}
def ck(name,condition):
 checks[name]=checks.get(name,0)+1
 if not condition:raise ArithmeticError(name)
pins={'remaining33_global_root_exclusion_certificate.json':'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4',
      'clustered_global_phase_fixture.json':'4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6'}
inputs={}
for name,pin in pins.items():
 raw=(args.directory/name).read_bytes();ck('input pin',sha256(raw).hexdigest()==pin);inputs[name]=json.loads(raw)
C=list(map(F,inputs['remaining33_global_root_exclusion_certificate.json']['combined512_coefficients']))
ck('complete512 nonnegative fees',len(C)==512 and min(C)>=0)
Q=(7,11,13,17,19);g=F(200163067,201247200);gamma=F(193,100000)
B=[F(157,210)]+[F(q-2,q-1)-F(2,q*(q-2)) for q in Q[1:]]
r=[F(1,q-1) for q in Q];a=[F(1,q*(q-2)) for q in Q]
den=[lcm(b.denominator,r0.denominator,a0.denominator) for b,r0,a0 in zip(B,r,a)]
zs=[[int(den[i]*max(F(),B[i]-r[i]*n)) for n in range(9)] for i in range(5)]
bet=[[int((a[i]*r[j]+r[i]*a[j]+2*r[i]*r[j])*den[i]*den[j]) for j in range(5)] for i in range(5)]
D=[prod(den[i] for i in range(5) if m>>i&1) for m in range(32)]
def matching(ns):
 H=[1]+[0]*31
 for m in range(1,32):
  i=(m&-m).bit_length()-1;rest=m^(1<<i)
  H[m]=zs[i][ns[i]]*H[rest]-sum(bet[i][j]*H[rest^(1<<j)] for j in range(i+1,5) if rest>>j&1)
 return H
fd=lcm(g.denominator*D[31],*(C[T].denominator*D[31^T] for T in range(32)))
fg=g*fd/D[31];fm=[C[T]*fd/D[31^T] for T in range(32)]
ck('integer fullmode0 coefficients',fg.denominator==1 and all(x.denominator==1 for x in fm))
fg=int(fg);fm=list(map(int,fm))
def fnum(H):return fg*H[31]-sum(fm[T]*H[31^T] for T in range(32))
slopes=(35110,17555,10551,4824,4138)
minH=None;positive=0;equalities=[];constant3=None
for ns in product(range(9),repeat=5):
 H=matching(ns);f=fnum(H);aff=140440-sum(c*n for c,n in zip(slopes,ns))
 gap=max(f,0)*1000000-aff*fd
 ck('all59049 affine inequalities',gap>=0)
 if not gap:equalities.append(ns)
 if f>0:
  positive+=1
  for m in range(32):
   ck('retained induced polynomial positive',H[m]>0)
   v=F(H[m],D[m])
   if minH is None or v<minH[0]:minH=(v,ns,m)
 if ns==(3,3,3,3,3):constant3=F(f,fd)
ck('15894 retained count vectors',positive==15894)
ck('two affine equalities',equalities==[(0,8,0,0,0),(4,0,0,0,0)])
ck('exact strict margin',minH[0]==F(28028831665337,8462661375168000))
ck('constantthree check',constant3==F(8482754828806680432735281,3678667717609532583936000000))
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5)
coords=[(l,m) for l,m in product(I,J) if not(l<3 and m<5)]
res={c:(3*(c[0]%3)+c[0]//3)+9*((5*(c[1]%5)+c[1]//5-(3*(c[0]%3)+c[0]//3))*14%25) for c in coords}
ds=(3,5,15,9,25,45,75,225);corners=[]
for i,j in product(I,J):
 w={c:F((1 if c[0]==i else 2)*(3 if c[1]==j else 4),675) for c in coords}
 maxima=[max(sum((w[c] for c in coords if res[c]%d==s),F()) for s in range(d)) for d in ds]
 bound=F(3511,25000)*sum(w.values(),F())-F(36089,500000)*sum(maxima,F())
 ck('all95 coherent corner bounds',bound>=F(64121,3125000))
 corners.append(dict(corner=[i,j],bound=str(bound),mass=str(sum(w.values(),F())),maxima=list(map(str,maxima))))
minimum=min(F(c['bound']) for c in corners)
ck('sharp finite affine corner minimum',minimum==F(64121,3125000))
ck('mode0 proposed remaining budget',minimum-gamma==F(232359,12500000))

# The phase81 regression uses original numerical labels in the existing101
# fixture. No phases are selected separately by cell or selector.
originals=inputs['clustered_global_phase_fixture.json']['actual_originals']
lookup={o['modulus']:o['residue'] for o in originals}
ck('101 distinct numerical originals',len(lookup)==len(originals)==101)
for q,d in product(Q,ds):ck('40 actual globally fixed star phases',lookup[d*q]%d==81%d)
for u,q in enumerate(Q):
 if u:C[256+(1<<u)]+=g*F(1,q*(q-2))
hs=[matching(tuple(sum(res[c]%d==lookup[d*q]%d for d in ds) for q in Q)) for c in coords]
chi=[fnum(h)>0 for h in hs];i,j=4,10
ck('actual chi retains74 cells',sum(chi)==74)
source=g*sum(F((1 if l==i else 2)*(3 if m==j else 4)*h[31],675*D[31]) for (l,m),h,t in zip(coords,hs,chi) if t)
fees=[];menus=0;screens=0
for mode in range(16):
 ex,ey=divmod(mode,4);cx=((0,),(0,1),I,I)[ex];cy=((0,),tuple(range(4)),J,J)[ey]
 selectors=[]
 for aa,bb in product(cx,cy):
  vec=[]
  for l,m in coords:
   x=2*(1 if l==i else 2);y=3 if m==j else 4
   if ex==1:x*=l//3==aa
   elif ex==2:x*=l==aa
   elif ex==3:x=18*(l==aa)
   if ey==1:y*=m//5==bb
   elif ey==2:y*=m==bb
   elif ey==3:y=60*(m==bb)
   vec.append(x*y)
  selectors.append(vec)
 menus+=len(selectors);fee=F()
 for T in range(32):
  if not C[mode*32+T]:continue
  val=max(sum(v*h[31^T] for v,h,t in zip(vec,hs,chi) if t) for vec in selectors)
  screens+=len(selectors);ck('nonnegative complete query maximum',val>=0)
  fee+=C[mode*32+T]*F(val,1350*D[31^T])
 fees.append(fee)
ck('all559 literal selector candidates',menus==559)
gate=source-sum(fees,F());rest=sum(fees[1:],F())
ck('exact policy counterexample',gate==-F(34684038567037034905564050721,275900078820714943795200000000))
ck('proposed uniform remaining bound refuted',rest>minimum-gamma and gate<0)
result=dict(schema='coherent-star-mode0-and-policy-refutation-v1',status='PASS',new_lean_verification=False,
 scope='One corner-independent field for arbitrary coherent forty-star phases has the stated MODE0 lower bound under the declared conservative matching source. All59049 counts and95corners checked. The SAME field fails the corrected complete512 gate on the fixed phase81 fixture. Other fields/sources and unrestricted Erdos7 remain unresolved.',
 input_sha256=pins,program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
 count_vectors=9**5,positive_vectors=positive,minimum_positive_response=str(minH[0]),minimum_response_witness=[minH[1],minH[2]],
 affine_intercept='3511/25000',affine_slopes=[str(F(v,1000000)) for v in slopes],affine_equalities=equalities,
 constant_three=str(constant3),minimum_corner=str(minimum),proposed_remaining_budget=str(minimum-gamma),corners=corners,
 counterexample=dict(corner=[i,j],phase=81,retained_cells=sum(chi),source_mass=str(source/g),mode0=str(source-fees[0]),remaining_debit=str(rest),
                    full_gate=str(gate),full_gate_decimal=float(gate),fees_by_mode=list(map(str,fees)),literal_selector_candidates=menus,query_screens=screens,
                    charge_repair='Fullmode8 additions g/[q(q-2)] for9q² atq=11,13,17,19; no guarded mode9 substitution.'),
 checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in('corners','checks','input_sha256')},indent=2))
