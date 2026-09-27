#!/usr/bin/env python3
"""Exact constants for simultaneous selected-overlap query and loss credits.

Python 3.9+ standard library only. Place beside the pinned input or pass
--source-dir. Rational grids supplement the all-real proof in Report583.
Floats are display-only. No original phase or actual source is changed.
"""
from argparse import ArgumentParser
from hashlib import sha256
from fractions import Fraction as F
from itertools import product
from math import gcd, prod
import json
from pathlib import Path

def thirty_original_control(B, K3, K7, alpha, need):
    """Inputs are exact supplier Fractions; need(name, bool) raises on failure."""
    Q = (5, 7, 11, 13, 17, 19)
    ds = Q + (25,)
    t4 = (0, 6, 9, 15, 18, 24, 27)
    t5 = (33, 36, 42, 45, 51, 54, 60)
    def ex(x):
        x = F(x)
        return {'exact': str(x), 'decimal': float(x)}
    def crt(t, q3, r, d):
        if gcd(q3, d) != 1:
            raise ValueError('noncoprime original CRT inputs')
        return (t + q3 * (((r-t) * pow(q3, -1, d)) % d)) % (q3*d)
    originals = [{'modulus':3,'phase':1,'e':1,'d':1,'t':1,'r':0},
                 {'modulus':9,'phase':3,'e':2,'d':1,'t':3,'r':0}]
    for j,d in enumerate(ds):
        for e,r,t in ((0,0,0),(1,1,2),(4,2,t4[j]),(5,2,t5[j])):
            modulus = 3**e*d
            phase = r if e == 0 else crt(t, 3**e, r, d)
            originals.append({'modulus':modulus,'phase':phase,'e':e,'d':d,'t':t,'r':r})
    need('30 control distinct odd numerical originals',len(originals)==30 and len({o['modulus'] for o in originals})==30 and all(o['modulus']>1 and o['modulus']%2 for o in originals))
    need('30 control globally consistent original CRT phases',all(o['phase']%o['d']==o['r']%o['d'] and o['phase']%(3**o['e'])==o['t']%(3**o['e']) for o in originals))
    need('30 control selected phases cover every shallow original',all(o['r'] in (0,1) for o in originals if o['d']>1 and o['e']<=3))
    # The 25 constraints, both in the selection and in the shallow original
    # table, add nothing after the corresponding root5 constraints.
    need('30 control selected25 phases redundant',all(r%5 in (0,1) for r in (0,1)))
    for e in (0,1):
        parent = next(o for o in originals if o['e']==e and o['d']==5)
        child = next(o for o in originals if o['e']==e and o['d']==25)
        need('30 control shallow25 redundancy e='+str(e),child['modulus']%parent['modulus']==0 and child['phase']%parent['modulus']==parent['phase'])
    caps = {11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}
    source_rows = []
    for q in Q:
        roots = tuple(range(2,q))
        need('30 control normalized actual PA row '+str(q),sum((F(1,q-2) for _ in roots),F(0))==1)
        if q in caps:
            need('30 control inactive PA cap '+str(q),F(q,q-2)<caps[q])
            # These are the only selected cylinders in this actual q-row.
            U = F(2,q)
            union = F(len({0,1}),q)
            overlap = U-union
            tau = 1-1/caps[q]
            gamma = caps[q]*min(overlap,max(U-tau,0))
            need('30 control actual selected overlap zero '+str(q),gamma==0)
        source_rows.append({'prime':q,'allowed_roots':roots,'root_mass':ex(F(1,q-2)),'density':ex(F(q,q-2))})
    source_density = prod((F(q,q-2) for q in Q),start=F(1))
    need('30 control same actual density supplier',source_density<=9/alpha)
    need('30 control all deep phases lie in A',all(t%9 in (0,6) for t in t4+t5))
    need('30 control same-height disjoint cylinders',len(set(t4))==len(set(t5))==7)
    need('30 control no overlap across actual depths',all((a-b)%81 for a in t4 for b in t5))
    fibre_count = 0
    min_cA = F(1)
    # I25 implies I5. These96 patterns exhaust possible Q incidences.
    for i5,i25 in ((0,0),(1,0),(1,1)):
        for rest in product((0,1),repeat=5):
            active = (i5,)+rest+(i25,)
            n = sum(active)
            forbidden = {t for t in range(243) if any(active[j] and (t%81==t4[j] or t==t5[j]) for j in range(7))}
            countA = sum(t%9 in (0,6) and t not in forbidden for t in range(243))
            cA = F(countA,54)
            union_loss = 1-cA
            singleton_loss = n*(F(1,18)+F(1,54))
            if union_loss != singleton_loss or cA != 1-F(2*n,27):
                raise ValueError('30 control actual fibre overlap failure')
            min_cA = min(min_cA,cA)
            fibre_count += 1
    need('30 control all actual incidence patterns checked',fibre_count==96)
    need('30 control minimum reserve and seven-active exception',min_cA==F(13,27) and min_cA<F(1,2))
    actual_RQ = prod((1+F(q,(q-1)*(q-2)) for q in Q),start=F(1))-1
    need('30 control actual complete source query norm',actual_RQ==F(214267985,147806208))
    rho = sum((F(1,q-2) for q in Q),F(0))+F(1,15)
    N_generic = B+F(10,11)*(1+B)
    rho_star = 33*(1-F(49,566)*N_generic-K3/66-K7/22)
    need('30 control generic580 rho test fails',rho>rho_star)
    mass_lower = 1-rho/33-K3/66-K7/22
    N_actual = actual_RQ+F(10,11)*(1+actual_RQ)
    query_actual = N_actual/mass_lower
    need('30 control actual580 source budget passes',mass_lower>0 and query_actual<F(566,49))
    all_active_mass = F(1,15)*prod((F(1,q-2) for q in Q[1:]),start=F(1))
    need('30 control seven-active positive source event',all_active_mass==F(1,1893375))
    return {'originals':originals,'original_count':30,'source_rows':source_rows,
            'source_density':ex(source_density),'source_complete_RQ':ex(actual_RQ),
            'rho_A':ex(rho),'generic580_rho_threshold':ex(rho_star),'rho_excess':ex(rho-rho_star),
            'gamma_overlap':ex(0),'actual_incidence_patterns':fibre_count,
            'minimum_cA':ex(min_cA),'seven_active_source_mass':ex(all_active_mass),
            'actual580_mass_lower':ex(mass_lower),'actual580_raw_query_upper':ex(N_actual),
            'actual580_normalized_query_upper':ex(query_actual),
            'scope':'The two shallow d25 originals are redundant. Actual-source 580 already passes; this control is not a new noncoverage class. Seven active labels occur, so the separate <=6 two-height corollary does not apply.'}



parser=ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
INPUT='height_three_clipping_envelope.json'
INPUT_SHA256='276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685'
B=F(432040125182653876501,86355045355449035400)
qs=[11,13,17,19]
cs=[F(5,3),F(3,2),F(2),F(9,5)]
ts=[2,2,4,4]
eta=[F(641451990131,13653911814400),F(130632977,5642112320),F(118307,16692640),F(1,6498)]
checks=0

def need(c,name=None):
 global checks
 if not c: raise ValueError(name or 'exact check '+str(checks+1))
 checks+=1

def spec(p,c=None,mass=F(1)):
 if c is None:return mass,mass+F(1,p-1),lambda n:(mass-F(1,p) if n==1 else F(p-1,p**n))
 return F(1),1+c/F(p-1),lambda n:(1-c/F(p) if n==1 else c*F(p-1,p**n))

def hinge(ss,t):
 mass=F(1);mean=F(1);low={1:F(1)}
 for m,mu,atom in ss:
  mass*=m;mean*=mu
  new={}
  for v,z in low.items():
   for n in range(1,t):
    if v*n<t:new[v*n]=new.get(v*n,F(0))+z*atom(n)
  low=new
 return mean-t*mass+sum(((t-v)*z for v,z in low.items()),F(0)),low

suffix={r:[hinge([spec(q,c) for q,c in zip(qs[i:],cs[i:])],r)[0] for i in range(5)] for r in [3,4,8]}
for i in range(4):need(suffix[3][i]==suffix[3][i+1]+cs[i]*eta[i])
K={3:F(0),7:F(0)}
corner_rows=[]
for x,y in product([F(1,2),F(1)],[F(2,3),F(1)]):
 ss=[spec(5,mass=x),spec(7,mass=y)]
 prefix=x*y-F(1,12);charges=[];J=F(0)
 for q,c,t,e in zip(qs,cs,ts,eta):
  fq,low=hinge(ss,t)
  aq=2*c/F(q-1);charges.append(aq*fq)
  d=lambda n:e*(c-F(q-1,q-1-2*n))
  J+=sum((d(n)*low.get(n,F(0)) for n in range(1,t)),F(0))-d(1)*(x*y-prefix)
  prefix-=charges[-1]
  ss.append(spec(q,c))
 alpha=prefix
 ph3=hinge(ss,3)[0]
 d0=suffix[3][0]/12+sum((s*z for s,z in zip(suffix[3][1:],charges)),F(0))
 need((B-2)*alpha-ph3+d0+J>=0)
 row={'x':str(x),'y':str(y),'alpha':str(alpha),'B_corner_margin':str((B-2)*alpha-ph3+d0+J)}
 for t in [3,7]:
  ph=hinge(ss,t+1)[0]
  debit=suffix[t+1][0]/12+sum((s*z for s,z in zip(suffix[t+1][1:],charges)),F(0))
  z=(ph-debit)/alpha;K[t]=max(K[t],z);row['K'+str(t)]=str(z)
 corner_rows.append(row)
for t in [3,7]:
 for z in suffix[t+1]:need(K[t]>=z)
# Compare independently reconstructed K values with retained arithmetic artifacts.
raw=(args.source_dir/INPUT).read_bytes()
need(sha256(raw).hexdigest()==INPUT_SHA256)
data=json.loads(raw)
need(B==F(data['B']))
for t in [3,7]:need(K[t]==max(F(c['K_integer'][t]) for c in data['corners']))

# The decisive joint-penalty inequality, retaining old eta and J coefficients.
for q,C,e,zeta in zip(qs,cs,eta,suffix[3][1:]):
 w=B-2-zeta;tau=1-1/C
 need(w>=e*C)
 def penalty(v):
  if v>=tau:return w*C*(v-tau)
  return -e*(C-1/(1-v))
 for i in range(41):
  f=F(i,40)
  for j in range(i,161):
   U=F(j,40);D=U-f
   gam=C*min(D,max(U-tau,0))
   need(penalty(U)-penalty(f)>=w*gam)
   # Exact actual loss identity works even when nominal U exceeds one.
   need(C*max(f-tau,0)==C*max(U-tau,0)-gam)

c3=F(10,33)*(K[3]-suffix[4][1])
cR=F(10,33)*(B-2-suffix[3][1])
N=B+F(10,11)*(1+B)
rho=33*(1-F(49,566)*N-K[3]/66-K[7]/22)
eps0=rho+c3/2+F(3087,566)*cR-6
need(eps0>0)
need(c3/2+F(3087,566)*cR<6)
control=thirty_original_control(B,K[3],K[7],min(F(c['alpha']) for c in data['corners']),lambda name,c:need(c,name))
result={'zero_overlap_control':control,'schema':'actual-selected-overlap-v1','sources':[{'path':INPUT,'sha256':INPUT_SHA256}],'scope':'Ordinary joint overlap refinement; rational checks supplement the general proof. Conditional continuation, not new Lean or unrestricted Erdos7' ,'checks':checks,'K':{str(k):str(v) for k,v in K.items()},'suffix':{str(k):[str(v) for v in z] for k,z in suffix.items()},'corner_rows':corner_rows,'c3':str(c3),'cR':str(cR),'rho_star':str(rho),'epsilon0':str(eps0),'epsilon0_decimal':float(eps0)}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['checks','c3','cR','epsilon0','epsilon0_decimal']},indent=2))
