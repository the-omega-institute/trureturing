#!/usr/bin/env python3
"""Report479: exact union-inventory envelope for independent center choices.

Keeps A+B-C, so labels matching both centers occur only once. The actual
source law need not have independent coordinates. This finite certificate
consumes the ordinary source construction and analytic tail theorem; it
does not enumerate original families or constitute Lean certification.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import gcd,lcm,prod
from functools import reduce
from hashlib import sha256
from pathlib import Path
import argparse,json
STATES=tuple((a,b,c) for a in range(1,20) for b in range(1,20) for c in range(1,min(a,b)+1) if a+b-c<=19)
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
SPLITS=tuple(range(1,20)) #19 covers all h>=19 and coincident paths
BOXES=((2,2),(3,1))
INPUTS={'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d','common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def row(p,h,cap=F(1),pure=False):
 out=defaultdict(F)
 def put(i,j,w):out[(i+1,j+1,min(i,j)+1)]+=w
 for j in range(h):put(j,j,F(p-1,p**(j+1)))
 if h<19:
  put(h,h,F(p-2,p**(h+1)))
  for j in range(h+1,19):
   put(j,h,F(p-1,p**(j+1)));put(h,j,F(p-1,p**(j+1)))
 out={s:cap*w for s,w in out.items()};out[(1,1,1)]+=1-cap
 mass=F(1)
 if pure:out[(1,1,1)]-=F(1,p-1);mass-=F(1,p-1)
 need(all(w>=0 for w in out.values()) and sum(out.values())<=mass,'positive comparison row')
 return out,mass

def compare_monotone(table,den,mass):
 top=mass*den;need(top.denominator==1,'integer mass');top=top.numerator
 need(all(0<=v<=top for v in table.values()),'range')
 for a,b,c in STATES:
  old=table[(a,b,c)]
  for u in range(1,20//a+1):
   for v in range(1,20//b+1):
    nxt=(a*u,b*v,c*min(u,v))
    need(old<=table.get(nxt,top),'multiplicative baseline monotonicity')

def advance(table,den,p,cap,pure=False):
 # All omitted local atoms already have union load at least twenty.
 # Compute total mass minus the finite GOOD contribution using integers.
 measures=[row(p,h,cap,pure) for h in SPLITS]
 d=lcm(*(w.denominator for out,mass in measures for w in out.values()))
 mass=measures[0][1];newden=den*d;top=mass*newden
 need(top.denominator==1,'transition mass denominator');top=top.numerator
 rows=[tuple((*s,(w*d).numerator) for s,w in out.items() if w) for out,_ in measures]
 need(all((w*d).denominator==1 for out,_ in measures for w in out.values()),'integer transition weights')
 new={};choices={}
 for a,b,c in STATES:
  values=[top-sum(w*(den-table.get((a*u,b*v,c*t),den)) for u,v,t,w in rr) for rr in rows]
  j=max(range(len(values)),key=values.__getitem__);new[(a,b,c)]=values[j];choices[(a,b,c)]=SPLITS[j]
  need(all(new[(a,b,c)]>=v for v in values),'all action inequalities')
 divisor=reduce(gcd,new.values(),newden)
 if divisor>1:newden//=divisor;new={s:v//divisor for s,v in new.items()}
 compare_monotone(new,newden,mass)
 need(all(new[a,b,c]==new[b,a,c] for a,b,c in STATES),'center exchange symmetry')
 return new,newden,choices

def valuation(n,p):
 need(n!=0,'finite valuation at zero');e=0
 while n%p==0:n//=p;e+=1
 return e

DEPTH=19
BAD=(20,20,20)
def local(p,E,forbidden,min_h):
 # Enumerate reference prefixes; every deeper split has an exact geometric
 # law. DEPTH represents all later splits, including coincident paths.
 den=p**DEPTH;P=p**E;sigs={};raw=0
 for a in range(P):
  for b in range(P):
   for h in (range(E,20) if a==b else (valuation(a-b,p),)):
    if h<min_h:continue
    raw+=1;roots=[defaultdict(int) for _ in range(p)]
    for x in range(P):
     if any(x%m==r for m,r in forbidden):continue
     inc=defaultdict(int)
     def put(i,j,w):inc[(i+1,j+1,min(i,j)+1)]+=w
     if x!=a and x!=b:put(valuation(x-a,p),valuation(x-b,p),p**(DEPTH-E))
     elif a!=b:
      for j in range(E,DEPTH):
       if x==a:put(j,h,(p-1)*p**(DEPTH-j-1))
       else:put(h,j,(p-1)*p**(DEPTH-j-1))
     else:
      for j in range(E,h):put(j,j,(p-1)*p**(DEPTH-j-1))
      if h<DEPTH:
       put(h,h,(p-2)*p**(DEPTH-h-1))
       for j in range(h+1,DEPTH):
        put(j,h,(p-1)*p**(DEPTH-j-1));put(h,j,(p-1)*p**(DEPTH-j-1))
     inc[BAD]+=p**(DEPTH-E)-sum(inc.values())
     need(all(w>=0 for w in inc.values()) and sum(inc.values())==p**(DEPTH-E),'cell mass')
     for s,w in inc.items():roots[x%p][s]+=w
    sig=tuple(tuple(sorted((s,w) for s,w in rr.items() if w)) for rr in roots)
    for r,rr in enumerate(roots):
     cells=sum(x%p==r and not any(x%m==v for m,v in forbidden) for x in range(P))
     need(sum(rr.values())==cells*p**(DEPTH-E),'root mass')
    sigs.setdefault(sig,(a,b,h))
 return tuple((ref,sig) for sig,ref in sigs.items()),den,raw

def combine(roots,ids):
 out=defaultdict(int)
 for r in ids:
  for s,w in roots[r]:out[s]+=w
 return tuple(sorted(out.items()))

def anchor(table,den,m3,m5):
 l3,d3,raw3=local(3,3,((3,0),(9,1),(27,4)),m3)
 l5,d5,raw5=local(5,2,((5,0),(25,1)),m5)
 r3=[(ref,combine(rr,(1,)),combine(rr,(2,))) for ref,rr in l3]
 r5=[(ref,combine(rr,(1,2,3,4)),combine(rr,(1,3,4))) for ref,rr in l5]
 for _,r1,r2 in r3:need(sum(w for _,w in r1)*27==5*d3 and sum(w for _,w in r2)*3==d3,'R1 R2')
 for _,v,w in r5:need(sum(z for _,z in v)*25==19*d5 and sum(z for _,z in w)*25==14*d5,'V5 W5')
 c5=tuple(sorted({s for _,v,w in r5 for rr in (v,w) for s,z in rr}))
 c3=tuple(sorted({s for _,v,w in r3 for rr in (v,w) for s,z in rr}))
 values={(s,t):table.get(tuple(a*b for a,b in zip(s,t)),den) for s in c3 for t in c5}
 best=-1;wit=None;checks=0
 for ref3,r1,r2 in r3:
  ev={t:sum(w*values[s,t] for s,w in r1) for t in c5};ew={t:sum(w*values[s,t] for s,w in r2) for t in c5}
  for ref5,v,w in r5:
   val=sum(z*ev[s] for s,z in v)+sum(z*ew[s] for s,z in w);checks+=1
   if val>best:best=val;wit=(ref3,ref5)
 result=F(best,d3*d5*den)
 need(result<F(63,4000),'positive source target')
 return {'prefix_depths':(m3,m5),'maximum':result,'upper_bound':F(63,4000),'maximizer':wit,'raw_ternary_cases':raw3,'raw_quinary_cases':raw5,'ternary_signatures':len(l3),'quinary_signatures':len(l5),'joint_checks':checks}

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [encode(v) for v in x]
 return x

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);a=ap.parse_args()
 inputs={}
 for name,sha in INPUTS.items():
  raw=(a.input_dir/name).read_bytes();need(sha256(raw).hexdigest()==sha,'input identity '+name);inputs[name]=json.loads(raw)
 source=inputs['common_law_mass_tail.json']['common_seven_core_law'];m7=F(source['unnormalized_mass_lower']);cap=F(source['unnormalized_joint_density_cap'])
 need(m7==F(7235955529,450000000000) and cap==F(27,2),'same source constants')
 need([F(x) for x in source['conditional_caps']]==[c for p,c in CAPS],'same conditional caps')
 need(len(STATES)==1330 and prod(c for p,c in CAPS)==cap,'state count and joint density cap')
 table={s:0 for s in STATES};den=1;stages=[]
 for p,c in reversed(CAPS):
  table,den,_=advance(table,den,p,c);stages.append({'prime':p,'unit_BAD_upper':F(table[1,1,1],den)});print('stage',p,float(F(table[1,1,1],den)),flush=True)
 anchored=[anchor(table,den,*box) for box in BOXES]
 t5,d5,_=advance(table,den,5,F(1),True)
 # Positive half-mass pure3 comparison; t5 is a3/4-mass payoff.
 top5=F(3,4)*d5;need(top5.denominator==1,'pure5 absorbing value')
 generic=max(sum(w*F(t5.get(s,top5.numerator),d5) for s,w in row(3,h,F(1),True)[0].items()) + (F(1,2)-sum(row(3,h,F(1),True)[0].values()))*F(3,4) for h in SPLITS)
 need(generic<F(9,400),'other coarse types generic bound')
 groups=defaultdict(list)
 for rr in inputs['query_stoploss_completion.json']['rows']:groups[tuple(rr['node'][:3])].append(F(rr['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()),'all coarse source vertices')
 gap=m7-F(63,4000);margins={}
 for key,ms in groups.items():
  upper=F(63,4000) if key==(2,4,1) else F(9,400);margins[str(key)]=min(ms)-upper
  need(margins[str(key)]>=gap,'same source margin')
 need(gap>F(1,3100),'uniform GOOD mass')
 need(min((22-u)*(28-u)-u for u in range(1,20))==8,'original fibre floor')
 haar=gap/(cap*77);need(haar>F(1,3222450),'original density')
 # Chapter33 applies after switching to Haar restricted to head survivors.
 B=150000000;ell=17
 M2=prod(F(p*(p+1),(p-1)**2) for p in (3,5,7,11,13,17,19,23,29))
 c=F(2*ell*ell+1,2*ell*ell-1);series=F(1);falling=1
 for j in range(1,8):
  falling*=8-j;series+=F(falling,ell**j)
 need(B>=286 and ell>=4 and 3**ell<=B and c==F(579,577),'analytic tail parameters')
 need(M2==F(14003665,540672),'head second moment factor')
 tau=c**7/F(B)*F(B,B-3)**2*series
 loss=M2*tau;remaining=F(1,3222450)-loss
 need(remaining>F(1,40000000),'positive distorted tail mass')
 tail={'head_second_moment_factor':M2,'B':B,'ell':ell,'c':c,'falling_factorial_series':series,'tau7':tau,'loss_upper':loss,'head_seed_strict_lower':F(1,3222450),'remaining_distorted_mass_lower':remaining,'remaining_distorted_mass_strict_lower':F(1,40000000),'ordinary_analytic_input':'Chapter33 SH11-SH13 analytic prime-product bound, not reproved by this consumer'}
 out={'scope':'independent per-full-label choice of two references; each p>=7 shares first digit; ternary/quinary depths satisfy (h3>=2,h5>=2) OR (h3>=3,h5>=1); arbitrary simultaneous deeper splits, old-only residues and finite heights','inputs':INPUTS,'state_count':len(STATES),'stages':stages,'generic_pure_upper':generic,'generic_rational_bound':F(9,400),'anchors':anchored,'coarse_good_margins':margins,'same_source_mass_lower':m7,'same_source_density_cap':cap,'uniform_GOOD_lower':gap,'uniform_GOOD_strict_lower':F(1,3100),'original_fibre_mass_floor':F(1,77),'original_Haar_lower':haar,'original_Haar_strict_lower':F(1,3222450),'unrestricted_large_prime_tail':tail,'source_producers_rerun':False,'Lean_rerun':False,'unrestricted_erdos7_resolved':False}
 if a.output:a.output.write_text(json.dumps(encode(out),indent=2)+'\n')
 print('generic',float(generic),'anchors',[float(x['maximum']) for x in anchored],'gap',gap,'Haar',haar,flush=True)
if __name__=='__main__':main()
