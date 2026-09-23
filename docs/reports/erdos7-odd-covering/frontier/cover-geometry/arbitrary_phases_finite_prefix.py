#!/usr/bin/env python3
"""Report480: unsafe-mass bound for arbitrary phases after a common prefix.

Ordinary inputs: the actual source law, conditional domination, source-budget
interpolation, finite-prefix inventory implication and analytic prime tail.
The finite calculation is not Lean certification or original-family enumeration.
"""
from fractions import Fraction as F
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from math import prod,gcd
import argparse,json
P=(3,5,7,11,13,17,19)
CAPS=(F(1),F(1),F(3,2),F(5,3),F(3,2),F(2),F(9,5))
HEIGHTS=(5,4,3,3,3,3,3)
INPUTS={'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d','common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def valuation(x,p):
 need(x!=0,'valuation at zero');j=0
 while x%p==0:j+=1;x//=p
 return j

def safe_convolution(primes,caps,heights,pure=False):
 need(len(primes)==len(caps)==len(heights),'one cap and prefix per coordinate')
 dist={1:F(1)};mass=F(1)
 for p,cap,h in zip(primes,caps,heights):
  need(h>=1,'positive prefix depth')
  row={v+1:cap*F(p-1,p**(v+1)) for v in range(min(h,19))};row[1]=1-cap/p
  local_mass=F(1)
  if pure and p in (3,5):row[1]-=F(1,p-1);local_mass-=F(1,p-1)
  need(all(w>=0 for w in row.values()) and sum(row.values())<=local_mass,'positive safe submeasure')
  nxt=defaultdict(F)
  for a,w in dist.items():
   for b,z in row.items():
    if a*b<20:nxt[a*b]+=w*z
  dist=dict(nxt);mass*=local_mass
 need(all(w>=0 for w in dist.values()) and sum(dist.values())<=mass,'safe convolution mass')
 return dist,mass

def anchor_positions(p,E,h,forbidden):
 """Exact common-reference distribution:20 is already unsafe, not a depth."""
 size=p**E;sigs={}
 for a in range(size):
  roots=[defaultdict(F) for _ in range(p)]
  for x in range(size):
   if any(x%m==r for m,r in forbidden):continue
   inc=defaultdict(F)
   if x!=a:
    v=valuation(x-a,p);inc[v+1 if v<h and v<19 else 20]+=F(1,size)
   else:
    for v in range(E,min(h,19)):inc[v+1]+=F(p-1,p**(v+1))
    inc[20]+=F(1,size)-sum(inc.values())
   need(all(w>=0 for w in inc.values()) and sum(inc.values())==F(1,size),'anchor cell mass')
   for t,w in inc.items():roots[x%p][t]+=w
  for r,row in enumerate(roots):
   count=sum(x%p==r and not any(x%m==z for m,z in forbidden) for x in range(size))
   need(sum(row.values())==F(count,size),'anchor root mass')
  sig=tuple(tuple(sorted((t,w) for t,w in row.items() if w)) for row in roots);sigs.setdefault(sig,a)
 return tuple((a,sig) for sig,a in sigs.items())

def combine(roots,ids):
 out=defaultdict(F)
 for r in ids:
  for t,w in roots[r]:out[t]+=w
 return tuple(sorted(out.items()))

def actual_anchor_bound(heights):
 later,total=safe_convolution(P[2:],CAPS[2:],heights[2:]);need(total==1,'later source comparison total')
 payoff={t:F(1)-sum(w for d,w in later.items() if t*d<20) for t in range(1,21)}
 need(all(payoff[t]<=payoff[t+1] for t in range(1,20)) and payoff[20]==1,'monotone unsafe payoff')
 r3=anchor_positions(3,3,heights[0],((3,0),(9,1),(27,4)))
 r5=anchor_positions(5,2,heights[1],((5,0),(25,1)))
 maxval=F(-1);witness=None;checks=0
 for a,roots3 in r3:
  R1=combine(roots3,(1,));R2=combine(roots3,(2,))
  need(sum(w for t,w in R1)==F(5,27) and sum(w for t,w in R2)==F(1,3),'ternary region masses')
  ev={t:sum(w*payoff[min(s*t,20)] for s,w in R1) for t in range(1,21)}
  ew={t:sum(w*payoff[min(s*t,20)] for s,w in R2) for t in range(1,21)}
  for b,roots5 in r5:
   V5=combine(roots5,(1,2,3,4));W5=combine(roots5,(1,3,4))
   need(sum(w for t,w in V5)==F(19,25) and sum(w for t,w in W5)==F(14,25),'quinary region masses')
   value=sum(w*ev[t] for t,w in V5)+sum(w*ew[t] for t,w in W5);checks+=1
   if value>maxval:maxval=value;witness=(a,b)
 need(maxval<F(3,200),'worst source unsafe bound')
 return {'maximum':maxval,'upper_bound':F(3,200),'reference_prefix_maximizer':witness,'raw_ternary_positions':27,'raw_quinary_positions':25,'ternary_signatures':len(r3),'quinary_signatures':len(r5),'joint_checks':checks,'later_safe_product_weights':later}

def phase_scope_control(D):
 d=3**6;old=[0,3**5,2*3**5];rows=[]
 for j,r in enumerate(old,1):
  new=23**j;m=d*new;c=(r+d*((-r*pow(d,-1,new))%new))%m
  need(c%d==r and c%new==0 and (c%gcd(d,D))==0,'literal original CRT phase')
  rows.append({'m':m,'c':c,'old_cofactor':d,'old_residue':r,'new_exponent':j})
 need(len({r['m'] for r in rows})==3 and len({r['old_residue'] for r in rows})==3,'three independent residues at one cofactor')
 return {'classes':rows,'excludes_two_center_representation':'All three original labels have the same old cofactor and three distinct old residues; two fixed centers can supply at most two such residues.'}

def enc(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [enc(v) for v in x]
 return x

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);args=ap.parse_args()
 inputs={}
 for name,sha in INPUTS.items():
  raw=(args.input_dir/name).read_bytes();need(sha256(raw).hexdigest()==sha,'retained source identity '+name);inputs[name]=json.loads(raw)
 law=inputs['common_law_mass_tail.json']['common_seven_core_law'];m7=F(law['unnormalized_mass_lower']);cap=F(law['unnormalized_joint_density_cap'])
 need(m7==F(7235955529,450000000000) and cap==F(27,2),'same source constants')
 need(tuple(F(x) for x in law['conditional_caps'])==CAPS[2:],'same conditional caps')
 need(prod(CAPS[2:])==cap,'joint source density cap')
 groups=defaultdict(list)
 for row in inputs['query_stoploss_completion.json']['rows']:groups[tuple(row['node'][:3])].append(F(row['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()) and min(groups[(2,4,1)])==m7,'complete coarse source binding')
 generic_dist,mass=safe_convolution(P,CAPS,HEIGHTS,True);generic=mass-sum(generic_dist.values())
 need(mass==F(3,8) and generic<F(17,1000),'generic pure-anchor unsafe upper')
 anchor=actual_anchor_bound(HEIGHTS);gap=m7-F(3,200);margins={}
 for coarse,vs in groups.items():
  bound=F(3,200) if coarse==(2,4,1) else F(17,1000);margins[str(coarse)]=min(vs)-bound
  need(margins[str(coarse)]>=gap,'same source uniform safe margin')
 need(min((22-u)*(28-u)-u for u in range(1,20))==8,'original fibre floor')
 haar=gap/(cap*77);need(haar>F(1,1000000),'original survivor Haar bound')
 D=prod(p**h for p,h in zip(P,HEIGHTS));need(D==5133293432417701175625,'finite prefix modulus')
 control=phase_scope_control(D)
 B=100000000;ell=16;c=F(2*ell*ell+1,2*ell*ell-1);series=F(1);falling=1
 for j in range(1,8):falling*=8-j;series+=F(falling,ell**j)
 M2=prod(F(p*(p+1),(p-1)**2) for p in (*P,23,29));need(M2==F(14003665,540672),'head moment factor')
 need(B>=286 and ell>=4 and 3**ell<=B and c==F(513,511),'analytic-tail integer premises')
 tau=c**7/F(B)*F(B,B-3)**2*series;loss=M2*tau;remaining=F(1,1000000)-loss
 need(remaining>F(1,2000000),'unrestricted large-prime tail survives')
 out={'scope':'arbitrary independently chosen deeper old residues, requiring c=a mod gcd(d,D) for every original23/29-touching label; old-only residues and all finite heights unrestricted','inputs':INPUTS,'prefix_primes':P,'prefix_heights':HEIGHTS,'D':D,'generic_unsafe_upper':generic,'generic_rational_bound':F(17,1000),'six_cylinder_anchor':anchor,'coarse_safe_margins':margins,'uniform_safe_mass_lower':gap,'original_fibre_floor':F(1,77),'original_Haar_lower':haar,'original_Haar_strict_lower':F(1,1000000),'three_phase_scope_control':control,'large_prime_tail':{'B':B,'ell':ell,'M2':M2,'c':c,'tau7':tau,'loss_upper':loss,'remaining_distorted_mass_lower':remaining,'remaining_distorted_mass_strict_lower':F(1,2000000),'ordinary_analytic_input':'Chapter33 SH11-SH13 prime-product estimate as used in reports477-479'},'source_producers_rerun':False,'Lean_rerun':False,'unrestricted_erdos7_resolved':False}
 if args.output:args.output.write_text(json.dumps(enc(out),indent=2)+'\n')
 print('generic',float(generic),'anchor',float(anchor['maximum']),'source safe>',gap,'Haar>',haar,'tail remaining>',remaining)
if __name__=='__main__':main()
