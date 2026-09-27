#!/usr/bin/env python3
"""Exact BAD bounds for independent class choices with one differing coordinate.
The original-fibre inventory, common actual source, conditional domination,
source interpolation and normalization transport are ordinary proof inputs.
No Lean or unrestricted Erdos7 conclusion is claimed.
"""
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
from hashlib import sha256
from math import prod
import argparse,json
PRIMES=(3,5,7,11,13,17,19)
CAPS={3:F(1),5:F(1),7:F(3,2),11:F(5,3),13:F(3,2),17:F(2),19:F(9,5)}
INPUTS={'query_stoploss_completion.json':'44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d','common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def shell(p,j):return F(p-1,p**(j+1))
def valuation(n,p):
 need(n!=0,'finite valuation called at zero');e=0
 while n%p==0:n//=p;e+=1
 return e

def haar_max(p,j,h):
 if h is None or j<h:return shell(p,j)
 if j==h:return F(p-2,p**(j+1))
 return 2*shell(p,j)

def local_weights(p,h,pure=False):
 cap=CAPS[p]
 weights={j+1:cap*haar_max(p,j,h) for j in range(19)}
 weights[1]=1-cap*(1-haar_max(p,0,h))
 mass=F(1)
 if pure:
  need(p in (3,5),'pure scope')
  deleted=F(1,p-1);weights[1]-=deleted;mass-=deleted
 need(all(w>=0 for w in weights.values()) and sum(weights.values())<=mass,'positive capped or pure comparison')
 return weights,mass

def convolve(primes,q,h,pure=False):
 weights={1:F(1)};mass=F(1)
 for p in primes:
  row,r_mass=local_weights(p,h if p==q else None,pure and p in (3,5));mass*=r_mass
  out=defaultdict(F)
  for a,w in weights.items():
   for b,v in row.items():
    if a*b<=19:out[a*b]+=w*v
  weights=dict(out)
 need(all(v>=0 for v in weights.values()) and sum(weights.values())<=mass,'finite GOOD mass')
 return weights,mass

def split_depths(q):return tuple(range(1 if q in (3,5) else 0,20))

def generic(q):
 vals={}
 for h in split_depths(q):
  weights,mass=convolve(PRIMES,q,h,True)
  need(mass==F(3,8),'pure product carrier mass');vals[h]=mass-sum(weights.values())
 best=max(vals,key=vals.get)
 need(vals[best]<F(9,500),'every admitted generic bound is below9/500')
 return {'all_depth_bounds':vals,'maximum':vals[best],'maximizing_split':best,'positive_comparison_mass':F(3,8)}

def local_anchor(p,E,forbidden,split,same_root):
 """Filter physical path prefixes before exact signature deduplication."""
 sigs={};raw=0;P=p**E
 for a in range(P):
  for b in (range(P) if split else (a,)):
   if same_root and a%p!=b%p:continue
   hs=range(E,20) if split and a==b else (valuation(a-b,p),) if split else (19,)
   for h in hs:
    raw+=1;roots=[defaultdict(F) for _ in range(p)]
    for x in range(P):
     if any(x%m==r for m,r in forbidden):continue
     inc=defaultdict(F)
     if x!=a and x!=b:inc[max(valuation(x-a,p),valuation(x-b,p))+1]=F(1,P)
     elif a!=b:
      for j in range(E,19):inc[j+1]+=shell(p,j)
     else:
      for j in range(E,19):inc[j+1]+=haar_max(p,j,h)
     inc[20]+=F(1,P)-sum(inc.values())
     need(all(w>=0 for w in inc.values()) and sum(inc.values())==F(1,P),'anchor cell mass')
     for t,w in inc.items():roots[x%p][t]+=w
    for r,row in enumerate(roots):
     count=sum(x%p==r and not any(x%m==v for m,v in forbidden) for x in range(P))
     need(sum(row.values())==F(count,P),'root mass')
    sig=tuple(tuple(sorted((t,w) for t,w in row.items() if w)) for row in roots)
    sigs.setdefault(sig,(a,b,h))
 return tuple((ref,sig) for sig,ref in sigs.items()),raw

def combine(roots,ids):
 out=defaultdict(F)
 for r in ids:
  for t,w in roots[r]:out[t]+=w
 return tuple(sorted(out.items()))

def anchor(q,subtract_pure3_tail=False):
 need(q in (3,7,11),'selected anchor scope')
 rows3,raw3=local_anchor(3,3,((3,0),(9,1),(27,4)),q==3,q==3)
 rows5,raw5=local_anchor(5,2,((5,0),(25,1)),False,False)
 regions3=[(ref,combine(roots,(1,)),combine(roots,(2,))) for ref,roots in rows3]
 regions5=[(ref,combine(roots,(1,2,3,4)),combine(roots,(1,3,4))) for ref,roots in rows5]
 for _,r1,r2 in regions3:need(sum(w for _,w in r1)==F(5,27) and sum(w for _,w in r2)==F(1,3),'R1/R2 masses')
 for _,v,w in regions5:need(sum(z for _,z in v)==F(19,25) and sum(z for _,z in w)==F(14,25),'V5/W5 masses')
 best=F(-1);wit=None;count=0
 for h in (range(20) if q in (7,11) else (19,)):
  dist,mass=convolve((7,11,13,17,19),q,h)
  need(mass==1,'later comparator probability')
  payoff={t:F(1)-sum(w for d,w in dist.items() if t*d<=19) for t in range(1,21)}
  need(all(isinstance(v,F) for v in payoff.values()),'exact rational payoff')
  need(all(payoff[t]<=payoff[t+1] for t in range(1,20)),'increasing payoff')
  for ref5,v,w in regions5:
   vpay={t:sum(z*payoff[min(20,t*s)] for s,z in v) for t in range(1,21)}
   wpay={t:sum(z*payoff[min(20,t*s)] for s,z in w) for t in range(1,21)}
   for ref3,r1,r2 in regions3:
    original=sum(z*vpay[t] for t,z in r1)+sum(z*wpay[t] for t,z in r2)
    credit=F()
    if subtract_pure3_tail:
     min1=min(t for t,z in r1 if z);min2=min(t for t,z in r2 if z)
     credit=F(1,54)*min(vpay[min1],wpay[min2])
    value=original-credit
    need(0<=value<=1 and credit>=0,'anchor upper range')
    count+=1
    if value>best:best=value;wit={'ternary_reference':ref3,'quinary_reference':ref5,'split_depth':h if q in (7,11) else ref3[2],'six_cylinder_integral':original,'pure3_tail_credit':credit}
 bounds={3:F(19,1200),7:F(1601,100000),11:F(3,200)}
 need(best<bounds[q],'chosen rational anchor upper')
 return {'maximum':best,'upper_bound':bounds[q],'maximizer':wit,'raw_ternary_cases':raw3,'raw_quinary_cases':raw5,'ternary_signatures':len(rows3),'quinary_signatures':len(rows5),'joint_checks':count,'pure3_tail_mass':F(1,54) if subtract_pure3_tail else F()}

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [encode(v) for v in x]
 return x

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input-dir',type=Path,default=Path(__file__).parent);ap.add_argument('--output',type=Path);args=ap.parse_args()
 inputs={}
 for name,expected in INPUTS.items():
  raw=(args.input_dir/name).read_bytes();need(sha256(raw).hexdigest()==expected,'retained input identity: '+name);inputs[name]=json.loads(raw)
 law=inputs['common_law_mass_tail.json']['common_seven_core_law']
 m7=F(law['unnormalized_mass_lower']);cap=F(law['unnormalized_joint_density_cap'])
 need(m7==F(7235955529,450000000000) and cap==F(27,2),'same source constants')
 need([F(c) for c in law['conditional_caps']]==[CAPS[p] for p in (7,11,13,17,19)],'same conditional caps')
 groups=defaultdict(list)
 for row in inputs['query_stoploss_completion.json']['rows']:groups[tuple(row['node'][:3])].append(F(row['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()),'all32 source vertices')
 need(min(groups[(2,4,1)])==m7 and all(min(v)>=m7 for v in groups.values()),'same coarse source lower bounds')
 gen={q:generic(q) for q in PRIMES};anc={q:anchor(q,q==7) for q in (3,7,11)}
 common_bound=F(1601,100000);gap=m7-common_bound
 margins={}
 for q in PRIMES:
  margins[q]={}
  for coarse,masses in groups.items():
   bound=anc[q]['upper_bound'] if q in anc and coarse==(2,4,1) else gen[q]['maximum']
   margins[q][str(coarse)]=min(masses)-bound
   need(margins[q][str(coarse)]>=gap,'every allowed coordinate and source has uniform gap')
 need(gap>F(1,15000),'positive same-source GOOD margin')
 need(prod(CAPS[p] for p in (7,11,13,17,19))==cap,'joint density cap')
 need(min(max(22-q,0)*max(28-q,0)-q for q in range(1,20))==8,'original fibre floor')
 haar=gap/(cap*77)
 need(haar>F(1,15592500)>F(1,16000000),'original Haar lower')
 B=1000000000;ell=18
 M2=prod(F(p*(p+1),(p-1)**2) for p in (*PRIMES,23,29))
 need(M2==F(14003665,540672),'head Haar second moment factor')
 c=F(2*ell*ell+1,2*ell*ell-1);series=F(1);falling=1
 for j in range(1,8):
  falling*=8-j;series+=F(falling,ell**j)
 need(B>=286 and ell>=4 and 3**ell<=B and c==F(649,647),'analytic-tail arithmetic parameters')
 tau=c**7/F(B)*F(B,B-3)**2*series
 loss=M2*tau;remaining=F(1,15592500)-loss
 need(remaining>F(1,50000000),'positive distorted tail mass')
 tail={'head_second_moment_factor':M2,'B':B,'ell':ell,'c':c,'falling_factorial_series':series,'tau7':tau,'loss_upper':loss,'head_seed_strict_lower':F(1,15592500),'remaining_distorted_mass_lower':remaining,'remaining_distorted_mass_strict_lower':F(1,50000000),'ordinary_analytic_input':'Chapter33 SH11-SH13 analytic prime-product premise, as retained in report477; not reproved by this consumer'}
 out={'scope':'independent per-original-class choice of two reference residues; references may differ in one old coordinate q; q=3 or5 requires a shared first digit; other six coordinates share every original queried depth; original old-only phases and all finite heights unrestricted','inputs':INPUTS,'same_source_mass_lower':m7,'same_source_density_cap':cap,'generic_bounds':gen,'six_cylinder_bounds':anc,'all_coarse_margins':margins,'uniform_BAD_bound_at_worst_source':common_bound,'uniform_GOOD_mass_lower':gap,'uniform_GOOD_strict_lower':F(1,15000),'original_fibre_mass_floor':F(1,77),'original_Haar_lower':haar,'original_Haar_strict_lower':F(1,15592500),'rounded_original_Haar_strict_lower':F(1,16000000),'unrestricted_large_prime_tail':tail,'source_producers_rerun':False,'Lean_rerun':False,'unrestricted_erdos7_resolved':False}
 text=json.dumps(encode(out),indent=2)+'\n'
 if args.output:args.output.write_text(text)
 for q in PRIMES:
  print('coordinate',q,'generic',float(gen[q]['maximum']),'anchor',float(anc[q]['maximum']) if q in anc else None)
 print('GOOD>',gap,'Haar>',haar)
if __name__=='__main__':main()
