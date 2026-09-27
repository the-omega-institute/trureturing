"""Reconstruct every coarse source's initial joint anchor and scalar BAD20.

All seven old coordinates have distinct A/B first digits. A is globally labelled
root2 at3, B root1; both5 references lie in distinct nonzero roots. Other deleted
first-root cases require the accompanying finite original-family reduction.
Only Python's standard library and the canonical source identity verifier are
used; no worst-type weight table or scratch producer is imported.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import prod,factorial
import argparse,hashlib,importlib.util,json
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M_OTHER=F(5891133457,225000000000)
MAX_FACTOR=39
HAAR_FLOOR=F(1,400000)

def need(b,msg):
 if not b:raise ValueError(msg)

@lru_cache(None)
def shell(p,E,ref,cells):
 out=[F() for _ in range(MAX_FACTOR)]
 for x in cells:
  if x==ref:
   for f in range(E+1,MAX_FACTOR):out[f]+=F(p-1,p**f)
  else:
   d=x-ref;v=0
   while d%p==0:d//=p;v+=1
   out[v+1]+=F(1,p**E)
 need(sum(out)+(F(1,p**(MAX_FACTOR-1)) if ref in cells else F())==F(len(cells),p**E),
      'complete initial shell and geometric tail mass')
 return tuple(out)

@lru_cache(None)
def finish(a,b,threshold,index=0):
 # Q=A+B-1, so Q<threshold iff A+B<=threshold.
 if a+b>threshold:return F()
 if index==len(CAPS):return F(1)
 p,c=CAPS[index]
 baseline=1-2*c/p;need(baseline>=0,'positive two-axis conditional comparison')
 value=baseline*finish(a,b,threshold,index+1)
 for f in range(2,(threshold-b)//a+1):
  value+=c*F(p-1,p**f)*finish(a*f,b,threshold,index+1)
 for f in range(2,(threshold-a)//b+1):
  value+=c*F(p-1,p**f)*finish(a,b*f,threshold,index+1)
 return value

def patterns(threshold):
 out=[]
 for region in ('AA','AB','AO','BA','BB','BO'):
  for u in range(2,threshold):
   for v in ((1,) if region[1]=='O' else range(2,threshold)):
    a=(u if region[0]=='A' else 1)*(v if region[1]=='A' else 1)
    b=(u if region[0]=='B' else 1)*(v if region[1]=='B' else 1)
    if a+b<=threshold:out.append((region,u,v,finish(a,b,threshold)))
 return out

def classes(alpha,beta,gamma):
 c3A=tuple(x for x in range(27) if x%3==2 and x%9!=1 and x!=beta)
 c3B=tuple(x for x in range(27) if x%3==1 and x%9!=1 and x!=beta)
 def cells5(root3):
  return tuple(y for y in range(25) if y%5!=0 and y!=gamma
               and not(root3==alpha and y%5==alpha))
 c5A,c5B=cells5(2),cells5(1)
 mass=F(len(c3A)*len(c5A)+len(c3B)*len(c5B),675)
 literal=sum(all(n%m!=a for a,m in ((0,3),(1,9),(beta,27),(0,5),(gamma,25),(alpha,15))) for n in range(675))
 need(mass==F(literal,675),'literal six anchors match joint rectangles')
 vectors=[];index={}
 def intern(v):
  if v not in index:index[v]=len(vectors);vectors.append(v)
  return index[v]
 t3A={a:intern(shell(3,3,a,c3A)) for a in range(2,27,3)}
 t3B={b:intern(shell(3,3,b,c3B)) for b in range(1,27,3)}
 allowed5=[r for r in range(25) if r%5]
 t5={};others={}
 for name,cells in (('A',c5A),('B',c5B)):
  for a in allowed5:
   t5[name,a]=intern(shell(5,2,a,tuple(y for y in cells if y%5==a%5)))
  for a,b in product(allowed5,repeat=2):
   if a%5==b%5:continue
   v=[F() for _ in range(MAX_FACTOR)];v[1]=F(sum(y%5 not in (a%5,b%5) for y in cells),25)
   others[name,a,b]=intern(tuple(v))
 out={}
 for a3,b3,a5,b5 in product(t3A,t3B,allowed5,allowed5):
  if a5%5==b5%5:continue
  key=(t3A[a3],t3B[b3],t5['A',a5],t5['A',b5],others['A',a5,b5],
       t5['B',a5],t5['B',b5],others['B',a5,b5])
  out.setdefault(key,{'reference':[a3,b3,a5,b5],'configuration_count':0})['configuration_count']+=1
 need(sum(r['configuration_count'] for r in out.values())==24300,'all ordered reference configurations')
 return mass,vectors,out

def large_prime_tail():
 B=100000000;ell=16;c=F(2*ell*ell+1,2*ell*ell-1)
 need(B>=286 and ell>=4 and 3**ell<=B,'inherited Chapter33 tail hypotheses')
 M2=prod(F(p*(p+1),(p-1)**2) for p in (3,5,7,11,13,17,19,23,29))
 tau=c**7/F(B)*F(B,B-3)**2*sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 loss=M2*tau;remaining=HAAR_FLOOR-loss
 need(remaining>F(1,500000),'positive distorted mass after arbitrary large-prime continuation')
 return {'B':B,'ell':ell,'c':str(c),'M2':str(M2),'head_Haar_strict_lower':str(HAAR_FLOOR),
         'loss_upper':str(loss),'remaining_distorted_mass_lower':str(remaining),
         'remaining_distorted_mass_lower_float':float(remaining),
         'remaining_distorted_mass_strict_lower':'1/500000',
         'ordinary_input':'Chapter33 analytic prime-product estimate; this checker only evaluates its exact rational consumer.'}

def verify(input_dir,canonical):
 need(canonical.CAPS==CAPS,'paired comparison caps match actual source')
 identities=canonical.source_inputs(input_dir)
 src=json.loads((input_dir/'query_stoploss_completion.json').read_text());groups=defaultdict(list)
 for r in src['rows']:groups[tuple(r['node'][:3])].append(F(r['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()),'all32 source vertices')
 masses={k:min(v) for k,v in groups.items()}
 need(min(v for k,v in masses.items() if k!=(2,4,1))==M_OTHER,'seven-source common minimum')
 for p,c in CAPS:
  need(1-2*c/p+2*sum(c*F(p-1,p**f) for f in range(2,39))+2*c/F(p**38)==1,
       'paired positive law and both infinite geometric tails')
 P20,P39=patterns(20),patterns(39)
 need(all(finish(a,b,t)==finish(b,a,t) for t in (20,39) for a in range(1,t) for b in range(1,t-a+1)),
      'later paired payoff keeps global centre-exchange symmetry')
 results=[]
 for key in product((1,2),(2,4),(1,2)):
  mass,vecs,cc=classes(*key);rows=[]
  for sig,meta in cc.items():
   a3,b3,aA,bA,oA,aB,bB,oB=(vecs[i] for i in sig)
   coords={'AA':(a3,aA),'AB':(a3,bA),'AO':(a3,oA),'BA':(b3,aB),'BB':(b3,bB),'BO':(b3,oB)}
   good20=sum(coords[r][0][u]*coords[r][1][v]*pay for r,u,v,pay in P20)
   good39=sum(coords[r][0][u]*coords[r][1][v]*pay for r,u,v,pay in P39)
   bad=mass-good20;overflow=mass-good39;need(0<=overflow<=bad<=mass,'full initial and later tails retained')
   rows.append({**meta,'BAD20':str(bad),'BAD20_float':float(bad),'overflow39':str(overflow),
                'source_gap':str(masses[key]-bad),'passes_own_source_mass':bad<masses[key],
                'passes_common_nonworst_mass':bad<M_OTHER})
  rows.sort(key=lambda r:F(r['BAD20']),reverse=True)
  maxbad=F(rows[0]['BAD20']);gap=masses[key]-maxbad
  results.append({'coarse_type':list(key),'anchor_mass':str(mass),'anchor_cells_mod675':int(mass*675),
                  'source_mass_lower':str(masses[key]),'source_mass_lower_float':float(masses[key]),
                  'reference_configurations':24300,'weight_classes':len(rows),
                  'worst':rows[0],'failed_own_mass_classes':sum(not r['passes_own_source_mass'] for r in rows),
                  'failed_common_mass_classes':sum(not r['passes_common_nonworst_mass'] for r in rows),
                  'strict_original_Haar_bound_if_positive':str(gap/F(27,2)/77),
                  'all_classes':rows})
 nonworst=[r for r in results if r['coarse_type']!=[2,4,1]]
 rounded=F(47,2000)
 need(all(F(r['worst']['BAD20'])<rounded<M_OTHER for r in nonworst),'all seven literal anchors below one strict scalar bound')
 haar=(M_OTHER-rounded)/F(27,2)/77
 need(haar>HAAR_FLOOR,'strict common nonworst original Haar floor')
 return {'scope':__doc__,'source_inputs':identities,'comparison_baselines':[str(1-2*c/p) for p,c in CAPS],
         'common_nonworst_mass_lower':str(M_OTHER),'strict_nonworst_BAD_upper':str(rounded),
         'strict_nonworst_original_Haar_lower':str(haar),'readable_nonworst_Haar_strict_lower':'1/400000',
         'all_source_types':results,
         'nonworst_types_passing_own_mass':sum(r['failed_own_mass_classes']==0 for r in nonworst),
         'nonworst_types_passing_common_mass':sum(r['failed_common_mass_classes']==0 for r in nonworst),
         'nonworst_worst_BAD20':str(max(F(r['worst']['BAD20']) for r in nonworst)),
         'nonworst_worst_BAD20_float':float(max(F(r['worst']['BAD20']) for r in nonworst)),
         'unrestricted_large_prime_tail':large_prime_tail(),
         'source_producers_rerun':False,'Lean_rerun':False,
         'boundary':'Scalar comparison of literal coarse anchors with globally labelled references and all seven first digits split; same-source geometry must be paired with its own coarse lower mass. The finite deleted-root reduction, selectable completion for a missing shallow modulus, full-history comparison and Chapter33 analytic tail estimate are ordinary arguments or inputs. The worst coarse type is not settled; unrestricted Erdos7 remains open.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--output',type=Path);args=ap.parse_args()
 helper=Path(__file__).resolve().parent/'fixed_anchor_two_fibre.py'
 need(helper.is_file(),'adjacent canonical source verifier is missing')
 spec=importlib.util.spec_from_file_location('canonical_pair',helper)
 need(spec is not None and spec.loader is not None,'canonical source verifier cannot be loaded')
 canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
 out=verify(args.input_dir,canonical)
 if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==out,'adjacent retained exact result differs')
 print(json.dumps({'nonworst_pass_types':out['nonworst_types_passing_own_mass'],
                   'nonworst_common_mass_pass_types':out['nonworst_types_passing_common_mass'],
                   'nonworst_worst_BAD20':out['nonworst_worst_BAD20_float'],
                   'type_summaries':[{'type':r['coarse_type'],'classes':r['weight_classes'],
                                     'maxBAD':r['worst']['BAD20_float'],'mass':r['source_mass_lower_float'],
                                     'fail_classes':r['failed_own_mass_classes']} for r in out['all_source_types']]},indent=2))
if __name__=='__main__':main()
