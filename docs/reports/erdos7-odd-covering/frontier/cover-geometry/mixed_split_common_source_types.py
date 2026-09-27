"""Exact nonworst source bounds for every split/common pattern at five primes.

Report491. The centres have distinct first roots at3,5; at each remaining old
prime they either split at the first root or share every queried digit.
This checker uses a backward rational recursion, the literal eight joint
anchors and all32 source vertices. The actual-source comparison is ordinary
mathematics; this is not new Lean certification.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod,factorial
from pathlib import Path
import argparse,importlib.util,json

CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))

def need(ok,message):
 if not ok:raise ValueError(message)

def adjacent_module(name,filename):
 path=Path(__file__).resolve().parent/filename
 need(path.is_file(),'missing adjacent helper: '+filename)
 spec=importlib.util.spec_from_file_location(name,path)
 need(spec is not None and spec.loader is not None,'cannot load helper: '+filename)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 return module

@lru_cache(None)
def good(a,b,c,mask,index=0):
 if c*(a+b-1)>19:return F()
 if index==len(CAPS):return F(1)
 p,cap=CAPS[index];split=bool(mask&(1<<index))
 base=1-(2 if split else 1)*cap/p
 need(base>=0,'positive comparison baseline')
 value=base*good(a,b,c,mask,index+1)
 if split:
  for f in range(2,(19//c+1-b)//a+1):
   value+=cap*F(p-1,p**f)*good(a*f,b,c,mask,index+1)
  for f in range(2,(19//c+1-a)//b+1):
   value+=cap*F(p-1,p**f)*good(a,b*f,c,mask,index+1)
 else:
  for f in range(2,19//(c*(a+b-1))+1):
   value+=cap*F(p-1,p**f)*good(a,b,c*f,mask,index+1)
 return value

def patterns(mask):
 result=[]
 for region in ('AA','AB','AO','BA','BB','BO'):
  for u in range(2,20):
   for v in ((1,) if region[1]=='O' else range(2,20)):
    a=(u if region[0]=='A' else 1)*(v if region[1]=='A' else 1)
    b=(u if region[0]=='B' else 1)*(v if region[1]=='B' else 1)
    if a+b<=20:result.append((region,u,v,good(a,b,1,mask)))
 return result

def tail_bound():
 B=100000000;ell=16;c=F(2*ell*ell+1,2*ell*ell-1)
 need(B>=286 and ell>=4 and 3**ell<=B,'Chapter33 analytic tail parameters')
 M2=prod(F(p*(p+1),(p-1)**2) for p in (3,5,7,11,13,17,19,23,29))
 loss=M2*c**7/F(B)*F(B,B-3)**2*sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 reserve=F(1,2000000)-loss
 need(reserve>F(1,20000000),'positive distorted tail reserve')
 return {'B':B,'ell':ell,'c':str(c),'M2':str(M2),'head_Haar_strict_lower':'1/2000000',
         'loss_upper':str(loss),'remaining_distorted_lower':str(reserve),
         'remaining_distorted_lower_float':float(reserve),
         'remaining_distorted_strict_lower':'1/20000000'}

def verify(input_dir):
 canonical=adjacent_module('mixed_source_pair','fixed_anchor_two_fibre.py')
 scalar=adjacent_module('mixed_source_anchor','all_first_root_source_types.py')
 need(canonical.CAPS==scalar.CAPS==CAPS,'same full-history source caps')
 identities=canonical.source_inputs(input_dir)
 groups=defaultdict(list)
 for row in json.loads((input_dir/'query_stoploss_completion.json').read_text())['rows']:
  groups[tuple(row['node'][:3])].append(F(row['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()),'all32 source vertices')
 masses={t:min(v) for t,v in groups.items()}
 initial={t:scalar.classes(*t) for t in product((1,2),(2,4),(1,2))}
 for p,cap in CAPS:
  for multiplicity in (1,2):
   need(1-multiplicity*cap/p+ multiplicity*(sum(cap*F(p-1,p**f) for f in range(2,20))+cap/F(p**19))==1,
        'each comparison law retains its full geometric tail')
 subsets=[];all_gaps=[]
 for mask in range(32):
  pattern=patterns(mask);types=[]
  for typ,(anchor,vectors,classes) in initial.items():
   rows=[]
   for sig,meta in classes.items():
    a3,b3,aA,bA,oA,aB,bB,oB=(vectors[i] for i in sig)
    coords={'AA':(a3,aA),'AB':(a3,bA),'AO':(a3,oA),'BA':(b3,aB),'BB':(b3,bB),'BO':(b3,oB)}
    safe=sum(coords[tag][0][u]*coords[tag][1][v]*pay for tag,u,v,pay in pattern)
    bad=anchor-safe;gap=masses[typ]-bad
    need(0<=bad<=anchor,'complete safe/bad mass accounting')
    if typ!=(2,4,1):
     need(gap>F(3,5000),'nonworst class exceeds common positive margin')
     all_gaps.append(gap)
    rows.append({**meta,'BAD20':str(bad),'BAD20_float':float(bad),
                 'margin_own_source':str(gap),'passes_own_source':gap>0})
   worst=max(rows,key=lambda r:F(r['BAD20']))
   types.append({'coarse_type':list(typ),'source_mass':str(masses[typ]),
                 'anchor_mass':str(anchor),'anchor_cells':int(anchor*675),
                 'weight_classes':len(rows),'worst':worst,
                 'failed_own_source_classes':sum(not r['passes_own_source'] for r in rows),
                 'all_classes':rows})
  subsets.append({'mask':mask,'split_primes':[p for j,(p,cap) in enumerate(CAPS) if mask&(1<<j)],
                  'all_source_types':types})
 need(len(all_gaps)==8832,'all32 times276 nonworst reference classes')
 gap=min(all_gaps);haar=gap/F(27,2)/77
 need(haar>F(1,2000000),'uniform nonworst original Haar floor')
 return {'scope':__doc__,'source_inputs':identities,'subsets':32,
         'source_types_per_subset':8,'classes_per_subset':320,
         'nonworst_classes':len(all_gaps),'nonworst_reference_configurations':32*7*24300,
         'all_subsets':subsets,'uniform_nonworst_margin_own_source':str(gap),
         'uniform_nonworst_original_Haar_lower':str(haar),
         'uniform_nonworst_original_Haar_lower_float':float(haar),
         'original_Haar_strict_lower':'1/2000000','large_prime_tail':tail_bound(),
         'source_producers_rerun':False,'Lean_rerun':False,
         'boundary':'All32 split/common patterns at7,11,13,17,19 with first-root splits at3,5. The seven nonworst source types pass. Same-source conditional domination, deleted-root transport and legal completion are ordinary arguments. Worst-source mixed patterns, arbitrary finite separation depths, unrelated old residues and unrestricted Erdos7 are not settled.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--output',type=Path);args=ap.parse_args();result=verify(args.input_dir)
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==result,'retained result differs')
 print(json.dumps({k:result[k] for k in ('subsets','nonworst_classes','nonworst_reference_configurations',
       'uniform_nonworst_original_Haar_lower_float','original_Haar_strict_lower')},indent=2))

if __name__=='__main__':main()
