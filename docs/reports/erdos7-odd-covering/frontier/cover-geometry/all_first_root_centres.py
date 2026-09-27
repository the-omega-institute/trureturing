"""Verify all seven first-root splits with four exact pair certificates.

Report489. The standard-library consumer reconstructs every signed profile,
all44 worst-source reference weight classes and all used literal pair bounds.
The same-source construction, full-graph upward comparison and pair theorem
are ordinary mathematical inputs, not new Lean certification.
"""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import prod,factorial
from pathlib import Path
import argparse,hashlib,importlib.util,json

FLOOR_DENOMINATOR=10000000000000
HAAR_FLOOR=F(1,1000000000)
KAPPA=F(1,3)

def need(ok,message):
 if not ok:raise ValueError(message)

def natural(value):
 need(type(value) in (int,str),'integer certificate field')
 n=int(value)
 need(n>=0 and str(n)==str(value),'canonical nonnegative integer')
 return n

def adjacent_module(name,filename):
 path=Path(__file__).resolve().parent/filename
 need(path.is_file(),'missing adjacent helper: '+filename)
 spec=importlib.util.spec_from_file_location(name,path)
 need(spec is not None and spec.loader is not None,'cannot load helper: '+filename)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 return module

def profiles():
 rows=[]
 def extend(prefix,a,b):
  if len(prefix)==7:
   if a+b>=21:rows.append(prefix)
   return
  extend(prefix+(0,),a,b)
  for f in range(2,1+(39-b)//a):extend(prefix+(f,),a*f,b)
  for f in range(2,1+(39-a)//b):extend(prefix+(-f,),a,b*f)
 for sign in (1,-1):
  for u in range(2,39):
   for sign5 in (1,-1,0):
    for v in (range(2,39) if sign5 else (1,)):
     a=(u if sign>0 else 1)*(v if sign5>0 else 1)
     b=(u if sign<0 else 1)*(v if sign5<0 else 1)
     if a+b<=39:extend((sign*u,sign5*v),a,b)
 need(len(rows)==577578 and len(set(rows))==len(rows),'complete distinct retained profiles')
 return rows

def initial_weights(signature,vectors,rootkeys):
 a3,b3,aA,bA,oA,aB,bB,oB=(vectors[i] for i in signature)
 out=[]
 for s3,s5 in rootkeys:
  ternary=a3 if s3>0 else b3
  quinary=((aA,bA,oA) if s3>0 else (aB,bB,oB))[0 if s5>0 else 1 if s5<0 else 2]
  out.append(ternary[abs(s3)]*quinary[abs(s5) if s5 else 1])
 return out

def tail_bound():
 B=100000000000;ell=23;c=F(2*ell*ell+1,2*ell*ell-1)
 need(B>=286 and ell>=4 and 3**ell<=B,'Chapter33 tail applicability')
 M2=prod(F(p*(p+1),(p-1)**2) for p in (3,5,7,11,13,17,19,23,29))
 series=sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 loss=M2*c**7/F(B)*F(B,B-3)**2*series
 remaining=HAAR_FLOOR-loss
 need(remaining>F(1,2000000000),'strict positive distorted tail reserve')
 return {'B':B,'ell':ell,'c':str(c),'M2':str(M2),'series':str(series),
         'head_Haar_strict_lower':str(HAAR_FLOOR),'loss_upper':str(loss),
         'remaining_distorted_lower':str(remaining),
         'remaining_distorted_lower_float':float(remaining),
         'remaining_distorted_strict_lower':'1/2000000000',
         'ordinary_input':'Chapter33 analytic prime-product estimate and conditional continuation.'}

def verify(input_dir,certificate_path):
 canonical=adjacent_module('all_first_pair','fixed_anchor_two_fibre.py')
 scalar=adjacent_module('all_first_scalar','all_first_root_source_types.py')
 scalar_result=scalar.verify(input_dir,canonical)
 worst=next(r for r in scalar_result['all_source_types'] if r['coarse_type']==[2,4,1])
 need(F(worst['source_mass_lower'])==canonical.M7,'same worst source mass')
 mass,vectors,classes=scalar.classes(2,4,1)
 need(mass==F(221,675) and len(classes)==44,'worst joint anchor and weight classes')
 scalars={tuple(r['reference']):r for r in worst['all_classes']}
 need(sum(r['configuration_count'] for r in classes.values())==24300,'complete reference coverage')
 rows=profiles();N=len(rows)
 q=[prod(max(1,f) for f in s)+prod(max(1,-f) for f in s)-1 for s in rows]
 need(all(20<=x<=38 for x in q),'retained profile range')
 rootkeys=sorted(set(s[:2] for s in rows));rootindex={s:i for i,s in enumerate(rootkeys)}
 rootids=[rootindex[s[:2]] for s in rows]
 @lru_cache(None)
 def later(fs):
  return prod(1-2*c/p if f==0 else c*F(p-1,p**f) for (p,c),f in zip(canonical.CAPS,fs))
 laterweights=[later(tuple(abs(f) for f in s[2:])) for s in rows]
 @lru_cache(None)
 def pair_bound(a,b,n):return canonical.solve(a,b,n)['K']
 need(pair_bound(20,20,40)==0 and pair_bound(20,39,40)==0,'diagonal and overflow zero witnesses')
 initial={tuple(meta['reference']):initial_weights(sig,vectors,rootkeys) for sig,meta in classes.items()}
 payload=certificate_path.read_bytes();certs=json.loads(payload)['certificates']
 need(len(certs)==4,'four retained certificates')
 certificates=[];metadata=[];edge_union=set();minimum=None
 for cert in certs:
  denominator=natural(cert['denominator'])
  need(denominator>0 and denominator%FLOOR_DENOMINATOR==0,'certificate and floor denominators')
  reference=tuple(cert['reference']);need(reference in initial,'certificate reference class')
  incident=defaultdict(int);seen=set();budget=0;cert_min=None
  for row in cert['edges']:
   need(len(row)==3,'edge triple');i,j,units=(natural(v) for v in row)
   need(i<N and j<N and i!=j and units>0,'valid positive edge')
   key=(min(i,j),max(i,j));need(key not in seen,'duplicate undirected edge');seen.add(key)
   cross1=prod(min(max(1,x),max(1,-y)) for x,y in zip(rows[i],rows[j]))
   cross2=prod(min(max(1,-x),max(1,y)) for x,y in zip(rows[i],rows[j]))
   nn=q[i]+q[j]+2-cross1-cross2
   need(max(q[i],q[j])+1<=nn<=q[i]+q[j],'literal common-selector capacity')
   k=pair_bound(min(q[i],q[j]),max(q[i],q[j]),nn)
   need(k>=KAPPA,'used edge below threshold')
   cert_min=k if cert_min is None else min(cert_min,k)
   incident[i]+=units;incident[j]+=units;budget+=units
  need(budget>0,'nonempty positive certificate')
  own=initial[reference]
  for i,units in incident.items():
   w=own[rootids[i]]*laterweights[i]
   need(units*w.denominator<=denominator*w.numerator,'certificate exceeds own exact weight')
  edge_union.update(seen);minimum=cert_min if minimum is None else min(minimum,cert_min)
  certificates.append((denominator,incident,budget))
  metadata.append({'reference':list(reference),'denominator':str(denominator),
                   'edge_rows':len(seen),'incident_vertices':len(incident),
                   'budget_units':str(budget),'minimum_K':str(cert_min)})
 allclasses=[]
 for sig,meta in classes.items():
  ref=tuple(meta['reference']);base=scalars[ref];weights=initial[ref]
  need(base['configuration_count']==meta['configuration_count'],'same reference-class multiplicity')
  bad=F(base['BAD20']);bounds=[]
  # A downward rational floor can only enlarge the unpaid capacity deficit.
  @lru_cache(None)
  def floor_weight(rootid,laterweight):
   a=weights[rootid];numer=a.numerator*laterweight.numerator*FLOOR_DENOMINATOR
   return numer//(a.denominator*laterweight.denominator)
  for index,(denominator,incident,budget) in enumerate(certificates):
   scale=denominator//FLOOR_DENOMINATOR
   deficit=sum(max(0,units-scale*floor_weight(rootids[i],laterweights[i])) for i,units in incident.items())
   bound=bad-F(budget-deficit,denominator)
   bounds.append({'certificate_index':index,'capacity_deficit_units':str(deficit),
                  'exact_upper':str(bound),'upper_float':float(bound)})
  best=min(range(len(bounds)),key=lambda i:F(bounds[i]['exact_upper']))
  upper=F(bounds[best]['exact_upper']);need(upper<canonical.M7,'reference class not below same-source mass')
  allclasses.append({'reference':list(ref),'configuration_count':meta['configuration_count'],
                    'BAD20':str(bad),'overflow39':base['overflow39'],
                    'certificate_bounds':bounds,'best_certificate_index':best,
                    'best_exact_upper':str(upper),'best_upper_float':float(upper)})
 uniform=max(F(r['best_exact_upper']) for r in allclasses)
 margin=canonical.M7-uniform;haar=margin/F(49896)
 need(haar>HAAR_FLOOR and F(scalar_result['strict_nonworst_original_Haar_lower'])>HAAR_FLOOR,
      'all source types have the common original Haar floor')
 return {'scope':__doc__,'source_inputs':scalar_result['source_inputs'],
         'certificate_sha256':hashlib.sha256(payload).hexdigest(),
         'profiles':N,'reference_configurations':24300,'classes':44,
         'floor_weight_denominator':str(FLOOR_DENOMINATOR),'source_mass_lower':str(canonical.M7),
         'certificates':metadata,'distinct_used_edges':len(edge_union),
         'capacity_triples':pair_bound.cache_info().currsize,'minimum_K':str(minimum),
         'selected_certificate_counts':dict(Counter(str(r['best_certificate_index']) for r in allclasses)),
         'all_classes':allclasses,'uniform_exact_upper':str(uniform),
         'uniform_upper_float':float(uniform),'uniform_margin':str(margin),
         'uniform_original_Haar_lower':str(haar),'uniform_original_Haar_lower_float':float(haar),
         'original_Haar_strict_lower':str(HAAR_FLOOR),
         'nonworst_reference_classes':sum(r['weight_classes'] for r in scalar_result['all_source_types'] if r['coarse_type']!=[2,4,1]),
         'unrestricted_large_prime_tail':tail_bound(),'source_producers_rerun':False,'Lean_rerun':False,
         'boundary':'All seven first digits split; full original labels choose two fixed centres independently. Source construction, pair optimizer theorem, full-theoretical-graph upward closure, full-history comparison, deleted-root transport and analytic tail estimate are ordinary arguments or inherited inputs. Arbitrary separation depths, unrelated old residues and unrestricted Erdos7 remain unresolved.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);adjacent=Path(__file__).resolve().parent
 ap.add_argument('--input-dir',type=Path,default=adjacent)
 ap.add_argument('--certificate',type=Path,default=adjacent/'all_first_root_centres_certificate.json')
 ap.add_argument('--output',type=Path);args=ap.parse_args()
 result=verify(args.input_dir,args.certificate)
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==result,'retained exact result differs')
 print(json.dumps({key:result[key] for key in ('profiles','classes','distinct_used_edges','minimum_K',
       'uniform_upper_float','uniform_original_Haar_lower_float','original_Haar_strict_lower')},indent=2))

if __name__=='__main__':main()
