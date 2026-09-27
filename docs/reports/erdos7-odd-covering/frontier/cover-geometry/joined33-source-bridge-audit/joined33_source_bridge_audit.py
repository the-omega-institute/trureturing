#!/usr/bin/env python3
"""Independently realize joined marginals from explicit retained NPZ fields.

No debit transform or producer imports. Rebuild each outside category from its
literal q^2 residues; check all original predicates are constant on categories;
then contract their exact common mass with root-event indicator fractions.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from hashlib import sha256
from math import prod
import argparse,json,time,base64,io
import numpy as np
BASE=Path(__file__).resolve().parent
Q=(7,11,13,17,19); P=(3,5)+Q;CHECKS=0
def ck(condition,label):
 global CHECKS
 CHECKS+=1
 if not condition:raise AssertionError(label)

def audit(path):
 start=time.perf_counter();data=json.loads(path.read_text())
 for name,digest in data['source_sha256'].items():ck(sha256((BASE/name).read_bytes()).hexdigest()==digest,'raw source pin')
 originals=json.loads((BASE/'clustered_global_phase_fixture.json').read_text())['actual_originals']
 high=json.loads((BASE/'clustered_higher_pure_capacity_obstruction.json').read_text())['first_tested_success']
 added=high['added_higher_pure_originals'];all_originals=originals+added
 ck(len(all_originals)==len({o['modulus'] for o in all_originals})==109,'all109 actual original labels')
 ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)},'actual eight higher pure phases')
 def pure_power(d,p):
  while d%p==0:d//=p
  return d==1
 leaf_weights={};leaf_support={};central_source=[]
 for p in (3,5):
  pure=[o for o in all_originals if pure_power(o['modulus'],p)]
  depth=max(o['modulus'] for o in pure)
  survivors=[z for z in range(depth) if all(z%o['modulus']!=o['residue'] for o in pure)]
  capacities={r:F(sum(z%(p*p)==r for z in survivors),depth) for r in range(p*p)}
  row=next(r for r in high['capacities'] if r['prime']==p)
  weak=row['weak_leaf_residue'];reference_density=F(row['reference_density'])
  ck(capacities[weak]==F(row['haar_capacity']),'enumerated weak actual-survivor capacity')
  ck(F(row['weight'])/(reference_density*capacities[weak])==F(row['gamma'])==F(high['gamma'+str(p)]),'assigned weak-leaf density normalization')
  ck(all(cap==F(1,p*p) for r,cap in capacities.items() if cap and r!=weak),'all nonweak occupied leaves remain complete')
  weights={r:(F(row['weight']) if r==weak else reference_density*cap) for r,cap in capacities.items() if cap}
  ck(sum(weights.values(),F(0))==1,'assigned central coordinate reference is a probability')
  # Root-major indices are obtained from actual occupied residues, rather
  # than presumed from the published five/nineteen-element menus.
  leaf_support[p]=sorted((r%p)*p+r//p for r in weights)
  leaf_weights[p]={(r%p)*p+r//p:mass for r,mass in weights.items()}
  central_source.append({'prime':p,'enumerated_residues':depth,'actual_pure_survivors':len(survivors),
                         'weak_capacity':str(capacities[weak]),'weak_assigned_mass':str(weights[weak]),
                         'normal_reference_density':str(reference_density),'weak_gamma':row['gamma']})
 # Original mixed numerical moduli split into exactly one central component
 # and at most two outside components; all actual deletion phases are read.
 local={q:[] for q in Q};outside_pairs=[];contained_pairs=[]
 for row in all_originals:
  d,b=row['modulus'],row['residue'];central=d;factors=[]
  for q in Q:
   power=1
   while central%q==0:central//=q;power*=q
   if power>1:factors.append((q,power))
  if len(factors)==1:
   q,power=factors[0]
   ck(225%central==0 and power<=q*q,'local mixed predicate resolved by declared central/outside atoms')
   local[q].append((central,b%central,power,b%power))
  if len(factors)==2:
   q,r=(factor[0] for factor in factors);pq=q*r
   # Literal E(d,b) is a subset of E(pq,1) exactly under this divisibility
   # and residue condition, even when d also has central/higher factors.
   ck(d%pq==0 and b%pq==1,'every two-outside original lies in corresponding pure pq-phase1 deletion')
   contained_pairs.append((d,b,pq))
   if d==pq:
    ck(b==1,'literal pure pq original canonical phase')
    outside_pairs.append((d,b,tuple(factors)))
  ck(len(factors)<=2,'actual source local/pair original format')
 ck(len(outside_pairs)==10 and {(d,b) for d,b,_ in outside_pairs}=={(q*r,1) for q,r in combinations(Q,2)},'all10 containing pure pq deletion events are original classes')
 ck(len(contained_pairs)==40,'all40 two-outside originals accounted for by exact event containment')
 cats={q:[(1,),tuple(1+q*k for k in range(1,q))]+
          [tuple(r+q*k for k in range(q)) for r in range(2,min(q,9))]+
          ([tuple(r+q*k for r in range(9,q) for k in range(q))] if q>9 else []) for q in Q}
 shape=tuple(len(cats[q]) for q in Q)
 central_mixed=[o for o in originals if all(o['modulus']%q for q in Q)
                and not pure_power(o['modulus'],3) and not pure_power(o['modulus'],5)]
 ck([(o['modulus'],o['residue']) for o in central_mixed]==[(15,0)],'literal central mixed deletion')
 cells=[]
 for l,m in product(leaf_support[3],leaf_support[5]):
  z=next(z for z in range(225) if z%9==3*(l%3)+l//3 and z%25==5*(m%5)+m//5)
  if all(z%o['modulus']!=o['residue'] for o in central_mixed):cells.append((l,m))
 # Use an independent CRT search instead of the producer's closed formula.
 residues=[next(z for z in range(225) if z%9==3*(l%3)+l//3 and z%25==5*(m%5)+m//5) for l,m in cells]
 ck(data['central']['residues_mod225']==residues,'central canonical coordinate order')
 ck(data['central']['points']==[[z%9,z%25] for z in residues],'central points from same residue')
 source=np.zeros((len(cells),)+shape,dtype=np.int64)
 # Pair exclusions are tested on literal category representatives. Every
 # category has one fixed truth value for being root1, so this is exact.
 pair_allowed=np.ones(shape,dtype=bool)
 for d,b,factors in outside_pairs:
  (q,qp),(r,rp)=factors;i,j=Q.index(q),Q.index(r)
  rows=[]
  for t in (q,r):
   values=[]
   for cat in cats[t]:
    hits=[z%t==b%t for z in cat];ck(all(hits) or not any(hits),'pair predicate constant per category');values.append(all(hits))
   rows.append(np.array(values,dtype=bool))
  si=[1]*5;sj=[1]*5;si[i]=len(cats[q]);sj[j]=len(cats[r])
  pair_allowed&=~(rows[0].reshape(si)&rows[1].reshape(sj))
 for ci,((l,m),z) in enumerate(zip(cells,residues)):
  central_numerator=675*leaf_weights[3][l]*leaf_weights[5][m]
  ck(central_numerator.denominator==1,'derived assigned central product numerator')
  tensor=np.full(shape,int(central_numerator),dtype=np.int64)
  for axis,q in enumerate(Q):
   counts=[]
   for cat in cats[q]:
    keep=[all(z%cm!=cr or atom%qm!=qr for cm,cr,qm,qr in local[q]) for atom in cat]
    ck(all(keep) or not any(keep),'literal original local deletion constant on pooled category')
    counts.append(sum(keep))
   dims=[1]*5;dims[axis]=len(counts);tensor*=np.array(counts,dtype=np.int64).reshape(dims)
  source[ci]=tensor*pair_allowed
 source_den=675*prod(q*(q-1) for q in Q)
 ck(int(np.count_nonzero(source))==2125830 and F(int(source.sum()),source_den)==F(305684996597,646498195200),'whole original fixed source counts')
 if data['field_file'] is None:
  ck(data['field'] in ('allone','all_one_actual109') and data['field_sha256'] is None,'explicit constant-one source field only')
  fd=1;fn=(source>0).astype(np.uint8)
 else:
  field_path=Path(data['field_file'])
  if not field_path.is_absolute():field_path=path.parent/field_path
  field_bytes=field_path.read_bytes();ck(sha256(field_bytes).hexdigest()==data['field_sha256'],'explicit field byte pin')
  field_source=io.BytesIO(base64.b64decode(field_bytes,validate=True)) if field_path.suffix=='.b64' else io.BytesIO(field_bytes)
  with np.load(field_source,allow_pickle=False) as saved:
   fn=saved['numerators'].copy();fd=int(saved['denominator'][0])
   ck(fn.shape==source.shape and fn.dtype.kind in 'iu','finite field integer carrier')
   ck(np.array_equal(saved['central_residues'],residues),'field coordinate order')
 ck(np.all(fn>=0) and np.all(fn<=fd) and np.all(fn[source==0]==0),'literal submeasure0≤f≤1')
 mass=source.astype(object)*fn.astype(object)
 ck(int(data['denominator'])==source_den*fd,'one common mass denominator')
 # Verify every root pair by a direct event-matrix contraction of the full
 # retained tensor. This does not infer joint realizability from consistency.
 rootkernels={}
 for q in Q:
  rootkernels[q]=np.array([[F(sum(z%q==a for z in cat),len(cat)) for a in range(q)] for cat in cats[q]],dtype=object)
 central=mass.sum(axis=(1,2,3,4,5))
 ck(list(map(int,central))==data['central']['weights'],'all80 fine central masses')
 one={3:[sum(int(n) for z,n in zip(residues,central) if z%3==a) for a in range(3)],
      5:[sum(int(n) for z,n in zip(residues,central) if z%5==a) for a in range(5)]}
 matrices={}
 matrices[3,5]=np.array([[sum(int(n) for z,n in zip(residues,central) if z%3==a and z%5==b) for b in range(5)] for a in range(3)],dtype=object)
 for i,q in enumerate(Q):
  axis=i+1
  marginal=mass.sum(axis=tuple(k for k in range(6) if k!=axis))
  one[q]=list(marginal@rootkernels[q])
  central_joint=mass.sum(axis=tuple(k for k in range(1,6) if k!=axis))
  physical_joint=central_joint@rootkernels[q]
  for p in (3,5):
   matrices[p,q]=np.array([[sum(physical_joint[ci,b] for ci,z in enumerate(residues) if z%p==a) for b in range(q)] for a in range(p)],dtype=object)
 for i,j in combinations(range(5),2):
  q,r=Q[i],Q[j];marginal=mass.sum(axis=tuple(k for k in range(6) if k not in (i+1,j+1)))
  matrices[q,r]=rootkernels[q].T@marginal@rootkernels[r]
 for p in P:
  ck(all(F(v).denominator==1 for v in one[p]),'integral common unary numerators')
  ck(list(map(int,one[p]))==data['unary'][str(p)],'same actual unary projection')
 for p,q in combinations(P,2):
  ck(all(F(v).denominator==1 for v in matrices[p,q].flat),'integral common pair numerators')
  ck(np.array_equal(matrices[p,q],np.array(data['pairs'][f'{p},{q}'],dtype=object)),'same actual pair projection')
 ck(F(int(central.sum()),source_den*fd)==F(data['source_mass']),'retained source mass')
 return {'input':str(path),'field':data['field'],'source_states':int(np.count_nonzero(source)),
         'retained_mass':data['source_mass'],'central_cells':80,'unary_tables':7,'joint_pair_tables':21,
         'central_source':central_source,
         'outside_pair_originals':len(contained_pairs),'pure_pair_originals':len(outside_pairs),
         'contained_nonpure_pair_originals':len(contained_pairs)-len(outside_pairs),
         'source_scope':'All109 original phases, actual central pure-survivor capacities and assigned leaf reference reconstructed; all relevant projections of ONE explicit retained tensor. The declared reference assigns the published leaf masses uniformly on each actual surviving leaf; no claim for arbitrary marginal inputs.',
         'field_scope':'NPZ exact field bounds and byte/coordinate pins verified; candidate construction and512 original screens are not verified by this independent source/projection check.',
         'seconds':time.perf_counter()-start}

def main():
 global BASE
 ap=argparse.ArgumentParser();ap.add_argument('inputs',nargs='+',type=Path);ap.add_argument('--base',type=Path,default=BASE.parent);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();BASE=a.base
 result={'status':'PASS','results':[audit(p) for p in a.inputs],'checks':CHECKS,'no_lean':True}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
