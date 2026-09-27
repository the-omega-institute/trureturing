"""Exact four-point Boolean-selector budget directions.
Enumerate only3 independent normals among40 ternary4 normals modulo sign.
Standard library, integer determinants, no solver or sampled weight grid.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
from itertools import product,combinations,permutations
from math import gcd,comb
from collections import Counter
import json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output",type=Path)
args=parser.parse_args()

def need(x,m):
 if not x:raise ValueError(m)
def det3(a):
 return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def normal_sign(a):
 for x in a:
  if x:return 1 if x>0 else -1
 return 0
normals=sorted(n for n in product((-1,0,1),repeat=4) if normal_sign(n)==1)
need(len(normals)==40 and comb(len(normals),3)==9880,'all ternary normals modulo sign')
for j in range(4):need(tuple(int(i==j) for i in range(4)) in normals,'all coordinate boundary hyperplanes')
rays={};rank3=0;nonnegative=0;mixed=0;rankdef=0
for ids in combinations(range(40),3):
 A=[normals[i] for i in ids]
 v=tuple((-1)**j*det3([[a[k] for k in range(4) if k!=j] for a in A]) for j in range(4))
 need(all(dot(a,v)==0 for a in A),'cofactor kernel identity')
 if not any(v):rankdef+=1;continue
 rank3+=1
 if all(x>=0 for x in v):pass
 elif all(x<=0 for x in v):v=tuple(-x for x in v)
 else:mixed+=1;continue
 nonnegative+=1;d=gcd(*v);need(d>0,'nonzero primitive denominator')
 v=tuple(x//d for x in v)
 need(gcd(*v)==1 and all(x>=0 for x in v),'primitive nonnegative ray')
 rays.setdefault(v,ids)
need(rankdef+rank3==9880 and nonnegative+mixed==rank3,'full independent triple census')

expected_types={(0,0,0,1):4,(0,0,1,1):6,(0,1,1,1):4,(0,1,1,2):12,
 (1,1,1,1):1,(1,1,1,2):4,(1,1,1,3):4,(1,1,2,2):6,
 (1,1,2,3):12,(1,1,2,4):12,(1,2,2,3):12,(1,2,3,4):24}
need(Counter(tuple(sorted(r)) for r in rays)==expected_types,'exact101-ray permutation classification')
three_rays={w for w in product((0,1),repeat=3) if any(w)}|set(permutations((1,1,2)))
for j in range(4):
 face={tuple(r[k] for k in range(4) if k!=j) for r in rays if r[j]==0}
 need(face==three_rays,'each coordinate face contains exactly the complete three-point ray family')

counts=Counter(tuple(sorted(r)) for r in rays)
orbits=[]
for representative,count in sorted(counts.items()):
 orbit=set(permutations(representative))
 need(len(orbit)==count and orbit<=rays.keys(),'complete permutation orbit')
 orbits.append({'sorted_representative':list(representative),'orbit_size':count,
                'support_size':sum(x>0 for x in representative)})
# Every Boolean pair difference is zero or one of the enumerated normals
# up to sign. This is the complete label-comparison hyperplane family.
boolean=list(product((0,1),repeat=4));comparison_count=0
for A,B in product(boolean,repeat=2):
 delta=tuple(a-b for a,b in zip(A,B));sgn=normal_sign(delta)
 if sgn:need(tuple(sgn*x for x in delta) in normals,'Boolean comparison covered')
 else:need(A==B,'zero comparison is tie')
 comparison_count+=1
out={'dimension':4,'normal_count':len(normals),'normal_triples_checked':9880,
 'independent_normal_triples':rank3,'dependent_normal_triples':rankdef,
 'nonnegative_kernel_triples':nonnegative,'mixed_sign_kernel_triples':mixed,
 'ray_count':len(rays),'permutation_type_count':len(orbits),
 'rays_by_support_size':{str(k):sum(sum(x>0 for x in r)==k for r in rays) for k in range(1,5)},
 'normal_representatives':[list(n) for n in normals],
 'permutation_types':orbits,
 'rays':[{'ray':list(r),'normal_indices':list(rays[r]),'independent_normals':[list(normals[i]) for i in rays[r]]} for r in sorted(rays)],
 'boolean_comparisons_checked':comparison_count,
 'scope':'Universal finite generating directions for nonnegative weighted budgets formed from Boolean A/B selectors at four tested points. Includes coordinate faces and degenerate ties.',
 'boundary':'Completeness concerns weighted necessary inequalities, using chamberwise common selectors and the ordinary polyhedral-cone proof. It is not arithmetic realization, simultaneous phase feasibility, a positive survivor bound or Lean formalization.'}

# A literal original-label countermodel to arithmetic realizability of all
# weighted budgets. The ordinary report proves the statement for every
# prime p>=7 and finite J>=1; these fixed CRT families verify the construction.
old_points=(0,1,10,6);old_labels=(3,5)
A=tuple(tuple(int(x%d==0) for x in old_points) for d in old_labels)
B=tuple(tuple(int(x%d==1) for x in old_points) for d in old_labels)
need(A==((1,0,0,1),(1,0,1,0)) and B==((0,1,1,0),(0,1,0,1)),
     'literal numerical old-label memberships')
def inventory(w):return sum(max(dot(w,a),dot(w,b)) for a,b in zip(A,B))
choice_sums=[]
for selectors in product((0,1),repeat=2):
 c=tuple(sum((A if selectors[k]==0 else B)[k][i] for k in range(2)) for i in range(4))
 need(sorted(c)==[0,1,1,2],'each common selector misses one old point')
 choice_sums.append(c)
need(tuple(sum(v[i] for v in choice_sums) for i in range(4))==(4,4,4,4),
     'target one-vector is a convex mean of actual selector sums')
need(all(sum(w)<=inventory(w) for w in rays),'all101 target inventory budgets')
prime=7;height=3;power=prime**height;lam=1-F(1,power);tau=F(2,prime)-F(2,power)
moduli=[d*prime**j for d in old_labels for j in range(1,height+1)]
need(len(set(moduli))==2*height and all(m>1 and m%2 for m in moduli),
     'distinct original odd numerical labels')
def label_rows(select):
 out=[]
 for k,d in enumerate(old_labels):
  for j in range(1,height+1):
   pp=prime**j;phase=(k+1)*prime**(j-1);bit=select(k,j)
   residue=bit+d*((phase-bit)*pow(d,-1,pp)%pp)
   need(0<=residue<d*pp and residue%d==bit and residue%pp==phase,
        'one CRT residue for each complete numerical label')
   out.append({'d':d,'height':j,'modulus':d*pp,'residue':residue,'old_selector':bit,'new_phase':phase})
 return out
def actual_loss(classes):
 counts=[]
 for x in old_points:
  count=0
  for y in range(power):
   n=x+15*((y-x)*pow(15,-1,power)%power)
   need(n%15==x and n%power==y,'same finite CRT source')
   count+=any(n%r['modulus']==r['residue'] for r in classes)
  counts.append(count)
 return tuple(F((prime-1)*c,power) for c in counts),counts
cylinders=[{y for y in range(power) if y%(prime**j)==k*prime**(j-1)}
           for k in (1,2) for j in range(1,height+1)]
need(sum(map(len,cylinders))==len(set().union(*cylinders)),'all new-prime cylinders disjoint')
families=[]
for selectors,counts in zip(product((0,1),repeat=2),choice_sums):
 classes=label_rows(lambda k,j:selectors[k]);loss,covered=actual_loss(classes)
 need(loss==tuple(lam*c for c in counts),'actual constant-selector family attains inventory vector')
 families.append({'constant_old_selectors':list(selectors),'classes':classes,
                  'covered_new_residues':covered,'normalized_loss':list(map(str,loss))})
sharp_classes=label_rows(lambda k,j:0 if j==1 else 1)
sharp_loss,sharp_counts=actual_loss(sharp_classes)
need(sharp_loss==(F(2*(prime-1),prime),tau,lam,lam) and min(sharp_loss)==tau,
     'sharp first-level omission construction')
need(lam-tau==1-F(2,prime)+F(1,power)>0,'strict finite realization gap')
out['arithmetic_countermodel']={'old_centres_mod15':[0,1],'old_points':list(old_points),
 'old_labels':list(old_labels),'membership_A':[list(a) for a in A],'membership_B':[list(b) for b in B],
 'four_selector_sums':[list(v) for v in choice_sums],
 'example_prime':prime,'example_height':height,'carrier':15*power,
 'finite_inventory_factor':str(lam),'relaxed_minimum_loss_optimum':str(lam),
 'actual_minimum_loss_optimum':str(tau),'realization_gap':str(lam-tau),
 'four_actual_families':families,'sharp_family':{'classes':sharp_classes,
 'covered_new_residues':sharp_counts,'normalized_loss':list(map(str,sharp_loss))},
 'ordinary_general_statement':'For every prime p>=7 and J>=1, with exactly the original labels3*p^j and5*p^j for1<=j<=J, old residues independently0 or1 per full label and arbitrary new-prime phases, max_family min_i((p-1)*axis_union_loss_i)=2/p-2/p^J. All nonnegative weighted finite-inventory budgets plus the axis cap instead permit max min_i t_i=1-1/p^J.',
 'scope':'The pointwise weighted-budget representation is convex and need not be one actual original-label selector family, even at fixed finite height. Other old cofactors can alter the bound, so this is not a cut for the full mixed chart or an Erdos7 covering counterexample.'}
out['Lean_rerun']=False
out['boundary']='The101 directions completely describe the weighted necessary inequalities. The finite arithmetic countermodel has a sharp ordinary proof for all stated p and J and explicit checked CRT instances. Neither weighted-budget completeness nor convex feasibility supplies arithmetic realization. No global source-mass estimate, unrestricted covering resolution, or Lean certification is claimed.'
p=args.output or Path(__file__).with_suffix('.json')
if args.output:p.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(p.read_text())==out,'retained result differs')
print(json.dumps({'rays':len(rays),'permutation_types':len(orbits),
 'example_relaxed':str(lam),'example_actual':str(tau),'example_gap':str(lam-tau)},indent=2))
