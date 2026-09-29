"""Exact universal three-coordinate selector-capacity fan. Report498.
Finite boolean sign verification certifies linearity on explicitly covering
real cones; bounded numerical weight sampling is not used as a proof.
"""
from itertools import product,combinations,permutations
from functools import reduce
from math import gcd
from pathlib import Path
import argparse,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
def need(t,m):
 if not t:raise ValueError(m)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def primitive(v):
 d=reduce(gcd,map(abs,v),0)
 need(d>0,'nonzero direction')
 return tuple(x//d for x in v)
def canonical(v):
 v=primitive(v)
 return tuple(-x for x in v) if next(x for x in v if x)!=abs(next(x for x in v if x)) else v
normals=sorted({canonical(v) for v in product((-1,0,1),repeat=3) if any(v)})
need(len(normals)==13,'all hyperplanes modulo sign')
rays={};eligible=0
for a,b in combinations(normals,2):
 v=cross(a,b);need(any(v),'distinct canonical normals independent')
 if all(x<=0 for x in v):v=tuple(-x for x in v)
 if not all(x>=0 for x in v):continue
 eligible+=1;v=primitive(v);rays.setdefault(v,[]).append((a,b))
expected=set(product((0,1),repeat=3))-{(0,0,0)};expected.update(permutations((1,1,2)))
need(set(rays)==expected,'exact ten-ray inventory')
need((1,2,2) not in rays,'122 is not a fan ray')
# Sorted coordinates w=(a,b,c), 0<=a<=b<=c.
# c>=a+b: coefficients a,b-a,c-a-b for (112),(011),(001).
# c<=a+b: coefficients b-a,c-b,a+b-c for (011),(112),(111).
sorted_cones=[
 {'name':'dominant','generators':((1,1,2),(0,1,1),(0,0,1)),
  'coefficients':((1,0,0),(-1,1,0),(-1,-1,1)),
  'region':'0<=a<=b<=c and c>=a+b'},
 {'name':'triangle','generators':((0,1,1),(1,1,2),(1,1,1)),
  'coefficients':((-1,1,0),(0,-1,1),(1,1,-1)),
  'region':'0<=a<=b<=c and c<=a+b'}]
boolean=list(product((0,1),repeat=3));cones=[];checks=0
for cone in sorted_cones:
 g=cone['generators'];c=cone['coefficients']
 need(all(sum(g[k][i]*c[k][j] for k in range(3))==int(i==j) for i in range(3) for j in range(3)),'symbolic real decomposition identity')
 for perm in permutations(range(3)):
  def transport(v):
   r=[0]*3
   for i,j in enumerate(perm):r[j]=v[i]
   return tuple(r)
  gs=tuple(map(transport,g));choices=[]
  for a,b in product(boolean,repeat=2):
   av=tuple(dot(x,a) for x in gs);bv=tuple(dot(x,b) for x in gs)
   if all(x>=y for x,y in zip(av,bv)):choices.append(0)
   elif all(y>=x for x,y in zip(av,bv)):choices.append(1)
   else:raise ValueError('boolean max switches inside proposed cone')
   checks+=1
  # No ternary normal changes sign over a cone. Its two boundary equations
  # may vanish on a face, but it cannot cut the positive cone interior.
  need(all(all(dot(n,r)>=0 for r in gs) or all(dot(n,r)<=0 for r in gs) for n in normals),'all arrangement signs fixed')
  cones.append({'sorted_coordinate_order':perm,'type':cone['name'],'generators':gs,'selector_choices_for_64_boolean_pairs':choices})
# Show 122 is genuinely interior to an arrangement face, not a missing ray:
# (1,2,2)=(1,1,1)+(0,1,1), with both summands in its sorted triangle cone.
need(tuple(x+y for x,y in zip((1,1,1),(0,1,1)))==(1,2,2),'122 decomposition')
out={'verified':True,'canonical_hyperplane_normals':normals,'normal_count':len(normals),'independent_normal_pairs':len(normals)*(len(normals)-1)//2,'nonnegative_ray_intersections_counting_repetitions':eligible,'rays':[{'primitive':r,'witness_normal_pairs':pairs} for r,pairs in sorted(rays.items())],'ray_count':len(rays),'sorted_cones':sorted_cones,'all_coordinate_cones':cones,'boolean_pair_common_selector_checks':checks,'theorem':'For any finite index set of labels and arbitrary A_d,B_d in{0,1}^3 with nonnegative label weights, N(w)=sum_d lambda_d max(w.A_d,w.B_d). For every v in R^3, all w>=0 satisfy w.v<=N(w) iff the ten enumerated primitive weights do. This uses explicit real cone decompositions and termwise common maximizers, not sampling.','boundary':'Completeness concerns nonnegative weighted selector budgets only, not arithmetic realization, same-selector relations across multiple axis vectors, joint phases or a global mass bound. No new Lean verification.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==json.loads(json.dumps(out)),
          'retained result differs')
print(json.dumps({'normal_count':len(normals),'independent_normal_pairs':len(normals)*(len(normals)-1)//2,'eligible_intersections':eligible,'ray_count':len(rays),'rays':sorted(rays),'cones':len(cones),'boolean_pair_checks':checks},indent=2))
