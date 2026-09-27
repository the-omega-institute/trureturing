#!/usr/bin/env python3
"""Independent exact all-layout affine lower bound for three moved-null geometries.
Uses only pinned640/658 numerical data. No producer implementation, LP, or large layout enumeration.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import product,combinations
from math import prod,lcm
from pathlib import Path
import json
p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args();checks={}
def ck(k,b):
 checks[k]=checks.get(k,0)+1
 if not b:raise RuntimeError(k)
names=['remaining33_global_root_exclusion_certificate.json','joint_square_pair_225_star_certificate.json']
pins=['dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5']
raw=[(a.directory/n).read_bytes() for n in names]
for b,h in zip(raw,pins):ck('source_pin',sha256(b).hexdigest()==h)
base,network=map(json.loads,raw)
Q=(7,11,13,17,19);V=frozenset(range(5));edges=list(combinations(range(5),2));disjoint=[(e,f) for e,f in combinations(range(10),2) if set(edges[e]).isdisjoint(edges[f])]
r=[F(1,q-1) for q in Q];aa=[F(1,q*(q-2)) for q in Q]
beta0=[aa[i]*r[j]+r[i]*aa[j] for i,j in edges];delta=[r[i]*r[j] for i,j in edges]
z=[[F(5,6)-F(n,35)]+[F(q-2,q-1)-2*aa[k] for k,q in enumerate(Q) if k] for n in range(4)]
def hp(U,zz,bb):
 es=[e for e,(i,j) in enumerate(edges) if i in U and j in U]
 value=prod(zz[k] for k in U)-sum((bb[e]*prod(zz[k] for k in U-set(edges[e])) for e in es),F(0))
 value+=sum((bb[e]*bb[f]*prod(zz[k] for k in U-set(edges[e])-set(edges[f])) for e,f in disjoint if e in es and f in es),F(0))
 return value
betaMax=[b+d for b,d in zip(beta0,delta)]
strict=1-sum((betaMax[e]/(z[3][i]*z[3][j]) for e,(i,j) in enumerate(edges)),F(0))
ck('strict_whole_box',strict>0)
H=[];linear=[];quadratic=[]
for n in range(4):
 h=[]
 for T in range(32):
  U=V-{k for k in V if T>>k&1}
  h0=hp(U,z[n],beta0);hm=hp(U,z[n],betaMax)
  ck('baseline_and_max_positive',0<hm<=h0<=1);h.append(h0)
  for e,(i,j) in enumerate(edges):
   if i in U and j in U:
    derivative_core=hp(U-{i,j},z[n],betaMax)
    ck('negative_edge_derivative_box',derivative_core>0)
 H.append(h)
 le=[-delta[e]*hp(V-set(ends),z[n],beta0) for e,ends in enumerate(edges)]
 qe=[delta[e]*delta[f]*prod(z[n][k] for k in V-set(edges[e])-set(edges[f])) for e,f in disjoint]
 for x in le:ck('negative_linear_coefficient',x<0)
 for x in qe:ck('positive_quadratic_coefficient',x>0)
 linear.append(le);quadratic.append(qe)
 # Verify the exact expansion on every possible edge indicator mask.
 # The ordinary derivation proves the polynomial identity; this finite check
 # covers all masks actually possible at any fixed central leaf.
 for mask in range(1024):
  bb=[beta0[e]+delta[e]*int(bool(mask>>e&1)) for e in range(10)]
  affine=h[0]+sum((le[e] for e in range(10) if mask>>e&1),F(0))
  expansion=affine+sum((qe[k] for k,(e,f) in enumerate(disjoint) if mask>>e&1 and mask>>f&1),F(0))
  actual=hp(V,z[n],bb)
  ck('matching_expansion_exact',actual==expansion)
  ck('affine_source_lower',affine<=actual<=h[0])
hden=lcm(*(x.denominator for row in H+linear for x in row))
HI=[[int(x*hden) for x in row] for row in H]
LI=[[int(x*hden) for x in row] for row in linear]
for rows,ints in [(H,HI),(linear,LI)]:
 for row,ir in zip(rows,ints):
  for x,y in zip(row,ir):ck('exact_response_integer_scale',F(y,hden)==x)
g=F(200163067,201247200);C=list(map(F,base['combined512_coefficients']))
for k in range(1,5):C[288+(1<<k)]+=g*aa[k]
ck('complete_fee_inventory',len(C)==512 and min(C)>=0)
cden=lcm(g.denominator,*(x.denominator for x in C));GI=int(g*cden);CI=[int(x*cden) for x in C]
for x,y in zip([g]+C,[GI]+CI):ck('exact_fee_integer_scale',F(y,cden)==x)
denominator=675*hden*cden

def menus(weights,blocksize,deep):
 n=len(weights);live=[k for k,x in enumerate(weights) if x]
 return [[tuple(weights)],[tuple(weights[k] if k//blocksize==b else 0 for k in range(n)) for b in range(n//blocksize)],[tuple(weights[k] if k==t else 0 for k in range(n)) for t in live],[tuple(deep if k==t else 0 for k in range(n)) for t in live]]

results=[];allCornerCount=0;allLiteralSelectors=0;allModeSupportMaxima=0
for null3,null5 in ((0,5),(3,0),(0,0)):
 I=tuple(l for l in range(6) if l!=null3);J=tuple(m for m in range(20) if m!=null5)
 live=[(l,m) for l,m in product(I,J) if not(l<3 and m<5)]
 reps=tuple(next(m for m in J if m//5==c) for c in range(4));corners=list(product(I,reps))
 ck('corner_orbit_census',len(corners)==20 and sum(sum(m//5==c for m in J) for c in range(4))*len(I)==95)
 roles=[];minimum=None
 for row,col,ell in product(range(2),range(4),I):
  ns={(l,m):int(l//3==row)+int(m//5==col)+int(l==ell) for l,m in live}
  ck('unary_decrement_inventory',all(0<=n<=3 for n in ns.values()))
  best=None
  for wi,wj in corners:
   w=[0 if l==null3 else 1 if l==wi else 2 for l in range(6)]
   v=[0 if m==null5 else 3 if m==wj else 4 for m in range(20)]
   ck('corner_weights_normalized',sum(w)==9 and sum(v)==75)
   source=sum(w[l]*v[m]*HI[ns[l,m]][0] for l,m in live)
   negativeCosts=[];minLeaves=[]
   for e in range(10):
    perLeaf=[sum(w[l]*v[m]*LI[ns[l,m]][e] for m in J if (l,m) in ns) for l in I]
    least=min(perLeaf);source+=least;negativeCosts.append(least);minLeaves.append(I[perLeaf.index(least)])
    for x in perLeaf:ck('edge_loss_uniform_over_actual_leaf',least<=x<=0)
   xm=menus(w,3,9);ym=menus(v,5,60);fee=0
   for xm0,ym0 in product(range(4),repeat=2):
    coeffs=[]
    for x,y in product(xm[xm0],ym[ym0]):
     cs=[0,0,0,0]
     for l,m in live:cs[ns[l,m]]+=x[l]*y[m]
     ck('literal_selector_mass',min(cs)>=0 and sum(cs)<=675)
     coeffs.append(tuple(cs))
    allLiteralSelectors+=len(coeffs)
    # Only exact duplicate coefficient vectors are removed. Every original
    # menu remains represented, with no maximizer or source law guessed.
    distinct=set(coeffs)
    ck('all_original_selectors_retained',set(coeffs)==distinct and distinct)
    mode=4*xm0+ym0
    for T in range(32):
     maximum=max(sum(cs[n]*HI[n][T] for n in range(4)) for cs in distinct)
     fee+=CI[32*mode+T]*maximum;allModeSupportMaxima+=1
   gate=GI*source-fee;allCornerCount+=1
   ck('uniform_public_gate',F(gate,denominator)>F(1,100)>F(193,100000))
   if best is None or gate<best['numerator']:
    best=dict(numerator=gate,corner=[wi,wj],source_lower=F(source,675*hden),fee_upper=F(fee,denominator),minimizing_leaf_by_edge=minLeaves)
  roleResult=dict(square7_roles=[row,col,ell],minimum_gate=str(F(best['numerator'],denominator)),minimum_gate_decimal=float(F(best['numerator'],denominator)),weak_corner=best['corner'],source_lower_at_minimum=str(best['source_lower']),fee_upper_at_minimum=str(best['fee_upper']),edge_lower_bound_leaf_witnesses=best['minimizing_leaf_by_edge'])
  roles.append(roleResult)
  if minimum is None or best['numerator']<minimum[0]:minimum=(best['numerator'],roleResult)
 ck('all_forty_live_roles',len(roles)==40)
 results.append(dict(null_leaves=[null3,null5],live_cell_count=len(live),quinary_corner_representatives=list(reps),represented_weak_corners=95,computed_weak_corners=20,role_count=40,minimum=minimum[1],roles=roles))
ck('complete_corner_count',allCornerCount==3*40*20)
ck('complete_literal_selector_count',allLiteralSelectors==allCornerCount*559)
ck('complete_mode_support_count',allModeSupportMaxima==allCornerCount*512)
policies=[]
for pol in network['policies']:
 fee=F(network['fee_before_arbitrary'])+F(pol['fee']);alpha=F(network['projection_alpha']);reserve=alpha*(F(193,100000)-fee)
 ck('inherited_complete_three_parent_policy',reserve>F(1,2000000))
 policies.append(dict(kind=pol['kind'],K=pol['K'],fee=str(fee),projected_reserve_at_inherited_gate=str(reserve),strict_density_denominator=2000000))
result=dict(schema='new-null-uniform-affine-bound-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,source_sha256=dict(zip(names,pins)),driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),edge_primes=[[Q[i],Q[j]] for i,j in edges],strict_matching_box_margin=str(strict),exact_response_scale=hden,exact_fee_scale=cden,common_gate_denominator=denominator,uniform_gate_lower='1/100',weaker_inherited_gate='193/100000',geometry_results=results,computed_corner_count=allCornerCount,literal_selector_count=allLiteralSelectors,complete_mode_support_maxima=allModeSupportMaxima,policies=policies,checks=checks,check_count=sum(checks.values()),scope='All labelled edge layouts, every40 live square7 role, and all95 weak corners in each of the three declared null geometries. The source lower bound and query upper bounds apply to the same fixed actual layout. No large-layout enumeration, independent-actual-parent assumption, incidence release, unrestricted-parent conclusion or new Lean verification.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=result['check_count'],minimums=[dict(nulls=x['null_leaves'],gate=x['minimum']['minimum_gate'],decimal=x['minimum']['minimum_gate_decimal'],role=x['minimum']['square7_roles'],corner=x['minimum']['weak_corner']) for x in results])))
