#!/usr/bin/env python3
"""The fixed631 common thinning pays the complete natural190 support-four family.

All 120 pair labels have arbitrary globally fixed central phases and outside
endpoints. The first central pure roots and seven-star central roles are fixed;
central square and higher pure phases are arbitrary. One common rational
thinning is used for all ordered zero/weak source corners. Uses exact standard-library
arithmetic and all 512 inherited costs; no Lean or large source scan.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
QS=(7,11,13,17,19)
CORE=(3,5)+QS
EDGES=tuple(combinations(range(5),2))
STAR=(0,2,0,2,0,10)
PINS={
 'actual_pair_activation_certificate.json':'2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f',
 'unanchored_square_source_certificate.json':'b8c38f05cbcd65607e25bc138ecc5a20961cd5bb786b18ad41df5583986bb1a4',
}
W3=[F() if l==3 else F(1,5) for l in range(6)]
W5=[F() if m==5 else F(1,19) for m in range(20)]
CELLS=tuple((l,m) for l,m in product(range(6),range(20))
            if W3[l] and W5[m] and (l//3,m//5)!=(0,0))
CHECKS={}

def ck(name,condition):
 if not condition:raise ArithmeticError(name)
 CHECKS[name]=True

def quinary(h):
 out=[F()]*4
 for j in range(4):
  root=F()
  for k in range(5):
   m=5*j+k
   if not W5[m]:continue
   value=W5[m]*h[m]
   root+=value
   out[2]=max(out[2],value)
   out[3]=max(out[3],F(4,5)*h[m])
  out[0]+=root
  out[1]=max(out[1],root)
 return out

def screens(h):
 out=[F()]*16
 roots=[[F()]*20 for _ in range(2)]
 for l in range(6):
  if not W3[l]:continue
  q=quinary(h[l])
  for e in range(4):
   out[8+e]=max(out[8+e],W3[l]*q[e])
   out[12+e]=max(out[12+e],q[e])
  for m in range(20):roots[l//3][m]+=W3[l]*h[l][m]
 total=quinary([roots[0][m]+roots[1][m] for m in range(20)])
 left,right=quinary(roots[0]),quinary(roots[1])
 for e in range(4):
  out[e]=total[e]
  out[4+e]=max(F(),left[e],right[e])
 return out

def menu(n,block,weights,zero,deep,mode):
 if mode==0:return [weights]
 if mode==1:
  return [[weights[k] if k//block==j else F() for k in range(n)]
          for j in range(n//block)]+[[F()]*n]
 return [[(weights[k] if mode==2 else deep) if k==leaf else F()
          for k in range(n)] for leaf in range(n) if leaf!=zero]+[[F()]*n]


THIN=(F(0),F(0),F(0),F(147,250),F(0),F(1),F(97,250),F(389,1000),F(377,500),F(119,200))
CATEGORIES=tuple((i,j) for i,j in product(range(3),range(4)) if not(i<2 and j==0))

def category(l,m):
 return (0 if l==0 else 1 if l<3 else 2,
         0 if m<5 else 2 if m==10 else 3 if m//5==2 else 1)

def thinning(l,m):
 if (l//3,m//5)==(0,0):return F()
 return THIN[CATEGORIES.index(category(l,m))]

def signature(l,m):
 return ((l//3,m//5)==(0,0),l//3==0,m//5==2,
         (l//3,m//5)==(0,2),l==0,m==10)

def swap(n,a,b):
 p=list(range(n));p[a],p[b]=p[b],p[a];return p

def source_orbits(n,generators):
 unseen={(z,w) for z in range(n) for w in range(n) if z!=w};answer=[]
 while unseen:
  seed=min(unseen);orbit={seed};pending=[seed]
  while pending:
   z,w=pending.pop()
   for p in generators:
    target=(p[z],p[w])
    if target not in orbit:orbit.add(target);pending.append(target)
  ck(f'orbit_partition_{n}_{seed}',orbit<=unseen)
  unseen-=orbit
  answer.append({'representative':list(seed),'size':len(orbit),'members':[list(x) for x in sorted(orbit)]})
 ck('full_ordered_corner_domain_'+str(n),sum(row['size'] for row in answer)==n*(n-1))
 return answer

def main():
 global W3,W5
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source-dir',type=Path,default=HERE)
 ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
 args=ap.parse_args()
 data={}
 for name,pin in PINS.items():
  raw=(args.source_dir/name).read_bytes()
  ck('source_pin_'+name,sha256(raw).hexdigest()==pin)
  data[name]=json.loads(raw)
 source=data['actual_pair_activation_certificate.json']
 inherited=data['unanchored_square_source_certificate.json']
 c=F(source['constants']['continuation_c']);g=1-c;alpha=F(inherited['Haar_factor'])
 ck('constants',c==F(1084133,201247200) and alpha==F(2673,110656))
 loss=list(map(F,source['complete_coefficients']['loss']))
 query=list(map(F,source['complete_coefficients']['weighted_nonunit_query']))
 ck('complete_512_nonnegative_costs',len(loss)==len(query)==512 and min(loss+query)>=0 and loss[0]==query[0]==0)
 r=[F(1,q-1) for q in QS];square=[F(1,q*(q-2)) for q in QS]
 pair=[F()]*512;labels=[]
 for q,s in EDGES:
  T=(1<<q)+(1<<s)
  for eq,es in [(1,1),(2,1),(1,2)]:
   cap=(r[q] if eq==1 else square[q])*(r[s] if es==1 else square[s])
   for a,b in product(range(2),repeat=2):
    pair[32*(4*a+b)+T]+=cap
    labels.append({'modulus':3**a*5**b*QS[q]**eq*QS[s]**es,'edge':[QS[q],QS[s]],
      'central_exponents':[a,b],'outside_exponents':[eq,es],'outside_cap':str(cap)})
 ck('all120_distinct_pair_labels',len(labels)==len({x['modulus'] for x in labels})==120)
 added=[F()]*512;added_labels=[];missing=[]
 for e in product(range(3),repeat=7):
  support=sum(a>0 for a in e)
  if not(2<=support<=4 and (e[0]==2 or e[1]==2)):continue
  if support==2 and sum(a>0 for a in e[:2])==1 and sum(e[2:])==1:continue
  modulus=prod(p**a for p,a in zip(CORE,e))
  admit=(support==4 and (sum(a>0 for a in e[:2])==1 or (all(e[:2]) and 1 not in e[2:])))
  if not admit:
   missing.append({'modulus':modulus,'exponents':list(e),'support':support});continue
  T=sum(1<<i for i,a in enumerate(e[2:]) if a)
  cap=prod(r[i] if a==1 else square[i] for i,a in enumerate(e[2:]) if a)
  added[32*(4*e[0]+e[1])+T]+=cap
  added_labels.append({'modulus':modulus,'exponents':list(e),'outside_cap':str(cap),'mode':4*e[0]+e[1],'support_mask':T})
 ck('190_distinct_new_originals',len(added_labels)==len({x['modulus'] for x in added_labels})==190)
 ck('160_one_centre_30_two_centre',sum(sum(a>0 for a in x['exponents'][:2])==1 for x in added_labels)==160)
 ck('new_labels_not_already_retained_pairs',not({x['modulus'] for x in labels}&{x['modulus'] for x in added_labels}))
 ck('213_remaining_inventory',len(missing)==213 and [sum(x['support']==k for x in missing) for k in (2,3,4)]==[13,110,90])
 for T in range(32):
  ix=[i for i in range(5) if T>>i&1]
  for a,b in product(range(4),repeat=2):
   expected=(prod(r[i]+square[i] for i in ix) if len(ix)==3 and (a,b) in [(2,0),(0,2)] else
             prod(square[i] for i in ix) if len(ix)==2 and (a,b) in [(2,1),(1,2),(2,2)] else F())
   ck(f'added_coefficient_formula_{a}_{b}_{T}',added[32*(4*a+b)+T]==expected)
 co=[g*(l+p+d)+c*w for l,p,d,w in zip(loss,pair,added,query)]
 ck('common_thinning_domain',len(THIN)==len(CATEGORIES)==10 and all(0<=x<=1 for x in THIN))
 gens3=[swap(6,1,2),swap(6,3,4),swap(6,4,5)]
 gens5=[]
 for block in [list(range(5)),list(range(5,10)),list(range(11,15)),list(range(15,20))]:
  for a,b in zip(block,block[1:]):gens5.append(swap(20,a,b))
 p=list(range(20))
 for k in range(5):p[5+k],p[15+k]=p[15+k],p[5+k]
 gens5.append(p)
 for i,p in enumerate(gens3):
  ck('whole_field_invariance3_'+str(i),all(signature(l,m)==signature(p[l],m)
      and thinning(l,m)==thinning(p[l],m) for l,m in product(range(6),range(20))))
 for i,p in enumerate(gens5):
  ck('whole_field_invariance5_'+str(i),all(signature(l,m)==signature(l,p[m])
      and thinning(l,m)==thinning(l,p[m]) for l,m in product(range(6),range(20))))
 orb3,orb5=source_orbits(6,gens3),source_orbits(20,gens5)
 ck('stabilizer_orbit_count',len(orb3)==8 and len(orb5)==16)
 rawR=[[[F()]*20 for _ in range(6)] for T in range(32)]
 for l,m in product(range(6),range(20)):
  if (l//3,m//5)==(0,0):continue
  Z=[1-(r[q]+square[q])*(int(l//3==0)+int(m//5==2))
       -r[q]*(int((l//3,m//5)==(0,2))+int(l==0)+int(m==10)) for q in range(5)]
  ck(f'positive_star_lower_{l}_{m}',all(1-5*r[q]-2*square[q]<=Z[q]<=1 for q in range(5)) and min(Z)>0)
  for T in range(32):rawR[T][l][m]=prod(Z[q] for q in range(5) if not T>>q&1)
 def evaluate(z,w,zz,ww):
  global W3,W5
  W3=[F() if l==z else F(1,9) if l==w else F(2,9) for l in range(6)]
  W5=[F() if m==zz else F(3,75) if m==ww else F(4,75) for m in range(20)]
  response=[[[thinning(l,m)*rawR[T][l][m] if l!=z and m!=zz else F()
              for m in range(20)] for l in range(6)] for T in range(32)]
  readings=[screens(h) for h in response]
  mass=readings[0][0]
  debit=sum((co[32*mode+T]*readings[T][mode] for mode in range(16) for T in range(32)),F())
  return response,readings,mass,debit,g*mass-debit
 rows=[]
 for i,j in product(range(len(orb3)),range(len(orb5))):
  z,w=orb3[i]['representative'];zz,ww=orb5[j]['representative']
  response,readings,mass,debit,gate=evaluate(z,w,zz,ww)
  ck(f'positive_complete_corner_{i}_{j}',gate>F(1,626))
  rows.append({'case':[i,j],'source':[z,w,zz,ww],
               'orbit_size':orb3[i]['size']*orb5[j]['size'],
               'mass':str(mass),'debit':str(debit),'gate':str(gate)})
 ck('literal_corner_coverage',len(rows)==128 and sum(row['orbit_size'] for row in rows)==11400)
 worst=min(rows,key=lambda row:F(row['gate']))
 ck('exact_minimum',F(worst['gate'])==F(529198781643667928189551074379,331080094584857932554240000000000))
 z,w,zz,ww=worst['source']
 response,readings,mass,debit,gate=evaluate(z,w,zz,ww)
 cells=[(l,m) for l,m in product(range(6),range(20)) if l!=z and m!=zz and (l//3,m//5)!=(0,0)]
 for T in range(32):
  for e3,e5 in product(range(4),repeat=2):
   direct=max(sum((x[l]*y[m]*response[T][l][m] for l,m in cells),F())
    for x,y in product(menu(6,3,W3,z,F(1),e3),menu(20,5,W5,zz,F(4,5),e5)))
   ck(f'worst_direct_menu_{T}_{e3}_{e5}',direct==readings[T][4*e3+e5])
 head=alpha*gate
 ck('strict_head_bound',head>F(1,26000))
 result={'schema':'fixed-star-support-four190-common-thinning-v1','status':'PASS',
  'scope':{
   'fixed_geometry':'Central first pure roots2mod3 and4mod5, central15mask0mod15, seven-star central roles(R,C,I,J,L,M)=(0,2,0,2,0,10). Missing first-root/mask originals may be imposed as auxiliary deletions.',
   'free_central_pures':'Actual pure9 and25 residues and all higher pure phases/heights are arbitrary; missing/source-null square slots may be replaced by one auxiliary live null leaf.',
   'free_pairs':'All120 pair labels have arbitrary globally fixed central phases, outside roots and higher lifts; no within-edge shared-root condition.',
   'other_originals':'All other Report626 mixed inventory PLUS every190 natural support-four original (one central square and three outside first/square exponents; or both centres with a square present and two outside squares); unrestricted23/29/31 continuation, literal reference head primes and distinct numerical labels.',
   'source':'One fixed rational central thinning, same for all32 raw-product responses and every central source weight vector. Pair events are paid globally; no positive avoidance in every cell or strict Shearer condition is required.',
   'not_claimed':'Arbitrary central first-root/mask geometry or arbitrary seven-star central roles; LP optimality; unrestricted Erdos7; Lean verification.'},
  'dependencies':PINS,'constants':{'c':str(c),'g':str(g),'alpha':str(alpha)},
  'thinning_categories':[list(x) for x in CATEGORIES],'common_thinning':list(map(str,THIN)),
  'generators3':gens3,'generators5':gens5,'source_orbits3':orb3,'source_orbits5':orb5,
  'added_labels':sorted(added_labels,key=lambda row:row['modulus']),'added_loss_coefficients':list(map(str,added)),'remaining_missing':sorted(missing,key=lambda row:row['modulus']),'pair_labels':sorted(labels,key=lambda row:row['modulus']),'pair_loss_coefficients':list(map(str,pair)),
  'source_corners':rows,'minimum':worst,'gate_strict_lower':'1/626',
  'head_haar_lower':str(head),'head_strict_lower':'1/26000',
  'checks':CHECKS,'check_count':len(CHECKS),'new_lean_verification':False,
  'LP_solved_by_producer':False,'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['status','check_count','minimum','head_haar_lower','head_strict_lower']},indent=2))

if __name__=='__main__':main()
