#!/usr/bin/env python3
"""A source conditioned on30 unconditional pair labels pays370 fixed-star additions.

Condition the same actual star-product source only on qs,q²s,qs² at each edge.
Pay the90 remaining central-conditional pair labels on its simultaneous query
grids, with globally fixed arbitrary phases. Fixed631 STAR/first roots/mask;
arbitrary central square/higher pure phases and one common631 rational thinning.
Exact standard-library verification, no optimization or new Lean claim.
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
    if a or b:pair[32*(4*a+b)+T]+=cap
    labels.append({'modulus':3**a*5**b*QS[q]**eq*QS[s]**es,'edge':[QS[q],QS[s]],
      'central_exponents':[a,b],'outside_exponents':[eq,es],'outside_cap':str(cap)})
 ck('all120_distinct_pair_labels',len(labels)==len({x['modulus'] for x in labels})==120)
 stage_names=('support4_280','mixed355','mixed370')
 added={name:[F()]*512 for name in stage_names};added_labels={name:[] for name in stage_names};missing={name:[] for name in stage_names}
 for e in product(range(3),repeat=7):
  support=sum(a>0 for a in e)
  if not(2<=support<=4 and (e[0]==2 or e[1]==2)):continue
  if support==2 and sum(a>0 for a in e[:2])==1 and sum(e[2:])==1:continue
  modulus=prod(p**a for p,a in zip(CORE,e))
  centre_count=sum(a>0 for a in e[:2]);out=[a for a in e[2:] if a]
  admit355=support==4 or(support==3 and 2 in out)
  admit370=admit355 or(e[:2]==(0,2)and((support==2 and out==[2])or(support==3 and out==[1,1])))
  decisions=(support==4,admit355,admit370)
  T=sum(1<<i for i,a in enumerate(e[2:]) if a)
  cap=prod(r[i] if a==1 else square[i] for i,a in enumerate(e[2:]) if a)
  for name,admit in zip(stage_names,decisions):
   if not admit:missing[name].append({'modulus':modulus,'exponents':list(e),'support':support});continue
   added[name][32*(4*e[0]+e[1])+T]+=cap
   added_labels[name].append({'modulus':modulus,'exponents':list(e),'outside_cap':str(cap),'mode':4*e[0]+e[1],'support_mask':T})
 gap403={row['modulus']for row in added_labels['support4_280']+missing['support4_280']}
 ck('literal_old403_gap',len(gap403)==403)
 for name,num,rem,by_support in zip(stage_names,(280,355,370),(123,48,33),((13,110,0),(13,35,0),(8,25,0))):
  ck(name+'_distinct_added_originals',len(added_labels[name])==len({x['modulus']for x in added_labels[name]})==num)
  ck(name+'_disjoint_from_retained_pairs',not({x['modulus']for x in labels}&{x['modulus']for x in added_labels[name]}))
  ck(name+'_remaining_inventory',len(missing[name])==rem and tuple(sum(x['support']==k for x in missing[name])for k in(2,3,4))==by_support)
  added_set={x['modulus']for x in added_labels[name]};missing_set={x['modulus']for x in missing[name]}
  ck(name+'_403_partition',not(added_set&missing_set)and added_set|missing_set==gap403)
  ck(name+'_disjoint_all_retained_labels',not(added_set&{x['modulus']for x in source['retained_inventory']}))
  for T in range(32):
   ix=[i for i in range(5)if T>>i&1]
   for e3,e5 in product(range(4),repeat=2):
    expected=F()
    if len(ix)==3 and(e3,e5)in((2,0),(0,2)):expected=prod(r[i]+square[i]for i in ix)
    if len(ix)==2 and(e3,e5)in((2,1),(1,2),(2,2)):expected=prod(r[i]+square[i]for i in ix)
    if name!='support4_280':
     if len(ix)==1 and(e3,e5)in((2,1),(1,2),(2,2)):expected=square[ix[0]]
     if len(ix)==2 and(e3,e5)in((2,0),(0,2)):
      expected=prod(square[i]for i in ix)
      if name in('mixed355','mixed370'):
       q,s=ix;expected+=r[q]*square[s]+square[q]*r[s]
    if name=='mixed370'and(e3,e5)==(0,2):
     if len(ix)==1:expected+=square[ix[0]]
     if len(ix)==2:expected+=prod(r[i]for i in ix)
    ck(name+f'_full512_fee_{e3}_{e5}_{T}',added[name][32*(4*e3+e5)+T]==expected)
 co={name:[g*(l+p+d)+c*w for l,p,d,w in zip(loss,pair,added[name],query)]for name in stage_names}
 for name in stage_names:ck(name+'_complete512_nonnegative_costs',len(co[name])==512 and min(co[name])>=0 and co[name][0]==0)
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
 edge_masks=[sum(1<<q for q in e)for e in EDGES]
 disjoint=[(e,f)for e,f in combinations(range(10),2)if set(EDGES[e]).isdisjoint(EDGES[f])]
 kappa=[r[q]*r[s]+square[q]*r[s]+r[q]*square[s]for q,s in EDGES]
 floor=[1-3*r[q]-2*square[q]for q in range(5)]
 def strict_box(scale):
  u=[scale*kappa[e]/(floor[q]*floor[s])for e,(q,s)in enumerate(EDGES)];values=[]
  for mask in range(1024):
   val=1-sum((u[e]for e in range(10)if mask>>e&1),F())+sum((u[e]*u[f]for e,f in disjoint if mask>>e&1 and mask>>f&1),F())
   ck(f'strict_box_{scale}_{mask}',val>0);values.append(val)
  return min(values)
 strict_kappa=strict_box(1)
 # The stronger4kappa domain is recorded as a capability bound, not needed by this source.
 strict_four_kappa=strict_box(4)
 rawR=[[[F()]*20 for _ in range(6)]for T in range(32)];cell_data=[]
 for l,m in product(range(6),range(20)):
  if not thinning(l,m):continue
  Z=[1-(r[q]+square[q])*(int(l//3==0)+int(m//5==2))-r[q]*(int((l//3,m//5)==(0,2))+int(l==0)+int(m==10))for q in range(5)]
  ck(f'star_mass_above_uniform_floor_{l}_{m}',all(floor[q]<=Z[q]<=1 for q in range(5)))
  raw=[prod(Z[q]for q in range(5)if not T>>q&1)for T in range(32)];conditional=[]
  for T in range(32):
   h=raw[T]-sum((kappa[e]*raw[T|edge_masks[e]]for e in range(10)if not(T&edge_masks[e])),F())+sum((kappa[e]*kappa[f]*raw[T|edge_masks[e]|edge_masks[f]]for e,f in disjoint if not(T&(edge_masks[e]|edge_masks[f]))),F())
   ck(f'positive_conditional_query_{l}_{m}_{T}',0<h<=raw[T]);rawR[T][l][m]=h;conditional.append(str(h))
  cell_data.append({'cell':[l,m],'Z':list(map(str,Z)),'conditional_responses':conditional})
 def evaluate(z,w,zz,ww):
  global W3,W5
  W3=[F() if l==z else F(1,9) if l==w else F(2,9) for l in range(6)]
  W5=[F() if m==zz else F(3,75) if m==ww else F(4,75) for m in range(20)]
  response=[[[thinning(l,m)*rawR[T][l][m] if l!=z and m!=zz else F()
              for m in range(20)] for l in range(6)] for T in range(32)]
  readings=[screens(h) for h in response]
  mass=readings[0][0]
  debit={name:sum((co[name][32*mode+T]*readings[T][mode]for mode in range(16)for T in range(32)),F())for name in stage_names}
  return response,readings,mass,debit,{name:g*mass-debit[name]for name in stage_names}
 rows={name:[]for name in stage_names}
 for i,j in product(range(len(orb3)),range(len(orb5))):
  z,w=orb3[i]['representative'];zz,ww=orb5[j]['representative']
  response,readings,mass,debit,gates=evaluate(z,w,zz,ww)
  for name in stage_names:
   ck(name+f'_positive_complete_corner_{i}_{j}',gates[name]>0)
   rows[name].append({'case':[i,j],'source':[z,w,zz,ww],'orbit_size':orb3[i]['size']*orb5[j]['size'],'mass':str(mass),'debit':str(debit[name]),'gate':str(gates[name])})
 minima={name:min(rows[name],key=lambda row:F(row['gate']))for name in stage_names}
 for name in stage_names:
  ck(name+'_literal_corner_coverage',len(rows[name])==128 and sum(row['orbit_size']for row in rows[name])==11400)
 worst=minima['mixed370'];z,w,zz,ww=worst['source'];response,readings,mass,debit,gates=evaluate(z,w,zz,ww)
 cells=[(l,m)for l,m in product(range(6),range(20))if l!=z and m!=zz and(l//3,m//5)!=(0,0)]
 for T in range(32):
  for e3,e5 in product(range(4),repeat=2):
   direct=max(sum((x[l]*y[m]*response[T][l][m]for l,m in cells),F())for x,y in product(menu(6,3,W3,z,F(1),e3),menu(20,5,W5,zz,F(4,5),e5)))
   ck(f'worst_direct_menu_{T}_{e3}_{e5}',direct==readings[T][4*e3+e5])
 head={name:alpha*F(minima[name]['gate'])for name in stage_names}
 expected_gates=(F(18511371415535025960401955530167,2483100709386434494156800000000000),F(8943699239601424101098195893687,2483100709386434494156800000000000),F(3365813748958907912564595063607,2483100709386434494156800000000000))
 thresholds=(F(1,5600),F(1,11500),F(1,31000))
 for name,expected,threshold in zip(stage_names,expected_gates,thresholds):
  ck(name+'_exact_minimum',F(minima[name]['gate'])==expected)
  ck(name+'_head_strict_bound',head[name]>threshold)
 result={'schema':'fixed-star-unconditional30-source-v1','status':'PASS',
  'scope':{'fixed_geometry':'Central first pure roots2mod3 and4mod5, central15mask0mod15, seven-star central roles(R,C,I,J,L,M)=(0,2,0,2,0,10).',
   'free_pures':'Arbitrary central square and higher pure phases at every finite height, with631 actual-source hypotheses; arbitrary outside pure inventories under624/626.',
   'conditioned_originals':'Only30 unconditional pair labels qs,q²s,qs²; arbitrary outside endpoints and lifts, unions on the ten edges.',
   'paid_pairs':'The remaining90 pair labels have arbitrary globally fixed central and outside phases; their costs use this conditional source query grid. No within-edge endpoint sharing.',
   'source':'One actual conditional source per family, one fixed rational theta common to all32 responses and all source weights; no adaptive pair-phase mask on its positive support.',
   'continuation':'Inherited complete mixed-height L/W bounds and unrestricted23/29/31 continuation.',
   'not_claimed':'Arbitrary STAR/central first-root/mask geometry, unrestricted prime support, unrestricted Erdos7, optimality or new Lean verification.'},
  'dependencies':PINS,'constants':{'c':str(c),'g':str(g),'alpha':str(alpha)},'thinning_categories':[list(x)for x in CATEGORIES],'common_thinning':list(map(str,THIN)),
  'generators3':gens3,'generators5':gens5,'source_orbits3':orb3,'source_orbits5':orb5,
  'kappa':list(map(str,kappa)),'uniform_Z_floor':list(map(str,floor)),
  'strict_kappa_minimum':str(strict_kappa),'optional_strict_four_kappa_minimum':str(strict_four_kappa),'cell_evidence':cell_data,
  'conditioned30_labels':[x for x in labels if x['central_exponents']==[0,0]],'paid90_labels':[x for x in labels if x['central_exponents']!=[0,0]],'paid_pair_loss_coefficients':list(map(str,pair)),
  'old_gap_count':403,'head_strict_thresholds':{name:str(t)for name,t in zip(stage_names,thresholds)},
  'stages':{name:{'added_labels':sorted(added_labels[name],key=lambda row:row['modulus']),'added_loss_coefficients':list(map(str,added[name])),'combined_coefficients':list(map(str,co[name])),'remaining_missing':sorted(missing[name],key=lambda row:row['modulus']),'source_corners':rows[name],'minimum':minima[name],'head_haar_lower':str(head[name])}for name in stage_names},
  'checks':CHECKS,'check_count':len(CHECKS),'new_lean_verification':False,'LP_solved_by_producer':False,'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'check_count':len(CHECKS),'minima':minima,'head_lower':{name:str(head[name])for name in stage_names}},indent=2))

if __name__=='__main__':main()
