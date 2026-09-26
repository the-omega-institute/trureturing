#!/usr/bin/env python3
"""Exact certificate for a common-root restricted ten-prime family.

One actual pure-product source, one further excluded outside root per q, all
32 outside-support responses and all512 original/query fees. Every11400
central pure-source comparison corner is evaluated with theta=1. No symmetry
reduction, LP, finite-height extrapolation, Lean claim or unrestricted #7 claim.
"""
import argparse,json,time
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from hashlib import sha256
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args();D=args.source_dir;Q=(7,11,13,17,19);core=(3,5)+Q;E=tuple(combinations(Q,2));CHECKS={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 CHECKS[k]=True
raw=(D/'actual_pair_activation_certificate.json').read_bytes()
ck('base_pin',sha256(raw).hexdigest()=='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f')
base=json.loads(raw);raw635=(D/'conditional30_fixedstar_augmented_certificate.json').read_bytes();v635=json.loads(raw635)
ck('certificate635_pin',sha256(raw635).hexdigest()=='eb45a79b8943ac56b72153c72472bf40b098366574deb249840ea28f504a9345')
c=F(1084133,201247200);g=1-c;alpha=F(2673,110656)
r={q:F(1,q-1)for q in Q};a={q:F(1,q*(q-2))for q in Q};A={q:1-r[q]for q in Q}
ck('continuation_binding',c==F(base['constants']['continuation_c'])==F(v635['constants']['c'])and alpha==F(v635['constants']['alpha']))
oldstars={d*q for d in(3,5,15,9,25)for q in Q}|{d*q*q for d in(3,5)for q in Q}
newstars={9*q*q for q in Q}|{d*q for d in(45,75,225)for q in Q}
oldpairs={q**u*s**v for q,s in E for u,v in((1,1),(2,1),(1,2))}
newpairs={9*q*s for q,s in E}
paidpairs={d*n for d in(3,5,15)for n in oldpairs}
extra=set()
for p in(3,5):
 for trip in combinations(Q,3):
  for ee in product((1,2),repeat=3):extra.add(p*p*prod(q**e for q,e in zip(trip,ee)))
for d in(45,75,225):
 for q,s in E:
  for u,v in product((1,2),repeat=2):extra.add(d*q**u*s**v)
for p in(3,5):
 for q,s in E:
  for u,v in((2,2),(2,1),(1,2)):extra.add(p*p*q**u*s**v)
for d in(45,75,225):
 for q in Q:extra.add(d*q*q)
extra|={25*q*q for q in Q}|{25*q*s for q,s in E}
central={45,75,225}
blocks=[oldstars,newstars,oldpairs,newpairs,paidpairs,extra,central,{15}]
ck('full_disjoint_inventory',list(map(len,blocks))==[35,20,30,10,90,370,3,1]and len(set.union(*blocks))==559)
ck('635_370_labels',extra=={x['modulus']for x in v635['stages']['mixed370']['added_labels']})
ck('635_remaining33',newstars|newpairs|central=={x['modulus']for x in v635['stages']['mixed370']['remaining_missing']})
# All max-exponent<=2 mixed labels are covered by the original unrestricted
# base inventory or exactly the additional10 oldcentral-square stars+403.
base_low=set();all_low=set()
for ee in product(range(3),repeat=7):
 support=sum(e>0 for e in ee)
 if support<2:continue
 n=prod(p**e for p,e in zip(core,ee));all_low.add(n)
 if(ee[0]<=1 and ee[1]<=1)or support>=5:base_low.add(n)
ck('all2172_low_mixed_covered',len(all_low)==2172 and len(base_low)==1759 and all_low==base_low|set.union(*blocks))
def fees(labels):
 out=[F()]*512
 for n in labels:
  m=n;ee=[]
  for p in core:
   e=0
   while m%p==0:m//=p;e+=1
   ee.append(e)
  ck('factor_'+str(n),m==1 and max(ee)<=2)
  T=sum(1<<i for i,e in enumerate(ee[2:])if e)
  cap=prod(r[q]if e==1 else a[q]for q,e in zip(Q,ee[2:])if e)
  out[32*(4*ee[0]+ee[1])+T]+=cap
 return out
P=fees(paidpairs);DD=fees(extra);Cen=fees(central)
ck('P90_exact',P==list(map(F,v635['paid_pair_loss_coefficients'])))
ck('D370_exact',DD==list(map(F,v635['stages']['mixed370']['added_loss_coefficients'])))
ck('central3_modes',[(i,x)for i,x in enumerate(Cen)if x]==[(192,F(1)),(288,F(1)),(320,F(1))])
L=list(map(F,base['complete_coefficients']['loss']));W=list(map(F,base['complete_coefficients']['weighted_nonunit_query']))
co=[g*(l+p+d+k)+c*w for l,p,d,k,w in zip(L,P,DD,Cen,W)]
ck('complete512_nonnegative',len(co)==512 and min(co)>=0)
ck('635_fee_inheritance',[v-g*k for v,k in zip(co,Cen)]==list(map(F,v635['stages']['mixed370']['combined_coefficients'])))
# H_T=M15 product_(q notinT) A_q. The factor is independent of all central
# phases; 45/75/225 are paid exactly once as above, not inserted in the mask.
h=[prod(A[q]for i,q in enumerate(Q)if not T>>i&1)for T in range(32)]
hden=lcm(*(x.denominator for x in h));hv=[int(x*hden)for x in h]
hi=[[[0 if l<3 and m<5 else hv[T]for m in range(20)]for l in range(6)]for T in range(32)]
cden=lcm(g.denominator,*(x.denominator for x in co));ci=[int(x*cden)for x in co];gi=int(g*cden)
ck('exact_integer_scales',all(F(hv[T],hden)==h[T]for T in range(32))and all(F(ci[j],cden)==co[j]for j in range(512)))
def qscreen(row,zz,ww):
 out=[0,0,0,0]
 for block in range(4):
  total=0
  for m in range(5*block,5*block+5):
   if m==zz:continue
   v=(3 if m==ww else 4)*row[m];total+=v
   out[2]=max(out[2],v);out[3]=max(out[3],60*row[m])
  out[0]+=total;out[1]=max(out[1],total)
 return out
start=time.monotonic();minimum=None;records=[];central_templates={}
for z,w in product(range(6),repeat=2):
 if z==w:continue
 uw=[0 if l==z else 1 if l==w else 2 for l in range(6)]
 roots=[]
 for T in range(32):
  left=[sum(uw[l]*hi[T][l][m]for l in range(3))for m in range(20)]
  right=[sum(uw[l]*hi[T][l][m]for l in range(3,6))for m in range(20)]
  roots.append((left,right,[a+b for a,b in zip(left,right)]))
 for zz,ww in product(range(20),repeat=2):
  if zz==ww:continue
  ss=[[0]*32 for _ in range(16)]
  for T in range(32):
   left,right,total=roots[T];lc=qscreen(left,zz,ww);rc=qscreen(right,zz,ww);tc=qscreen(total,zz,ww)
   for e5 in range(4):ss[e5][T]=tc[e5];ss[4+e5][T]=max(lc[e5],rc[e5])
   for l in range(6):
    if not uw[l]:continue
    qs=qscreen(hi[T][l],zz,ww)
    for e5 in range(4):ss[8+e5][T]=max(ss[8+e5][T],uw[l]*qs[e5]);ss[12+e5][T]=max(ss[12+e5][T],9*qs[e5])
  screens=[x for row in ss for x in row]
  # The outside factor is constant in(l,m), so each512 screen factors into
  # its32 response times the corresponding one of16 central selector values.
  selector_tuple=tuple(ss[mode][0]//hv[0]for mode in range(16))
  ck('all512_separable_'+'_'.join(map(str,(z,w,zz,ww))),all(ss[mode][T]==selector_tuple[mode]*hv[T]for mode in range(16)for T in range(32)))
  if selector_tuple not in central_templates:central_templates[selector_tuple]={'corner':(z,w,zz,ww),'multiplicity':0}
  central_templates[selector_tuple]['multiplicity']+=1
  debit=sum(x*y for x,y in zip(ci,screens));numer=gi*screens[0]-debit
  ck('positive_'+'_'.join(map(str,(z,w,zz,ww))),numer>0)
  records.append({'source_corner':[z,w,zz,ww],'gate_numerator':str(numer)})
  if minimum is None or numer<minimum[0]:minimum=(numer,(z,w,zz,ww),screens[0],debit)
ck('literal11400',len(records)==11400)
gden=cden*hden*675;gate=F(minimum[0],gden)
ck('gate_over_1_28',gate>F(1,28));ck('Haar_over_1_1200',alpha*gate>F(1,1200))
# Literal jointly released labels are charged back on the SAME source.
# Released originals keep their numerical identity; only phase restrictions
# are removed, and one original is never charged twice within a joint set.
release_sets={
 'new_square_and_pair15':{9*q*q for q in Q}|{9*q*s for q,s in E},
 'new_linear15':{d*q for d in(45,75,225)for q in Q},
 'new10_pairs':set(newpairs),
 'new5_square_stars':{9*q*q for q in Q},
 'old30_pairs':set(oldpairs),
 'all40_pairs':oldpairs|newpairs,
 'all20_new_stars':set(newstars),
 'all30_new_outside':newstars|newpairs,
 'all55_stars':oldstars|newstars,
}
anchor95=oldstars|newstars|oldpairs|newpairs
ck('two_joint15_disjoint',len(release_sets['new_square_and_pair15'])==len(release_sets['new_linear15'])==15 and release_sets['new_square_and_pair15'].isdisjoint(release_sets['new_linear15']))
ck('all11400_template_counts',sum(v['multiplicity']for v in central_templates.values())==11400)
release_results={}
for name,labels in release_sets.items():
 ck('release_inventory_'+name,labels<=anchor95)
 ff=fees(labels)
 folded=[sum(((co[32*m+T]+g*ff[32*m+T])*h[T]for T in range(32)),F())for m in range(16)]
 candidates=[(g*h[0]*F(sel[0],675)-sum((cost*F(v,675)for cost,v in zip(folded,sel)),F()),info['corner'])for sel,info in central_templates.items()]
 value,corner=min(candidates)
 release_results[name]={'released_labels':sorted(labels),'remaining_anchored_count':len(anchor95-labels),'minimum_corner':corner,'gate':str(value),'gate_float':float(value),'positive':value>0,'Haar_bound':str(alpha*value)if value>0 else None,'release512_coefficients':list(map(str,ff))}
ck('joint_square_pair15_positive',F(release_results['new_square_and_pair15']['gate'])>F(1,71))
ck('joint_linear15_positive',F(release_results['new_linear15']['gate'])>F(1,417))
ck('joint_square_pair15_haar',F(release_results['new_square_and_pair15']['Haar_bound'])>F(1,3000))
ck('joint_linear15_haar',F(release_results['new_linear15']['Haar_bound'])>F(1,18000))
for name in('old30_pairs','all40_pairs','all20_new_stars','all30_new_outside','all55_stars'):ck('direct_fee_not_positive_'+name,not release_results[name]['positive'])
out={'schema':'global-root-exclusion-complete-source-certificate-v1','status':'POSITIVE_ALL11400','scope':'One common root t_q at each outside prime. All55 star labels have that root; each40 pair label has at least one endpoint equal to its coordinate root. All their central phases and opposite pair endpoints arbitrary. All other core labels, pure higher phases/heights, and23/29/31 originals arbitrary subject to635 base conventions. Distinct numerical moduli, globally fixed phases. Fixed firstpure3/5 roots2/4 and15phase0. This restricted phase geometry does not settle arbitrary33 or unrestricted Erdos7. No Lean.', 'minimum':{'source_corner':minimum[1],'gate':str(gate),'gate_float':float(gate),'Haar_bound':str(alpha*gate),'mass':str(F(minimum[2],hden*675)),'complete512_debit':str(F(minimum[3],gden))},'inventory':{'root_stars55':sorted(oldstars|newstars),'root_pairs40':sorted(oldpairs|newpairs),'paid_pairs90':sorted(paidpairs),'paid370':sorted(extra),'paid_central3':sorted(central),'old15_mask':15,'low_mixed_labels':len(all_low)},'constants':{'c':str(c),'g':str(g),'alpha':str(alpha)},'all32_outside_responses':list(map(str,h)),'combined512_coefficients':list(map(str,co)),'gate_common_denominator':str(gden),'source_corner_count':len(records),'all_source_gates_sha256':sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest(),'anchor_release':{'scope':'Each release row is one fixed JOINT set; its entire512 fee is added on the unchanged source. The two positive15-label groups are alternatives, not jointly released. All11400 corners are covered by the exact512-to16 selector factorization and recorded template multiplicities. Negative rows only reject this direct fee bound.','distinct_central_templates':len(central_templates),'source_corner_count':sum(v['multiplicity']for v in central_templates.values()),'central_templates':[{'selectors':list(k),**v}for k,v in central_templates.items()],'groups':release_results},'checks':len(CHECKS),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'dependencies':{'actual_pair_activation_certificate.json':sha256(raw).hexdigest(),'conditional30_fixedstar_augmented_certificate.json':sha256(raw635).hexdigest()},'new_lean_verification':False}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in('status','scope','minimum','checks')},indent=2))
