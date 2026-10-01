"""Exact retained-source moment model and rational three-point negative dual.
Standard library only. Rebuilds complete384 envelopes, full hinge and tail.
No solver, external data, float proof steps or Lean claim.
"""
from fractions import Fraction as F
from itertools import product
from math import prod,comb,factorial,isqrt
from collections import Counter,defaultdict
from functools import lru_cache
import argparse
from pathlib import Path
import json

POINTS=((4,63),(0,32),(3,63))
Q=(5,7,11,13,17,19,23)
LEAVES=(4,7,2,5,8)
V5=((F(0),F(1,5),F(4,5)),(F(0),F(4,15),F(11,15)),(F(1,5),F(0),F(4,5)),(F(4,15),F(0),F(11,15)),(F(4,15),F(4,15),F(7,15)))
CHECKS=0
def need(ok,msg):
 global CHECKS
 CHECKS+=1
 if not ok:raise ValueError(msg)
def a4(q):
 t=F(1,q-1)
 return 15*t+50*t*t+60*t**3+24*t**4

def build(c):
 need(c['primes']==list(Q) and c['leaves']==list(LEAVES),'literal actual808 coordinates')
 parts=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in Q[1:]]
 need(c['partitions']==parts,'literal first-digit partitions')
 family=dict(c['actual_family']);selected=c['selected_labels']
 need(len(selected)==len(set(selected))==23,'23 unique selected labels')
 need(len(family)==len(c['actual_family'])==25 and set(selected)==set(family)-{3,9},'complete selected originals')
 need(family[3]==0 and family[9]==1 and family[45]==11,'actual opposing phases')
 patterns=list(product(range(3),*[range(2) for q in Q[1:]]))
 beta=[prod((F(1,q-2) for i,q in enumerate(Q) if D>>i&1),start=F(1)) for D in range(128)]
 R={(D,h):(beta[D] if D and (h or D.bit_count()>1) else F(0)) for D in range(128) for h in range(3)}
 forced=set()
 for m in selected:
  n=m;h=0
  while n%3==0:n//=3;h+=1
  ids=[i for i,q in enumerate(Q) if n%q==0];D=sum(1<<i for i in ids)
  rem=n
  for i in ids:
   while rem%Q[i]==0:rem//=Q[i]
  need(rem==1 and n>1 and h<=2 and (h or len(ids)>1),'complete selected inventory')
  R[D,h]-=prod((F(Q[i]-1,Q[i]-2) for i in ids),start=F(1))/n
  for sid,s in enumerate(patterns):
   if all(family[m]%Q[i] in parts[i][s[i]] for i in ids):
    for l,leaf in enumerate(LEAVES):
     if leaf%3**h==family[m]%3**h:forced.add((l,sid))
 need(len(forced)==750 and min(R.values())>=0,'forced table and nonnegative complete inventory')
 loss={(D,h):R[D,h]+(beta[D]/2 if h==2 else 0) for D in range(128) for h in range(3)}
 W=[prod((F(q-1,q-2)*a4(q) for i,q in enumerate(Q) if D>>i&1),start=F(1)) for D in range(128)]
 T29=1+F(28,27)*a4(29);T=F(c['tail']['expected_upper'])
 need(T==F(4301685063112470380207,10**30),'unchanged complete804 tail')
 H0,Hr,Hv=(F(c['expected_hinge'][k]) for k in ('H0','Hr','Hv'))
 need(min(H0,Hr,Hv)>=0 and sum(W)*T29==F(c['expected_hinge']['Kq']),'complete moment support sum and inherited comparator')
 moments=(F(1),F(15),F(216))
 debit={(D,h):12*loss[D,h]+27*T29*T*W[D]*moments[h] for D in range(128) for h in range(3)}
 need(len(debit)==384 and min(debit.values())>0,'all384 source/moment coefficients strictlypositive')
 moment_only=[(D,h) for D,h in debit if loss[D,h]==0]
 need(moment_only==[(0,0),(0,1)]+[(1<<i,0) for i in range(7)],'nine explicit moment-only support/type classes')
 names=[('w',l) for l in range(5)]+[('r',),('v',),('epsilon',)]
 rix,vix,eix=5,6,7;uid={}
 for l in range(5):
  for sid in range(192):
   if (l,sid) not in forced:
    uid[l,sid]=len(names);names.append(('u',l,sid))
 zid={}
 for vi in range(3):
  for D,h in debit:
   zid[vi,D,h]=len(names);names.append(('z',vi,D,h))
 need(len(names)==1370 and len(uid)==210 and len(zid)==1152,'complete model dimensions')
 probabilities=[]
 for vi,mask in POINTS:
  pi=[V5[vi]]+[(F(q-1,q*(q-2)),1-F(q-1,q*(q-2))) if mask>>j&1 else (F(0),F(1)) for j,q in enumerate(Q[1:])]
  need(all(sum(p)==1 and min(p)>=0 for p in pi),'normalized vertex law')
  probabilities.append(pi)
 rows=[]
 def add(label,terms,rhs=F(0)):
  merged={}
  for idx,coef in terms:
   if coef:merged[idx]=merged.get(idx,F(0))+coef
  terms=[(idx,coef) for idx,coef in sorted(merged.items()) if coef]
  rows.append((label,terms,rhs))
 for (l,sid),idx in uid.items():add(('retained_cap',l,sid),[(idx,F(1)),(l,F(-1))])
 for root in ((0,1),(2,3,4)):add(('root_cap',*root),[(l,F(1)) for l in root]+[(rix,F(-1))])
 for l in range(5):add(('leaf_cap',l),[(l,F(1)),(vix,F(-1))])
 add(('v_le_r',),[(vix,F(1)),(rix,F(-1))])
 menu=Counter();omitted=Counter();epicount=Counter()
 for vi,pi in enumerate(probabilities):
  for D in range(128):
   inside=[i for i in range(7) if D>>i&1];outside=[i for i in range(7) if not D>>i&1]
   groups={}
   for sid,s in enumerate(patterns):
    kappa=tuple(s[i] for i in inside)
    p=prod((pi[i][s[i]] for i in outside),start=F(1))
    groups.setdefault(kappa,[]).append((sid,p))
   for h in range(3):
    leafsets=(tuple(range(5)),) if h==0 else (((0,1),(2,3,4)) if h==1 else tuple((l,) for l in range(5)))
    for kappa,matching in groups.items():
     for ls in leafsets:
      menu[vi,h]+=1
      terms=[(uid[l,sid],p) for l in ls for sid,p in matching if p and (l,sid) in uid]
      if not terms:
       omitted[vi,h]+=1
       continue
      terms.append((zid[vi,D,h],F(-1)))
      add(('epigraph',vi,D,h,kappa,ls),terms)
      epicount[vi,h]+=1
  mass=[prod((pi[i][s[i]] for i in range(7)),start=F(1)) for s in patterns]
  need(sum(mass)==1,'full192 pattern mass')
  add(('joint_slack',vi),[(eix,F(1)),(rix,Hr),(vix,Hv)]+
      [(zid[vi,D,h],coef) for (D,h),coef in debit.items()]+
      [(idx,-12*mass[sid]) for (l,sid),idx in uid.items()],-H0)
 need(sum(menu.values())==3*23328,'all common-colour query menus considered')
 bounds=[(F(0),F(1)) for _ in names]
 bounds[eix]=(-(H0+Hr+Hv),F(12))
 # A zero retained kernel gives a finite exact feasible point at the lower
 # epsilon bound. Thus that bound cannot discard a better maximizer.
 control=[F(0)]*len(names);control[0]=control[rix]=control[vix]=F(1);control[eix]=bounds[eix][0]
 for label,terms,rhs in rows:need(sum((coef*control[idx] for idx,coef in terms),F(0))<=rhs,'exact zero-kernel feasible control')
 need(sum(control[:5])==1,'weight equality control')
 info={'scope':'One shared retained source at three fixed categorical vertices. Build only; no claim of uniform positivity or atlas.',
  'points':[list(x) for x in POINTS],'normalization':'nu_u restricted to U / nu_u(U); no normalized full-lambda source used for retained K',
  'variables':len(names),'variable_counts':{'w':5,'r':1,'v':1,'epsilon':1,'u':len(uid),'z':len(zid)},
  'inequality_rows':len(rows),'equality_rows':1,'matrix_nonzeros':sum(len(t) for _,t,_ in rows),
  'row_counts':dict(Counter(label[0] for label,_,_ in rows)),
  'epigraph_menu_rows':sum(menu.values()),'identicallyzero_query_rows_omitted':sum(omitted.values()),
  'epigraph_rows_by_point_type':[[epicount[vi,h] for h in range(3)] for vi in range(3)],
  'moment_only_types':[list(x) for x in moment_only],'all_envelope_types_per_point':384,
  'H0':str(H0),'Hr':str(Hr),'Hv':str(Hv),'T29':str(T29),'T1600':str(T),'sum_W':str(sum(W)),
  'epsilon_bounds':list(map(str,bounds[eix])),
  'joint_row':'epsilon + Hr*r + Hv*v + sum_(D,h)[12loss_Dh +27T29*T1600*W_D*(1,15,216)_h]z_viDh -12M(pi_vi,u) <= -H0',
  'coefficients':[{'D':D,'h':h,'loss':str(loss[D,h]),'W':str(W[D]),'joint_debit':str(debit[D,h])} for D,h in debit],
  'zero_kernel_control':'exact feasible with w0=r=v=1, u=z=0, epsilon=-(H0+Hr+Hv); no solver invoked'}
 return names,bounds,rows,info


def full_hinge_coefficients(h):
 @lru_cache(None)
 def pmf(k,n):
  if k==0:return F(n==1)
  q=Q[k-1];C=F(q-1,q-2)
  def tail(e):return F(1) if e==0 else C/q**e
  return sum(((tail(d-1)-tail(d))*pmf(k-1,n//d) for d in range(1,n+1) if n%d==0),F(0))
 mean=prod((1+F(1,q-2) for q in Q),start=F(1))
 H0,Hr,Hv=mean-h,mean,3*mean/2
 for n in range(1,h):
  p1=pmf(len(Q),n);p2=pmf(len(Q),n//2) if n%2==0 else F(0)
  pv=sum((F(2,3**(d-2))*pmf(len(Q),n//d) for d in range(3,n+1) if n%d==0),F(0))
  H0+=(h-n)*p1;Hr+=(h-n)*(p2-p1);Hv+=(h-n)*(pv-p2)
 return H0,Hr,Hv

def complete_tail(t):
 need((t['lower'],t['upper'],t['ell'],t['growth'])==(1600,3000,7,21),'complete804 tail shape')
 delta=F(t['delta']);scale=t['scale']
 need(delta==F(2,7) and scale==10**30,'full tail distortion/grid')
 C=F(27,256)/(delta**3*(1-delta))
 need(C==F(64827,10240),'analytic tail constant')
 need(all(F(x)/(1-delta)<=comb(21,i) for i,x in enumerate((15,50,60,24),1)),'complete quartic growth comparison')
 series=sum((F(factorial(21),factorial(21-j)*21**j) for j in range(22)),F(0))
 total=C/3*F(99,97)**21*F(3000,2999**4)*series
 ps=[p for p in range(1601,3001) if all(p%d for d in range(2,isqrt(p)+1))]
 need(ps==t['primes'] and len(ps)==179,'all179 prime bridge factors')
 for p in reversed(ps):
  raw=C/(p-1)**4+(1+F(7,5)*a4(p))*total
  total=F(-((-raw.numerator*scale)//raw.denominator),scale)
  need(0<=total-raw<F(1,scale),'exact upward rounding')
 need(total==F(t['expected_upper'])==F(4301685063112470380207,10**30),'complete fullT1600')
 return total

def verify(c):
 need(c['schema']=='e7-retained-moment-threepoint-dual-v1','schema')
 need(c['points']==[list(p) for p in POINTS] and c['threshold']==16,'three fixed probability points andh16')
 H0,Hr,Hv=full_hinge_coefficients(16)
 Kq=prod((1+F(q-1,q-2)*a4(q) for q in Q),start=F(1))*(1+F(28,27)*a4(29))
 T=complete_tail(c['tail'])
 for key,value in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=Kq,T1600=T).items():
  need(F(c['expected_hinge'][key])==value,'exact full comparator '+key)
 names,bounds,rows,info=build(c)
 need(c['epsilon_bounds']==list(map(str,bounds[7])) and c['box_for_other_variables']==['0','1'],'literal actual variable boxes')
 key=lambda label:json.dumps(label,separators=(',',':'))
 lookup={key(label):(terms,rhs) for label,terms,rhs in rows}
 need(len(lookup)==len(rows),'unique mathematical row labels')
 aggregate=[F(0)]*len(names);rhs_total=F(0);seen=set();tagcounts=Counter();joint=[]
 for entry in c['inequality_multipliers']:
  label=entry['row'];k=key(label);y=F(entry['multiplier'])
  need(k in lookup and k not in seen,'valid unique reconstructed dual row')
  need(y>=0,'nonnegative exact inequality multiplier')
  seen.add(k);tagcounts[label[0]]+=1
  terms,rhs=lookup[k]
  for idx,coef in terms:aggregate[idx]+=y*coef
  rhs_total+=y*rhs
  if label[0]=='joint_slack':joint.append({'point_index':label[1],'point':info['points'][label[1]],'multiplier':str(y)})
 mu=F(c['equality_multiplier'])
 for l in range(5):aggregate[l]+=mu
 residual=[F(i==7)-aggregate[i] for i in range(len(names))]
 boxterms=[max(e*lo,e*hi) for e,(lo,hi) in zip(residual,bounds)]
 box=sum(boxterms,F(0));upper=rhs_total+mu+box
 need(upper==F(c['expected_upper']),'recomputed exact dual upper')
 need(box==F(c['expected_residual_correction']),'recomputed complete box correction')
 need(upper<F(-3,100),'strict fixedh16 shared-kernel obstruction below -3/100')
 need(residual[7]==1-sum((F(x['multiplier']) for x in joint),F(0)),'epsilon normalization residual fully accounted')
 result={'schema':'e7-retained-moment-threepoint-obstruction-result-v1',
  'scope':'Fixedh16, sameactual808 phases, one common192-pattern retained kernel/weight law over the three declared categorical points. Normalization nu_u|U/nu_u(U); full384 retained fourth-moment envelope and completeT1600. Not an all-threshold, source-adaptive or unrestricted covering obstruction.',
  'model':{k:v for k,v in info.items() if k!='coefficients'},'joint_coefficients':info['coefficients'],
  'nonnegative_dual_multipliers':len(seen),'dual_row_counts':dict(tagcounts),'joint_multipliers':joint,
  'equality_multiplier':str(mu),'inequality_rhs_contribution':str(rhs_total),
  'positive_box_terms':sum(t>0 for t in boxterms),'epsilon_residual':str(residual[7]),
  'epsilon_box_contribution':str(boxterms[7]),'residual_box_correction':str(box),
  'residual_box_correction_decimal':float(box),'upper_bound':str(upper),'upper_bound_decimal':float(upper),
  'strict_upper_bound':'-3/100','checks':CHECKS,'evidence':'Exact Fraction reconstruction of all mathematical rows and complete box correction. No solver input or external file used.'}
 return result

def main():
 here=Path(__file__).resolve().parent
 parser=argparse.ArgumentParser()
 parser.add_argument('--certificate',type=Path,default=here/'retained_moment_threepoint_obstruction_certificate.json')
 parser.add_argument('--result',type=Path,default=here/'retained_moment_threepoint_obstruction.json')
 parser.add_argument('--write-result',action='store_true')
 args=parser.parse_args();c=json.loads(args.certificate.read_text());result=verify(c)
 if args.write_result:args.result.write_text(json.dumps(result,indent=2)+'\n')
 elif json.loads(args.result.read_text())!=result:raise ValueError('saved exact result does not match recomputation')
 print(json.dumps({k:result[k] for k in ('checks','nonnegative_dual_multipliers','upper_bound_decimal','strict_upper_bound')},indent=2))

if __name__=='__main__':main()
