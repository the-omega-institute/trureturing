#!/usr/bin/env python3
"""Exact mask-aware universal retained-core debit under Report604 source caps.
Standard-library only. This verifies finite arithmetic and inventory; the
universal cylinder-cap/source theorem is the explicitly cited Report604 FA6.
No Lean or full continuation certificate is claimed.
"""
from fractions import Fraction as Q
from itertools import product,combinations
from pathlib import Path
import json,argparse

QS=(7,11,13,17,19)
PURE3=((3,2),(9,7),(27,4),(81,13),(243,40),(729,121))
CHECKS=[]
def check(name,truth,scope=1):
 if not truth:raise ArithmeticError(name)
 CHECKS.append(dict(name=name,evaluations=scope))
def main():
 words=[x for x in range(729) if all(x%mod!=r for mod,r in PURE3)]
 check('actual ternary survivor count',len(words)==365,729*len(PURE3))
 w=[Q(sum(x%9==l for x in words),365) for l in range(9)]
 v=[Q(0) if x%5==4 or x==2 else Q(1,4*(4 if x%5==2 else 5)) for x in range(25)]
 check('central source normalization',sum(w)==sum(v)==1,34)
 mass={(l,m):w[l]*v[m] for l,m in product(range(9),range(25))}
 def live(l,m):return not (l%3==0 and m%5==0)
 unmasked=sum(p for (l,m),p in mass.items() if live(l,m));M=1-unmasked
 check('fixed central15 mask',M==Q(243,1460),225)
 check('positive unmasked cells',sum(p>0 and live(l,m) for (l,m),p in mass.items())==80,225)
 def support(fn):return sum(p for (l,m),p in mass.items() if live(l,m) and fn(l,m))
 profiles={
  'row':[support(lambda l,m,i=i:l%3==i) for i in range(3)],
  'column':[support(lambda l,m,j=j:m%5==j) for j in range(5)],
  'point':[support(lambda l,m,i=i,j=j:l%3==i and m%5==j) for i,j in product(range(3),range(5))],
  'leaf9':[support(lambda l,m,a=a:l==a) for a in range(9)],
  'leaf25':[support(lambda l,m,a=a:m==a) for a in range(25)]}
 maxima={key:max(vals) for key,vals in profiles.items()}
 wanted=dict(row=Q(729,1460),column=Q(1,4),point=Q(243,1460),leaf9=Q(81,365),leaf25=Q(1,16))
 check('every actual central role bounded including source-null roles',maxima==wanted,57*225)
 r={q:Q(1,q-1) for q in QS};a={q:Q(1,q*(q-2)) for q in QS}
 star_coefs=sum(maxima.values());square_coefs=maxima['row']+maxima['column']
 star=star_coefs*sum(r.values())+square_coefs*sum(a.values())
 kap=sum(r[q]*r[s]+a[q]*r[s]+r[q]*a[s] for q,s in combinations(QS,2))
 pair_coefs=unmasked+sum(maxima[k] for k in ('row','column','point'));pair=pair_coefs*kap
 lower=unmasked-star-pair
 check('star exact debit',star==Q(1456983547,2423366400),35)
 check('pair exact debit',pair==Q(776404835189,4369848912000),120)
 check('universal retained-source lower bound',lower==Q(3344320856939,61177884768000) and lower>Q(1,19))
 inventory=[15]
 for q in QS:inventory.extend([3*q,5*q,15*q,9*q,25*q,3*q*q,5*q*q])
 for q,s in combinations(QS,2):
  for e,f in ((1,1),(2,1),(1,2)):
   for i,j in product(range(2),repeat=2):inventory.append(3**i*5**j*q**e*s**f)
 check('156 odd pairwise-distinct actual labels',len(inventory)==len(set(inventory))==156 and all(x>1 and x%2 for x in inventory),156)
 D=Q(2)*Q(5,3)
 for q in QS:D*=Q(q,q-2)
 haar=lower/D
 check('source density conversion',D==Q(3458,405) and haar==Q(3344320856939,522353396364800) and haar>Q(1,160))
 return dict(scope='Fixed FA1 and central15=0; arbitrary globally fixed central/outside star and pair phases; all outside pure phases arbitrary; 156 retained labels only; no L/W continuation claim.',source_caps='Report604 FA4-FA6; r_q=1/(q-1), a_q=1/[q(q-2)], rho<=D Haar',w=w,v=v,central_mask=M,central_role_masses=profiles,central_role_maxima=maxima,star_coefficient=star_coefs,square_coefficient=square_coefs,r_sum=sum(r.values()),a_sum=sum(a.values()),kappa_sum=kap,pair_coefficient=pair_coefs,star_debit=star,pair_debit=pair,retained_source_lower=lower,haar_lower=haar,density_cap=D,labels=sorted(inventory),checks=CHECKS,predicates=len(CHECKS),evaluations=sum(c['evaluations'] for c in CHECKS))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',default=str(Path(__file__).with_suffix('.json')));args=p.parse_args()
 result=main();Path(args.out).write_text(json.dumps(result,default=str,indent=2)+'\n')
 print(json.dumps({key:result[key] for key in ('retained_source_lower','haar_lower','predicates','evaluations')},default=str))
