#!/usr/bin/env python3
"""General actual-root consumer: arbitrary finite two-copy Q-smooth family.
Q={5,7,11,13,17,19}. Each selected row satisfies its stated bound on
active current-prime roots, or its same-source integrated root excess.
No old comb, first11 table, or old-phase template is imposed.
"""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
from pathlib import Path
import argparse,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
checks={}
def ck(k,v):
 if not v or k in checks:raise ValueError(k)
 checks[k]=True
# Full first moment plus exact below-four convolution reconstructs every hinge.
def law(p,total,cap):
 return total,total+cap/F(p-1),{1:total-cap/F(p),2:cap*F(p-1,p*p),3:cap*F(p-1,p**3)}
def mul(a,b):
 pmf=defaultdict(F)
 for i,u in a[2].items():
  for j,v in b[2].items():
   if i*j<4:pmf[i*j]+=u*v
 return a[0]*b[0],a[1]*b[1],pmf
def hinge(a,t):return a[1]-t*a[0]+sum(((t-i)*v for i,v in a[2].items() if i<t),F())
def pa(x,y):
 a=mul(law(5,x,F(1)),law(7,y,F(1)));mass=x*y-F(1,12);hs={}
 for p,t,c in ((11,2,F(5,3)),(13,2,F(3,2)),(17,4,F(2)),(19,4,F(9,5))):
  hs[p]=hinge(a,t);mass-=2*c/F(p-1)*hs[p];a=mul(a,law(p,F(1),c))
 return mass,hinge(a,3),hs
T=F(257,51);a13=F(5,26)
def payoff(x,y):
 m,phi,_=pa(x,y);return (T-2)*m-phi
base=payoff(F(1,2),F(2,3));kreq=-base/(T-2)
A5=2*(payoff(F(1),F(2,3))-base);A7=3*(payoff(F(1,2),F(1))-base)
A57=6*(payoff(F(1),F(1))-base-A5/2-A7/3)
rows=[]
for i,(x,y) in enumerate(product((F(1,2),F(1)),(F(2,3),F(1)))):
 mass,phi,hs=pa(x,y)
 purecredit=(A5*(x-F(1,2))+A7*(y-F(2,3))+A57*(x-F(1,2))*(y-F(2,3)))/(T-2)
 saving=purecredit+hs[13]/4-a13*(x*y-F(1,12)-hs[11]/3)
 margin=saving-kreq
 alpha6=(1-a13)*(x*y-F(1,12)-hs[11]/3)-hs[17]/4-hs[19]/5
 ck('positive_alpha_'+str(i),alpha6>0)
 ck('margin_mass_identity_'+str(i),alpha6-phi/(T-2)==margin)
 ck('positive_margin_'+str(i),margin>0)
 rows.append({'x':x,'y':y,'hinges':hs,'Phi':phi,'purecredit':purecredit,'saving':saving,'margin':margin,'alpha6':alpha6,'query_bound':2+phi/alpha6})
minimum=min(r['margin'] for r in rows);R=max(r['query_bound'] for r in rows);minalpha=min(r['alpha6'] for r in rows)
ck('minimum_margin_at_anchor',minimum==rows[0]['margin'])
ck('maximum_query_at_anchor',R==rows[0]['query_bound'])
ck('full_query_strict_target',R<T)
for k in range(14):ck('root_profile_'+str(k),max(F(0),F(3*k-13,26))<=F(5,26)+F(3,26)*max(k-6,0))
# General one-row root certificates, all under this same actual PA law.
stages=((11,2,F(5,3),F(1,3)),(13,2,F(3,2),F(1,4)),(17,4,F(2),F(1,4)),(19,4,F(9,5),F(1,5)))
root_consumers=[]
for index,(q,t,C,a) in enumerate(stages):
 scans=[]
 for K in range(q+1):
  r=min(F(1),C*(1-F(K,q)));cr=[]
  for corner in rows:
   x,y,hs=corner['x'],corner['y'],corner['hinges']
   B=x*y-F(1,12)-sum((aa*hs[pp] for pp,tt,cc,aa in stages[:index]),F())
   later=sum((aa*hs[pp] for pp,tt,cc,aa in stages[index+1:]),F())
   alpha=r*B-later
   gap=alpha-corner['Phi']/(T-2)
   cr.append({'x':x,'y':y,'prefix_lower':B,'later_charge':later,'alpha':alpha,'Phi':corner['Phi'],'gap':gap,'R':2+corner['Phi']/alpha if alpha>0 else None})
  scans.append({'K':K,'rowmass':r,'certified':all(c['alpha']>0 and c['gap']>0 for c in cr),'corners':cr})
 good=[a for a in scans if a['certified']];chosen=good[-1]
 ck('threshold_exists_'+str(q),bool(good))
 ck('threshold_below_q_'+str(q),chosen['K']<q)
 ck('threshold_initial_interval_'+str(q),[a['K'] for a in good]==list(range(chosen['K']+1)))
 ck('next_threshold_not_certified_'+str(q),not scans[chosen['K']+1]['certified'])
 best_bound=max(c['R'] for c in chosen['corners']);gapmin=min(c['gap'] for c in chosen['corners'])
 Jthreshold=F(q)/C*gapmin
 for k in range(q+1):
  ck('profile_envelope_'+str(q)+'_'+str(k),max(F(),1-C*(1-F(k,q)))<=1-chosen['rowmass']+C/F(q)*max(k-chosen['K'],0))
 root_consumers.append({'q':q,'cap':C,'maximum_certified_root_threshold':chosen['K'],'rowmass':chosen['rowmass'],
 'corners':chosen['corners'],'next_threshold':scans[chosen['K']+1],
 'uniform_R':best_bound,'uniform_R_decimal':float(best_bound),'uniform_margin':gapmin,
 'strict_root_excess_integral_threshold':Jthreshold,'strict_root_excess_integral_threshold_decimal':float(Jthreshold),
 'strict_exceptional_mass_threshold':Jthreshold/(q-chosen['K']),
 'scan_summary':[{'K':a['K'],'certified':a['certified'],'minimum_alpha':min(c['alpha'] for c in a['corners']),'minimum_gap':min(c['gap'] for c in a['corners'])} for a in scans]})
result={'statement':'Four actual-root one-row consumers for arbitrary finite two-copy Q-smooth families. No oldcomb, first11-table or oldphase restrictions.',
'PA_corners':rows,'A5':A5,'A7':A7,'A57':A57,'kreq':kreq,'root_consumers':root_consumers,
'checks':checks,'check_count':len(checks),
'scope':'Maximum integer threshold certified by this one-row PA lower-mass bound. Failure at the next K is certificate failure, not an actual-family counterexample. All root-excess integrals use the actual prefix law from the same original family. Ordinary proof, no Lean.'}
def enc(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x).__name__)
args.output.write_text(json.dumps(result,default=enc,indent=2)+'\n',encoding='utf-8')
for row in root_consumers:
 print('q',row['q'],'K',row['maximum_certified_root_threshold'],'r',row['rowmass'],'R',row['uniform_R'],row['uniform_R_decimal'],'gap',row['uniform_margin'],'Jlimit',row['strict_root_excess_integral_threshold'],row['strict_root_excess_integral_threshold_decimal'])
print('checks',len(checks))
