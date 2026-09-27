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
# Actual counterexamples to scalar cross-stage monotonicity. A fixed later
# family reads a retained root whose density increases, then reaches its cap.
def actual_extension_examples():
 def crt_class(parts):
  residue=0;modulus=1
  for p,r in parts:
   residue+=modulus*((r-residue)*pow(modulus,-1,p)%p);modulus*=p
  if not (0<=residue<modulus and all(residue%p==r for p,r in parts)):
   raise ValueError('actual extension CRT')
  return modulus,residue
 parts=((),((5,4),),((7,6),),((5,4),(7,6)))
 first=[crt_class(old+((11,2*i+j),)) for i,old in enumerate(parts) for j in (1,2)]
 later=[crt_class(old+((11,0),(13,2*i+j))) for i,old in enumerate(parts) for j in (1,2)]
 examples=[]
 for n in (2,4,6,8):
  originals=first[:n]+later
  counts=defaultdict(int)
  for m,r in originals:counts[m]+=1
  ck('extension_labels_'+str(n),all(m>1 and m%2 and counts[m]==2 for m in counts)
     and len(set(originals))==len(originals))
  J11=F();J13=F();mass11=F();mass13=F();safe=F()
  for x5,x7 in product(range(5),range(7)):
   forbidden11=set()
   for z11 in range(11):
    _,old=crt_class(((5,x5),(7,x7),(11,z11)))
    if any(old%m==r for m,r in first[:n]):forbidden11.add(z11)
   h11=min(F(5,3),F(11,11-len(forbidden11)))
   J11+=F(1,35)*max(len(forbidden11)-5,0)
   mass11+=F(1,35)*h11*F(11-len(forbidden11),11)
   for z11 in range(11):
    if z11 in forbidden11:continue
    weight=h11/F(385)
    forbidden13=set()
    for z13 in range(13):
     _,full=crt_class(((5,x5),(7,x7),(11,z11),(13,z13)))
     if any(full%m==r for m,r in later):forbidden13.add(z13)
    excess=max(len(forbidden13)-6,0)
    if excess != 2*int((x5,x7,z11)==(4,6,0)):
     raise ValueError('actual later excess support')
    if (x5,x7,z11)==(4,6,0):safe+=weight
    J13+=weight*excess
    h13=min(F(3,2),F(13,13-len(forbidden13)))
    mass13+=weight*h13*F(13-len(forbidden13),13)
  expected_J11={2:F(),4:F(),6:F(1,35),8:F(3,35)}[n]
  expected_J13={2:F(2,315),4:F(2,245),6:F(2,231),8:F(2,231)}[n]
  expected_loss={2:F(),4:F(),6:F(8,1155),8:F(6,385)}[n]
  ck('extension_J11_'+str(n),J11==expected_J11)
  ck('extension_J13_'+str(n),J13==expected_J13)
  ck('extension_loss11_'+str(n),1-mass11==expected_loss)
  ck('extension_retained_root_'+str(n),safe==F(1,385)*min(F(5,3),F(11,11-n)))
  ck('extension_later_payoff_'+str(n),J13==2*safe)
  ck('extension_mass13_'+str(n),mass13==mass11-F(11,26)*safe)
  ck('extension_positive_mass_'+str(n),mass13>0)
  examples.append({'first11_original_count':n,'originals':originals,
   'J11_union':J11,'J13_union':J13,'loss11':1-mass11,
   'mass11':mass11,'mass13':mass13,'retained_root_mass':safe})
 ck('extension_increases_later_excess',examples[1]['J13_union']>examples[0]['J13_union'])
 ck('extension_increases_both_loss_and_later_excess',
    examples[2]['loss11']>examples[1]['loss11'] and examples[2]['J13_union']>examples[1]['J13_union'])
 ck('extension_cap_preserves_later_excess',examples[3]['loss11']>examples[2]['loss11']
    and examples[3]['J13_union']==examples[2]['J13_union'])
 return {'families':examples,
  'refuted_claims':['Increasing the earlier actual forbidden union cannot increase the later union excess.',
                    'A strict increase of earlier actual row loss must strictly decrease the later union excess.'],
  'scope':'Each case is one actual finite two-copy family with the same later13 originals. No old5/7 or later17/19 originals. Not a simultaneous-four-threshold counterexample, PA failure, or odd covering.'}
extensions=actual_extension_examples()
result={'statement':'Four actual-root one-row consumers for arbitrary finite two-copy Q-smooth families. No oldcomb, first11-table or oldphase restrictions.',
'PA_corners':rows,'A5':A5,'A7':A7,'A57':A57,'kreq':kreq,'root_consumers':root_consumers,
'actual_extension_counterexamples':extensions,
'checks':checks,'check_count':len(checks),
'scope':'Maximum integer threshold certified by this one-row PA lower-mass bound. Failure at the next K is certificate failure, not an actual-family counterexample. All root-excess integrals use the actual prefix law from the same original family. Ordinary proof, no Lean.'}
def enc(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x).__name__)
args.output.write_text(json.dumps(result,default=enc,indent=2)+'\n',encoding='utf-8')
for row in root_consumers:
 print('q',row['q'],'K',row['maximum_certified_root_threshold'],'r',row['rowmass'],'R',row['uniform_R'],row['uniform_R_decimal'],'gap',row['uniform_margin'],'Jlimit',row['strict_root_excess_integral_threshold'],row['strict_root_excess_integral_threshold_decimal'])
print('checks',len(checks))
