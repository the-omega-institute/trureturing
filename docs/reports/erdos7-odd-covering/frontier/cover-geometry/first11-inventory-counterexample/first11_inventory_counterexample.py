#!/usr/bin/env python3
"""Exact independent verification of a fixed first-eleven counterexample.
The50-slot certificate is expanded into200 actual CRT originals and124
query cylinders.  No old producer, family optimization, or Lean is run.
"""
from fractions import Fraction as F
from collections import Counter,defaultdict
from itertools import product
from math import prod
from pathlib import Path
import argparse,hashlib,json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
# Each row has a,b and (r5,r7,color) for the two fixed numerical copies.
TABLE=(
 (0,0,(0,0,6),(0,0,3)),(0,1,(0,5,1),(0,5,5)),(0,2,(0,47,4),(0,33,4)),(0,3,(0,166,4),(0,19,4)),(0,4,(0,635,7),(0,215,4)),
 (1,0,(4,0,2),(4,0,8)),(1,1,(4,3,4),(4,3,1)),(1,2,(3,19,7),(4,31,5)),(1,3,(4,235,1),(3,145,7)),(1,4,(3,306,0),(4,637,4)),
 (2,0,(4,0,0),(24,0,7)),(2,1,(19,3,7),(9,5,0)),(2,2,(19,26,4),(15,47,0)),(2,3,(19,94,5),(9,81,1)),(2,4,(18,768,7),(19,1825,7)),
 (3,0,(24,0,0),(79,0,7)),(3,1,(34,3,0),(9,3,0)),(3,2,(124,21,4),(99,42,5)),(3,3,(43,313,8),(94,73,5)),(3,4,(95,565,2),(104,511,5)),
 (4,0,(249,0,0),(224,0,0)),(4,1,(299,5,0),(279,4,5)),(4,2,(129,18,5),(198,19,2)),(4,3,(84,304,5),(265,341,8)),(4,4,(53,187,8),(59,1123,5)),
)
N=4;L5=5**N;L7=7**N;L11=11**N;OLD=L5*L7
T5={1:4,2:14,3:14,4:14};D5={a:3 for a in range(1,5)}
T7={1:5,2:19,3:19,4:19};D7={b:6 for b in range(1,5)}
checks={}
def require(name,value):
 checks[name]=bool(value)
 if not value:raise ValueError(name)
def crt(parts):
 parts=[(m,r%m) for m,r in parts if m>1];M=prod(m for m,r in parts)
 return M,sum(r*(M//m)*pow(M//m,-1,m) for m,r in parts)%M

def original(parts,**meta):
 d,a=crt(parts)
 if any(a%m!=r%m for m,r in parts):raise ValueError('CRT residual')
 return {'modulus':d,'residue':a,'components':parts,**meta}
old_originals=[]
for p in (5,7):
 for e in range(1,5):
  for copy in (1,2):old_originals.append(original([(p**e,copy*p**(e-1))],kind='old_pure'))
for a,b in product(range(1,5),repeat=2):
 for t in (3,4):old_originals.append(original([(5**a,3*5**(a-1)),(7**b,t*7**(b-1))],kind='old_mixed'))
slots=[];eleven=[]
for a,b,row0,row1 in TABLE:
 for copy,(r5,r7,g) in enumerate((row0,row1)):
  slots.append((a,b,copy,r5,r7,g))
  require('normalized_slot_'+str(len(slots)),0<=r5<5**a and 0<=r7<7**b and 0<=g<10)
  for c in range(1,5):
   phase11=11**(c-1)-1+g*11**(c-1)
   eleven.append(original([(5**a,r5),(7**b,r7),(11**c,phase11)],kind='first11',a=a,b=b,c=c,copy=copy,color=g))
queries=[]
for a,b,c in product(range(5),repeat=3):
 if not(a or b or c):continue
 if a and b:
  r5=D5[a];r7=T7[b] if c else D7[b]
 else:r5=T5[a] if a else 0;r7=D7[b] if b else 0
 parts=[(5**a,r5),(7**b,r7)]
 if c:parts.append((11**c,9))
 queries.append(original(parts,kind='finite_query',a=a,b=b,c=c))
row13=[original([(q['modulus'],q['residue']),(13,0)],kind='row13') for q in queries]
require('old_original_count',len(old_originals)==48)
require('first11_original_count',len(eleven)==200)
require('query_count',len(queries)==124)
require('query_numerical_identity_once',len({q['modulus'] for q in queries})==124)
require('first11_exactly_two_per_label',len(Counter(q['modulus'] for q in eleven))==100 and set(Counter(q['modulus'] for q in eleven).values())=={2})
require('first11_distinct_modulus_residue_pairs',len({(q['modulus'],q['residue']) for q in eleven})==200)
all_originals=old_originals+eleven+row13
multiplicity=Counter(q['modulus'] for q in all_originals)
require('global_two_copy_rule',max(multiplicity.values())==2 and len(all_originals)==372 and len(multiplicity)==248)
require('all_full_CRT_phases_normalized',all(0<=q['residue']<q['modulus'] for q in all_originals+queries))
require('all_moduli_odd_nonunit',all(q['modulus']>1 and q['modulus']%2 for q in all_originals+queries))

# Literal finite coordinate generation, independent of any aggregate result.
pure5=[x for x in range(L5) if all(x%(5**e) not in (5**(e-1),2*5**(e-1)) for e in range(1,5))]
pure7=[x for x in range(L7) if all(x%(7**e) not in (7**(e-1),2*7**(e-1)) for e in range(1,5))]
mix5={x for x in pure5 if any(x%(5**e)==3*5**(e-1) for e in range(1,5))}
mix7={x for x in pure7 if any(x%(7**e) in (3*7**(e-1),4*7**(e-1)) for e in range(1,5))}
left={x:(sum(1<<i for i,(a,b,j,r5,r7,g) in enumerate(slots) if x%(5**a)==r5),sum(x%(5**a)==T5[a] for a in T5),sum(x%(5**a)==D5[a] for a in D5)) for x in pure5}
right={x:(sum(1<<i for i,(a,b,j,r5,r7,g) in enumerate(slots) if x%(7**b)==r7),sum(x%(7**b)==T7[b] for b in T7),sum(x%(7**b)==D7[b] for b in D7)) for x in pure7}
profiles=Counter();budget_profiles=Counter();color_cache={}
copy0=sum(1<<i for i,slot in enumerate(slots) if slot[2]==0)
copy1=sum(1<<i for i,slot in enumerate(slots) if slot[2]==1)
for x in pure5:
 bm5,t5,d5=left[x]
 for y in pure7:
  if x in mix5 and y in mix7:continue
  bm7,t7,d7=right[y];active=bm5&bm7
  if active not in color_cache:
   bits=active;colors=0
   while bits:
    bit=bits&-bits;colors|=1<<slots[bit.bit_length()-1][5];bits^=bit
   color_cache[active]=colors
  profiles[color_cache[active],t5,d5,t7,d7]+=1
  budget_profiles[color_cache[active],(active&copy0).bit_count()-1,(active&copy1).bit_count()-1]+=1
histK=Counter()
for (colors,*rest),count in profiles.items():histK[colors.bit_count()]+=count
survivors=sum(profiles.values());w5=F(len(pure5),L5);w7=F(len(pure7),L7)
oldmass=F(survivors,OLD);mixedmass=F(len(mix5)*len(mix7),OLD)
require('literal_old_source_mass',survivors==376313 and oldmass==w5*w7-mixedmass)
require('full_old_profile_count',len(profiles)==186)
require('old_color_distribution',dict(histK)=={2:111704,4:106709,5:55852,6:38052,7:44578,8:17316,9:2102})
require('query_color9_absent_in_originals',all(not(colors&(1<<9)) for colors,*rest in profiles))

# Compute EACH 11^4 word's original comb membership and complete query prefix
# load directly from literal congruences.  Disjointness is checked here.
word_color=[];word_q=[];color_sizes=Counter()
for z in range(L11):
 hits=[g for g in range(10) if any(z%(11**c)==11**(c-1)-1+g*11**(c-1) for c in range(1,5))]
 if len(hits)>1:raise ValueError('color combs intersect')
 color=hits[0] if hits else None
 word_color.append(color);word_q.append(sum(z%(11**c)==9 for c in range(1,5)))
 if color is not None:color_sizes[color]+=1
beta=F(sum(word_q),L11)
require('all_color_combs_size_from_words',set(color_sizes.values())=={1464} and len(color_sizes)==10)
require('query_prefix_mean_from_words',beta==sum((F(1,11**c) for c in range(1,5)),F()))
newmass=F();hinge=F();linear_load=F();profile_results=[]
for (colors,t5,d5,t7,d7),count in sorted(profiles.items()):
 L0=1+t5+d7+d5*d7;M=1+t5+d7+d5*t7
 allowed_count=0;rawhinge=0;rawload=0
 for z,(color,q) in enumerate(zip(word_color,word_q)):
  if color is not None and colors&(1<<color):continue
  allowed_count+=1;L=L0+M*q;rawhinge+=max(L-2,0);rawload+=L
 g=F(allowed_count,L11);h=min(F(5,3),1/g);s=h*g
 if g!=1-beta*colors.bit_count():raise ValueError('literal forbidden-union mass')
 # Independent hinge identity: every query9 prefix survives because color9
 # occurs in no original; only L0=1 contributes the union-root correction.
 analytic=max(L0-2,0)*g+M*beta-(F(1,11) if L0==1 else F())
 if F(rawhinge,L11)!=analytic:raise ValueError('literal word hinge vs analytic identity')
 mass=F(count,OLD);newmass+=mass*s;hinge+=mass*h*F(rawhinge,L11);linear_load+=mass*h*F(rawload,L11)
 profile_results.append({'color_mask':colors,'old_query_counts':[t5,d5,t7,d7],'old_residue_count':count,'L0':L0,'M':M,'allowed11_word_count':allowed_count,'capped_density':str(h),'raw_hinge_word_sum':rawhinge})
require('all_actual_fibre_mass_at_most_one',newmass<=oldmass)
actual_loss=oldmass-newmass

# Recompute PA/NC4 constants from their geometric auxiliary laws.  Only
# atoms below the hinge threshold are enumerated; the mean is exact all-height.
def pure_coordinate(p,w):return (w,w+F(1,p-1),lambda n:w-F(1,p) if n==1 else F(p-1,p**n))
def capped_coordinate(p,c):return (F(1),1+c/F(p-1),lambda n:1-c/F(p) if n==1 else c*F(p-1,p**n))
def pa_hinge(coords,t):
 ans=prod(z[1] for z in coords)-t*prod(z[0] for z in coords)
 for ns in product(range(1,t),repeat=len(coords)):
  m=prod(ns)
  if m<t:ans+=(t-m)*prod(z[2](v) for z,v in zip(coords,ns))
 return ans
def pa_data(x,y):
 coords=[pure_coordinate(5,x),pure_coordinate(7,y)];mass=x*y-F(1,12);charges={}
 for p,t,c,a in ((11,2,F(5,3),F(1,3)),(13,2,F(3,2),F(1,4)),(17,4,F(2),F(1,4)),(19,4,F(9,5),F(1,5))):
  charges[p]=pa_hinge(coords,t);mass-=a*charges[p];coords.append(capped_coordinate(p,c))
 return mass,pa_hinge(coords,3),charges
T=F(257,51);alpha0,phi0,_=pa_data(F(1,2),F(2,3));c0=phi0-(T-2)*alpha0;kreq=c0/(T-2)
alpha,phi,charges=pa_data(w5,w7);F11=charges[11];F13=charges[13]
S11=F11/3-actual_loss;deficit=F13-hinge;joint=S11+deficit/4
G={}
for x,y in product((F(1,2),F(1)),(F(2,3),F(1))):
 a,p,_=pa_data(x,y);G[x,y]=(T-2)*a-p
base=G[F(1,2),F(2,3)]
A5=2*(G[F(1),F(2,3)]-base);A7=3*(G[F(1,2),F(1)]-base)
A57=6*(G[F(1),F(1)]-base-A5/2-A7/3)
d5=w5-F(1,2);d7=w7-F(2,3);old_mixed_deficit=F(1,12)-mixedmass
credit=(A5*d5+A7*d7+A57*d5*d7)/(T-2)+old_mixed_deficit
require('NC4_affine_reconstruction',base==-c0 and (T-2)*alpha-phi==-c0+A5*d5+A7*d7+A57*d5*d7)
require('strict_simplified_criterion_counterexample',joint<kreq)
require('fixed_prefix_repairs_this_finite_query_score',joint+credit>kreq)
# Exact actual row13 completion: all current phases equal zero, hence its
# forbidden fibre is empty or one13-root.  Both allowed masses exceed2/3,
# so capped PA normalization has fibre mass1.  There are no17/19 originals.
require('actual_row13_phases_all_zero',all(q['residue']%13==0 for q in row13))
require('actual_row13_loss_zero',min(F(3,2),F(13,12))*F(12,13)==1)
actual_savings={11:S11,13:charges[13]/4,17:charges[17]/4,19:charges[19]/5}
actual_NC4=(T-2)*newmass-phi
require('complete_actual_NC4_identity',actual_NC4==-c0+(T-2)*(credit+sum(actual_savings.values(),F())))
require('complete_actual_NC4_positive',actual_NC4>0)

# Inventory-sensitive inequality on the SAME complete old source.  The two
# pure slots occur at every retained depth; the nonpure old inventory is
# identical at those four depths but phases remain globally fixed.
pure_inventory=sum((F(5,11**q['c']) for q in eleven if q['a']==q['b']==0),F())
require('literal_pure_inventory',pure_inventory==10*beta==1-F(1,L11))
G_integral=F();defect_integral=F();loss_integral=F();slot_hinges=[F(),F()]
for (colors,n0,n1),count in budget_profiles.items():
 mass=F(count,OLD);r=beta*colors.bit_count();ell=max(5*r-2,F())/3
 Gpoint=5*beta*(max(n0-1,0)+max(n1-1,0))
 bpoint=5*beta*(int(n0>0)+int(n1>0))
 if (4-pure_inventory)*ell>Gpoint:raise ValueError('actual inventory-sensitive point inequality')
 G_integral+=mass*Gpoint;loss_integral+=mass*ell
 if ell>0:defect_integral+=mass*(2-pure_inventory-bpoint)
 slot_hinges[0]+=mass*max(n0-1,0);slot_hinges[1]+=mass*max(n1-1,0)
require('inventory_loss_matches_literal_kernel',loss_integral==actual_loss)
require('both_actual_slot_queries_below_F11',all(v<=F11 for v in slot_hinges))
require('integrated_inventory_inequality',(4-pure_inventory)*actual_loss<=G_integral<=F11)
inventory_saving_bound=F11*(1-pure_inventory)/(3*(4-pure_inventory))
sharper_saving_bound=(F11-G_integral+defect_integral)/3
require('both_inventory_saving_bounds',S11>=inventory_saving_bound and S11>=sharper_saving_bound)
p_one=F(5,11)+2*F(5,11*10)
rare_root_saving=F11*(1-p_one)/(3*(4-p_one))
require('at_most_one_root_inventory',p_one==F(6,11))
require('at_most_one_root_saving',rare_root_saving==5*F11/114 and rare_root_saving>kreq)
# Arbitrary two-copy old-source consequence: the nonnegative PA hinge
# increases with each pure-survivor mass, so use their universal minima.
_,_,baseline_charges=pa_data(F(1,2),F(2,3))
general_F11=baseline_charges[11]
general_root11_saving=5*general_F11/114
general_root11_margin=(T-2)*(general_root11_saving-kreq)
general_root11_bound=T-general_root11_margin
require('arbitrary_old_source_F11_minimum',general_F11==F(97,840))
require('arbitrary_old_source_root11_saving',general_root11_saving==F(97,19152))
require('arbitrary_old_source_root11_strict',general_root11_saving-kreq==F(2188590908071012189,1650097635185615616000)>0)
require('arbitrary_old_source_root11_NC4_margin',general_root11_margin==F(2188590908071012189,542935350932041267200))
require('arbitrary_old_source_root11_query_bound',general_root11_bound==F(2733779746141627138211,542935350932041267200)<T)


# External claimed constants are comparison targets ONLY; all result values
# above are reconstructed from the fixed phase certificate and PA definitions.
expected={'F11':F(4159811,36015000),'lambda11_mass':F(1272755929,5991995625),'first11_loss':F(45972376,1198399125),'S11':F(20023321,143807895000),'finite_hinge':F(112300666826237333,616568590178165625),'row13_deficit':F(407818078583196991,29595292328551950000),'finite_joint_saving':F(141433689662930477,39460389771402600000),'kreq':F(6168733163201163811,1650097635185615616000),'fixed_prefix_credit':F(18036721551129456405721,27793832042657713032000000)}
computed={'F11':F11,'lambda11_mass':newmass,'first11_loss':actual_loss,'S11':S11,'finite_hinge':hinge,'row13_deficit':deficit,'finite_joint_saving':joint,'kreq':kreq,'fixed_prefix_credit':credit}
for key,value in expected.items():require('independent_'+key,computed[key]==value)
result={'scope':'fixed actual globally phased two-copy counterexample to the simplified first11+finite-row13-deficit criterion; not a counterexample to fixed-old-slot554 or Erdos7',
 'oracle_task_id':'7b760625-5ad4-4822-bf8f-5744789dffc9','old_period':OLD,'old_originals':old_originals,'first11_originals':eleven,'finite_query_cylinders':queries,'optional_actual_row13_originals':row13,
 'full_numerical_label_multiplicity':{str(d):multiplicity[d] for d in sorted(multiplicity)},
 'old_survivor_count':survivors,'old_profiles_count':len(profiles),'old_color_distribution':{str(k):histK[k] for k in sorted(histK)},'profiles':profile_results,
 'pure5_mass':str(w5),'pure7_mass':str(w7),'old_mixed_union_mass':str(mixedmass),'old_survivor_mass':str(oldmass),'comb_mass':str(beta),
 'computed':{k:str(v) for k,v in computed.items()},'failure_margin':str(kreq-joint),'finite_query_score_after_credit_margin':str(joint+credit-kreq),
 'NC4_coefficients':{'c0':str(c0),'A5':str(A5),'A7':str(A7),'A57':str(A57)},
 'prefix_deficits':{'d5':str(d5),'d7':str(d7),'mixed_deficit':str(old_mixed_deficit)},
 'all_PA_prefix_hinges':{str(p):str(v) for p,v in charges.items()},'actual_PA_savings':{str(p):str(v) for p,v in actual_savings.items()},
 'actual_final_PA_mass':str(newmass),'PA_final_query_hinge_envelope':str(phi),'complete_actual_NC4_margin':str(actual_NC4),
 'complete_actual_PA_query_bound':str(2+phi/newmass),
 'inventory_sensitive':{'pure_inventory':str(pure_inventory),'old_budget_profile_count':len(budget_profiles),'actual_nonpure_slot_hinges':[str(v) for v in slot_hinges],'weighted_excess_integral':str(G_integral),'positive_loss_defect_integral':str(defect_integral),'uniform_saving_lower':str(inventory_saving_bound),'sharper_saving_lower':str(sharper_saving_bound),'one_root_inventory_upper':str(p_one),'one_root_saving_lower':str(rare_root_saving),'one_root_margin_above_kreq':str(rare_root_saving-kreq)},
 'arbitrary_old_source_root11':{'F11_minimum':str(general_F11),'saving_minimum':str(general_root11_saving),'NC4_margin':str(general_root11_margin),'complete_query_bound':str(general_root11_bound)},
 'logical_boundary':'finite hinge lower-bounds the completed-query supremum; positive finite-query repaired score alone is not an all-query theorem. Separate actual row13 zero-loss and full NC4 calculation certify this particular completed family.',
 'checks':checks,'passed_count':len(checks)}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed_count':len(checks),'old_profiles':len(profiles),'finite_joint_saving':str(joint),'failure_margin':str(kreq-joint),'credit_margin':str(joint+credit-kreq),'actual_NC4_margin':str(actual_NC4),'actual_PA_query_bound':str(2+phi/newmass),'output':str(args.output),'sha256':hashlib.sha256(args.output.read_bytes()).hexdigest()},indent=2))
