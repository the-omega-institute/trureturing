#!/usr/bin/env python3
"""Exact same-law counterexample to the universal shallow-mixed G-budget claim."""
import argparse
from fractions import Fraction as F
from math import factorial, prod
import json
from pathlib import Path

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()

P=(3,5,7,11,13,17,19)
L=315
FAMILY=((3,2),(5,1),(7,1),(9,1),(15,9),(21,12),(35,2),(45,25),(63,4),(105,18),(315,133))
PRIVATE={3:5,5:6,7:15,9:10,15:9,21:12,35:72,45:25,63:4,105:18,315:133}
LOW=F(31,100);HIGH=F(63,200)
ALPHA=F(7235955529,6075000000000);LAMBDA=1/ALPHA
C=F(4522277,500000);OLD_TARGET=F(565,51);NEW_TARGET=F(566,49)
checks={}
def check(name,p):
    if not p: raise AssertionError(name)
    checks[name]=True

def s(n,x):return sum((x**j/F(factorial(j)) for j in range(n+1)),F(0))
def affine(values,t):return values[0]+values[1]*t

labels=[d for d in range(1,L+1) if L%d==0]
check('all_nonunit_numerical_divisors_occupied',sorted(d for d,a in FAMILY)==labels[1:])
check('distinct_odd_nonunit_labels',len(set(d for d,a in FAMILY))==len(FAMILY) and all(d>1 and d%2 for d,a in FAMILY))
U=[x for x in range(L) if all(x%d!=a for d,a in FAMILY)]
check('survivor_has_74_points_and_zero',len(U)==74 and 0 in U)
for d,a in FAMILY:
    x=PRIVATE[d]
    check('private_'+str(d),x%d==a and all(x%e!=b for e,b in FAMILY if e!=d))

counts={d:[sum(x%d==a for x in U) for a in range(d)] for d in labels}
for d in labels:
    for t_name,t in [('lower',LOW),('upper',HIGH)]:
        qzero=t+(1-t)*F(counts[d][0],74)
        check('zero_is_maximizer_'+str(d)+'_'+t_name,
              all(qzero >= (1-t)*F(cnt,74)+t*(a==0) for a,cnt in enumerate(counts[d])))

free=prod(F(p,p-1) for p in P[3:])
weights={d:free*prod(F(p,p-1) for p,e in ((3,2),(5,1),(7,1)) if d%(p**e)==0) for d in labels}
# q_d(t)=count_d(0)/74 + (1-count_d(0)/74)t on the proved interval.
q_coeff={d:(F(counts[d][0],74),1-F(counts[d][0],74)) for d in labels}
r_coeff=(sum(weights[d]*q_coeff[d][0] for d in labels)-1,
         sum(weights[d]*q_coeff[d][1] for d in labels))
u_coeff=tuple(r_coeff[j]-sum(q_coeff[d][j] for d in labels[1:]) for j in (0,1))
mixed=[d for d in labels if sum(d%p==0 for p in P)>=2]
m_coeff=tuple(sum(q_coeff[d][j] for d in mixed) for j in (0,1))
check('seven_mixed_labels',mixed==[15,21,35,45,63,105,315])
check('mixed_affine_formula',m_coeff==(F(20,37),F(239,37)))
check('unused_increases_on_interval',u_coeff[1]>0)
check('total_increases_on_interval',r_coeff[1]>0)
check('mixed_increases_on_interval',m_coeff[1]>0)
max_density=L*(HIGH+(1-HIGH)/74)
check('density_cap',max_density<LAMBDA)
check('all_members_have_positive_full_survivor_density',0<LOW<=HIGH<1)

# Log bounds are proved by positive rational Taylor sums, no float tests.
v0hi=HIGH+(1-HIGH)/74
v1lo=(1-LOW)/74
check('spike_log_less_than_93_over_20',s(20,F(93,20))>L*v0hi)
check('ordinary_log_less_than_27_over_25',s(10,F(27,25))>L*v1lo)
kl_upper=F(27,25)+F(357,100)*v0hi
joint_upper=affine(u_coeff,HIGH)+kl_upper
check('unused_plus_entropy_less_than_20_over_3',joint_upper<F(20,3))
e_upper=s(8,F(1))+F(1,factorial(9))/(1-F(1,10))
check('e_less_than_68_over_25',e_upper<F(68,25))
check('e_to_20_over_3_less_than_800',F(68,25)**20<800**3)
check('Lambda_greater_than_800',LAMBDA>800)
new_gap=affine(m_coeff,LOW)-(NEW_TARGET-C)
old_gap=affine(m_coeff,LOW)-(OLD_TARGET-C)
check('new_shallow_budget_exceeded',new_gap>0)
check('old_shallow_budget_exceeded',old_gap>0)
check('counterexample_not_to_complete_query_target',affine(r_coeff,HIGH)<OLD_TARGET)
# The full-survivor Haar law remains a useful member of G.
# This shows the same original family has a good comparison law.
qhaar={d:F(max(counts[d]),74) for d in labels}
rhaar=sum(weights[d]*qhaar[d] for d in labels)-1
uhaar=rhaar-sum(qhaar[d] for d in labels[1:])
mhaar=sum(qhaar[d] for d in mixed)
check('comparison_haar_mixed_is_below_old_budget',mhaar<OLD_TARGET-C)
check('comparison_haar_log_density_less_than_3_over_2',s(12,F(3,2))>F(L,74))
check('comparison_haar_in_G',uhaar+F(3,2)<F(20,3) and F(L,74)<LAMBDA)

out={
 'scope':'Exact finite arithmetic and common-law counterexample; not Lean, not failure of existential G-law target.',
 'primes':P,'period':L,'family':FAMILY,'private_points':PRIVATE,'survivor':U,
 'interval':[str(LOW),str(HIGH)],'all_height_tail_weights':{str(d):str(weights[d]) for d in labels},
 'zero_counts':{str(d):counts[d][0] for d in labels},
 'maximum_query_affine_coefficients':{str(d):list(map(str,q_coeff[d])) for d in labels},
 'complete_query_affine_coefficients':list(map(str,r_coeff)),
 'unused_query_affine_coefficients':list(map(str,u_coeff)),
 'mixed_query_affine_coefficients':list(map(str,m_coeff)),
 'max_density':str(max_density),'KL_upper':str(kl_upper),'unused_plus_KL_upper':str(joint_upper),
 'positive_gap_from_new_shallow_budget':str(new_gap),'positive_gap_from_old_shallow_budget':str(old_gap),
 'complete_query_interval':[str(affine(r_coeff,t)) for t in (LOW,HIGH)],
 'comparison_Haar':{'complete':str(rhaar),'unused':str(uhaar),'mixed':str(mhaar)},
 'checks':checks,'check_count':len(checks)
}
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'unused_plus_KL_upper':str(joint_upper),'new_mixed_gap':str(new_gap),'interval_complete_R':out['complete_query_interval'],'comparison_Haar':out['comparison_Haar']}))
