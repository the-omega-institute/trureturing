"""Exact upper certificates for the two-axis private-prime union relaxation."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from math import prod
from itertools import product
from random import Random
from math import factorial
import json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--endpoint',required=True)
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
raw=Path(args.endpoint).read_bytes()
ep=json.loads(raw)
input_raw=Path(args.input).read_bytes()
data=json.loads(input_raw)
checks=0
def need(v,msg):
    global checks
    checks+=1
    if not v: raise ValueError(msg)

def root_bracket(x,k,d=10**18):
    lo,hi=0,d
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k*x.denominator<=x.numerator*d**k: lo=mid
        else: hi=mid
    a,b=F(lo,d),F(hi,d)
    need(a**k<=x<=b**k,'Integer-power bracket')
    return a,b

T5={int(q):F(v) for q,v in ep['group5']['T'].items()}
T7={int(q):F(v) for q,v in ep['additional_disjoint_group7']['T'].items()}
a5=F(ep['group5']['prefactor'])
s5=F(ep['group5']['S'])
W=a5*s5
a7=1/F(ep['additional_disjoint_group7']['S'])
need(ep['input_sha256']==sha256(input_raw).hexdigest(),'Endpoint bound to current inventory bytes')
need(set(ep['flipped_cofactors'])=={77,91,119,133},'Declared four-flip palette')
assignment=dict(data['selected_witness'])
for d in ep['flipped_cofactors']: assignment[d]=1
primes=data['primes']
heights=dict(zip(primes,data['heights']))
cf={q:F((q-1)*q**heights[q],(q-2)*q**heights[q]+1) for q in primes}
need(a5==cf[5]/5 and a7==cf[7]/7 and W==2-cf[5],'Current finite source caps')
for q in T5:
    need(T5[q]==cf[q]-1+cf[q]*sum((F(1,q**e) for e in range(1,heights[q]+1) if assignment.get(5*q**e)==1),F(0)),'Reconstructed raw5 budget')
for q in T7:
    need(T7[q]==cf[q]-1+cf[q]*sum((F(1,q**e) for e in range(1,heights[q]+1) if assignment.get(7*q**e)==1),F(0)),'Reconstructed raw7 budget')
need(W*a7==F(ep['additional_disjoint_group7']['prefactor']),'One common outside5 carrier')
qs=sorted(T7)
need(qs==sorted(q for q in T5 if q>7),'Same private prime coordinates')
need(all(T5[q]+T7[q]<1 for q in qs),'No clipping needed on this profile')
px=prod(1-T5[q] for q in qs)
py=prod(1-T7[q] for q in qs)
need(px>=(s5-2)**2,'Private5 group stays in two-full-row branch')
need(py>=(1/a7-5)**5,'Group7 stays in five-full-row branch')
xl,xh=root_bracket(px,2)
yl,yh=root_bracket(py,5)
Ux=2*a5*(1-xl)
Uy=5*W*a7*(1-yl)
need(0<=Ux<=W and 0<=Uy<=W,'Upper values in carrier range')
correction=a5*a7*sum((T5[q]*T7[q] for q in qs),F(0))
private_upper=Ux+Uy-Ux*Uy/W+correction
D57=a5*T5[7]
new_upper=D57+private_upper
old5=F(ep['group5']['union_formula_upper'])
old7=F(ep['additional_disjoint_group7']['union_formula_upper'])
old_upper=old5+old7
Elo=F(ep['both_group_root1_lower'])
# Compare to the exact old radicals conservatively using LOWER bounds on old union formulas.
old_union_lower=F(ep['group5']['union_formula_lower'])+F(ep['additional_disjoint_group7']['union_formula_lower'])
certified_new_lower=Elo+old_union_lower-new_upper
remaining=W-F(ep['old_endpoints_by_root']['1'])-F(ep['group5']['old_charge'])-F(ep['additional_disjoint_group7']['old_charge'])
direct_lower=W-remaining-new_upper
need(remaining>=0 and direct_lower>=certified_new_lower>F(1,1500),'Positive direct and inherited lower certificates')
need(3*prod(cf.values())<8 and direct_lower/(3*prod(cf.values()))>F(1,12000),'Finite profile density certificate')

def complete_height_certificate(cc):
    bb={q:cc[q]-1 for q in primes}
    ww=1-bb[5]
    aa5,aa7=cc[5]/5,cc[7]/7
    tt5={q:bb[q]+cc[q]*sum((F(1,q**e) for e in range(1,heights[q]+1) if assignment.get(5*q**e)==1),F(0)) for q in primes if q!=5}
    tt7={q:bb[q]+cc[q]*sum((F(1,q**e) for e in range(1,heights[q]+1) if assignment.get(7*q**e)==1),F(0)) for q in qs}
    need(all(0<=t<1 for t in tt5.values()) and all(0<=t<1 for t in tt7.values()),'Raw budgets lie in the admitted unclipped range')
    pp5=prod(1-tt5[q] for q in qs)
    pp7=prod(1-tt7[q] for q in qs)
    need(pp5>=(ww/aa5-2)**2 and pp7>=(1/aa7-5)**5,'Complete-height radical branches')
    rr5=root_bracket(pp5,2)
    rr7=root_bracket(pp7,5)
    ua=2*aa5*(1-rr5[0])
    ub=5*ww*aa7*(1-rr7[0])
    need(0<=ua<=ww and 0<=ub<=ww,'Complete-height monotone upper range')
    corr=aa5*aa7*sum((tt5[q]*tt7[q] for q in qs),F(0))
    upper=aa5*tt5[7]+ua+ub-ua*ub/ww+corr
    outside=[q for q in primes if q!=5]
    product_outside=prod(1+bb[q] for q in outside)
    free_charge=ww*(product_outside-1-sum(bb[q] for q in outside))+bb[5]*(product_outside-1)
    selected_charge=F(0)
    remaining_selected=F(0)
    selected_count=0
    remaining_selected_count=0
    group5_labels={5*q**e for q in primes if q!=5 for e in range(1,heights[q]+1) if assignment.get(5*q**e)==1}
    group7_labels={7*q**e for q in qs for e in range(1,heights[q]+1) if assignment.get(7*q**e)==1}
    need(len(group5_labels)==28 and len(group7_labels)==4 and not group5_labels.intersection(group7_labels),'Disjoint28/4 selected group inventories')
    for d,t in assignment.items():
        if t!=1: continue
        selected_count+=1
        weight=F(1)
        rem=d
        for q in primes:
            if rem%q==0:
                e=0
                while rem%q==0: rem//=q; e+=1
                weight*=cc[q]/q**e
        need(rem==1,'Actual palette factors on declared axes')
        charge=weight*(ww if d%5 else 1)
        selected_charge+=charge
        if d not in group5_labels and d not in group7_labels:
            remaining_selected+=charge
            remaining_selected_count+=1
    need(selected_count==191,'Keep the exact indexed191 palette')
    dg5=aa5*sum(tt5.values())
    dg7=ww*aa7*sum(tt7.values())
    remain=free_charge+selected_charge-dg5-dg7
    sb=sum(bb[q] for q in qs)
    e2=prod(1+bb[q] for q in qs)-1-sb
    positive_free=(1+bb[7])*e2+(bb[7]-ww*aa7)*sb+(bb[5]-aa5)*(bb[7]+sb)
    need(bb[7]-ww*aa7>=0 and bb[5]-aa5>=0 and remaining_selected_count==159,'Nonnegative remaining fee coefficients and159 mixed originals')
    need(remain==positive_free+remaining_selected,'Direct nonnegative remaining allowance decomposition')
    lower=ww-remain-upper
    need(remain>=0,'Direct remaining complete geometric allowance')
    return {'W':str(ww),'T5':{str(q):str(v) for q,v in tt5.items()},'T7':{str(q):str(v) for q,v in tt7.items()},'private5_residual':str(pp5),'private7_residual':str(pp7),'private5_root_bracket':[str(v) for v in rr5],'private7_root_bracket':[str(v) for v in rr7],'private5_upper':str(ua),'group7_upper':str(ub),'same_prime_correction':str(corr),'free_charge':str(free_charge),'selected_charge':str(selected_charge),'independent_group5':str(dg5),'independent_group7':str(dg7),'remaining_charge':str(remain),'remaining_free_positive_polynomial':str(positive_free),'remaining_selected_count':remaining_selected_count,'remaining_selected_positive_sum':str(remaining_selected),'joint_upper':str(upper),'survivor_lower':str(lower),'density_cap':str(3*prod(cc.values())),'decimals':{'joint_upper':float(upper),'remaining_charge':float(remain),'survivor_lower':float(lower)}}

reconstructed=complete_height_certificate(cf)
need(F(reconstructed['remaining_charge'])==remaining and F(reconstructed['survivor_lower'])==direct_lower,'Independent free-polynomial plus selected191 reconstruction')
cinf={q:F(q-1,q-2) for q in primes}
all_height=complete_height_certificate(cinf)
need(F(all_height['survivor_lower'])>F(1,2500),'All finite nonternary heights retain a strict positive margin')
need(F(all_height['density_cap'])<8 and F(all_height['survivor_lower'])/F(all_height['density_cap'])>F(1,20000),'All-height head Haar density certificate')

# Reuse Chapter33 SH11--SH13 after converting to a Haar seed; fixed3,5,7 transport only.
tail_B=10**7
tail_ell=14
tail_c=F(2*tail_ell**2+1,2*tail_ell**2-1)
moment=prod(F(p*(p+1),(p-1)**2) for p in [3]+primes)
polynomial=sum((F(factorial(7),factorial(7-j)*tail_ell**j) for j in range(8)),F(0))
tau=tail_c**7/F(tail_B)*F(tail_B,tail_B-3)**2*polynomial
tail_loss=moment*tau
tail_final=F(1,20000)-tail_loss
need(tail_B>=286 and tail_ell>=4 and 3**tail_ell<=tail_B,'Inherited analytic tail parameter guards')
need(moment==F(17517439415203,525533184000) and polynomial==F(1711167,941192),'Exact moment and tail polynomial')
need(F(all_height['survivor_lower'])/F(all_height['density_cap'])>F(1,20000),'Actual head supplies required Haar seed')
need(tail_loss<F(1,120000) and tail_final>F(1,24000),'Positive final supported tail mass')
tail={'B':tail_B,'ell':tail_ell,'c_ell':str(tail_c),'M2_upper':str(moment),'polynomial':str(polynomial),'tau7':str(tau),'seed_Haar_mass_lower':'1/20000','seed_density_upper':'1','tail_loss_upper':str(tail_loss),'final_supported_mass_lower':str(tail_final),'final_supported_mass_threshold':'1/24000','contract':'Fixed3,5,7 and componentwise larger distinct private head primes; the indexed191 head-only palette and chosen-root5-star condition remain. All primes outside the designated head exceed10^7. Tail-touching originals may have arbitrary finite exponents. Head-first then increasing tail order; head primes may be larger than tail primes. Uses existing Chapter33 SH11 analytic premise. Final mass is for a supported distorted law, not natural density.'}

# Independent finite product-space enumeration for the union defect inequality.
rng=Random(780057)
for trial in range(48):
    ww=[F(1,5),F(1,7),F(1,11)]
    vv=[F(1,7),F(2,7),F(1,7),F(3,7)]
    wx=sum(ww)
    xx=[[{s for s in range(3) if rng.randrange(2)} for i in ww] for q in range(3)]
    yy=[[{s for s in range(3) if rng.randrange(2)} for j in vv] for q in range(3)]
    ax=sum((ww[i]*(1-prod(1-F(len(xx[q][i]),3) for q in range(3))) for i in range(3)),F(0))
    by=wx*sum((vv[j]*(1-prod(1-F(len(yy[q][j]),3) for q in range(3))) for j in range(4)),F(0))
    exact=F(0)
    for i,j,state in product(range(3),range(4),product(range(3),repeat=3)):
        if any(state[q] in xx[q][i] or state[q] in yy[q][j] for q in range(3)):
            exact+=ww[i]*vv[j]/27
    corr=sum((sum((ww[i]*F(len(xx[q][i]),3) for i in range(3)),F(0))*sum((vv[j]*F(len(yy[q][j]),3) for j in range(4)),F(0)) for q in range(3)),F(0))
    capcorr=max(ww)*max(vv)*sum((sum(F(len(xx[q][i]),3) for i in range(3))*sum(F(len(yy[q][j]),3) for j in range(4)) for q in range(3)),F(0))
    need(exact<=ax+by-ax*by/wx+corr,'Actual finite joint union satisfies defect inequality')
    need(corr<=capcorr,'Raw row budgets safely bound correction')
    au=(ax+wx)/2
    bu=(by+wx)/2
    need(ax+by-ax*by/wx<=au+bu-au*bu/wx,'Upper substitution is monotone')

result={'contract':'Upper-bound relaxation on one common capped-simplex5/7 source; no scalar optimizer is asserted to be an actual p-adic phase realization.','endpoint_sha256':sha256(raw).hexdigest(),'input_sha256':sha256(input_raw).hexdigest(),'checks':checks,'all_nonternary_heights':all_height,'finite_product_controls':48,'private_primes':qs,'W':str(W),'a5':str(a5),'a7':str(a7),'private5_residual_product':str(px),'private7_residual_product':str(py),'private5_root_bracket':[str(xl),str(xh)],'private7_root_bracket':[str(yl),str(yh)],'private5_upper':str(Ux),'group7_upper':str(Uy),'same_prime_correction':str(correction),'D57_safe_charge':str(D57),'private_joint_upper':str(private_upper),'full_two_group_upper':str(new_upper),'old_two_group_upper':str(old_upper),'old_union_lower':str(old_union_lower),'new_survivor_lower':str(certified_new_lower),'direct_remaining_charge':str(remaining),'direct_survivor_lower':str(direct_lower),'survivor_threshold':'1/1500','density_threshold':'1/12000','decimals':{k:float(v) for k,v in [('private5_upper',Ux),('group7_upper',Uy),('same_prime_correction',correction),('D57_safe_charge',D57),('private_joint_upper',private_upper),('new_full_upper',new_upper),('old_full_upper',old_upper),('upper_improvement',old_upper-new_upper),('new_survivor_lower',certified_new_lower),('direct_survivor_lower',direct_lower)]}}
result['large_prime_tail']=tail
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result['decimals'],sort_keys=True))
print(json.dumps({'all_nonternary_heights':all_height['decimals'],'checks':checks},sort_keys=True))
