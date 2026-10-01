"""Exact controls for two restricted heads and restricted private coordinates."""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from math import factorial
from pathlib import Path
from random import Random
from hashlib import sha256
import json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--paired',required=True)
ap.add_argument('--endpoint',required=True)
args=ap.parse_args()
checks=0

def need(v,msg):
    global checks
    checks+=1
    if not v: raise ValueError(msg)

def root_lower(x,k,den=10**15):
    lo,hi=0,den
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k*x.denominator<=x.numerator*den**k: lo=mid
        else: hi=mid
    low=F(lo,den)
    need(low**k<=x<=F(hi,den)**k,'Certified root bracket')
    return low

def psi_upper(s,p):
    if s==0: return F(0)
    if p==0: return s
    if s<1: return s*(1-p)
    k=s.numerator//s.denominator
    rho=s-k
    if p>=rho**k:
        return k*(1-root_lower(p,k))
    return s-(k+1)*root_lower(rho*p,k+1)

def group_bound(headmass,othermass,G,cap,budgets):
    M=headmass*othermass*G
    if not M: return F(0)
    p=prod(max(F(0),1-v) for v in budgets)
    return min(M,othermass*G*cap*psi_upper(headmass/cap,p))

rng=Random(790579)
finite_cases=[]
zero_cases=0
for trial in range(72):
    sizes=[3,4,4,4,4]
    good=[{j for j in range(n) if rng.randrange(5)>0} for n in sizes]
    if trial%13==0: good[trial%5]=set()
    g=[F(len(s),n) for s,n in zip(good,sizes)]
    W5,W7=g[:2]
    G=prod(g[2:])
    M=W5*W7*G
    X=[[{z for z in range(4) if rng.randrange(7)<2} for i in range(3)] for q in range(3)]
    Y=[[{z for z in range(4) if rng.randrange(7)<2} for j in range(4)] for q in range(3)]
    u=v=actual=F(0)
    for state in product(*(range(n) for n in sizes)):
        if not all(state[k] in good[k] for k in range(5)): continue
        hitx=any(state[q+2] in X[q][state[0]] for q in range(3))
        hity=any(state[q+2] in Y[q][state[1]] for q in range(3))
        weight=F(1,prod(sizes))
        u+=weight*hitx
        v+=weight*hity
        actual+=weight*(hitx or hity)
    if not M:
        need(u==v==actual==0,'Zero carrier handled before division')
        zero_cases+=1
        continue
    w=[F(int(i in good[0]),3) for i in range(3)]
    z=[F(int(j in good[1]),4) for j in range(4)]
    x=[[F(len(X[q][i]&good[q+2]),len(good[q+2])) for i in range(3)] for q in range(3)]
    y=[[F(len(Y[q][j]&good[q+2]),len(good[q+2])) for j in range(4)] for q in range(3)]
    V5=[sum((F(len(a),4) for a in X[q]),F(0))/g[q+2] for q in range(3)]
    V7=[sum((F(len(a),4) for a in Y[q]),F(0))/g[q+2] for q in range(3)]
    need(all(sum(x[q])<=V5[q] and sum(y[q])<=V7[q] for q in range(3)),'Conditioned raw budgets require private survival denominator')
    eu=G*W7*sum((w[i]*(1-prod(1-x[q][i] for q in range(3))) for i in range(3)),F(0))
    ev=G*W5*sum((z[j]*(1-prod(1-y[q][j] for q in range(3))) for j in range(4)),F(0))
    need(u==eu and v==ev,'Correct two-head group normalizations')
    correction=G*sum((sum((w[i]*x[q][i] for i in range(3)),F(0))*sum((z[j]*y[q][j] for j in range(4)),F(0)) for q in range(3)),F(0))
    C=G*sum((min(W5,V5[q]/3)*min(W7,V7[q]/4) for q in range(3)),F(0))
    need(actual<=u+v-u*v/M+correction,'Exact common-source product defect bound')
    need(correction<=C,'Head-capped raw budget correction')
    U=group_bound(W5,W7,G,F(1,3),V5)
    V=group_bound(W7,W5,G,F(1,4),V7)
    need(u<=U<=M and v<=V<=M,'General one-axis carrier-clipped upper bounds')
    joint=min(M,U+V,U+V-U*V/M+C)
    need(actual<=joint,'Monotone endpoint substitution after clipping')
    finite_cases.append({'carrier':str(M),'actual':str(actual),'certified_joint_upper':str(joint),'private_G':str(G)})

# Explicit wrong-normalization example: two half-heads, a half-private survivor.
wrong_actual=F(1,16)
wrong_uncorrected_budget_bound=F(1,32)
correct_budget_bound=F(1,16)
count=0
for i,j,z in product(range(2),range(2),range(4)):
    if i==0 and j==0 and z in (2,3) and z==2: count+=1
need(F(count,16)==wrong_actual>wrong_uncorrected_budget_bound,'Omitting division by g_q creates false upper bound')
need(correct_budget_bound==wrong_actual,'Normalized budget repairs explicit example')

# Independent exponent enumeration checks the nonnegative free remainder identity.
fee_examples=[]
for trial in range(12):
    ps=[5,7,11,13]
    c={p:F((p-1)*p**2,(p-2)*p**2+1) for p in ps}
    b={p:c[p]*(F(1,p)+F(1,p**2)) for p in ps}
    gg={p:F(rng.randrange(1,11),10) for p in ps}
    pp=[11,13]
    B0=prod(gg[p] for p in pp)
    B1=sum((b[p]*prod(gg[q] for q in pp if q!=p) for p in pp),F(0))
    B2=prod(gg[p]+b[p] for p in pp)-B0-B1
    formula=(gg[5]+b[5])*(gg[7]+b[7])*B2+((b[5]-c[5]/5)*gg[7]+(b[7]-c[7]/7)*gg[5]+b[5]*b[7])*B1+b[5]*b[7]*B0
    direct=F(0)
    for es in product(range(3),repeat=4):
        support=[p for p,e in zip(ps,es) if e]
        if len(support)<2: continue
        grouped=(len(support)==2 and ((es[0]==1 and es[1]==0) or (es[1]==1 and es[0]==0)))
        if grouped: continue
        direct+=prod(c[p]/p**e if e else gg[p] for p,e in zip(ps,es))
    need(formula==direct>=0,'Direct exponent payment equals nonnegative remainder polynomial')
    fee_examples.append(str(formula))

raw=Path(args.input).read_bytes()
data=json.loads(raw)
primes=data['primes']
h=dict(zip(primes,data['heights']))
assignment=dict(data['selected_witness'])
for d in (77,91,119,133): assignment[d]=1
starroot={p:next(t for q,e,t in data['star_roots'] if q==p) for p in primes}
need(all(t==starroot[q] for q,e,t in data['star_roots']),'Fixture complete stars use one root per prime')

def arithmetic_root(r,all_heights):
    p,s=5,7
    private=[q for q in primes if q not in (p,s)]
    c={q:F(q-1,q-2) if all_heights else F((q-1)*q**h[q],(q-2)*q**h[q]+1) for q in primes}
    b={q:c[q]-1 for q in primes}
    gg={q:1-b[q] if starroot[q]==r else F(1) for q in primes}
    G=prod(gg[q] for q in private)
    Wp,Ws=gg[p],gg[s]
    M=Wp*Ws*G
    ap,ass=c[p]/p,c[s]/s
    rawp={q:(b[q]+c[q]*sum((F(1,q**e) for e in range(1,h[q]+1) if assignment.get(p*q**e)==r),F(0)))/gg[q] for q in private}
    raws={q:(b[q]+c[q]*sum((F(1,q**e) for e in range(1,h[q]+1) if assignment.get(s*q**e)==r),F(0)))/gg[q] for q in private}
    Up=group_bound(Wp,Ws,G,ap,list(rawp.values()))
    Us=group_bound(Ws,Wp,G,ass,list(raws.values()))
    C=G*sum((min(Wp,ap*rawp[q])*min(Ws,ass*raws[q]) for q in private),F(0))
    J=min(M,Up+Us,Up+Us-Up*Us/M+C)
    B0=G
    B1=sum((b[q]*prod(gg[k] for k in private if k!=q) for q in private),F(0))
    B2=prod(gg[q]+b[q] for q in private)-B0-B1
    frem=(Wp+b[p])*(Ws+b[s])*B2+((b[p]-ap)*Ws+(b[s]-ass)*Wp+b[p]*b[s])*B1+b[p]*b[s]*B0
    selected=F(0)
    selected_n=0
    grouped_n=0
    for d,t in assignment.items():
        if t!=r: continue
        es={}
        rem=d
        for q in primes:
            while rem%q==0:
                es[q]=es.get(q,0)+1
                rem//=q
        need(rem==1,'Selected label retains its actual prime factors')
        grouped=len(es)==2 and ((es.get(p)==1 and s not in es) or (es.get(s)==1 and p not in es))
        if grouped:
            grouped_n+=1
            continue
        selected_n+=1
        selected+=prod(c[q]/q**es[q] if q in es else gg[q] for q in primes)
    delta=M-frem-selected-J
    independent5=Ws*G*ap*sum(rawp.values())
    independent7=Wp*G*ass*sum(raws.values())
    baseline=M-frem-selected-independent5-independent7
    if not all_heights:
        old={1:F(-146353069717740910766193401918766135478840186351,2333849532135992506177716822537480405847422046272),2:F(-192899355550520959014862331059495339459686383741,65347786899807790172976071031049451363727817295616)}
        need(baseline==old[r],'Direct same-source fees reproduce the existing ungrouped root endpoint exactly')
    need(frem>=0 and selected>=0 and 0<=J<=M,'General arithmetic certificate components')
    return {'root':r,'all_nonternary_heights':all_heights,'W5':str(Wp),'W7':str(Ws),'private_G':str(G),'carrier_M':str(M),'raw5':{str(q):str(v) for q,v in rawp.items()},'raw7':{str(q):str(v) for q,v in raws.items()},'upper5':str(Up),'upper7':str(Us),'same_q_correction':str(C),'joint_upper':str(J),'free_remainder':str(frem),'selected_remainder':str(selected),'selected_remainder_labels':selected_n,'selected_grouped_labels':grouped_n,'independent_group5':str(independent5),'independent_group7':str(independent7),'independent_survivor_endpoint':str(baseline),'survivor_lower':str(delta),'nonnegative_survivor_lower':str(max(F(0),delta)),'full_Haar_root_lower':str(max(F(0),delta)/(3*prod(c.values()))),'decimals':{k:float(v) for k,v in [('carrier',M),('joint_upper',J),('survivor_lower',delta),('old_independent_endpoint',baseline)]}}

root_examples=[arithmetic_root(r,ah) for ah in (False,True) for r in (1,2)]
need(F(root_examples[0]['survivor_lower'])>F(1,1500),'General formula retains finite root1 positive certificate')
need(F(root_examples[2]['survivor_lower'])>F(1,2500),'General formula retains all-height root1 positive certificate')

def full_inventory_no5_star():
    private=[q for q in primes if q not in (5,7)]
    c={q:F(q-1,q-2) for q in primes}
    b={q:c[q]-1 for q in primes}
    gg={q:F(1) if q==5 else 1-b[q] for q in primes}
    G=prod(gg[q] for q in private)
    W5,W7=gg[5],gg[7]
    M=W5*W7*G
    a5,a7=c[5]/5,c[7]/7
    budgets={q:2*b[q]/gg[q] for q in private}
    U5=group_bound(W5,W7,G,a5,list(budgets.values()))
    U7=group_bound(W7,W5,G,a7,list(budgets.values()))
    C=G*sum((min(W5,a5*budgets[q])*min(W7,a7*budgets[q]) for q in private),F(0))
    J=min(M,U5+U7,U5+U7-U5*U7/M+C)
    B1=sum((b[q]*prod(gg[k] for k in private if k!=q) for q in private),F(0))
    B2=prod(gg[q]+b[q] for q in private)-G-B1
    frem=(W5+b[5])*(W7+b[7])*B2+((b[5]-a5)*W7+(b[7]-a7)*W5+b[5]*b[7])*B1+b[5]*b[7]*G
    delta=M-2*frem-J
    return {'contract':'Every mixed cofactor d and3d charged over the complete convergent nonternary exponent inventory. No5 stars on chosen root; all other prime star budgets enlarged to bq there. This is a sufficient-comparison calculation, not an actual infinite family.','carrier':str(M),'free_remainder':str(frem),'both_free_and_selected_remainder':str(2*frem),'raw_budgets':{str(q):str(v) for q,v in budgets.items()},'upper5':str(U5),'upper7':str(U7),'correction':str(C),'joint_upper':str(J),'comparison_lower':str(delta),'decimals':{'carrier':float(M),'remaining_charge':float(2*frem),'joint_upper':float(J),'comparison_lower':float(delta)}}
complete_inventory=full_inventory_no5_star()
root2_Haar=F(root_examples[3]['full_Haar_root_lower'])
need(root2_Haar>F(1,550),'Specified1947-palette all-height root has Haar density above1/550')
tail_B=100000
tail_ell=10
tail_c=F(2*tail_ell**2+1,2*tail_ell**2-1)
moment=prod(F(p*(p+1),(p-1)**2) for p in [3]+primes)
poly=sum((F(factorial(7),factorial(7-j)*tail_ell**j) for j in range(8)),F(0))
tail_loss=moment*tail_c**7/tail_B*F(tail_B,tail_B-3)**2*poly
tail_final=F(1,550)-tail_loss
need(tail_B>=286 and tail_ell>=4 and 3**tail_ell<=tail_B,'Inherited tail analytic parameter guards')
need(tail_loss<F(7,8000),'Existing large-prime tail loss threshold')
need(tail_final>F(83,88000),'Positive supported tail mass from actual Haar seed')
paired_raw=Path(args.paired).read_bytes();paired=json.loads(paired_raw)
endpoint_raw=Path(args.endpoint).read_bytes();endpoint=json.loads(endpoint_raw)
need(paired['endpoint_sha256']==sha256(endpoint_raw).hexdigest(),'Paired certificate bound to declared endpoint')
need(endpoint['input_sha256']==sha256(raw).hexdigest(),'Both roots use the same original numerical input')
need(endpoint['flipped_cofactors']==[77,91,119,133],'Both root palettes use the same four label moves')
paired_delta=F(paired['all_nonternary_heights']['survivor_lower'])
second_delta=F(root_examples[3]['survivor_lower'])
head_density_cap=3*prod(F(p-1,p-2) for p in primes)
need(paired_delta>F(1,500) and second_delta>F(7,500) and head_density_cap<8,'Both declared disjoint roots have the required actual-source margins')
combined_head=(paired_delta+second_delta)/head_density_cap
need(combined_head>F(1,500),'Disjoint root contributions add under common Haar density bound')
combined_tail=F(1,500)-tail_loss
need(combined_tail>F(9,8000),'Joint-root supported tail mass')
combined_roots={'contract':'Both specified191/1947 palettes and both star-interface conditions hold on the two distinct pure3-avoiding roots; all head-only v3<=1, arbitrary finite nonternary heights, fixed3,5,7 private-prime enlargement. Actual common input and globally fixed phases; disjoint Haar root contributions may be added. The root2-only theorem does not receive this stronger constant.','paired_sha256':sha256(paired_raw).hexdigest(),'endpoint_sha256':sha256(endpoint_raw).hexdigest(),'root1_mass_lower':str(paired_delta),'root2_mass_lower':str(second_delta),'head_Haar_lower':str(combined_head),'head_Haar_threshold':'1/500','tail_B':tail_B,'tail_loss_upper':str(tail_loss),'final_supported_mass_lower':str(combined_tail),'final_supported_mass_threshold':'9/8000'}
root2_tail={'contract':'Specified1947 root palette, no5 stars on chosen pure3-avoiding root; arbitrary other star phases and finite nonternary heights on fixed12-prime head. Every outside support prime exceeds100000; tail-touching powers unrestricted. Uses Chapter33 SH11--SH13, Haar seed density1. Final supported mass is not a full-family natural-density claim.','head_Haar_lower':str(root2_Haar),'head_Haar_threshold':'1/550','B':tail_B,'ell':tail_ell,'moment_upper':str(moment),'tail_loss_upper':str(tail_loss),'final_supported_mass_lower':str(tail_final),'final_supported_mass_threshold':'83/88000'}
result={'contract':'Two restricted head carriers and private star complements on one fixed actual product source. No unrestricted positivity claim; both retained roots use their own actual or certified enlarged blocker sets and the same global label assignment.','checks':checks,'input_sha256':sha256(raw).hexdigest(),'finite_product_cases':72,'zero_carrier_cases':zero_cases,'positive_carrier_cases':len(finite_cases),'finite_cases':finite_cases,'free_fee_identity_cases':len(fee_examples),'wrong_normalization':{'head5_survival':'1/2','head7_survival':'1/2','private_survival':'1/2','private_original_mass':'1/4','conditioned_private_mass':'1/2','actual_joint_mass':str(wrong_actual),'false_upper_if_unscaled':str(wrong_uncorrected_budget_bound),'correct_upper':str(correct_budget_bound)},'four_flip_roots':root_examples,'full_inventory_no5_star':complete_inventory,'specified1947_root_tail':root2_tail,'combined_declared_roots':combined_roots}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'finite_cases':len(finite_cases),'zero_carriers':zero_cases,'root_examples':[{'root':x['root'],'all_heights':x['all_nonternary_heights'],**x['decimals']} for x in root_examples]},sort_keys=True))
print(json.dumps(complete_inventory['decimals'],sort_keys=True))
