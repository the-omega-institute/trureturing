"""Bounded root recoloring of the fixed2138 numerical inventory.

Standard-library greedy proposal plus the unchanged canonical inventory
checker. No congruence phases or actual covering realization are inferred.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations
import json
from math import isqrt, prod
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--checker',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--candidate-output',help='Optional explicit path for the complete temporary candidate.')
ap.add_argument('--checker-output',help='Optional explicit path for the canonical checker output.')
args=ap.parse_args()
raw=Path(args.input).read_bytes();data=json.loads(raw);base=dict(data['selected_witness'])
primes=data['primes'];heights=dict(zip(primes,data['heights']))
stars={(q,e):t for q,e,t in data['star_roots']}
checks=0

def need(ok,msg):
    global checks
    checks+=1
    if not ok:raise ValueError(msg)

need(len(base)==len(data['selected_witness'])==2138,'Unchanged distinct numerical inventory')
need(all(stars[q,e]==(1 if q==5 else 2) for q in primes for e in range(1,heights[q]+1)),
     'Complete fixed star-root metadata')
c={q:F((q-1)*q**h,(q-2)*q**h+1) for q,h in heights.items()};b={q:c[q]-1 for q in primes}
B={(q,t):b[q] if t==(1 if q==5 else 2) else F(0) for q in primes for t in (1,2)}
powers={}
for d in base:
    need(d>1,'Positive mixed input')
    n=d;exps={}
    for q in primes:
        e=0
        while n%q==0:n//=q;e+=1
        if e:exps[q]=e
    need(n==1 and len(exps)>=2,'Numerical cofactor factorization')
    powers[d]=exps

def g(t,support):return prod((1-B[q,t] for q in primes if q not in support),start=F(1))
def charge(d,t):return g(t,powers[d])*prod((c[q] for q in powers[d]),start=F(1))/d
A={(d,t):charge(d,t) for d in base for t in (1,2)}
carrier={t:g(t,()) for t in (1,2)}
free={t:prod((1-B[q,t]+b[q] for q in primes),start=F(1))-carrier[t]
      -sum((b[q]*g(t,(q,)) for q in primes),F(0)) for t in (1,2)}

def endpoints(assignment):
    return {t:carrier[t]-free[t]-sum((A[d,t] for d,r in assignment.items() if r==t),F(0)) for t in (1,2)}

def nth_bounds(x,k,denom=10**15):
    # Exact kth-root enclosure, without a floating-point decision.
    goal=x.numerator*denom**k//x.denominator
    lo,hi=0,denom
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**k<=goal:lo=mid
        else:hi=mid
    low,high=F(lo,denom),F(lo+1,denom)
    need(low**k<=x<=high**k,'Exact rational kth-root enclosure')
    return low,high

def group(assignment,p,qs):
    budget={q:b[q]+c[q]*sum((F(1,q**e) for e in range(1,heights[q]+1)
                           if assignment.get(p*q**e)==1),F(0)) for q in qs}
    pref=g(1,[p]+list(qs))*c[p]/p
    # For these groups all excluded coordinates except5 are unblocked.
    # A fixed outside factor can be removed once before the row union.
    need(all(B[q,1]==0 for q in qs),'All private-coordinate blockers are absent on root1')
    need(all(0<=v<1 for v in budget.values()),'Per-coordinate original-label budgets')
    S=p*(1-B[p,1])/c[p];k=S.numerator//S.denominator;rho=S-k
    P=prod((1-v for v in budget.values()),start=F(1))
    old=pref*sum(budget.values(),F(0))
    low,high=nth_bounds(P,k)
    if P>=rho**k:
        lower_union=pref*k*(1-high)
        upper_union=pref*k*(1-low)
        branch='k-full-rows: P>=rho^k'
    else:
        # Safe declared fallback only; no incorrect k-row formula.
        lower_union=upper_union=min(old,pref*S)
        branch='independent-charge/carrier fallback'
    return {'prime':p,'private_primes':qs,'T':{str(q):str(v) for q,v in budget.items()},
            'S':str(S),'k':k,'rho':str(rho),'P':str(P),'root_lower':str(low),'root_upper':str(high),
            'branch':branch,'prefactor':str(pref),'old_charge':str(old),
            'union_formula_lower':str(lower_union),'union_formula_upper':str(upper_union),
            'gain_lower':str(old-upper_union),'gain_upper':str(old-lower_union)}

def corrected(assignment):
    ends=endpoints(assignment);cut=group(assignment,5,[q for q in primes if q!=5])
    return ends,cut,ends[1]+F(cut['gain_lower']),ends[1]+F(cut['gain_upper'])

# First bounded search: squarefree two-prime non5 labels. These moves
# leave all total capacities, CR9, closure, square capacities and Tq
# unchanged. Only their one root-pair occupancy moves between roots.
current=base.copy();counts=Counter()
for d,t in current.items():
    for p,q in combinations(powers[d],2):counts[p,q,t]+=1
rcaps={}
for p,q in combinations(primes,2):
    for t in (1,2):
        yp=int(stars[p,1]==t);yq=int(stars[q,1]==t)
        aa,bb=p-1-yp,q-1-yq
        rcaps[p,q,t]=aa*bb+min(aa,bb)-int(yp==yq==0)
proposals=[d for d,t in current.items() if t==2 and 5 not in powers[d]
           and len(powers[d])==2 and all(e==1 for e in powers[d].values())]
proposals.sort(key=lambda d:(-A[d,1],d))
flips=[];attempts=0
for d in proposals:
    attempts+=1
    p,q=sorted(powers[d])
    if counts[p,q,1]+1>rcaps[p,q,1]:continue
    trial=current.copy();trial[d]=1
    ends,cut,lower,upper=corrected(trial)
    if ends[2]>=0:continue
    current=trial;counts[p,q,1]+=1;counts[p,q,2]-=1;flips.append(d)
    if upper<0:break
ends,cut,lower,upper=corrected(current)
need(upper<0 and ends[2]<0,'The strengthened5-group formula has two strictly negative endpoints')
need(set(current)==set(base) and all(current[d]==base[d] for d in base if d not in flips),
     'Only the displayed root colors changed')
need(cut['T']==group(base,5,[q for q in primes if q!=5])['T'],'The5-group T budgets stayed exactly fixed')

candidate=deepcopy(data)
candidate['selected_witness']=[[d,current[d]] for d,r in data['selected_witness']]
candidate['strict_upper_threshold']='-1/1000000'
candidate['expected_endpoints']=[str(ends[2]),str(ends[1])]
# Invoke the ORIGINAL repository checker, with its complete current
# actual-star pair, root-pair, square, root-square, CR9 and closure checks.
spec=importlib.util.spec_from_file_location('e7_original_inventory_checker',args.checker)
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
verified=checker.check(candidate)
need(verified['capacity_contract']=='actual-star-roots','Complete canonical actual-star constraint contract')
need(verified['endpoints']==candidate['expected_endpoints'],'Canonical exact endpoint agreement')
second=group(current,7,[q for q in primes if q>7])
combined_lower=lower+F(second['gain_lower']);combined_upper=upper+F(second['gain_upper'])
first_labels={5*q**e for q in primes if q!=5 for e in range(1,heights[q]+1)}
second_labels={7*q**e for q in primes if q>7 for e in range(1,heights[q]+1)}
need(first_labels.isdisjoint(second_labels),'Two added group budgets have disjoint numerical cofactor sets')
need(upper<F(-1,500) and ends[2]<F(-1,500),'The full5-group formula stays below minus1/500 at both endpoints')
need(combined_upper<F(-1,1000) and ends[2]<F(-1,1000),'Both exact root-formula group cuts stay below minus1/1000 at both endpoints')
result={
 'contract':'Fixed2138-cofactor numerical/root relaxation with unchanged complete star roots, heights and scalar source. Root recoloring changes no numerical inventory. Negative comparisons do not construct AP phases, a cover, or negative actual survivor mass.',
 'input':args.input,'input_sha256':sha256(raw).hexdigest(),
 'checker':args.checker,'checker_sha256':sha256(Path(args.checker).read_bytes()).hexdigest(),
 'search':'Bounded deterministic greedy among original-root2 squarefree two-prime non5 labels, descending root1 debit; accept only root-pair-legal flips retaining a negative root2 endpoint.',
 'proposal_count':len(proposals),'attempt_count':attempts,'checks':checks,
 'flipped_cofactors':flips,'flipped_original_moduli':[3*d for d in flips],
 'root1_labels_before':sum(t==1 for t in base.values()),'root1_labels_after':sum(t==1 for t in current.values()),
 'old_endpoints_by_root':{str(t):str(v) for t,v in ends.items()},
 'group5':cut,'corrected_root1_lower':str(lower),'corrected_root1_upper':str(upper),
 'corrected_root1_interval_decimal':[float(lower),float(upper)],'root2_decimal':float(ends[2]),
 'canonical_constraint_verdict':'passed: original check(candidate), unchanged actual-star-roots constraint contract',
 'comparison_threshold_note':'Only the old witness output threshold is changed to -1/1000000; all structural capacity/source/closure/CR9 constraints are unchanged.',
 'group5_all_weight_strict_upper':'-1/500',
 'both_groups_all_weight_strict_upper':'-1/1000',
 'canonical_checks':{k:verified[k] for k in ('mixed_labels','star_labels','mixed_divisor_closure_edges','per_label_cr9_checks','pair_constraints','root_pair_constraints','square_constraints','root_square_constraints')},
 'additional_disjoint_group7':second,
 'both_group_root1_lower':str(combined_lower),'both_group_root1_upper':str(combined_upper),
 'both_group_root1_interval_decimal':[float(combined_lower),float(combined_upper)],
 'interpretation':'The original5-group cut alone does not close all root assignments in the existing numerical relaxation. The optional7-group result is an independent additional replacement, never counted twice with the5-group.'
}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
if args.candidate_output:
    Path(args.candidate_output).write_text(json.dumps(candidate,indent=2,sort_keys=True)+'\n')
if args.checker_output:
    Path(args.checker_output).write_text(json.dumps(verified,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('flipped_cofactors','proposal_count','attempt_count','checks','corrected_root1_interval_decimal','root2_decimal','both_group_root1_interval_decimal')},sort_keys=True))
