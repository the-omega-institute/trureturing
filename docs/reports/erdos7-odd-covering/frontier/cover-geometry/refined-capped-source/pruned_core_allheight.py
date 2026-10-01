#!/usr/bin/env python3
"""Exact arithmetic for one common-core source with arbitrary ternary heights.

The conditional theorem constrains only the selected shallow mixed labels.
All infinite exponent and remaining-label tails are retained analytically.
No optimization package, actual-family universality, or Lean claim is made.
"""
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from pathlib import Path
import argparse,heapq,importlib.util,json

P=(5,7,11,13,17,19,23)
W=(F(1,3),F(1,3),F(1,9),F(1,9),F(1,9))
CHECKS=0

def need(ok,msg):
    global CHECKS
    CHECKS+=1
    if not ok:
        raise ValueError(msg)

def load(name,path):
    need(path.is_file(),'required library absent: '+str(path))
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def smooth_numbers(limit):
    queue=[1];seen={1};out=[]
    while queue:
        n=heapq.heappop(queue)
        if n>limit:
            break
        out.append(n)
        for q in P:
            child=n*q
            if child not in seen:
                seen.add(child);heapq.heappush(queue,child)
    return out

def support(n):
    return tuple(i for i,q in enumerate(P) if n%q==0)

def calculate(config,hinge,helpers):
    need(config['schema']=='common-core-arbitrary-ternary-height-v1','certificate schema')
    need(tuple(config['primes'])==P,'fixed nonternary prime window')
    need(tuple(map(F,config['weights']))==W,'one fixed full probability source')
    need(config['enumeration_cutoff']==5000,'fixed exact sorting window')
    need(config['numeric_prefix_cutoff']==437,'fixed numerical-prefix comparison')
    need(config['outside_prime_cutoff']==3000 and config['tail_ell']==7,'fixed complete tail contract')
    C=tuple(F(q-1,q-2) for q in P)
    b=tuple(F(1,q-2) for q in P)
    t=tuple(c/q for c,q in zip(C,P))
    need(all(0<x<1 for x in t),'valid maximum Bernoulli parameters')
    RB=prod(1-x for x in t[1:])
    RA=(1-t[0])*(RB+sum(t[i]*prod(1-t[j] for j in range(1,7) if j!=i) for i in range(1,7)))
    # Reference mixed core: one 3q class per q, and one phase-two pq class.
    core=[]
    for i,q in enumerate(P):
        root=1 if i==0 else 2
        residue=2+q*(((root-2)*pow(q,-1,3))%3)
        core.append((3*q,residue))
    core.extend((p*q,2) for p,q in combinations(P,2))
    need(len(core)==28 and len({m for m,a in core})==28,'distinct mixed core labels')
    direct=[]
    for leaf in (4,7,2,5,8):
        mass=F(0)
        for bits in product((0,1),repeat=7):
            probability=prod(t[i] if bits[i] else 1-t[i] for i in range(7))
            survives=True
            for modulus,residue in core:
                if modulus%3==0 and leaf%3!=residue%3:
                    continue
                if all(bits[i] for i in support(modulus)):
                    survives=False;break
            expected=(not bits[0] and sum(bits[1:])<=1) if leaf in (4,7) else not any(bits[1:])
            need(survives==expected,'actual core event equals the Bernoulli description')
            if survives:
                mass+=probability
        direct.append(mass)
    need(direct==[RA,RA,RB,RB,RB],'closed core mass and independent event enumeration')
    M=sum(w*x for w,x in zip(W,direct))
    need(M==F(33324292966457,52178633632125),'exact common core mass lower bound')
    r=max(sum(W[:2]),sum(W[2:]));v=max(W)
    Qmean=prod(1+x for x in b)
    high=v*Qmean/2
    need(high==F(2048,5355),'all ternary heights at least three included')
    alpha_core=M-high
    total_low=sum(b)+2*(Qmean-1-sum(b))
    need(total_low>0,'complete low mixed inventory cap')
    # All omitted numerical labels have cap <= product(C)/5000.
    integers=smooth_numbers(config['enumeration_cutoff'])
    items=[]
    for n in integers:
        if n==1:
            continue
        s=support(n);cap=F(prod(C[i] for i in s),n)
        for a,factor in ((0,F(1)),(1,r),(2,v)):
            if a==0 and len(s)==1:
                continue
            items.append((factor*cap,3**a*n,a,n))
    items.sort(key=lambda row:(-row[0],row[1]))
    chosen=items[:103]
    expected_labels=config['selected_shallow_labels']
    actual_labels=[dict(modulus=m,ternary_height=a,nonternary_cofactor=n,cap=str(cap)) for cap,m,a,n in chosen]
    need(actual_labels==expected_labels,'exact selected 103-label list')
    need(len({row[1] for row in items})==len(items),'all enumerated full numerical labels are distinct')
    unseen=prod(C)/config['enumeration_cutoff']
    need(unseen<chosen[-1][0],'complete omitted sorting tail below the last selected cap')
    need(all(row[0]<=chosen[-1][0] for row in items[103:]),'finite remainder sorted below selected prefix')
    remaining=total_low-sum(row[0] for row in chosen)
    previous_remaining=remaining+chosen[-1][0]
    alpha=alpha_core-remaining
    alpha_previous=alpha_core-previous_remaining
    # Same-law arbitrary-phase query comparison, reusing the full hinge library.
    coefficients=hinge.hinge_coefficients()
    need(tuple(hinge.P)==P and len(coefficients)==27,'complete hinge window')
    H={h:(c+dr*r+dv*v)*(28-h) for h,(c,dr,dv) in enumerate(coefficients,1)}
    H[0]=(1+r+F(3,2)*v)*Qmean
    K0=(1+15*r+216*v)*prod(1+c*helpers.a4(q) for c,q in zip(C,P))
    factor29=1+F(28,27)*helpers.a4(29)
    tau=helpers.cutoff_tail(3000,7)
    gate29,h29=min((H[h]/(28-h),h) for h in range(28))
    gate_tail,h_tail=min(((H[h]+27*K0*factor29*tau)/(28-h),h) for h in range(28))
    need(alpha_previous<gate_tail<alpha,'102-label upper limitation and successful 103-label gate')
    need(alpha_previous>gate29,'the 102-label head separately passes the pure29 gate')
    def continuation(a):
        need(a>0,'positive same-source mass')
        B,h=min((F(j)+H[j]/a,j) for j in range(28))
        mass29=(28-B)/27
        K29=K0*factor29/a
        final=mass29-K29*tau
        return dict(alpha=str(a),alpha_decimal=float(a),hinge_threshold=h,B_upper=str(B),B_decimal=float(B),mass29_lower=str(mass29),mass29_decimal=float(mass29),K29=str(K29),final_lower=str(final),final_decimal=float(final))
    best=continuation(alpha)
    need(F(best['final_lower'])>F(19,1000),'selected-label complete tail reserve')
    whole=continuation(alpha_core)
    need(F(whole['final_lower'])>F(3,5),'all-low-core-contract complete tail reserve')
    # An easier uniform cofactor cutoff gives a larger, 111-label prefix.
    def numeric(N):
        restricted=[row for row in items if row[3]<=N]
        loss=total_low-sum(row[0] for row in restricted)
        return restricted,alpha_core-loss
    numeric437,a437=numeric(437)
    numeric436,a436=numeric(436)
    need(len(numeric437)==111,'uniform numerical-prefix label count')
    need(a436<gate29 and a437>gate_tail,'437 first numerical cutoff in this certificate')
    cutoff=continuation(a437)
    need(F(cutoff['final_lower'])>F(1,100),'uniform-cutoff complete tail reserve')
    # Concrete free slot control: a=2,n=437 lies outside the 103 labels and
    # has an actual phase meeting the common core survivor.
    free_modulus=9*437
    free_residue=437*((4*pow(437,-1,9))%9)
    need(free_modulus not in {m for cap,m,a,n in chosen},'displayed released low label is not constrained')
    need(free_residue%9==4 and free_residue%437==0,'released low label has one common CRT phase')
    control_period=prod(P)
    control_witness=control_period*((4*pow(control_period,-1,9))%9)
    need(control_witness%9==4 and all(control_witness%q==0 for q in P),'one common CRT witness with all nonternary roots zero')
    need(control_witness%free_modulus==free_residue,'released original contains the same witness')
    for d,a in core:
        need(control_witness%d!=a,'the same witness avoids every mixed core original')
    exact=dict(core_mass=str(M),high_ternary_debit=str(high),post_high_mass=str(alpha_core),total_low_mixed_cap=str(total_low),selected_low_remainder=str(remaining),selected_alpha=str(alpha),previous_alpha=str(alpha_previous),pure29_mass_gate=str(gate29),tail3000_mass_gate=str(gate_tail),selected_final_lower=best['final_lower'],cutoff437_alpha=str(a437),cutoff437_final_lower=cutoff['final_lower'],cutoff436_alpha=str(a436))
    need(exact==config['expected'],'fixed exact certificate results')
    return dict(schema='common-core-arbitrary-ternary-height-result-v1',status='PASS',checks=CHECKS,scope='Conditional noncoverage under one common-core null condition on 103 selected shallow mixed numerical labels (or 111 labels at cofactor cutoff437). All other old phases and heights, pure-q originals, arbitrary29 originals and the complete outside-prime tail above3000 are unrestricted. Minimality is only for the fixed source, displayed individual caps and inherited hinge/quartic-tail certificate. No unrestricted Erdos7, optimal-source, or Lean claim.',primes=list(P),weights=list(map(str,W)),core_originals=[dict(modulus=m,residue=a) for m,a in core],core_leaf_bounds=list(map(str,direct)),exact=exact,core_mass_decimal=float(M),high_ternary_debit_decimal=float(high),complete_query_mean=str(H[0]),raw_fourth=str(K0),pure29_fourth_factor=str(factor29),complete_tail3000=str(tau),all_hinges=[dict(h=h,H=str(H[h])) for h in range(28)],selected_prefix=best,selected_label_count=103,selected_shallow_labels=actual_labels,sorted_prefix_proof=dict(enumerated_cofactor_cutoff=5000,nonunit_cofactor_count=len(integers)-1,enumerated_mixed_label_count=len(items),last_selected_cap=str(chosen[-1][0]),all_unenumerated_cap_upper=str(unseen),largest_102_certificate_value=str(alpha_previous),fixed_method_mass_requirement=str(gate_tail)),numeric437_prefix=cutoff,numeric437_label_count=111,numeric436_certificate_value=str(a436),all_low_core_contract=whole,released_low_label=dict(modulus=free_modulus,residue=free_residue,common_witness=control_witness,common_period=9*control_period,pure_q_inventory='empty for this scope control only',meaning='The released original meets the common core survivor for this one actual pure inventory; no pointwise claim is made for arbitrary pure inventories.'))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).parent
    ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name(Path(__file__).stem+'_certificate.json'))
    ap.add_argument('--hinge-library',type=Path,default=here/'clipped_common_source_obstruction.py')
    ap.add_argument('--continuation-library',type=Path,default=here/'local_ternary_height_lift.py')
    ap.add_argument('--write-result',type=Path)
    args=ap.parse_args()
    hinge=load('e7_existing_common_hinge',args.hinge_library)
    helpers=load('e7_existing_allheight_tail',args.continuation_library)
    result=calculate(json.loads(args.certificate.read_text()),hinge,helpers)
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:
        need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained result equals exact replay')
    print(json.dumps(dict(status=result['status'],checks=result['checks'],selected_labels=103,selected_alpha=result['selected_prefix']['alpha_decimal'],B29=result['selected_prefix']['B_decimal'],final3000=result['selected_prefix']['final_decimal'],numeric437_final=result['numeric437_prefix']['final_decimal']),indent=2))

if __name__=='__main__':
    main()
