#!/usr/bin/env python3
"""Exact finite original-AP countercontrol for a uniform actual-fibre lift.
The head constants are literal mathematical input from original_head_exclusions;
the actual private head law and full original labels are independently checked.
No Lean certification or obstruction to every supported lift is asserted.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt
import argparse
import json
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def primes_until(n):
    return [p for p in range(11, n+1, 2)
            if all(p % d for d in range(3, isqrt(p)+1, 2))]


def crt(a, m, b, n):
    require(gcd(m,n)==1, 'coprime CRT')
    return a + m * (((b-a)*pow(m,-1,n)) % n)


def result():
    head = {5:0, 7:0, 25:21, 35:34, 49:48, 175:173, 245:242, 1225:241}
    source = [x for x in range(1225) if all(x%d!=a for d,a in head.items())]
    require(len(source)==736, 'actual common head avoid-set')
    law = {}
    def add(r,c,h,units):
        x = crt(r+5*c,25,r+7*h,49)
        require(x in source, 'actual private head point')
        require(x not in law, 'distinct literal head incidence')
        law[x] = F(units,60)
    for r in (2,3,4):
        for c in range(5):
            add(r,c,c,3)
    add(1,0,0,3)
    for c, endpoints, weights in ((1,(1,2),(3,1)),(2,(2,3),(2,2)),(3,(3,4),(1,3))):
        for h,w in zip(endpoints,weights):
            add(1,c,h,w)
    require(len(law)==22 and sum(law.values())==1, 'one supported normalized law')
    divs = (1,5,7,25,35,49,175,245,1225)
    expected = (F(1),F(1,4),F(1,4),F(1,15),F(1,4),F(1,20),F(1,15),F(1,20),F(1,20))
    caps={}
    cylinder_checks=0
    for d,cap in zip(divs,expected):
        masses=[sum(w for x,w in law.items() if x%d==a) for a in range(d)]
        require(max(masses)==cap, 'literal numerical cylinder maxima')
        caps[d]=cap
        cylinder_checks+=d
    envelope=sum(caps[d*e//gcd(d,e)] for d in divs for e in divs)
    require(envelope==F(25,3), 'complete nine-label 81-pair envelope')

    H=4
    weight=sum(F(3)**(1-e) for e in range(1,H+1))
    budget=(F(3)+F(3)**(1-H))/2
    require(weight==F(40,27) and budget==F(41,27), 'comb weights')
    P=[]
    S=F(0)
    previous=F(0)
    for p in primes_until(1000):
        previous=S
        P.append(p)
        S+=F(1,p-1)
        if weight*S>budget:
            break
    require(len(P)==138 and P[-1]==821 and P[-2]==811, 'minimal prime cutoff')
    require(weight*previous<=budget<weight*S, 'strict first threshold crossing')

    # Each record keeps the full original numerical modulus and literal residue.
    originals=[]
    for d,a in head.items():
        originals.append({'modulus':d,'residue':a,'kind':'head'})
    for e in range(1,H+1):
        originals.append({'modulus':3**e,'residue':3**(e-1)-1,'kind':'pure3','e':e})
    for p in P:
        originals.append({'modulus':p,'residue':0,'kind':'outside','p':p})
        for e in range(1,H+1):
            ae=2*3**(e-1)-1
            originals.append({'modulus':3**e*p,'residue':crt(ae,3**e,1,p),'kind':'mixed','e':e,'p':p})
    originals.sort(key=lambda t:t['modulus'])
    labels={i['modulus'] for i in originals}
    require(len(originals)==len(labels)==702, 'all original labels distinct')
    comparable=0
    for x,y in combinations(originals,2):
        d,e=x['modulus'],y['modulus']
        if e%d==0:
            comparable+=1
            require((x['residue']-y['residue'])%d!=0, 'actual comparable APs disjoint')
    closure_checks=0
    for d in labels:
        for a in range(2,isqrt(d)+1):
            if d%a==0:
                require(a in labels and d//a in labels, 'divisor closure above one')
                closure_checks+=1

    # Verify mutual disjointness of every pure/mixed ternary comb leaf.
    prefixes=[]
    for e in range(1,H+1):
        prefixes.extend(((3**e,3**(e-1)-1),(3**e,2*3**(e-1)-1)))
    for (m,a),(n,b) in combinations(prefixes,2):
        require((a-b)%gcd(m,n)!=0, 'all ternary comb leaves disjoint')
    require(all((3**H-1)%m!=a for m,a in prefixes), 'terminal spine is uncovered')

    # Symbolic CRT tuples avoid enumerating the huge full period. All components
    # are actual residue values; membership below is exactly original membership.
    base={'head':source[0],'three':3**H-1,'outside':{}}
    def contains(i,x):
        k=i['kind']
        if k=='head':
            return x['head']%i['modulus']==i['residue']
        if k=='pure3':
            return x['three']%i['modulus']==i['residue']
        if k=='outside':
            return x['outside'].get(i['p'],2)==0
        return (x['three']%(3**i['e'])==i['residue']%(3**i['e'])
                and x['outside'].get(i['p'],2)==1)
    private=[]
    checks=0
    for i in originals:
        w={'head':base['head'],'three':base['three'],'outside':{}}
        if i['kind']=='head':
            w['head']=next(x for x in range(1225) if x%i['modulus']==i['residue']
                          and all(x%d!=a for d,a in head.items() if d!=i['modulus']))
        elif i['kind']=='pure3':
            w['three']=i['residue']
        elif i['kind']=='outside':
            w['outside']={i['p']:0}
        else:
            w['three']=i['residue']%(3**i['e'])
            w['outside']={i['p']:1}
        active=[j['modulus'] for j in originals if contains(j,w)]
        checks+=len(originals)
        require(active==[i['modulus']], 'actual original private witness')
        private.append({'modulus':i['modulus'],'head':w['head'],'three':w['three'],'outside_overrides':w['outside']})
    require(not any(contains(i,base) for i in originals), 'actual full-family noncoverage witness')

    # R3 is exactly source times the nonzero outside roots; use its actual
    # uniform fibres, retaining the head law above.
    density=F(1)
    for p in P:
        density*=F(p-1,p)
    exact_load=weight*S
    gap=exact_load-budget
    zero_completion=F(1)
    for p in P:
        zero_completion*=F(p-2,p-1)
    spine=F(3)**(1-H)
    actual_union=weight*(1-zero_completion)
    uncovered=spine+weight*zero_completion
    overlap_credit=weight*(S-1+zero_completion)
    require(budget==spine+weight, 'the two-root remaining ternary mass')
    require(actual_union+uncovered==budget, 'same-law completion union and escape')
    require(exact_load-actual_union==overlap_credit, 'same-law exact multiplicity excess')
    require(exact_load-budget==overlap_credit-uncovered, 'exact overlap-minus-uncovered ledger')
    require(uncovered>spine>0, 'strictly positive uncovered mass')
    # Compact exact rational lower certificate, avoiding long decimals.
    scale=10**8
    lower_sum=sum(scale//(p-1) for p in P)
    require(S>=F(lower_sum,scale)>F(41,40), 'integer-floor sum certificate')
    # Full cofactor Gram for all 552 original mixed labels: e is retained.
    mixed=[i for i in originals if i['kind']=='mixed']
    gram_pair_checks=0
    for i in mixed:
        for j in mixed:
            p,q=i['p'],j['p']
            value=F(1,p-1) if p==q else F(1,(p-1)*(q-1))
            require(0<value<=min(F(1,p-1),F(1,q-1)), 'exact cofactor product Gram')
            compatible = (i['residue']-j['residue']) % gcd(i['modulus'],j['modulus']) == 0
            require(compatible == (i['e']==j['e']),
                    'full original CRT compatibility retains the ternary depth')
            full_mass = F(3)**(1-i['e'])*value if compatible else F(0)
            require((full_mass>0) == compatible, 'joint original Gram blocks by depth')
            gram_pair_checks+=1
    return {
        'scope':'Actual divisor-closed, locally irredundant distinct odd partial AP family; not a whole cover or a lexicographically extremal cover. Exact uniform-fibre lift method countercontrol, not an existential-lift obstruction.',
        'H':H,'head_originals':head,'head_source_points':len(source),
        'head_law':[{'residue':x,'mass':str(w)} for x,w in sorted(law.items())],
        'head_caps':{str(d):str(v) for d,v in caps.items()},
        'head_cylinder_checks':cylinder_checks,'head_ordered_pair_checks':81,'head_LCM_upper':str(envelope),
        'outside_primes':P,'outside_prime_count':len(P),'last_prime':P[-1],'previous_prime':P[-2],
        'reciprocal_sum':str(S),'previous_reciprocal_sum':str(previous),
        'comb_weight':str(weight),'whole_cover_budget':str(budget),
        'exact_uniform_completion_load':str(exact_load),'exact_gap':str(gap),
        'sum_floor_10pow8':lower_sum,'compact_load_lower':str(weight*F(lower_sum,scale)),
        'compact_gap_lower':str(weight*F(lower_sum,scale)-budget),
        'actual_fibre_density':str(density),
        'outside_all_mixed_missed_probability':str(zero_completion),
        'terminal_ternary_spine_mass':str(spine),
        'actual_mixed_union_mass':str(actual_union),
        'actual_uncovered_mass':str(uncovered),
        'actual_overlap_credit':str(overlap_credit),
        'mass_normalization':'Sum of the two nonprime first-3-root copies, each of mass one. Divide by three for full ternary Haar mass; divide by two to condition on a nonprime first root.',
        'compact_rational_enclosures':{name:[str(F((v*10**6).__floor__(),10**6)),str(F((v*10**6).__floor__()+1,10**6))]
           for name,v in [('reciprocal_sum',S),('zero_completion',zero_completion),('uniform_completion_load',exact_load),('uncovered_mass',uncovered),('overlap_credit',overlap_credit)]},
        'original_count':len(originals),'mixed_count':len(mixed),
        'comparable_AP_checks':comparable,'divisor_closure_checks':closure_checks,
        'private_witness_checks':checks,'cofactor_Gram_ordered_pairs':gram_pair_checks,
        'full_original_Gram_ordered_pairs':gram_pair_checks,
        'originals':originals,'private_witnesses':private,
        'uncovered_CRT_witness':{'head':base['head'],'three':base['three'],'all_outside_values':2},
        'alternative_supported_lift_completion_load':'0'
    }


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    data=result()
    payload=json.dumps(data,indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
        print(json.dumps({k:data[k] for k in ('head_source_points','head_LCM_upper','outside_prime_count','last_prime','previous_prime','original_count','mixed_count','comparable_AP_checks','divisor_closure_checks','private_witness_checks','cofactor_Gram_ordered_pairs','compact_gap_lower','compact_rational_enclosures')},indent=2))
    else:
        print(payload,end='')
