"""Exact exhaustive marginal-identifiability checks; no floats or solvers."""
from argparse import ArgumentParser
from itertools import product
from math import gcd, prod
from pathlib import Path
import json


def need(test, message):
    if not test:
        raise ValueError(message)


def divisors(n):
    return [d for d in range(1, n+1) if n%d==0]


def vp(n,p):
    e=0
    while n%p==0:
        n//=p;e+=1
    return e


def enumeration(Q, primes, include_unit=False):
    ds=[d for d in divisors(Q) if include_unit or d>1]
    Hs={p:vp(Q,p) for p in primes}
    Bs={p:Q//p**Hs[p] for p in primes}
    tables={}
    for p in primes:
        tables[p]=[]
        for d in ds:
            e=vp(d,p);m=d//p**e
            rows=[((0,)*Bs[p], None)]
            for a in range(d):
                scaled=tuple(p**(Hs[p]-e)*int(y%m==a%m) for y in range(Bs[p]))
                rows.append((scaled,a%m))
            tables[p].append(rows)
    marginal_seen={p:{} for p in primes}
    pair_seen={}
    accepted_scalar_noncover=None
    accepted_scalar_noncover_count=0
    all_marginals_at_least_one=0
    counter=0
    for choices in product(*(range(d+1) for d in ds)):
        counter+=1
        margins=[]
        for p in primes:
            rows=[tables[p][i][choice] for i,choice in enumerate(choices)]
            key=tuple(sum(row[0][y] for row in rows) for y in range(Bs[p]))
            signature=tuple(row[1] for row in rows)
            old=marginal_seen[p].setdefault(key,signature)
            need(old==signature,'single marginal has two projected families')
            margins.append(key)
        combined=tuple(margins)
        old=pair_seen.setdefault(combined,choices)
        if len(primes)>=2:
            need(old==choices,'two prime marginals fail full recovery')
        if all(min(key)>=p**Hs[p] for p,key in zip(primes,margins)):
            all_marginals_at_least_one+=1
            classes=[(choice-1,d) for d,choice in zip(ds,choices) if choice]
            counts=[sum(x%d==a for a,d in classes) for x in range(Q)]
            holes=[x for x,c in enumerate(counts) if not c]
            if holes:
                accepted_scalar_noncover_count+=1
                candidate={'classes':classes,'holes':holes,'multiplicity':counts,
                           'scaled_marginals':{str(p):list(key) for p,key in zip(primes,margins)},
                           'marginal_denominators':{str(p):p**Hs[p] for p in primes}}
                score=(len(classes),sum(d for a,d in classes),classes)
                if accepted_scalar_noncover is None or score<accepted_scalar_noncover[0]:
                    accepted_scalar_noncover=(score,candidate)
    expected=prod(d+1 for d in ds)
    need(counter==expected,'enumeration incomplete')
    need(all(len(marginal_seen[p])==prod(d//p**vp(d,p)+1 for d in ds)
             for p in primes),'projected signature count mismatch')
    return {'period':Q,'moduli':ds,'include_unit':include_unit,'families':counter,
            'single_prime_distinct_marginal_counts':{str(p):len(marginal_seen[p]) for p in primes},
            'expected_projected_signature_counts':{str(p):prod(d//p**vp(d,p)+1 for d in ds) for p in primes},
            'two_prime_marginal_pairs':len(pair_seen),
            'all_single_marginals_at_least_one_families':all_marginals_at_least_one,
            'noncover_families_passing_all_single_marginals':accepted_scalar_noncover_count,
            'least_class_noncover_control':None if accepted_scalar_noncover is None else accepted_scalar_noncover[1]}


def finite_character_layer_check(B,p):
    need(gcd(B,p)==1,'noncoprime layer fixture')
    ds=divisors(B)
    seen={};count=0
    for choices in product(*(range(d+1) for d in ds)):
        count+=1
        key=tuple(sum(choice>0 and x%d==choice-1 for d,choice in zip(ds,choices))%p for x in range(B))
        need(seen.setdefault(key,choices)==choices,'finite-field layer is not injective')
    return {'cofactor_period':B,'characteristic':p,'include_unit':True,'families':count,'distinct_mod_p_profiles':len(seen)}

# Intentional relaxed-assumption collisions, checked with literal scaled marginals.
def marginal(Q,p,classes):
    H=vp(Q,p);B=Q//p**H
    return tuple(sum(p**(H-vp(d,p))*int(y%(d//p**vp(d,p))==a%(d//p**vp(d,p))) for a,d in classes) for y in range(B))
def build_result():
    results=[enumeration(12,[2,3]),enumeration(45,[3,5]),enumeration(15,[3,5])]
    layers=[finite_character_layer_check(6,5),finite_character_layer_check(10,3),finite_character_layer_check(15,2),finite_character_layer_check(9,2)]
    carry_a=[(0,5)];carry_b=[(0,15),(5,15),(10,15)]
    need(marginal(15,3,carry_a)==marginal(15,3,carry_b),'expected repeated-label carry missing')
    checker_a=[(0,15),(1,15)];checker_b=[(6,15),(10,15)]
    need(all(marginal(15,p,checker_a)==marginal(15,p,checker_b) for p in [3,5]),'expected repeated-modulus two-marginal collision missing')
    # Coprimality is required by the finite-field layer lemma.
    noncoprime_a=[(0,3),(0,6)];noncoprime_b=[(3,6)]
    need(all(sum(x%d==a for a,d in noncoprime_a)%2==sum(x%d==a for a,d in noncoprime_b)%2 for x in range(6)),'expected noncoprime failure missing')
    # Every nontrivial coordinate average (p dividing Q) can be at least one
    # despite genuine holes. Outside the prime support, H=0 and M_p=c_A.
    # This control is even and redundant; it does not settle the odd irredundant case.
    noncover_classes=[(0,2),(0,3),(1,4),(5,6),(1,8),(11,12),(13,24)]
    Q=24
    need(len({d for a,d in noncover_classes})==len(noncover_classes),'noncover label repetition')
    counts=[sum(x%d==a for a,d in noncover_classes) for x in range(Q)]
    holes=[x for x,c in enumerate(counts) if c==0]
    need(holes==[7,19],'unexpected period-24 holes')
    scaled_marginals={p:marginal(Q,p,noncover_classes) for p in [2,3]}
    for p,values in scaled_marginals.items():
        H=vp(Q,p);B=Q//p**H
        direct=tuple(sum(counts[x] for x in range(Q) if x%B==y) for y in range(B))
        need(values==direct,'AP formula and literal fibre counts disagree')
        need(min(values)>=p**H,'noncover marginal below one')
    need(scaled_marginals[2]==(15,8,13),'unexpected p2 marginal')
    need(scaled_marginals[3]==(4,8,4,3,4,6,4,3),'unexpected p3 marginal')
    need(sum(counts)==36,'unexpected incidence total')
    outside_prime=5
    outside_marginal=marginal(Q,outside_prime,noncover_classes)
    need(vp(Q,outside_prime)==0,'outside-support control prime divides period')
    need(outside_marginal==tuple(counts),'height-zero marginal must equal multiplicity')
    need(outside_marginal[7]==0 and outside_marginal[19]==0,
         'outside-support prime must detect both holes')
    outside_control={'prime':outside_prime,'height':0,'marginal_denominator':1,
        'scaled_marginal':outside_marginal,'zero_residues':holes,
        'scope':'For p not dividing Q, the prime coordinate is trivial and M_p is the literal multiplicity function, so its values at the holes are zero.'}
    noncover_control={'period':Q,'support_primes':[2,3],'classes':noncover_classes,'holes':holes,
        'multiplicity':counts,'scaled_marginals':scaled_marginals,
        'marginal_denominators':{p:p**vp(Q,p) for p in [2,3]},
        'total_incidence':sum(counts),'outside_support_prime_control':outside_control,
        'scope':'All support-prime averages (p dividing Q, here 2 and 3) are at least one. This does not hold for primes outside the support. Numerically distinct, nonunit, even and redundant; not an odd or irredundant example.'}
    out={'result':'PASS','exhaustive':results,'finite_field_layer_controls':layers,
         'repeated_label_one_marginal_carry':{'period':15,'prime':3,'first':carry_a,'second':carry_b},
         'repeated_label_two_marginal_collision':{'period':15,'primes':[3,5],'first':checker_a,'second':checker_b},
         'noncoprime_finite_field_layer_collision':{'cofactor_period':6,'characteristic':2,'first':noncoprime_a,'second':noncoprime_b},
         'all_support_prime_marginals_at_least_one_noncover':noncover_control,
         'scope':'Complete exact finite enumerations and explicit boundary examples, not an implementation of the constructive decoder. Mathematical generality comes from the ordinary Fourier/layer proof; no Lean or odd-cover impossibility claimed.'}
    return out


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True,
                        help='Path for the deterministic exact JSON result.')
    args=parser.parse_args()
    result=build_result()
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n', encoding='utf-8')
    print('PASS: exact marginal reconstruction checks and boundary controls')


if __name__ == '__main__':
    main()
