#!/usr/bin/env python3
"""Exact four-predecessor charge certificate for one deterministic schedule.

Thresholds: delta_7=1/5, delta_11=1/3, delta_p=1/2 for p>=13.
The ordinary proof must establish the actual-law comparison and the
all-depth four-slot assignment. This program checks their rational
premises and fees, not an optimization claim or a Lean theorem.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
from math import isqrt, prod
import json
from pathlib import Path
import sys


HELPER_SHA256 = '6282f94780ba7d16307bfe8420b316addc227ddb8ac90267361504d8c9890f69'
ROOT = ((3,Q(2)),(5,Q(4,3)))
THREE = ROOT + ((7,Q(3,2)),)
EARLY_FOUR = THREE + ((11,Q(5,3)),)
FOUR = THREE + ((11,Q(24,13)),)


def bounded_tuples(length,limit,prefix=(),value=1):
    if length == 0:
        yield prefix,value
        return
    for n in range(1,limit//value+1):
        yield from bounded_tuples(length-1,limit,prefix+(n,),value*n)


def main():
    if sys.version_info < (3,10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper',type=Path,required=True)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    raw=args.helper.read_bytes()
    assert sha256(raw).hexdigest()==HELPER_SHA256
    spec=importlib.util.spec_from_file_location('book_density',args.helper)
    helper=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    rows=[]
    primes=[p for p in range(7,98) if all(p%d for d in range(2,isqrt(p)+1))]
    assert len(primes)==22 and primes[:4]==[7,11,13,17] and primes[-1]==97
    for p in primes:
        delta=Q(1,5) if p==7 else Q(1,3) if p==11 else Q(1,2)
        parameters=ROOT if p==7 else THREE if p==11 else EARLY_FOUR if p==13 else FOUR
        threshold=1+(p-2)*delta
        denominator=(p-2)*(1-delta)
        mean=prod(helper.moments(q,c)[0] for q,c in parameters)
        correction=Q(0)
        terms=0
        for indices,value in bounded_tuples(len(parameters),threshold.numerator//threshold.denominator):
            weight=prod(helper.mass(n,q,c) for n,(q,c) in zip(indices,parameters))
            assert weight>=0
            correction+=(threshold-value)*weight
            terms+=1
        charge=(mean-threshold+correction)/denominator
        assert charge>=0
        rows.append(dict(prime=p,delta=str(delta),parameters=[(q,str(c)) for q,c in parameters],
                         threshold=str(threshold),denominator=str(denominator),
                         complete_mean=str(mean),finite_complement_terms=terms,
                         exact_fee=str(charge)))
    assert Q(rows[0]['exact_fee'])==Q(41,180)
    finite=sum(Q(row['exact_fee']) for row in rows)
    assert finite<Q(16,25)
    moment_rows=[helper.moments(q,c) for q,c in FOUR]
    third=prod(m[2] for m in moment_rows)-3*prod(m[1] for m in moment_rows)+3*prod(m[0] for m in moment_rows)-1
    odd_tail=Q(1,97**3)+Q(1,4*97**2)
    tail=Q(32,27)*third*odd_tail
    assert tail<Q(1,60)
    private_ceiling=Q(16,25)+Q(1,60)
    root_charge=Q(1,3)
    reserve=1-root_charge-private_ceiling
    assert private_ceiling==Q(197,300) and reserve==Q(1,100)

    # All-depth comparison is reduced to e=1; each later ratio multiplies
    # by a prime ratio <=1. Different slots always represent distinct parents.
    c7,c11,c13=Q(3,2),Q(5,3),Q(24,11)
    cap7,cap11=Q(3,2),Q(24,13)
    assert cap7==max(c7,7*c11/11,7*c13/13)
    assert cap11==max(c11,11*c13/13)
    assert c13/13 <= Q(4,15)
    assert Q(2)*Q(16,15)/17 <= Q(2,3)
    for p,c in FOUR:
        assert 0<c/p<1
    density7=Q(4,5)/Q(6,5)
    density11=Q(2,3)/Q(10,9)
    density_later=Q(1,2)/Q(12,11)
    assert (density7,density11,density_later)==(Q(2,3),Q(3,5),Q(11,24))
    prefactor=reserve/Q(8,3)
    assert prefactor==Q(3,800)
    out=dict(schema='four-predecessor-one-schedule-v1',
             scope='Natural increasing prime order; at most four actual earlier neighbours per prime; arbitrary finite original heights/residues and distinct odd nonunit numerical moduli.',
             helper_sha256=HELPER_SHA256,
             schedule={'7':'1/5','11':'1/3','p>=13':'1/2'},
             common_comparison_parameters=[(p,str(c)) for p,c in FOUR],
             early_fees=rows,finite_prime_cutoff=97,finite_fee_sum=str(finite),
             strict_finite_fee_upper='16/25',common_third_moment=str(third),
             odd_integer_tail=str(odd_tail),prime_tail_upper=str(tail),
             strict_tail_upper='1/60',strict_private_fee_upper=str(private_ceiling),
             mixed_root_fee_upper=str(root_charge),strict_actual_survivor_lower=str(reserve),
             full_haar_prefactor=str(prefactor),uniform_per_private_prime_factor='11/24',
             endpoint_dominance_ratios={'actual11_to7':str((c11/11)/(cap7/7)),
                                       'late13_to7':str((c13/13)/(cap7/7)),
                                       'actual11_to11':str(c11/cap11),
                                       'late13_to11':str((c13/13)/(cap11/11)),
                                       'third_private13_to5':str((c13/13)/Q(4,15))},
             verification='Exact rational replay of one declared schedule. No global optimization, unrestricted covering result, or new Lean verification claimed.')
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: 22 exact fees, all-depth cap premises, complete third moment, analytic tail and reserve.')
    print('finite fees =',float(finite),'< 16/25; analytic tail =',float(tail),'< 1/60')
    print('weighted survivor > 1/100; full Haar > (3/800)*(11/24)^M')
    print('third moment =',third)


if __name__=='__main__':main()
