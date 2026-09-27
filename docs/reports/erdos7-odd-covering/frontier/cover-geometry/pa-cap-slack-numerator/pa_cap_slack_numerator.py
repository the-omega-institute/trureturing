#!/usr/bin/env python3
"""Exact coefficients of the same-law complete-query cap-slack debit.

Report559 supplies the arbitrary-phase and all-height proof. These
calculations verify its coefficients and conditional arithmetic consumer.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from math import prod
from pathlib import Path
import json


ROWS = ((11,F(5,3)), (13,F(3,2)), (17,F(2)), (19,F(9,5)))
checks = {}


def check(name, value):
    if name in checks or not value:
        raise ValueError(name)
    checks[name] = True


def beta(q, z):
    if z == 1:
        return F(1,q*q*(q-1))
    if z == 2:
        return F(q+1,q*(q-1))
    return F(z,q-1)


def finite_beta(q, z, height):
    return sum((F(max((e+1)*z-3,0)-max(e*z-3,0),q**e)
                for e in range(1,height+1)),F())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    results = []
    expected = (F(641451990131,13653911814400),F(130632977,5642112320),
                F(118307,16692640),F(1,6498))
    for index,(q,cap) in enumerate(ROWS):
        future = ROWS[index+1:]
        mean = prod((1+c/(p-1) for p,c in future),start=F(1))
        one = prod((1-c/p for p,c in future),start=F(1))
        two = sum((c*F(p-1,p*p)*prod((1-d/r for r,d in future if r != p),
                                    start=F(1)) for p,c in future),F())
        eta = mean/(q-1)-F(q+1,q*q)*one-two/q
        check('coefficient_'+str(q), eta == expected[index] and eta > 0)
        check('piecewise_expectation_'+str(q), eta == beta(q,1)*one+beta(q,2)*two
              +(mean-one-2*two)/(q-1))
        finite = []
        # Keys include the current row: each future coordinate is evaluated
        # once here per row, so reset-free check names remain unique.
        for height in (1,2,3,6):
            law = {1:F(1)}
            for p,c in future:
                coordinate = {1:1-c/p, height+1:c/p**height}
                coordinate.update({n:c*(p-1)/p**n for n in range(2,height+1)})
                nxt = defaultdict(F)
                for i,w in law.items():
                    for j,v in coordinate.items():
                        nxt[i*j] += w*v
                law = nxt
            check(f'finite_mass_{q}_{height}',sum(law.values()) == 1)
            value = sum((w*finite_beta(q,z,height) for z,w in law.items()),F())
            check(f'finite_bound_{q}_{height}',0 <= value <= eta)
            if finite:
                check(f'finite_monotone_{q}_{height}',finite[-1]['eta'] <= value)
            finite.append(dict(height=height,eta=value))
        results.append(dict(q=q,cap=cap,EZ=mean,P1=one,P2=two,eta=eta,
                            eta_decimal=float(eta),finite=finite))
    corner = F(6168733163201163811,542935350932041267200)
    sample = sum((r['eta']*k for r,k in zip(results,(F(1,6),F(1,8),F(1,10)))),F())
    check('sample_strict_margin',sample-corner == F(3502514252639023,49357759175640115200))
    first_only_gap = corner-F(2,9)*results[0]['eta']
    check('eleven_only_insufficient',first_only_gap == F(26345565509485633,28575544785896908800))
    output = dict(rows=results,corner_deficit=corner,
                  sample_slacks={'11':F(1,6),'13':F(1,8),'17':F(1,10)},
                  sample_D=sample,sample_margin=sample-corner,
                  first11_only_corner_gap=first_only_gap,
                  scope='Exact coefficients; sample slack thresholds are sufficient assumptions, not claimed jointly attained or universal. Ordinary mathematics, no Lean.',
                  checks=checks,check_count=len(checks))
    args.output.write_text(json.dumps(output,default=str,indent=2)+'\n')
    for row in results:
        print('eta',row['q'],row['eta'],row['eta_decimal'])
    print('sample margin',sample-corner,'checks',len(checks))


if __name__ == '__main__':
    main()
