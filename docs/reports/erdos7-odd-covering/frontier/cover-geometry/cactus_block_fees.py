#!/usr/bin/env python3
"""Exact finite fees for c=2/3 cactus block bounds; standard library only.

Literal formulas are evaluated independently of any LP or partition probe.
The infinite-range argument belongs to the accompanying ordinary proof.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json


def primes_upto(n):
    return [p for p in range(5, n+1) if all(p % d for d in range(2, isqrt(p)+1))]


def beta(p):
    return F(3, 2*(p-1))


def fee(p):
    return F(1, 4) if p == 5 else F(1, 6) if p == 7 else F(1, 2**((p-1)//2))


def certify(kind, s, t, lam, K, charge):
    minimum_R = 1 if s == 5 else 2
    candidates = []
    R = minimum_R
    while True:
        gap = 1-K-(R-1)*lam
        if gap <= 0:
            break
        candidates.append((lam/(2*3**(R-1)*gap), R, gap))
        R += 1
    assert candidates
    cost, R, gap = min(candidates)
    assert gap > 0 and cost <= charge
    return {'kind': kind, 's': s, 't': t, 'R': R, 'lambda': lam,
            'K': K, 'exact_gap': gap, 'cost': cost, 'charge': charge,
            'charge_minus_cost': charge-cost, 'cost_to_charge': cost/charge}


def serializable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): serializable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serializable(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    primes = primes_upto(97)
    small_square = sum((F(1, (p-1)**2) for p in primes if p <= 73), F())
    odd_tail = F(1, 74**2)+F(1, 148)
    assert small_square+odd_tail < F(13, 100)
    rows = []
    for s in primes:
        if s == 97:
            continue
        rows.append(certify('bridge', s, None, beta(s), F(), fee(s)))
        for t in primes:
            if t <= s:
                continue
            x, y = beta(s), beta(t)
            eligible = F(9, 4)*(F(13, 100)-sum(
                (F(1, (q-1)**2) for q in primes if q < t and q != s), F()))
            charge = fee(s) if t == 97 else fee(s)+fee(t)
            long = certify('long_cycle', s, t, x+y, eligible-(x+y)**2/4, charge)
            long['eligible_beta_square_budget'] = eligible
            rows.append(long)
            rows.append(certify('triangle', s, t, x+y+x*y, x*y, charge))
    assert len(rows) == 528
    assert all(row['s'] == 5 or row['R'] >= 2 for row in rows)
    worst = max(rows, key=lambda row: row['cost_to_charge'])
    assert (worst['kind'], worst['s'], worst['t'], worst['R']) == ('long_cycle', 5, 11, 2)
    assert worst['cost'] == F(80, 287) and worst['charge'] == F(9, 32)
    assert 9**16 >= 6*8**16
    # These finite polynomial identities display the algebra used for n>=48.
    for n in (1, 2, 3, 48):
        lam = F(24*n+21, 16*n*(n+1))
        K = F(9*(n+1), 16*n*n)
        assert 1-K-(F(2*n, 3)-2)*lam == F(41*n*n+24*n-9, 16*n*n*(n+1))
    # Direct coefficient identities, independently of selected evaluation points.
    # Numerator of the gap after multiplying by 16*n^2*(n+1).
    gap_coefficients = tuple(a-b-c for a,b,c in zip(
        (0, 0, 16, 16), (9, 18, 9, 0), (0, -42, -34, 16)))
    assert gap_coefficients == (-9, 24, 41, 0)
    # 2*(41n^2+24n-9)-3n*(24n+21), then substitute n=k+3.
    ratio_coefficients = (-18, -15, 10)
    shifted = (ratio_coefficients[0]+3*ratio_coefficients[1]+9*ratio_coefficients[2],
               ratio_coefficients[1]+6*ratio_coefficients[2], ratio_coefficients[2])
    assert shifted == (27, 45, 10)
    root_total = F(1,4)+F(1,6)+F(1,16)
    p5_total = F(3,10)*(F(1,6)+F(1,16))
    p7_total = root_total/3
    assert root_total == F(23,48) < F(1,2)
    assert p5_total == F(11,160) < F(1,12)
    assert p7_total == F(23,144) < F(1,6)
    data = {
        'scope': 'Finite exact blocker-fee certificate and arithmetic constants; '
                 'the infinite cactus theorem requires the accompanying ordinary proof.',
        'child_density': F(2,3), 'root_parent': 3, 'finite_primes': primes,
        'safe_square_sum': {'finite_prime_cutoff':73,'finite_sum':small_square,
                            'all_odd_tail_bound':odd_tail,'strict_upper_bound':F(13,100)},
        'row_count':len(rows),'rows':rows,'maximum_cost_to_charge_row':worst,
        'boundary_rule':'At t=97 charge only f_s, for extension to all t>=97.',
        'large_minimum_prime_tail': {
            's_parameter':'s=2*n+1, n>=48', 'lambda_bound':'(24*n+21)/(16*n*(n+1))',
            'K_bound':'9*(n+1)/(16*n^2)', 'chosen_cutoff':'floor(2*n/3)-1',
            'gap_lower_bound':'(41*n^2+24*n-9)/(16*n^2*(n+1))',
            'gap_numerator_coefficients_low_degree_first':gap_coefficients,
            'two_thirds_ratio_positive_polynomial_after_n_equals_k_plus_3':shifted,
            'exponential_base_left':9**16,'exponential_base_right':6*8**16,
            'mod_three_required_factors':[3,6,4],
            'result_used_in_ordinary_proof':'lambda/gap<=2/3 and 3^(-cutoff)<=2^(-n)'},
        'fee_totals': {'root3':root_total,'nonroot5':p5_total,'nonroot7':p7_total},
    }
    output=Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(serializable(data),indent=2)+'\n')
    print(json.dumps(serializable({'rows':len(rows),'worst':worst,'fee_totals':data['fee_totals']}),indent=2))


if __name__=='__main__':
    main()
