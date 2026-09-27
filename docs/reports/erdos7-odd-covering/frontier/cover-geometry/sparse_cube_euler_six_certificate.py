#!/usr/bin/env python3
"""Complete sparse-cube and exponent-six owner budgets on the Report648 head.

This computes exact rational inequalities and directed finite products. The
uniform source, infinite-tail and analytic arguments are in Report649. The
Rosser--Schoenfeld branch uses its stated literature theorem; the elementary
branch does not. Neither branch is new Lean verification or unrestricted #7.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from math import comb, factorial, isqrt, prod
from pathlib import Path
import json

parser = ArgumentParser(description=__doc__)
parser.add_argument('--directory', type=Path, default=Path(__file__).parent)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
checks, sources = Counter(), {}


def check(name, predicate):
    if not predicate:
        raise ArithmeticError(name)
    checks[name] += 1


def read(name, expected):
    raw = (args.directory / name).read_bytes()
    sources[name] = sha256(raw).hexdigest()
    check('input_digest', sources[name] == expected)
    return json.loads(raw)


network = read('order_matched_owner_network_certificate.json',
               '9988d52c1c56a776e159295a8b98ed3b389e484a7946edb5b435aca8709adb4c')
pairs = read('induced_square_pair_boundary_certificate.json',
             '1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
gamma = F(next(s for s in pairs['scopes'] if s['scope'] == 'twenty')['worst']['gate'])
alpha, ordinary = F(2673, 110656), F(1, 65536)
check('unchanged648_head_gate', gamma == F(203129722400814193208791597, 20692505911553620784640000000))
B, scale = 3**10, 2**160
flags = bytearray(b'\1') * (B + 1)
flags[:2] = b'\0\0'
for p in range(2, isqrt(B) + 1):
    if flags[p]:
        flags[p*p::p] = b'\0' * ((B - p*p)//p + 1)
primes = [p for p in range(3, B + 1, 2) if flags[p]]
check('finite_prime_count', len(primes) == 5967)
check('finite647_prime_count', sum(p < 971 for p in primes) == 162)


def depth(p):
    n = 7
    while p > 3**n:
        n += 1
    return n


def shifted_polynomial(coefficients, start):
    return [sum(F(c)*comb(i, j)*start**(i-j)
                for i, c in enumerate(coefficients) if i >= j)
            for j in range(len(coefficients))]


# 3(n^3+2)-((n+1)^3+2)>0 for n>=8 proves both inductions.
induction = shifted_polynomial([3, -3, -3, 2], 8)
check('cubic_growth_induction_coefficients', induction == list(map(F, [811, 333, 45, 2])))
check('cubic_growth_positive_all_n_ge8', min(induction) > 0)
check('half_band_base', 2*(8**3 + 2) <= 3**7)
check('fifth_band_base', 5*(11**3 + 2) <= 3**10)
check('initial_cube_cap', F(2*(971-1), 971-7**3-2) < 4)
# p^2-27p+16>=0 for p>=27 gives the rational local-factor bound.
factor_induction = shifted_polynomial([16, -27, 1], 27)
check('local_factor_bound_polynomial', factor_induction == list(map(F, [16, 27, 1])))

# Complete cube moment majorant from625 ST8, checked at its monotone base.
reference = [(3, F(2)), (5, F(4, 3)), (7, F(7, 5))]
T = [1+d*(F(3, p-1)+F(2, (p-1)**2)) for p, d in reference]
diagonal = [d*p*(p+1)*F(1, p**7*(p-1)**2) for p, d in reference]
cross = [d*F(1, p**6*(p-1))*(8+F(2, p-1)) for p, d in reference]
base_moment = sum(diagonal[i]*prod(T[j] for j in range(3) if j != i) for i in range(3))
base_moment += 2*sum(cross[i]*cross[j]*T[3-i-j] for i in range(3) for j in range(i+1, 3))
check('complete_cube_majorant_base', base_moment*3**7 == F(8040996178, 337640625) < 24)
for i in range(3):
    check('cube_diagonal_scaled_ratio', F(3, reference[i][0]) <= 1)
    for j in range(i+1, 3):
        check('cube_cross_scaled_ratio', F(3, reference[i][0]*reference[j][0])*F(9, 8)**2 < 1)

bands, cube_tail = [], F()
for n in range(7, 21):
    a = 971 if n == 7 else 3**(n-1)+1
    b, c = 3**n, n**3+2
    fee = F(24, 3**n)*(F(1, a-c-1)-F(1, b-c))
    check('cube_band_positive_denominators', a-c-1 > 0 and fee > 0)
    if n >= 8:
        check('cube_band_geometric_envelope', fee <= F(144, 9**n))
    cube_tail += fee
    bands.append(dict(n=n, first_integer=a, last_integer=b, integral_fee=str(fee)))
cube_remainder = F(162, 9**21)
check('complete_cube_remainder_sum', cube_remainder == F(144, 9**21)/(1-F(1, 9)))
cube_tail += cube_remainder
check('strict_improvement_on625_tail', 0 < cube_tail < F(512, 9529569))

# Sum n>=11 of(n^3+1)/3^n using all geometric moments, no truncation.
geometric = [F(1), F(1, 2), F(1), F(11, 4)]
excess = F(24, 3**11)*(sum(comb(3, j)*11**(3-j)*geometric[j] for j in range(4))+1)
# Independent generating-function form for the same full polynomial tail.
q = F(1, 3)
moments = [1/(1-q), q/(1-q)**2, q*(1+q)/(1-q)**3,
           q*(1+4*q+q*q)/(1-q)**4]
check('complete_logarithmic_excess_identity', excess == 16*q**11*(sum(comb(3, j)*11**(3-j)*moments[j] for j in range(4))+moments[0]))
check('exponential_geometric_majorant', 0 < excess < 1)
tail_factor = 1/(1-excess)
check('exponent_six_binomial_dominates', [comb(6, j)-(1 if j == 0 else 6 if j == 1 else 4 if j == 2 else 0) for j in range(7)] == [0, 0, 11, 20, 15, 6, 1])
log_base_lower, rs_ratio = F(263, 24), F(201, 199)
check('log3_positive_series_lower', 10*2*sum(F(1, 2**(2*j+1)*(2*j+1)) for j in range(3)) == log_base_lower)
# log2 =2 atanh(1/3); bound its tail after the first term geometrically.
check('log2_upper_seven_tenths', F(2, 3)+2*F(1, 27)/(3*(1-F(1, 9))) < F(7, 10))
check('RS286_range_and_ratio', B >= 286 and rs_ratio == F(2*10**2+1, 2*10**2-1))


def product_interval(factors, bits, reverse=False):
    unit = 2**bits
    lo = hi = unit
    for factor in reversed(factors) if reverse else factors:
        lo = lo*factor.numerator//factor.denominator
        hi = (hi*factor.numerator+factor.denominator-1)//factor.denominator
    return F(lo, unit), F(hi, unit)


Plo, Phi = product_interval([F(p, p-1) for p in primes], 160)
check('positive_odd_Mertens_base', 1 < Plo <= Phi)
results = {}
for order, analytic_k, analytic_den, elementary_k, elementary_den in (
        (3, 47, 140000, 69, 21000000), (4, 48, 68000, 70, 159000)):
    data = network['results'][str(order)]
    finite_caps = {e['prime']: F(e['cap']) for e in data['finite_Euler_factors']}
    check('all_actual_finite_caps', sorted(finite_caps) == [p for p in primes if p < 971])
    factors, largest_cube_cap = [], F()
    for p in primes:
        if p < 971:
            cap = finite_caps[p]
            if p >= 37:
                check('finite_parent_invariant', cap < F(p, 5))
        else:
            n = depth(p)
            D = p-n**3-2
            cap = F(2*(p-1), D)
            largest_cube_cap = max(largest_cube_cap, cap)
            check('sparse_cube_admissibility', D > 0 and 2 < cap < 4 < F(p, 5))
            check('arbitrary_parent_cap_dominated', F(2*(p-1), p-3) <= cap)
            check('depth_band', n == 7 and 971 <= p <= 3**7 or n >= 8 and 3**(n-1) < p <= 3**n)
        factor = 1+cap*(F(3, p-1)+F(2, (p-1)**2))
        check('positive_padding_factor', factor > 1)
        factors.append(factor)
    lo, hi = product_interval(factors, 160)
    reverse_lo, reverse_hi = product_interval(factors, 192, reverse=True)
    check('directed_product_cross_check', lo <= reverse_lo <= reverse_hi <= hi)
    W = F(data['finite_owner_fee'])+cube_tail
    A = hi*tail_factor/Plo**6
    branches = {}
    for kind, K, den in [('rosser_schoenfeld', analytic_k, analytic_den),
                         ('elementary', elementary_k, elementary_den)]:
        V = 2**K
        if kind == 'rosser_schoenfeld':
            upper_log = F(7*K, 10)
            polynomial = sum(F(factorial(6), factorial(6-j))*upper_log**(6-j) for j in range(7))
            E = hi*tail_factor*rs_ratio**6*F(V, V-3)**2*polynomial/(2*(V-1)*log_base_lower**6)
            check('decreasing_log_integrand_range', V-1 >= 2**(K-1) and F(K-1, 2) > 3)
            extra = dict(log_integral_polynomial=str(polynomial),
                         odd_integer_integral_lower_limit=V-1,
                         analytic_premise='Rosser--Schoenfeld1962 Theorem8 (3.28)--(3.29)')
        else:
            ratio = F(1, 2)*F(K+3, K+2)**6
            check('complete_dyadic_geometric_ratio', 0 < ratio < 1)
            E = 2*A*(4*(K+2))**6*F(1, V)/(1-ratio)
            extra = dict(dyadic_ratio_upper=str(ratio),
                         analytic_premise='Report621 UT15 elementary proof')
        margin = alpha*(gamma-W-ordinary-E)
        check('strict_full648_survivor_density', margin > F(1, den))
        branches[kind] = dict(threshold=V, threshold_power=K,
                              complete_arbitrary_parent_fee=str(E),
                              projected_margin=str(margin),
                              density_denominator=den, **extra)
    results[str(order)] = dict(finite_owner_fee=data['finite_owner_fee'],
        complete_three_parent_fee=str(W), base_product_lower=str(lo),
        base_product_upper=str(hi), base_product_interval_width=str(hi-lo),
        independent_192bit_reverse_lower=str(reverse_lo),
        independent_192bit_reverse_upper=str(reverse_hi),
        largest_cube_cap_through_base=str(largest_cube_cap),
        elementary_Euler_constant_upper=str(A), branches=branches)

out = dict(schema='sparse-cube-euler-six-v1', status='PASS',
    source_sha256=sources, producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    constants=dict(alpha=str(alpha), gamma648=str(gamma), ordinary_fee=str(ordinary),
        base_prime_limit=B, odd_prime_count=len(primes), fixedpoint_bits=160,
        logarithmic_excess=str(excess), exponential_upper=str(tail_factor),
        log_base_lower=str(log_base_lower), RS_ratio_upper=str(rs_ratio),
        odd_Mertens_base_lower=str(Plo), odd_Mertens_base_upper=str(Phi)),
    cube_bands=bands, complete_cube_remainder=str(cube_remainder),
    complete_cube_tail=str(cube_tail), results=results,
    checks=dict(checks), check_count=sum(checks.values()),
    remaining_scope='Report648 head; <=3 fixed declared parents below each threshold; Report625 ordinary/private interfaces',
    new_lean_verification=False, unrestricted_erdos7_resolved=False)
args.output.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(dict(status=out['status'], check_count=out['check_count'],
                     results=results), indent=2))
