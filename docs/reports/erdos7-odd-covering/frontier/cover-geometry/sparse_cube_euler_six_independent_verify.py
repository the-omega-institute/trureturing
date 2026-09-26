#!/usr/bin/env python3
"""Independent exact numerical audit; analytic proof is reported separately.
Uses trial division, a telescoping infinite sum and256-bit reverse products.
Does not import the producer; the analytic/source arguments are in Report649.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import isqrt, factorial
from hashlib import sha256
import argparse
import json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
BASE=args.directory
checks = {}
def require(name, claim):
    if not claim:
        raise RuntimeError(name)
    checks[name] = checks.get(name, 0) + 1
raw = (BASE / 'order_matched_owner_network_certificate.json').read_bytes()
require('predecessor_digest', sha256(raw).hexdigest() == '9988d52c1c56a776e159295a8b98ed3b389e484a7946edb5b435aca8709adb4c')
data = json.loads(raw)
head_raw = (BASE / 'induced_square_pair_boundary_certificate.json').read_bytes()
require('head_digest', sha256(head_raw).hexdigest() == '1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
head = json.loads(head_raw)
gate = Q(next(x for x in head['scopes'] if x['scope'] == 'twenty')['worst']['gate'])
require('head_gate', gate == Q(203129722400814193208791597, 20692505911553620784640000000))

# Trial division, independent of producer's sieve.
prime_list = [2]
for m in range(3, 3**10 + 1, 2):
    prime = True
    for p in prime_list:
        if p*p > m:
            break
        if m % p == 0:
            prime = False
            break
    if prime:
        prime_list.append(m)
odd_primes = prime_list[1:]
require('prime_count', len(odd_primes) == 5967)
require('last_prime', odd_primes[-1] == 59029)

# All finite bands, followed by a geometric bound for the infinite remainder.
cube = Q(0)
bands = []
for depth in range(7, 21):
    left = 971 if depth == 7 else 3**(depth-1) + 1
    right = 3**depth
    offset = depth**3 + 2
    term = Q(24, 3**depth) * Q(right-left+1, (left-offset-1)*(right-offset))
    require('positive_band_denominators', left-offset-1 > 0 and right-offset > 0)
    cube += term
    bands.append([depth, str(term)])
remainder = Q(18, 9**20)  # sum_{n>=21} 144/9^n
require('infinite_cube_geometric_identity', remainder == Q(144, 9**21) / (1-Q(1, 9)))
cube += remainder
require('cube_improvement', 0 < cube < Q(512, 9529569))
# Induction for 3^(n-1) >= q(n^3+2); positive shift polynomial in n-8.
require('cubic_growth_identity', (2*8**3-3*8**2-3*8+3, 6*8**2-6*8-3, 6*8-3, 2) == (811, 333, 45, 2))
require('half_base', 3**7 >= 2*(8**3+2))
require('fifth_base', 3**10 >= 5*(11**3+2))
require('first_cube_cap', Q(2*970, 971-345) < 4)

# Infinite sum via telescoping polynomial: P(n)-P(n+1)/3=n^3+1.
def P(n):
    return Q(12*n**3 + 18*n**2 + 36*n + 45, 8)
# Both sides are cubics; four evaluations certify the polynomial identity.
for n in range(4):
    require('cubic_telescoper', P(n)-P(n+1)/3 == n**3+1)
gamma = 16*P(11)/3**11
require('gamma_range', 0 < gamma < 1)
correction = 1/(1-gamma)
# Exact logarithm bounds: positive log3 series; log2 tail by geometric series.
require('log3_series', 10*(1+Q(1, 12)+Q(1, 80)) == Q(263, 24))
log2_upper = Q(2, 3) + Q(2, 81)/(1-Q(1, 9))
require('log2_upper', log2_upper < Q(7, 10))
require('RS_ratio', Q(1+Q(1, 200), 1-Q(1, 200)) == Q(201, 199))

# Reverse 256-bit outward rounding: a distinct precision and multiplication order.
SCALE = 2**256
def interval(factors):
    low = high = SCALE
    for num, den in reversed(factors):
        low = (low*num)//den
        high = -((-high*num)//den)
        require('directed_product_step', low <= high)
    return Q(low, SCALE), Q(high, SCALE)

mertens_low, mertens_high = interval([(p, p-1) for p in odd_primes])
require('positive_mertens_base', 1 < mertens_low <= mertens_high)
out = {}
for order, exponent, denominator in [(3, 47, 140000), (4, 48, 68000)]:
    current = data['results'][str(order)]
    rows = current['rows']
    require('complete_finite_rows', [r['owner_prime'] for r in rows] == [p for p in odd_primes if 37 <= p < 971])
    finite_fee = Q(0)
    row_caps = {}
    for row in rows:
        v, n, d = row['owner_prime'], row['selected_nonunit_patterns'], row['complement_D']
        require('finite_domain', d == v-3-n and n >= 0 and d > 0)
        require('finite_threshold', Q(row['threshold']) == Q(order-1, order))
        cap = Q(order*(v-1), d)
        require('finite_cap', cap == Q(row['conditional_Haar_cap']) < Q(v, 5))
        fee = Q(row['complete_moment_upper']) / d**order
        require('finite_fee_row', fee == Q(row['violation_fee']))
        finite_fee += fee
        row_caps[v] = cap
    require('finite_fee_sum', finite_fee == Q(current['finite_owner_fee']))
    finite_caps = {x['prime']: Q(x['cap']) for x in current['finite_Euler_factors']}
    require('finite_cap_coverage', set(finite_caps) == {p for p in odd_primes if p < 971})
    for p, cap in row_caps.items():
        require('same_finite_cap', finite_caps[p] == cap)
    factors = []
    for p in odd_primes:
        if p < 971:
            cap = finite_caps[p]
        else:
            n = 7
            while 3**n < p:
                n += 1
            cap = Q(2*(p-1), p-n**3-2)
            require('sparse_cap', 2 < cap < 4 < Q(p, 5))
            require('large_row_cap_dominated', Q(2*(p-1), p-3) <= cap)
        factor = 1 + cap*(Q(3, p-1) + Q(2, (p-1)**2))
        require('padding_positive', factor > 1)
        factors.append((factor.numerator, factor.denominator))
    low, high = interval(factors)
    v = 2**exponent
    # Integration polynomial by Horner, independent of producer's factorial sum.
    ell = Q(7*exponent, 10)
    polynomial = Q(1)
    for degree in range(1, 7):
        polynomial = ell*polynomial + Q(factorial(6), factorial(6-degree))
    require('integral_polynomial', polynomial == sum(Q(factorial(6), factorial(6-j))*ell**(6-j) for j in range(7)))
    # Recurrence P_m'=m P_{m-1}, and (P_6-P_6')=ell^6 makes derivative -log^6(x)/x^2.
    for j in range(6):
        require('integral_coefficient_identity', Q(factorial(6), factorial(6-j))*(6-j) == Q(factorial(6), factorial(5-j)))
    require('integral_decreasing_range', exponent >= 47 and v-1 > 3**10)
    fee = high*correction*Q(201, 199)**6*Q(v, v-3)**2*polynomial/(2*(v-1)*Q(263, 24)**6)
    margin = Q(2673, 110656)*(gate-finite_fee-cube-Q(1, 65536)-fee)
    require('positive_projected_margin', margin > Q(1, denominator))
    elementary_exponent, elementary_denominator = (69, 21000000) if order == 3 else (70, 159000)
    ratio = Q(1, 2)*Q(elementary_exponent+3, elementary_exponent+2)**6
    require('elementary_ratio', 0 < ratio < 1)
    elementary_fee = 2*high*correction/mertens_low**6 * (4*(elementary_exponent+2))**6 / (2**elementary_exponent * (1-ratio))
    elementary_margin = Q(2673, 110656)*(gate-finite_fee-cube-Q(1, 65536)-elementary_fee)
    require('elementary_positive_margin', elementary_margin > Q(1, elementary_denominator))
    out[str(order)] = dict(elementary_exponent=elementary_exponent, elementary_fee=str(elementary_fee), elementary_margin=str(elementary_margin), elementary_lower=str(Q(1, elementary_denominator)), threshold_exponent=exponent, product_lower=str(low), product_upper=str(high), product_width=str(high-low), fee_upper=str(fee), margin_lower=str(margin), advertised_lower=str(Q(1, denominator)), fee_approx=float(fee), margin_approx=float(margin))

# Read producer output only after independent derivation, and compare containment.
producer_raw = (BASE / 'sparse_cube_euler_six_certificate.json').read_bytes()
producer = json.loads(producer_raw)
require('producer_cube_match', Q(producer['complete_cube_tail']) == cube)
require('producer_gamma_match', Q(producer['constants']['logarithmic_excess']) == gamma)
for order in ['3', '4']:
    r, p = out[order], producer['results'][order]
    require('producer_product_contains_independent_interval', Q(p['base_product_lower']) <= Q(r['product_lower']) <= Q(r['product_upper']) <= Q(p['base_product_upper']))
    e = p['branches']['rosser_schoenfeld']
    require('producer_fee_dominates_independent_fee', Q(e['complete_arbitrary_parent_fee']) >= Q(r['fee_upper']))
    require('producer_margin_safe', Q(e['projected_margin']) <= Q(r['margin_lower']) and Q(e['projected_margin']) > Q(r['advertised_lower']))
    e = p['branches']['elementary']
    require('producer_elementary_safe', Q(e['complete_arbitrary_parent_fee']) >= Q(r['elementary_fee']) and Q(r['elementary_margin']) >= Q(e['projected_margin']) > Q(r['elementary_lower']))
result = dict(status='PASS', checks=checks, check_count=sum(checks.values()), predecessor_sha256=sha256(raw).hexdigest(), head_sha256=sha256(head_raw).hexdigest(), reviewed_producer_result_sha256=sha256(producer_raw).hexdigest(), cube_tail=str(cube), gamma=str(gamma), results=out, new_lean_verification=False, producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(status='PASS', checks=result['check_count'], cube_tail=float(cube), gamma=float(gamma), results={k:{j:v[j] for j in ['threshold_exponent','fee_approx','margin_approx','advertised_lower']} for k,v in out.items()}), indent=2))
