#!/usr/bin/env python3
"""Exact finite constants for a parent-count-free large-owner tail.

The accompanying ordinary proof establishes the complete Euler-product and
prime-tail bounds. These exact checks supply finite caps, rational constants
and source bindings; they are not Lean verification or a finite substitute
for the universal proof.
"""
import argparse
import json
from fractions import Fraction as F
from hashlib import sha256
from math import comb, isqrt, prod
from pathlib import Path


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).with_name('growing_parent_sets_forward_kernels.json'))
    parser.add_argument('--caps-source', type=Path, default=Path(__file__).with_name('unrestricted_triple_parent_forward_kernels.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = {}

    def require(name, condition):
        if not condition:
            raise ArithmeticError(name)
        checks[name] = True

    def read_source(path, label):
        raw = path.read_bytes()
        data = json.loads(raw)
        producer_hash = sha256(path.with_suffix('.py').read_bytes()).hexdigest()
        require(label + '_producer_binding', data['producer_sha256'] == producer_hash)
        require(label + '_prior_checks', bool(data['checks']) and all(item is True for item in data['checks'].values()))
        require(label + '_no_Lean_claim', data['new_lean_verification'] is False)
        return data, dict(name=path.name, sha256=sha256(raw).hexdigest(), producer_sha256=producer_hash)

    source, source_binding = read_source(args.source, 'report620')
    caps_source, caps_binding = read_source(args.caps_source, 'report619')
    require('report620_binds_exact_report619', source['source'] == caps_binding)
    alpha = F(source['constants']['alpha'])
    reserve = F(source['consequence']['simple_raw_lower'])
    require('inherited_projection', alpha == F(2673, 138320))
    require('inherited_raw_reserve', reserve == F(10417363, 5120000000))
    require('inherited_reserve_derivation', reserve == F(147, 5000) - F(531, 20000) - F(1, 65536) - F(1, 1250) - F(1, 10**7))
    require('inherited_actual_reserve_stronger', F(source['consequence']['raw_good_lower']) > reserve)
    require('inherited_head_reserve', alpha * reserve == F(source['consequence']['simple_head_lower']) > F(1, 26000))
    require('inherited_cubical_cap_boundary', caps_source['tail']['boundary'] == 971 and caps_source['tail']['selected_count'] == 'n^3-1' and caps_source['tail']['D'] == 'v-n^3-2')

    def prime(p):
        return p >= 2 and all(p % divisor for divisor in range(2, isqrt(p) + 1))

    head = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    rows = caps_source['finite_rows']
    require('complete_finite_outside_prime_list', [row['owner_prime'] for row in rows] == [p for p in range(37, 971) if prime(p)])
    require('finite_outside_count', len(rows) == 152)
    small_caps = [(p, F(2), 'joint_head_query') for p in head]
    for row in rows:
        p = row['owner_prime']
        d = row['complement_D']
        selected = row['selected_nonunit_patterns']
        cap = F(row['conditional_Haar_cap'])
        require(f'actual_row_{p}', d == p - 3 - selected and d >= 8 and 0 <= selected <= p - 11 and cap == F(2 * (p - 1), d) and cap <= F(p, 4))
        small_caps.append((p, cap, 'actual_report619_row'))
    require('all_small_odd_primes_once', [p for p, _, _ in small_caps] == [p for p in range(3, 971) if prime(p)])
    require('small_cap_count', len(small_caps) == 162)
    require('actual_exception_not_replaced_by_four', max((cap, p) for p, cap, _ in small_caps) == (F(161, 16), 967))

    factors = []
    for p, cap, kind in small_caps:
        moment = 1 + cap * (F(3, p - 1) + F(2, (p - 1)**2))
        correction = moment * F(p - 1, p)**12
        factors.append(dict(prime=p, cap=cap, cap_kind=kind, full_coordinate_moment=moment, euler_correction=correction))
    finite_product = prod(row['full_coordinate_moment'] for row in factors)
    correction = prod(row['euler_correction'] for row in factors)
    require('exact_finite_correction_identity', correction == finite_product * prod(F(p - 1, p)**12 for p, _, _ in small_caps))
    require('finite_product_bound', 0 < finite_product < 2**23)
    require('finite_correction_bound', 0 < correction < F(3, 1000))
    require('tail_factor_binomial_domination', comb(12, 1) == 12 and comb(12, 2) >= 8 and all(comb(12, j) > 0 for j in range(3, 13)))
    require('empty_selection_new_row_cap', F(2 * (971 - 1), 971 - 3) < 4 < F(971, 4))
    ratio = F(1, 2) * F(112, 111)**12
    require('all_k_ge109_geometric_ratio_base', ratio < F(3, 5))
    require('odd_count_dyadic_factor', F(2**(109-1), 2**(2*(109-1))) == F(2, 2**109))
    require('geometric_tail_factor', F(2, 1) / (1 - F(3, 5)) == 5)

    thresholds = []
    for k, denominator in ((109, 80000), (115, 26000), (120, 26000)):
        v = 2**k
        fee = F(15, 1000) * F((4 * (k + 2))**12, v)
        raw = reserve - fee
        head_lower = alpha * raw
        require(f'new_row_cap_at_{k}', F(2 * (v - 1), v - 3) < 4 < F(v, 4))
        require(f'geometric_ratio_at_{k}', F(1, 2) * F(k + 3, k + 2)**12 < F(3, 5))
        require(f'positive_raw_at_{k}', raw > 0)
        require(f'head_lower_at_{k}', head_lower > F(1, denominator))
        thresholds.append(dict(dyadic_exponent=k, uniform_owner_threshold=v, tail_fee_upper=fee,
                               raw_good_lower=raw, exact_head_lower=head_lower,
                               strict_head_lower=F(1, denominator), full_density_lower=f'1/({denominator} Q_off)'))
    require('threshold109_fee_exact', thresholds[0]['tail_fee_upper'] == F(10495351790806902569309763, 7737125245533626718119526400))
    require('threshold115_fee_exact', thresholds[1]['tail_fee_upper'] == F(19740202146111572828188083, 495176015714152109959649689600))

    result = dict(
        schema='uniform-large-owner-forward-kernels-v1',
        source=source_binding, caps_source=caps_binding,
        scope=dict(
            head='Complete fixed Report617 actual pure-source and relational-root hypotheses inherited through Reports619/620',
            below_threshold='Retain Report620 parent-count growth conditions and its actual row choices',
            above_threshold='Any fixed finite union of distinct smaller head or declared network parent primes; no parent-count growth condition; one N=0 row per owner',
            tuples='Merge and deduplicate actual numerical moduli across all tuples before choosing the one owner row',
            phases_and_heights='One globally fixed phase per distinct numerical modulus, with arbitrary finite exponent heights',
            common_law='One full head submeasure and normalized rows in increasing prime order; include dead fibres; no survival conditioning',
            ordinary='Inherited private-domain and component gluing restrictions, with each original assigned once',
            unresolved='Unrestricted head, owner restrictions below threshold, undeclared private crossings; unrestricted Erdos #7 remains open'),
        inherited=dict(alpha=alpha, simple_raw_reserve=reserve),
        small_prime_factors=factors,
        finite_product=finite_product,
        finite_euler_correction=correction,
        finite_euler_correction_strict_upper=F(3, 1000),
        full_moment_bound='M(v) <= A * product_(3<=p<v, p prime) (1-1/p)^(-12)',
        elementary_euler_bound='product_(3<=p<=2^k, p prime) (1-1/p)^(-1) <= 4(k+1), k>=2',
        tail=dict(minimum_k=109, ratio_at_minimum=ratio, geometric_ratio=F(3, 5),
                  odd_integers_per_band='2^(k-1)', band_fee_bound='2*A*[4(k+2)]^12*2^(-k)',
                  complete_fee_strict_upper='(15/1000)*[4(K+2)]^12*2^(-K), K>=109'),
        thresholds=thresholds, checks=checks,
        producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), new_lean_verification=False)
    args.output.write_text(json.dumps(encode(result), indent=2) + '\n')
    print(json.dumps(encode(dict(checks=len(checks), finite_correction_upper=F(3, 1000), thresholds=thresholds))))


if __name__ == '__main__':
    main()
