#!/usr/bin/env python3
"""Exact arithmetic for the conditional shallow-LP to full-survivor transfer.

Consumes the retained reciprocal tail. No smooth-label enumeration, original
source producer, phase-pattern enumeration, or LP solve is performed.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
import hashlib
import json
from math import prod
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name(
        'phase_resampling_arithmetic.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    source_hash = hashlib.sha256(raw).hexdigest()
    if source_hash != 'da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f':
        raise ValueError('expected the retained phase-resampling arithmetic data')
    data = json.loads(raw)
    alpha, tau = F(data['alpha']), F(data['tail'])
    cutoff = data['cutoff']
    primes = (3, 5, 7, 11, 13, 17, 19)
    cap = 1 / alpha
    delta = cap * tau
    target = F(565, 51)
    finite_target = F(1103257, 100000)
    epsilon = F(1, 10**7)
    reference_query_bound = F(70871, 3375)
    conditioned_cap = cap / (1 - delta)
    conditioned_bound = finite_target / (1 - delta)
    mixed_bound = (1 - epsilon) * conditioned_bound + epsilon * reference_query_bound
    mixed_cap = (1 - epsilon) * conditioned_cap + epsilon * cap
    heights = []
    period = 1
    for prime in primes:
        power, height = 1, 0
        while power * prime <= cutoff:
            power *= prime
            height += 1
        if not power <= cutoff < power * prime:
            raise ValueError('invalid period exponent')
        heights.append(height)
        period *= power
    divisor_count = prod(height + 1 for height in heights)
    checks = {
        'cutoff_is_one_billion': cutoff == 10**9,
        'positive_retained_mass': 0 < delta < 1,
        'finite_target_below_transfer_threshold': finite_target < target * (1 - delta),
        'fixed_mixture_has_query_margin': mixed_bound < target,
        'fixed_mixture_margin_above_54_over_ten_million': target - mixed_bound > F(54, 10**7),
        'conditioned_density_below_844': conditioned_cap < 844,
        'mixed_density_below_844': mixed_cap < 844,
        'lower_density_coefficient': epsilon / 5 == F(1, 50000000),
        'period_heights': heights == [18, 12, 10, 8, 8, 7, 7],
        'period_has_61_decimal_digits': len(str(period)) == 61,
        'divisor_count_is_14084928': divisor_count == 14084928,
    }
    if not all(checks.values()):
        raise ValueError(checks)
    with localcontext() as ctx:
        ctx.prec = 70

        def decimal(value):
            return str(Decimal(value.numerator) / Decimal(value.denominator))

        result = {
            'scope': 'Arithmetic of FT1--FT6 conditional on the finite LP bound; no LP solve or Lean verification',
            'input_sha256': source_hash,
            'primes': primes,
            'cutoff': cutoff,
            'alpha': str(alpha),
            'reciprocal_tail': str(tau),
            'initial_density_cap': str(cap),
            'delta': str(delta),
            'delta_decimal': decimal(delta),
            'query_target': str(target),
            'unmixed_finite_threshold_decimal': decimal(target * (1 - delta)),
            'required_finite_LP_upper': str(finite_target),
            'epsilon': str(epsilon),
            'reference_query_upper': str(reference_query_bound),
            'conditioned_query_upper': str(conditioned_bound),
            'conditioned_density_upper': str(conditioned_cap),
            'conditioned_density_upper_decimal': decimal(conditioned_cap),
            'mixed_query_upper': str(mixed_bound),
            'mixed_query_upper_decimal': decimal(mixed_bound),
            'mixed_query_margin': str(target - mixed_bound),
            'mixed_query_margin_decimal': decimal(target - mixed_bound),
            'mixed_density_upper': str(mixed_cap),
            'mixed_density_upper_decimal': decimal(mixed_cap),
            'full_support_lower_coefficient': str(epsilon / 5),
            'period_heights': heights,
            'finite_period': str(period),
            'period_decimal_digits': len(str(period)),
            'period_divisor_count': divisor_count,
            'checks': checks,
        }
    content = json.dumps(result, indent=2) + '\n'
    if args.output is None:
        print(content, end='')
    else:
        args.output.write_text(content, encoding='utf-8')


if __name__ == '__main__':
    main()
