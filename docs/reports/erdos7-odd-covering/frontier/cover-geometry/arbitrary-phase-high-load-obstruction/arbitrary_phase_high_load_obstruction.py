#!/usr/bin/env python3
"""Exact arithmetic for an actual-label obstruction to an R-only implication.

The query assignment is specified by a finite indexing rule. Its carrier and
label family are deliberately not enumerated. General measure and divisor
counting arguments, stated in the companion text, remain mathematical inputs.
"""
import argparse
from fractions import Fraction
from math import comb, prod
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify():
    primes = (3, 5, 7, 11, 13, 17, 19)
    height = 1000
    load = 20
    divisor_count = (height + 1) ** len(primes)
    exponent_sum_bound = 44
    small_label_upper = comb(exponent_sum_bound + len(primes), len(primes))
    support_count = (divisor_count - small_label_upper) // (load - 1)
    require(support_count > 0, 'Empty support')
    require(support_count < min(primes) ** (exponent_sum_bound + 1),
            'Small-divisor exponent-sum bound')
    require((load - 1) * support_count <= divisor_count - small_label_upper,
            'Insufficient distinct large numerical labels')
    base = prod(Fraction(p, p - 1) for p in primes)
    boundary_weight_count = prod(Fraction(height + 1) + Fraction(1, p - 1)
                                for p in primes)
    complete_upper = base + boundary_weight_count / support_count
    nonunit_upper = complete_upper - 1
    source_query_cap = Fraction(70871, 3375)
    source_density_cap = Fraction(6075000000000, 7235955529)
    require(nonunit_upper < 21 and nonunit_upper < source_query_cap,
            'All-depth query upper bound')
    # The actual period is much larger; this inexpensive lower bound is enough
    # to show that the source density assumption is not met.
    density_lower = Fraction(min(primes) ** height, support_count)
    require(density_lower > source_density_cap, 'Density boundary was lost')
    require(base == Fraction(323323, 110592), 'Euler product')
    require(support_count == 53001107107100275363, 'Retained support count')
    require(complete_upper == Fraction(32160131737868864198395243,
                                      1465374609297108413236224),
            'Retained rational complete-query upper bound')
    return {
        'result': 'PASS',
        'primes': primes,
        'height': height,
        'period': 'product(p^1000 for p in primes)',
        'divisor_count': divisor_count,
        'small_divisor_exponent_sum_upper': exponent_sum_bound,
        'small_divisor_count_upper': small_label_upper,
        'support_count': support_count,
        'large_labels_required': (load - 1) * support_count,
        'large_labels_available_lower': divisor_count - small_label_upper,
        'query_load_on_support_lower': load,
        'query_rule': ('List divisors d of the period with d >= support_count in '
                       'increasing numerical order. Assign consecutive blocks '
                       'of 19 such labels to i=0,...,support_count-1, with '
                       'residue i at each assigned label. Include the unit; '
                       'set every unused label phase to zero.'),
        'law': ('Haar conditioned on residues 0,...,support_count-1 modulo '
                'the period, with Haar completion at all greater depths.'),
        'euler_product': str(base),
        'boundary_weighted_divisor_count': str(boundary_weight_count),
        'complete_all_depth_query_upper': str(complete_upper),
        'nonunit_all_depth_query_upper': str(nonunit_upper),
        'source_nonunit_query_cap': str(source_query_cap),
        'source_cap_margin': str(source_query_cap - nonunit_upper),
        'source_density_cap': str(source_density_cap),
        'density_on_support': 'period / support_count',
        'density_lower_bound_used': '3^1000 / support_count',
        'below_21': True,
        'below_source_query_cap': True,
        'violates_source_density_cap': True,
        'scope': ('An actual finite fixed-phase divisor query and one '
                  'compatible all-depth probability law refute the implication '
                  'that support on load >=20 alone forces R>21. The density '
                  'cap fails, and this is not identified with a source-selected law. '
                  'No full original survivor-set realization, joint two-prime cover, '
                  'or full source-interface counterexample is claimed.'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(), indent=2) + '\n'
    if args.output is None:
        print(result, end='')
    else:
        args.output.write_text(result)


if __name__ == '__main__':
    main()
