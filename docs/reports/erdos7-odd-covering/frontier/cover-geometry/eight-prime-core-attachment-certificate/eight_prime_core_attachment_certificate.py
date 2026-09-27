#!/usr/bin/env python3
"""Exact CK certificate for the first eight odd primes with small attachments.

One actual core block has vertices 3,5,7,11,13,17,19,23; every other
block has at most seven vertices. Ordinary proof premises are specified
in Chapter 35. No geometry cache, source verifier, or Lean replay is used.
Python 3.10+; --output FILE works from any directory.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    core = (3, 5, 7, 11, 13, 17, 19, 23)
    children = (29, 31, 37, 41, 43, 47)
    # The existing descendant invariant has e_q < 1/2.
    b = tuple(Q(1, q - 3) for q in children)
    t = 17
    count = 1 << len(children)
    products = [Q(1)] * count
    for mask in range(1, count):
        bit = mask & -mask
        products[mask] = products[mask ^ bit] * b[bit.bit_length() - 1]
    v = [Q(0)] + [products[mask] * (t if mask.bit_count() == 1 else t + 1)
                   for mask in range(1, count)]
    z = [Q(1)] + [Q(0)] * (count - 1)
    for mask in range(1, count):
        bit = mask & -mask
        # The least vertex is unused, or belongs to a unique chosen support.
        value = z[mask ^ bit]
        support = mask
        while support:
            if support & bit:
                value -= v[support] * z[mask ^ support]
            support = (support - 1) & mask
        z[mask] = value
    assert all(value > 0 for value in z)
    L = sum((products[s] * z[(count - 1) ^ s] for s in range(1, count)), Q(0))
    K = L / (2 * 3 ** t * z[-1])
    assert K == Q(425021, 21704070634758)
    parent_ratios = tuple(Q(2 * 3 ** t, p ** t * (p - 1)) for p in core)
    assert all(ratio <= 1 for ratio in parent_ratios)
    fee_coefficients = tuple(Q(1) if p == 3 else Q(3, 10) if p == 5
                             else Q(2, p - 1) for p in core)
    assert max(fee_coefficients) == 1
    small = (29, 31, 37, 41, 43, 47, 53)
    tail = Q(1, 2 ** 28)  # sum over all odd q >= 59, not just primes
    deletion = len(small) * K + tail
    source_mass = Q(1, 1002375)
    survival = source_mass - deletion
    assert K < Q(1, 50000000)
    assert deletion < Q(1, 7000000)
    assert survival > Q(1, 1200000)
    result = {
        'schema': 'eight-prime-core-attachment-ck-v1',
        'scope': 'One actual core block on the first eight odd primes; every other graph block has at most seven vertices.',
        'source': {
            'doi': '10.5281/zenodo.22759614',
            'version': 'v1.0.1',
            'archive_sha256': '9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c',
            'result': 'Corollary C.2: uncovered Haar density at least 1/1002375',
        },
        'core': core,
        'source_measure': 'Haar restriction to the original uncovered core set; no renormalization',
        'source_mass_lower_bound': str(source_mass),
        'coordinate_marginal_caps': ['1'] * len(core),
        'descendant_expense_strict_upper_bound': '1/2',
        'proxy_children': children,
        'coordinate_caps': list(map(str, b)),
        'cutoff': t,
        'subset_residuals': list(map(str, z)),
        'minimum_residual': str(min(z)),
        'L': str(L),
        'K3': str(K),
        'parent_cost_ratios_to_K3': list(map(str, parent_ratios)),
        'standard_fee_coefficients': list(map(str, fee_coefficients)),
        'small_attachment_prime_set': small,
        'maximum_small_attachment_count': len(small),
        'large_attachment_minimum_child': 59,
        'large_attachment_fee_sum_bound': str(tail),
        'total_deletion_upper_bound': str(deletion),
        'extendible_core_configuration_haar_density_lower_bound': str(survival),
        'simple_extendible_core_configuration_haar_density_strict_lower_bound': '1/1200000',
        'verification': 'Exact Fraction arithmetic; ordinary proof premises, no Lean claim.',
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: 64 positive coordinate residuals, 8 parent comparisons, and shared attachment budget.')
    print('Total deletion upper bound:', deletion)
    print('Haar density of extendible core configurations > 1/1200000')


if __name__ == '__main__':
    main()
