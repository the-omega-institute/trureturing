#!/usr/bin/env python3
"""Exact constants for full-volume common-spine books.

Reads the existing Chapter 36 certificate. The actual conditional-law
thickening, joint density transport, and continuation theorem are ordinary
mathematical premises stated in Chapter 37. No geometry or Lean replay.
Python 3.10+; --input FILE --output FILE work from any directory.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import prod
from pathlib import Path
import sys


SOURCE_SHA256 = '1179712ddd5f6e90c1c23a23902bb111af54ea7a5061350c0df2471455dbefeb'


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path,
                        default=Path(__file__).with_name('spine_book_certificate.json'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    raw = args.input.read_bytes()
    assert sha256(raw).hexdigest() == SOURCE_SHA256
    source = json.loads(raw)
    assert source['schema'] == 'spine-book-certificate-v1'
    assert len(source['split_core_branches']) == 13 and len(source['fee_rows']) == 29
    S = Q(source['strict_total_fee_bound'])
    delta = min(Q(row['strict_margin']) for row in source['split_core_branches'])
    assert delta == Q(source['minimum_split_margin']) == Q(968925187, 2025000000000)
    assert Q(source['four_prime_margin']) > delta
    assert Q(source['anchor_only_reserve']) - S > delta
    eta = delta / (2 * S + delta)
    assert 0 < eta < 1 and S * eta / (1 - eta) == delta / 2
    z_row = min(source['fee_rows'], key=lambda row: Q(row['joint_residual']))
    z = min(Q(z_row['joint_residual']), Q(1, 2))
    assert z == Q(94, 6165)
    pure_domain_product = Q(11, 12) * Q(15, 16)
    a = eta * z * pure_domain_product
    assert a == Q(45539483789, 1528808537470752) and 0 < a < 1

    def joint_cap(row):
        return prod(Q(p - 1, p - 1 - t)
                    for p, t in zip(row['later_prime_proxies'], row['thresholds']))

    D4 = joint_cap(source['four_prime_core'])
    caps = [joint_cap(row['source']) for row in source['split_core_branches']]
    D = max([Q(1), D4] + caps)
    assert D4 == Q(5, 2) and D == Q(15, 2)
    prefactor = delta / (2 * D)
    assert prefactor == delta / 15 == Q(968925187, 30375000000000)
    result = {
        'schema': 'spine-book-full-density-v1',
        'scope': 'A book with N nonempty private pages of size at most two sharing the spine {3,5}; full Haar density, uniform in primes, finite heights and residues.',
        'chapter36_certificate_sha256': SOURCE_SHA256,
        'source': source['source'],
        'delta': str(delta), 'S': str(S),
        'eta': str(eta),
        'maximum_extra_outside_page_charge': str(S * eta / (1 - eta)),
        'finite_minimum_shallow_residual': str(z),
        'minimum_residual_row_prime': z_row['minimum_private_prime'],
        'analytic_tail_shallow_residual_lower_bound': '1/2',
        'outside_page_pure_domain_product_lower_bound': str(pure_domain_product),
        'uniform_outside_page_haar_fibre_lower_bound': str(a),
        'four_prime_source_joint_density_cap': str(D4),
        'uniform_core_joint_density_cap': str(D),
        'full_haar_density_bound': {
            'prefactor': str(prefactor),
            'per_page_factor': str(a),
            'formula': 'prefactor * per_page_factor^N',
            'N': 'number of nonempty private pages in the chosen original partition',
        },
        'verification': 'Exact rational consequences of the pinned Chapter 36 certificate; ordinary proof premises, no new Lean or geometry verification.',
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: shared charge inflation, all page residuals, pure-domain factor, and core joint caps.')
    print('Full Haar density >', prefactor, '* (', a, ')^N')


if __name__ == '__main__':
    main()
