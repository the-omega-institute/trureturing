#!/usr/bin/env python3
"""Exact certificate for the sharp height-two literal flow-cap bound.

Run with Python's standard library only, including under -I -S -B -O.
The script checks every literal cylinder of an explicit 53-atom measure,
its common-centre query square, and the arithmetic of the analytic upper
certificate. It does not enumerate arbitrary phase layouts. The general
upper proof uses: (1) every noncoherent layout has at least two incompatible
pairs, and (2) the coherent containment I25 union I35 subset I5 with
I25 intersection I35 = I175.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json
from math import lcm
from pathlib import Path
import sys

DENOMINATOR = 63
DIVISORS = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
NONUNIT = DIVISORS[1:]
AXES = {
    1: (1, 1), 5: (5, 1), 7: (1, 7), 25: (25, 1),
    35: (5, 7), 49: (1, 49), 175: (25, 7),
    245: (5, 49), 1225: (25, 49),
}
CAP_UNITS = {5: 21, 7: 21, 25: 7, 35: 21, 49: 7, 175: 6, 245: 7, 1225: 2}
BLOCK = (
    (2, 2, 2, 0, 0, 0, 0),
    (2, 2, 1, 1, 0, 0, 0),
    (2, 0, 0, 0, 0, 0, 0),
    (1, 2, 1, 1, 0, 0, 0),
    (0, 1, 1, 0, 0, 0, 0),
)


class VerificationError(Exception):
    """An exact certificate condition failed."""


class Checks:
    def __init__(self):
        self.count = 0

    def require(self, condition, message):
        self.count += 1
        if not condition:
            raise VerificationError(message)


def rational(numerator, denominator=DENOMINATOR):
    return str(Fraction(numerator, denominator))


def build_atoms():
    atoms = {}
    for root in range(4):
        for i, row in enumerate(BLOCK):
            for j, weight in enumerate(row):
                # Three full 21/63 blocks and one 15/63 block.
                if weight and (root < 3 or i != 0):
                    atoms[root + 5 * i, root + 7 * j] = weight
    return atoms


def verify():
    check = Checks()
    atoms = build_atoms()
    check.require(len(atoms) == 53, 'The certificate must have 53 positive atoms.')
    for (x, y), weight in atoms.items():
        check.require(0 <= x < 25 and 0 <= y < 49, 'Atom outside Z25 x Z49.')
        check.require(isinstance(weight, int) and weight > 0, 'Invalid atom weight.')
    mass_units = sum(atoms.values())
    check.require(mass_units == 78, 'The raw mass must equal 78/63.')

    literal_count = 0
    maxima = {}
    selected = {}
    for d in DIVISORS:
        p, q = AXES[d]
        check.require(p * q == d, 'Incorrect CRT cylinder dimensions.')
        masses = defaultdict(int)
        for (x, y), weight in atoms.items():
            masses[x % p, y % q] += weight
        for a in range(p):
            for b in range(q):
                literal_count += 1
                if d == 1:
                    check.require(masses[a, b] == mass_units, 'Incorrect unit cylinder.')
                else:
                    check.require(masses[a, b] <= CAP_UNITS[d], 'Literal cylinder cap failed.')
        maxima[d] = max(masses.values())
        selected[d] = masses[0, 0]
    check.require(literal_count == 1767, 'The full divisor-cylinder inventory was not checked.')
    check.require(
        tuple(selected[d] for d in NONUNIT) == (21, 21, 6, 21, 7, 6, 7, 2),
        'The selected cylinder masses do not match the certificate.',
    )

    # Unit counted exactly once: L=1+n and L^2-1=n^2+2n.
    square_units = 0
    nonunit_units = 0
    for (x, y), weight in atoms.items():
        n = sum(x % AXES[d][0] == 0 and y % AXES[d][1] == 0 for d in NONUNIT)
        square_units += weight * (1 + n) ** 2
        nonunit_units += weight * (n * n + 2 * n)
    check.require(square_units == mass_units + nonunit_units, 'Unit accounting failed.')
    check.require(nonunit_units == 625, 'The raw nonunit query value must equal 625/63.')
    check.require(square_units == 703, 'The full raw query square must equal 703/63.')
    query_lower = Fraction(square_units, mass_units)
    check.require(query_lower == Fraction(703, 78), 'The normalized witness must equal 703/78.')
    check.require(query_lower - 9 == Fraction(1, 78), 'Incorrect margin above nine.')

    # Arithmetic of the general upper proof, with no arbitrary-layout enumeration.
    coherent_coefficients = {d: 3 for d in NONUNIT}
    for d, e in combinations(NONUNIT, 2):
        coherent_coefficients[lcm(d, e)] += 2
    check.require(
        tuple(coherent_coefficients[d] for d in NONUNIT) == (3, 3, 5, 9, 5, 15, 15, 25),
        'Incorrect common-centre LCM coefficients.',
    )
    envelope_units = sum(coherent_coefficients[d] * CAP_UNITS[d] for d in NONUNIT)
    check.require(envelope_units == 630, 'The original cap envelope must equal ten.')
    check.require(
        sum(coherent_coefficients[d] * selected[d] for d in NONUNIT) == nonunit_units,
        'Direct square and common-centre LCM calculation disagree.',
    )

    # Add 5*(m5+m175-m25-m35), which is nonnegative by containment.
    conic_coefficients = dict(coherent_coefficients)
    for d, delta in ((5, 5), (175, 5), (25, -5), (35, -5)):
        conic_coefficients[d] += delta
    check.require(
        tuple(conic_coefficients[d] for d in NONUNIT) == (8, 3, 0, 4, 5, 20, 15, 25),
        'Incorrect conic certificate coefficients.',
    )
    check.require(all(value >= 0 for value in conic_coefficients.values()),
                  'The conic certificate must have nonnegative cap coefficients.')
    for x in range(25):
        for y in range(49):
            indicator = {d: int(x % AXES[d][0] == 0 and y % AXES[d][1] == 0)
                         for d in (5, 25, 35, 175)}
            check.require(indicator[5] + indicator[175] >= indicator[25] + indicator[35],
                          'The coherent pointwise containment certificate failed.')
    upper_units = sum(conic_coefficients[d] * CAP_UNITS[d] for d in NONUNIT)
    check.require(upper_units == 625, 'The coherent upper bound must equal 625/63.')
    minimum_pair_cap_units = min(CAP_UNITS[lcm(d, e)] for d, e in combinations(NONUNIT, 2))
    check.require(minimum_pair_cap_units == 2, 'Incorrect minimum pair-intersection cap.')
    noncoherent_upper_units = envelope_units - 2 * 2 * minimum_pair_cap_units
    check.require(noncoherent_upper_units == 622, 'Incorrect noncoherent upper arithmetic.')
    check.require(noncoherent_upper_units < upper_units, 'Coherent bound must control both cases.')
    check.require(envelope_units - upper_units == 5, 'The sharp saving must equal 5/63.')
    check.require(Fraction(5, 63) < Fraction(2, 21), 'The saving must be below the required 2/21.')
    check.require(78 + upper_units > 9 * 78 and 79 + upper_units < 9 * 79,
                  'The integral cut threshold must remain 79/63.')

    return {
        'status': 'PASS',
        'checks': check.count,
        'scope': {
            'finite_verification': 'All literal cylinders, the selected query, and upper-certificate arithmetic.',
            'general_phase_argument': 'Analytic: noncoherence forces at least two incompatible pairs; coherence gives the conic containment certificate.',
            'not_claimed': 'No enumeration of all phase layouts; no tree-blocking or flow-network realization claim.',
        },
        'inventory': {'divisors': list(DIVISORS), 'literal_cylinders_checked': literal_count,
                      'positive_atoms': len(atoms)},
        'mass': rational(mass_units),
        'caps': {str(d): rational(CAP_UNITS[d]) for d in NONUNIT},
        'literal_cylinder_maxima': {str(d): rational(maxima[d]) for d in DIVISORS},
        'selected_common_centre_masses': {str(d): rational(selected[d]) for d in DIVISORS},
        'upper_certificate': {
            'original_raw_nonunit_envelope': rational(envelope_units),
            'coherent_lcm_coefficients': [coherent_coefficients[d] for d in NONUNIT],
            'conic_cap_coefficients': [conic_coefficients[d] for d in NONUNIT],
            'coherent_raw_nonunit_upper': rational(upper_units),
            'noncoherent_raw_nonunit_upper': rational(noncoherent_upper_units),
            'sharp_raw_saving': rational(envelope_units - upper_units),
        },
        'witness': {
            'raw_nonunit_square': rational(nonunit_units),
            'raw_full_square': rational(square_units),
            'normalized_query_square_and_gamma_lower': str(query_lower),
            'margin_above_nine': str(query_lower - 9),
            'gamma_exact_with_general_analytic_upper': str(query_lower),
        },
        'construction': {
            'weight_denominator': DENOMINATOR,
            'block_table': [list(row) for row in BLOCK],
            'full_block_roots': [[0, 0], [1, 1], [2, 2]],
            'truncated_block_root': [3, 3],
            'truncated_block_deleted_row': 0,
            'atoms': [[x, y, w] for (x, y), w in sorted(atoms.items())],
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'),
                        help='JSON output path (default: sibling file with .json suffix).')
    args = parser.parse_args()
    try:
        result = verify()
    except VerificationError as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        return 1
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
