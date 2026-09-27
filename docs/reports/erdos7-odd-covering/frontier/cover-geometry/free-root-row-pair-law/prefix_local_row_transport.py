#!/usr/bin/env python3
"""Exact prefix-local same-Y row transport and concentrated-family controls.

The generic certificate validates the supplied coupling and both marginals.
The all-height conclusion uses the analytic proof in report 417, not the
finite source checks. Standard library; explicit exceptions also under -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import copy
import json

import concentrated_sharp_source_relabel_transport as family


def prefix_mismatch_profile(height, coupling):
    """Return the maximal actual disagreement mass in a prefix at each depth."""
    left, right, mismatch = family.coupling_marginals(height, coupling)
    profile = []
    for j in range(height+1):
        masses = defaultdict(F)
        for (row, other_row, y), mass in coupling.items():
            if row != other_row:
                masses[y % 7**j] += mass
        profile.append(max(masses.values(), default=F()))
    return {'left': left, 'right': right, 'mismatch': mismatch,
            'prefix_mismatch': tuple(profile),
            'uniform_layout_difference_bound':
                sum((3*(2*j+1)*d for j, d in enumerate(profile)), F())}


def verify_prefix_transport(height, left, right, coupling):
    """Validate this exact pair of laws, without assuming a branching cap."""
    left = family.probability(height, left)
    right = family.probability(height, right)
    result = prefix_mismatch_profile(height, coupling)
    family.need(result['left'] == left and result['right'] == right,
                'coupling marginals differ from the stated probabilities')
    return result


def family_profile_formula(height):
    family.integer(height, 2, 'height')
    k = height
    full = [F(25*3**(k-2)-7, 5**k)]
    full.extend(max(F(5*3**(k-j-1)), F(5*3**(k-j)-7, 2))/5**k
                for j in range(1, k))
    full.append(F(1, 5**k))
    pair = [F(1, 3**k)] + [F(1, 2*3**k)]*k
    full_bound = sum((3*(2*j+1)*d for j, d in enumerate(full)), F())
    pair_bound = sum((3*(2*j+1)*d for j, d in enumerate(pair)), F())
    error = F(5, 13)*full_bound + F(8, 13)*pair_bound
    simple_error = F(350, 39)*F(3, 5)**k + F(12, 13)*F((k+1)**2+1, 3**k)
    target = F(6)-F(2*(k+2), 3**k)
    family.need(error <= simple_error, 'simple error must dominate the exact profile')
    return {'height': k, 'full_profile': tuple(full), 'pair_profile': tuple(pair),
            'profile_error': error, 'simple_error': simple_error,
            'profile_upper': F(587, 104)+error,
            'simple_upper': F(587, 104)+simple_error,
            'target': target,
            'profile_margin': target-F(587, 104)-error,
            'simple_margin': target-F(587, 104)-simple_error}


def family_control(height):
    expected = family_profile_formula(height)
    cert = family.family_certificate(height)
    family.verify_family_certificate(cert)
    full = verify_prefix_transport(height, cert['full'], cert['full_bar'], cert['full_coupling'])
    family.need(full['prefix_mismatch'] == expected['full_profile'], 'actual full prefix mismatch')
    actual_error = F(5, 13)*full['uniform_layout_difference_bound']
    for pair in family.PAIRS:
        result = verify_prefix_transport(height, cert['pairs'][pair], cert['pairs_bar'][pair],
                                         cert['pair_couplings'][pair])
        family.need(result['prefix_mismatch'] == expected['pair_profile'], 'actual pair prefix mismatch')
        actual_error += F(8, 39)*result['uniform_layout_difference_bound']
    family.need(actual_error == expected['profile_error'], 'actual mixture error formula')
    old_error = F(5, 13)*family.row_relabel_shell_bound(height, 5, full['mismatch'])
    old_error += F(8, 13)*family.row_relabel_shell_bound(height, 3, F(1, 3**height))
    family.need(actual_error <= old_error, 'local prefix bound exceeds the old global estimate')
    return {'height': height, 'source_points': len(cert['source']),
            'actual_profile_error': actual_error, 'old_error': old_error,
            'formula': expected}


def generic_controls():
    coupling = {(1, 2, 0): F(1, 7), (3, 3, 0): F(2, 7),
                (4, 1, 1): F(1, 7), (2, 2, 6): F(3, 7)}
    result = prefix_mismatch_profile(1, coupling)
    family.need(result['prefix_mismatch'] == (F(2, 7), F(1, 7)), 'generic separated mismatch')
    moduli = family.layout_api.original_divisors(1)
    checked = 0
    for phases in product(*(range(d) for d in moduli)):
        scores = []
        for law in (result['left'], result['right']):
            scores.append(sum((mass*family.layout_api.literal_layout_cost(1, phases, point)
                               for point, mass in law.items()), F()))
        family.need(abs(scores[0]-scores[1]) <= result['uniform_layout_difference_bound'],
                    'literal independent layout violates transport bound')
        checked += 1
    diagonal = {(row, row, y): mass for (row, y), mass in result['left'].items()}
    family.need(prefix_mismatch_profile(1, diagonal)['uniform_layout_difference_bound'] == 0,
                'identity coupling must have zero transport loss')
    bad_marginal = copy.deepcopy(result['right'])
    point, mass = next(iter(bad_marginal.items()))
    del bad_marginal[point]
    new_point = next(p for p in product(range(1, 5), range(7)) if p not in bad_marginal and p != point)
    bad_marginal[new_point] = mass
    invalid = [
        ('boolean_height', lambda: prefix_mismatch_profile(True, coupling)),
        ('negative_mass', lambda: prefix_mismatch_profile(1, {(1, 2, 0): F(-1)})),
        ('float_mass', lambda: prefix_mismatch_profile(1, {(1, 2, 0): 1.0})),
        ('unnormalized_mass', lambda: prefix_mismatch_profile(1, {(1, 2, 0): F(1, 2)})),
        ('changes_y', lambda: prefix_mismatch_profile(1, {(1, 2, 0, 1): F(1)})),
        ('wrong_marginal', lambda: verify_prefix_transport(1, result['left'], bad_marginal, coupling)),
    ]
    rejected = []
    for name, action in invalid:
        try:
            action()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('malformed transport accepted: '+name)
    return {'all_literal_layouts_checked': checked, 'rejected': rejected}


def self_check():
    actual = [family_control(k) for k in range(2, 7)]
    threshold = family_profile_formula(7)
    family.need(threshold['simple_margin'] == F(16319233, 236925000) > F(1, 15),
                'height-seven threshold arithmetic')
    family.need(threshold['profile_margin'] == F(85217837, 1184625000),
                'height-seven exact profile arithmetic')
    return {'scope': 'exact transport checks; all-height proof is analytic in report 417',
            'generic': generic_controls(), 'actual_family': actual, 'threshold': threshold}


if __name__ == '__main__':
    print(json.dumps(family.jsonable(self_check()), indent=2, sort_keys=True))
