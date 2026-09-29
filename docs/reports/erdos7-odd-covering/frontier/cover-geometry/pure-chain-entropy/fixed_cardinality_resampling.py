#!/usr/bin/env python3
"""Fixed rational implications and an actual two-label resampling control.

The retained tail is consumed without rerunning its producer. Only the 15
root points that can lie in the old union need inspection, not its full CRT
period. This does not solve a query LP or verify the ordinary Gibbs proof.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
from itertools import combinations
import json
from math import gcd, lcm, prod
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
    primes = (3, 5, 7, 11, 13, 17, 19)
    A = prod(F(p, p - 1) for p in primes) - 1
    target = F(565, 51)
    small_lower = 800 * (F(31, 16) - A)
    large_lower = F(49, 4)
    labels = (525, 875)
    common = gcd(*labels)
    period = lcm(*labels)
    root_points = list(range(0, period, common))
    old_cover = [x for x in root_points if any(x % d == 0 for d in labels)]
    cover_cells = Counter(tuple(i for i, d in enumerate(labels) if x % d == 0)
                          for x in old_cover)
    singleton_subsets = [(frozenset([0]), F(1, 2)), (frozenset([1]), F(1, 2))]
    independent_subsets = [(frozenset(S), F(1, 4))
                           for k in range(3) for S in combinations(range(2), k)]
    correlated_subsets = [(frozenset(), F(1, 2)), (frozenset([0, 1]), F(1, 2))]
    sampling_tables = {
        'fixed_cardinality': singleton_subsets,
        'independent': independent_subsets,
        'both_or_neither': correlated_subsets,
    }
    sampling_masses = {name: sum((weight for _, weight in table), F(0))
                       for name, table in sampling_tables.items()}
    sampling_marginals = {
        name: [sum((weight for selected, weight in table if i in selected), F(0))
               for i in range(len(labels))]
        for name, table in sampling_tables.items()
    }

    def survives(x, selected):
        return all(x % d != (1 if i in selected else 0)
                   for i, d in enumerate(labels))

    def exterior_mass(sampling):
        return sum((weight * F(sum(survives(x, selected) for x in old_cover), period)
                    for selected, weight in sampling), F(0))

    fixed_leak = exterior_mass(singleton_subsets)
    independent_leak = exterior_mass(independent_subsets)
    survivor_mass = 1 - F(len(old_cover), period)
    private_checks = [all((x % d == 0) == (i == j) for j, d in enumerate(labels))
                      for i, x in enumerate(labels)]
    # Both-or-neither has the same marginals, but violates FR2 at survivor 1.
    positive_correlation_inside = sum(
        (weight for selected, weight in correlated_subsets if survives(1, selected)), F(0))
    checks = {
        'complete_reciprocal_excess': A == F(212731, 110592),
        'alpha_below_one_over_800': alpha < F(1, 800),
        'small_private_mass_gap': F(31, 16) - A == F(1541, 110592),
        'small_branch_lower_and_margin': small_lower == F(38525, 3456)
            and small_lower - target == F(4045, 58752) > 0,
        'large_branch_Haar_endpoint': A / target < F(7, 40),
        'large_branch_reciprocal_excess': A < F(39, 20),
        'large_branch_low_multiplicity_mass': (3 * F(33, 40) - F(39, 20)) / 2 == F(21, 80),
        'large_branch_paid_mass': F(21, 80) - F(1, 80) == F(1, 4),
        'large_branch_parameter_threshold': F(1, 200) < F(1, 14)**2,
        'large_branch_log_argument': F(1, 32) / F(1, 800) == 25 > 3**2,
        'large_branch_free_baseline': F(39, 20) - 1 + F(7, 40) == F(9, 8),
        'large_branch_lower_above_target': large_lower > target,
        'retained_tail_below_one_over_80': 0 <= tau < F(1, 80),
        'actual_numerical_labels': len(set(labels)) == 2 and all(d > 1 and d % 2 for d in labels),
        'actual_private_integers': all(private_checks),
        'common_and_complete_period': common == 175 and period == 2625,
        'only_15_possible_old_cover_roots': len(root_points) == 15,
        'exclusive_old_cover_counts': cover_cells == {(0,): 4, (1,): 2, (0, 1): 1},
        'complete_actual_survivor_mass': survivor_mass == F(2618, 2625),
        'exact_fixed_leak': fixed_leak == F(1, 875),
        'exact_independent_leak': independent_leak == F(13, 10500),
        'strict_validity_separation': fixed_leak < alpha < independent_leak,
        'sampling_tables_are_probability_laws': all(mass == 1 for mass in sampling_masses.values())
            and all(weight >= 0 for table in sampling_tables.values() for _, weight in table),
        'three_sampling_rules_have_same_marginals': all(
            marginals == [F(1, 2), F(1, 2)] for marginals in sampling_marginals.values()),
        'fixed_table_selects_exactly_one': all(len(selected) == 1 for selected, _ in singleton_subsets),
        'query_one_is_actual_survivor': all(1 % d != 0 for d in labels),
        'positive_correlation_inside_from_sampling': positive_correlation_inside == F(1, 2),
        'positive_correlation_exceeds_inverse_exp_lower': positive_correlation_inside > 1 / F(5, 2),
    }
    if not all(checks.values()):
        raise ValueError(checks)
    result = {
        'scope': 'Fixed arithmetic for UR and FR; not a proof of the Gibbs argument or the general query target',
        'retained_input_sha256': source_hash,
        'alpha': str(alpha),
        'reciprocal_excess': str(A),
        'target': str(target),
        'Haar_threshold': str(A / target),
        'small_branch_strict_lower': str(small_lower),
        'small_branch_margin': str(small_lower - target),
        'large_branch_strict_lower': str(large_lower),
        'large_branch_margin': str(large_lower - target),
        'retained_tail': str(tau),
        'originals': [{'modulus': d, 'residue': 0, 'private_integer': d} for d in labels],
        'replacement_query_phases': [1, 1],
        'common_divisor': common,
        'complete_period': period,
        'old_cover_root_points_inspected': len(root_points),
        'exclusive_cover_masses': {','.join(str(labels[i]) for i in key): str(F(value, period))
                                  for key, value in sorted(cover_cells.items())},
        'complete_survivor_mass': str(survivor_mass),
        'fixed_cardinality': 1,
        'sampling_probabilities': {
            name: [{'selected_labels': [labels[i] for i in sorted(selected)], 'mass': str(weight)}
                   for selected, weight in table]
            for name, table in sampling_tables.items()
        },
        'sampling_total_masses': {name: str(mass) for name, mass in sampling_masses.items()},
        'marginal_replacement_probabilities': {
            name: [str(value) for value in marginals]
            for name, marginals in sampling_marginals.items()
        },
        'fixed_cardinality_exterior_mass': str(fixed_leak),
        'independent_exterior_mass': str(independent_leak),
        'fixed_cardinality_beta': str(alpha - fixed_leak),
        'independent_beta': str(alpha - independent_leak),
        'same_marginals_positive_correlation_inside_at_one': str(positive_correlation_inside),
        'exponential_comparison': 'exp(1)>1+1+1/2=5/2, hence exp(-1)<2/5<1/2',
        'checks': checks,
    }
    content = json.dumps(result, indent=2) + '\n'
    if args.output is None:
        print(content, end='')
    else:
        args.output.write_text(content, encoding='utf-8')


if __name__ == '__main__':
    main()
