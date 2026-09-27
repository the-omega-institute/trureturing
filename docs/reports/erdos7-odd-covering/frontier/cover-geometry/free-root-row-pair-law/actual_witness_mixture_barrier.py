#!/usr/bin/env python3
"""Exact actual-witness obstruction for a universally fixed tree-mixture weight.

Construct two actual full-five-tree and six-pair-ternary-tree witness families.
Their literal original-divisor layout expectations at height six have a
minimum two-line envelope strictly above six. The coefficient may depend
on height, but is chosen uniformly over these permitted witness choices.

This does not bound the minimum over all laws on either source, or rule
out optimizing witnesses or selecting the coefficient from the witnesses.
Only the standard library and the sibling original-layout API are used.
Run without arguments; exact JSON results go to stdout, and no files are
written. Runtime checks remain active under Python -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import importlib.util
import json


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def _load_layout_api():
    path = Path(__file__).with_name('prime_layout_mixture_certificate.py')
    spec = importlib.util.spec_from_file_location('actual_witness_layout_api', path)
    if spec is None or spec.loader is None:
        raise ImportError('cannot load sibling original-layout API')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


api = _load_layout_api()
PAIRS = tuple(combinations(range(1, 5), 2))
PAIR_ROW = {(1, 2): 1, (1, 3): 1, (1, 4): 1,
            (2, 3): 2, (2, 4): 2, (3, 4): 3}


def _parameters(height, family):
    if type(height) is not int or height < 5:
        raise ValueError('height must be an integer at least five')
    if family not in ('A', 'B'):
        raise ValueError('family must be A or B')


def tree_leaves(height, branching):
    """Literal low-digit-first regular subtree leaves, embedded in base seven."""
    leaves = [0]
    for j in range(height):
        leaves = [y + digit * 7 ** j for y in leaves for digit in range(branching)]
    return leaves


def witness_family(height, family):
    """Return a four-active-row source and its seven actual witness laws."""
    _parameters(height, family)
    full, ternary = tree_leaves(height, 5), tree_leaves(height, 3)
    if family == 'A':
        row = lambda y: 1 if y % 7 == 0 else 2
    else:
        row = lambda y: 2 if y % 7 ** 5 == 0 else 1
    mu = {(row(y), y): F(1, 5 ** height) for y in full}
    eta = {pair: {(PAIR_ROW[pair], y): F(1, 3 ** height) for y in ternary}
           for pair in PAIRS}
    source = set(mu)
    for law in eta.values():
        source.update(law)
    source.add((4, 0))
    return source, mu, eta


def literal_phases(height, family):
    """All zero seven-adic phases; A uses row one, B rows 1,1,1,2,2,..."""
    _parameters(height, family)
    phases = []
    for j in range(height + 1):
        modulus = 7 ** j
        row = 1 if family == 'A' or j <= 2 else 2
        phases.extend((0, modulus * ((row * pow(modulus, -1, 5)) % 5)))
    return api.validate_layout(height, tuple(phases))


def expectation(height, phases, law):
    """Evaluate every original modulus on every supported point via the API."""
    return sum((mass * api.literal_layout_cost(height, phases, point)
                for point, mass in law.items()), F(0))


def omitted_row_mixture(mu, eta):
    beta = {r: sum((m for (row, _), m in mu.items() if row == r), F(0))
            for r in range(1, 5)}
    omega = defaultdict(F)
    for pair, law in eta.items():
        weight = (1 - beta[pair[0]] - beta[pair[1]]) / 3
        need(weight >= 0, 'pair weight must be nonnegative')
        for point, mass in law.items():
            omega[point] += weight * mass
    return beta, dict(omega)


def common_law(mu, omega, coefficient):
    if type(coefficient) not in (int, F) or not 0 <= coefficient <= 1:
        raise ValueError('coefficient must be an exact number in [0,1]')
    result = defaultdict(F)
    for point, mass in mu.items():
        result[point] += coefficient * mass
    for point, mass in omega.items():
        result[point] += (1 - coefficient) * mass
    return dict(result)


def prefix_count_average(height, branching, cost):
    """Independent finite distribution of the number of active zero prefixes."""
    return sum((F(branching - 1, branching ** p) * cost(p)
                for p in range(1, height + 1)), F(0)) + F(cost(height + 1), branching ** height)


def profile_moments(height, family):
    """Independent closed-profile moments, without source or CRT enumeration."""
    if family == 'A':
        s5 = sum((F(2*j + 1, 5 ** j) for j in range(height + 1)), F(0))
        s3 = sum((F(2*j + 1, 3 ** j) for j in range(height + 1)), F(0))
        return 4*s5 - F(12, 5), F(13, 5)*s3
    cost_a = lambda p: (p + min(p, 3)) ** 2
    cost_b = lambda p: (p + max(p-3, 0)) ** 2
    mu = prefix_count_average(height, 5, lambda p: cost_a(p) if p <= 5 else cost_b(p))
    beta_b = F(1, 3125)
    omega = (F(2, 3)*beta_b*prefix_count_average(height, 3, cost_a)
             + F(2, 3)*(1-beta_b)*prefix_count_average(height, 3, cost_b)
             + F(1, 3)*prefix_count_average(height, 3, lambda p: p*p))
    return mu, omega


def validate_family(height, family):
    source, mu, eta = witness_family(height, family)
    need({r for r, _ in source} == {1, 2, 3, 4}, 'all four source rows active')
    for law in (mu, *eta.values()):
        need(set(law) <= source and all(m > 0 for m in law.values())
             and sum(law.values()) == 1, 'each witness must be an actual supported probability')
    need(len(mu) == 5 ** height and api.contains_bary_tree({y for _, y in mu}, height, 5),
         'actual uniform full five-tree')
    for pair, law in eta.items():
        need(len(law) == 3 ** height and {r for r, _ in law} <= set(pair)
             and api.contains_bary_tree({y for _, y in law}, height, 3),
             'actual uniform labelled pair ternary-tree')
        need(api.contains_bary_tree({y for r, y in source if r in pair}, height, 3),
             'source pair-tree premise')
    need(api.contains_bary_tree({y for _, y in source}, height, 5), 'source full-tree premise')
    beta, omega = omitted_row_mixture(mu, eta)
    expected_beta = [F(1, 5), F(4, 5), F(0), F(0)] if family == 'A' else [F(3124, 3125), F(1, 3125), F(0), F(0)]
    need(list(beta.values()) == expected_beta, 'measured full-tree row distribution')
    need(set(omega) <= source and all(m >= 0 for m in omega.values())
         and sum(omega.values()) == 1, 'actual omitted-row common probability')
    phases = literal_phases(height, family)
    mu_moment = expectation(height, phases, mu)
    omega_moment = expectation(height, phases, omega)
    need((mu_moment, omega_moment) == profile_moments(height, family),
         'CRT original-label enumeration must equal independent profile formula')
    distribution = common_law(mu, omega, F(2, 3))
    need(sum(distribution.values()) == 1 and set(distribution) <= source,
         'the displayed mixed law is one supported probability')
    actual = expectation(height, phases, distribution)
    need(actual == F(2, 3)*mu_moment + F(1, 3)*omega_moment, 'same-law linearity')
    return {'height': height, 'family': family, 'source_points': len(source),
            'all_four_rows_active': True, 'all_six_actual_pair_trees': True,
            'actual_full_five_tree': True, 'original_divisors': api.original_divisors(height),
            'literal_phases': phases, 'beta': list(beta.values()),
            'mu_moment': mu_moment, 'omega_moment': omega_moment,
            'affine_intercept': omega_moment, 'affine_slope': mu_moment-omega_moment,
            'moment_at_two_thirds': actual}


def verify():
    controls = [validate_family(6, family) for family in ('A', 'B')]
    a, b = controls
    need((a['affine_intercept'], a['affine_slope'])
         == (F(28327, 3645), -F(30440987, 11390625)), 'family A exact affine line')
    need((b['affine_intercept'], b['affine_slope'])
         == (F(2595983, 759375), F(2974792, 759375)), 'family B exact affine line')
    need(a['affine_slope'] < 0 < b['affine_slope'], 'opposite strict affine slopes')
    coefficient = ((a['affine_intercept']-b['affine_intercept'])
                   / (b['affine_slope']-a['affine_slope']))
    minimum = a['affine_intercept'] + coefficient*a['affine_slope']
    need(0 < coefficient < 1, 'crossing lies strictly inside coefficient domain')
    need(minimum == b['affine_intercept'] + coefficient*b['affine_slope'], 'same crossing value')
    need(coefficient == F(49582130, 75062867)
         and minimum == F(1408882511647, 234571459375) and minimum > 6,
         'uniform-coefficient actual-witness obstruction')
    height_five = validate_family(5, 'B')
    need(height_five['moment_at_two_thirds'] == F(13701358, 2278125) > 6,
         'height-five actual-law counterexample for coefficient two thirds')
    return {'scope': 'actual-witness obstruction for coefficients uniform over witness choices; no source-minimax lower bound',
            'height_six': controls, 'height_five': height_five,
            'minimizing_coefficient': coefficient, 'minimum_of_two_actual_lines': minimum,
            'gap_above_six': minimum-6}


if __name__ == '__main__':
    print(json.dumps(verify(), default=str, indent=2))
