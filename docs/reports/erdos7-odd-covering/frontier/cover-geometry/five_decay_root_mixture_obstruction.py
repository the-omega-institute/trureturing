#!/usr/bin/env python3
"""Actual sharp sources obstruct all root mixtures of uniformly fast child laws.

Report 419 proves the all-height and all-law quantifiers analytically. This
module reuses the existing source constructors, checks supplied child laws,
and evaluates exact bounds and original-layout controls. It does not compute
the unrestricted source minimax. Running or importing it writes no files.
"""
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import concentrated_sharp_source_relabel_transport as family


def source_children(height):
    """Return the actual +2 child and four clean children at height K>=3."""
    family.integer(height, 3, 'height')
    h = height - 1
    return (family.source(h),) + tuple(family.clean_source(h, row) for row in family.ROWS)


def source(height):
    """Construct the canonical single-+2/four-clean sharp source of report 419."""
    return frozenset((row, column + 7*y)
                     for column, child in enumerate(source_children(height))
                     for row, y in child)


def five_leaves(height):
    family.integer(height, 0, 'height')
    leaves = {0}
    for j in range(height):
        leaves = {y + digit*7**j for y in leaves for digit in range(5)}
    return frozenset(leaves)


def five_sum(height):
    family.integer(height, 0, 'height')
    return sum((F(2*j+1, 5**j) for j in range(height+1)), F())


def five_decay_bounds(height):
    """Evaluate the analytic bound without constructing exponentially many leaves."""
    family.integer(height, 3, 'height')
    h = height - 1
    delta = F(25*3**(h-2)-7, 5**h)
    lower = (4-3*delta)*five_sum(height)
    target = F(6)-F(2*(height+2), 3**height)
    return {'height': height, 'centre_non1_fraction': delta,
            'clean_non1_fraction': F(3, 5)**(h-1),
            'row1_lower': 1-delta, 'cost_lower': lower,
            'target': target, 'target_gap_lower': lower-target,
            'ceiling_six_gap_lower': lower-6}


def decay_parameters(constant, ratio):
    constant = family.rational(constant, 'decay constant')
    ratio = family.rational(ratio, 'decay ratio')
    family.need(constant >= 1, 'decay constant must be at least one')
    family.need(F(1, 5) <= ratio < F(1, 3),
                'decay ratio must lie in [1/5,1/3)')
    return constant, ratio


def fast_decay_bounds(height, constant=1, ratio=F(1, 5)):
    """Bounds under fixed C>=1 and 1/5<=c<1/3, conditional on each child cap."""
    family.integer(height, 3, 'height')
    constant, ratio = decay_parameters(constant, ratio)
    delta = F(25, 9)*constant*(3*ratio)**(height-1)
    lower = (4-3*delta)*five_sum(height)
    target = F(6)-F(2*(height+2), 3**height)
    return {'height': height, 'constant': constant, 'ratio': ratio,
            'non1_upper': delta, 'row1_lower': 1-delta,
            'cost_lower': lower, 'target': target,
            'target_gap_lower': lower-target,
            'sufficient_target_condition': delta < F(4, 15)}


def coherent_layout(height, center):
    """One legal original layout centered at row one and the given five-tree leaf."""
    family.integer(height, 0, 'height')
    family.point(height, (1, center))
    remaining = center
    for _ in range(height):
        family.need(remaining % 7 < 5, 'center must lie in the standard five-tree')
        remaining //= 7
    phases = []
    for j in range(height+1):
        modulus = 7**j
        prefix = center % modulus
        phases.extend((prefix, prefix + modulus*((1-prefix)*pow(modulus, -1, 5) % 5)))
    return family.layout_api.validate_layout(height, tuple(phases))


def layout_average_lower_bound(height, law):
    """Exact dual average for any probability on four rows above the standard F_K."""
    law = family.probability(height, law)
    for _, y in law:
        for _ in range(height):
            family.need(y % 7 < 5, 'law projection must lie in the standard five-tree')
            y //= 7
    row_mass = sum((mass for (row, _), mass in law.items() if row == 1), F())
    return {'row1_mass': row_mass, 'dual_average': (1+3*row_mass)*five_sum(height)}


def uniform_child_laws(height, split_duplicates=False):
    """Actual five-decay witnesses; optionally split all duplicated fibres equally."""
    family.need(type(split_duplicates) is bool, 'split_duplicates must be boolean')
    h = family.integer(height, 3, 'height') - 1
    laws = []
    for child in source_children(height):
        if not split_duplicates:
            laws.append(family.uniform_tree_law(h, child, family.ROWS, 5))
            continue
        rows = defaultdict(list)
        for row, y in child:
            rows[y].append(row)
        laws.append(family.probability(h, {(row, y): F(1, len(labels)*5**h)
                                           for y, labels in rows.items() for row in labels}))
    return tuple(laws)


def verify_child_mixture(height, root_weights, child_laws, constant=1, ratio=F(1, 5)):
    """Validate one actual mixture against all required conditional prefix caps.

    Every supplied child law is normalized and checked, including zero-weight
    children. The returned lower bound concerns the full independent-phase
    maximum; the centered layouts are only a lower certificate.
    """
    children = source_children(height)
    h = height-1
    constant, ratio = decay_parameters(constant, ratio)
    family.need(type(root_weights) in (tuple, list) and len(root_weights) == 5,
                'five root weights required')
    weights = tuple(family.rational(w, 'root weight') for w in root_weights)
    family.need(all(w >= 0 for w in weights) and sum(weights, F()) == 1,
                'root weights must be nonnegative and sum to one')
    family.need(type(child_laws) in (tuple, list) and len(child_laws) == 5,
                'five child probabilities required')
    embedded = []
    for column, (child, raw_law) in enumerate(zip(children, child_laws)):
        law = family.probability(h, raw_law)
        family.need(set(law) <= child, 'child law has unsupported mass')
        for j in range(1, h+1):
            pure, _ = family.prefix_masses(law, j)
            family.need(max(pure.values()) <= constant*ratio**j,
                        'conditional child prefix cap violated')
        embedded.append({(row, column+7*y): mass for (row, y), mass in law.items()})
    law = family.mixture(height, list(zip(weights, embedded)))
    actual = layout_average_lower_bound(height, law)
    bound = fast_decay_bounds(height, constant, ratio)
    family.need(actual['row1_mass'] >= bound['row1_lower'], 'fast-decay row lower bound')
    family.need(actual['dual_average'] >= bound['cost_lower'], 'fast-decay cost lower bound')
    if constant == 1 and ratio == F(1, 5):
        bound = five_decay_bounds(height)
        exact_row = (1 - weights[0]*bound['centre_non1_fraction']
                     - sum(weights[2:], F())*bound['clean_non1_fraction'])
        family.need(actual['row1_mass'] == exact_row, 'exact five-decay row identity')
        family.need(actual['dual_average'] >= bound['cost_lower'], 'five-decay cost lower bound')
    return {'height': height, 'root_weights': weights, 'law': law,
            'row1_mass': actual['row1_mass'], 'dual_average': actual['dual_average'],
            'bounds': bound}


def source_control(height):
    children = source_children(height)
    h = height-1
    actual = source(height)
    family.need(len(actual) == 5**height+2, 'wrong sharp source size')
    projection = five_leaves(h)
    counts = []
    for column, child in enumerate(children):
        family.need({y for _, y in child} == projection, 'wrong child full projection')
        row1 = {y for row, y in child if row == 1}
        other = {y for row, y in child if row != 1}
        family.need(not row1 & other, 'row one and another row share a projected leaf')
        expected = (25*3**(h-2)-7 if column == 0
                    else 0 if column == 1 else 5*3**(h-1))
        family.need(len(other) == expected, 'wrong non-row-one projected leaf count')
        counts.append(len(other))
        for pair in combinations(family.ROWS, 2):
            good = family.layout_api.contains_bary_tree({y for row, y in child if row in pair}, h, 3)
            family.need(good == (column == 0 or column in pair), 'wrong actual child capability')
    for pair in combinations(family.ROWS, 2):
        family.need(family.layout_api.contains_bary_tree(
            {y for row, y in actual if row in pair}, height, 3), 'missing actual global pair tree')
    family.need(family.layout_api.contains_bary_tree({y for _, y in actual}, height, 5),
                'missing actual global five-tree')
    return {'height': height, 'source_points': len(actual),
            'non1_projected_leaf_counts': counts, 'bounds': five_decay_bounds(height)}


def literal_average_controls():
    checks = 0
    for height in (0, 1, 2):
        leaves = five_leaves(height)
        layouts = [coherent_layout(height, y) for y in leaves]
        for point in product(family.ROWS, leaves):
            measured = sum((F(family.layout_api.literal_layout_cost(height, phases, point), len(layouts))
                            for phases in layouts), F())
            expected = layout_average_lower_bound(height, {point: F(1)})['dual_average']
            family.need(measured == expected, 'literal centered-layout average identity')
            checks += len(layouts)
    return checks


def malformed_controls():
    laws = uniform_child_laws(3)
    weights = [F(1, 5)]*5
    unsupported = deepcopy(laws)
    point, mass = next(iter(unsupported[0].items()))
    del unsupported[0][point]
    family.need((1, 0) not in source_children(3)[0], 'unsupported control must be outside source')
    unsupported[0][1, 0] = mass
    concentrated = list(deepcopy(laws))
    concentrated[1] = {(1, 0): F(1)}
    cases = [
        ('boolean_height', lambda: source(True)),
        ('small_height', lambda: source(2)),
        ('float_constant', lambda: fast_decay_bounds(6, 1.0)),
        ('small_constant', lambda: fast_decay_bounds(6, F(1, 2))),
        ('ternary_endpoint', lambda: fast_decay_bounds(6, 1, F(1, 3))),
        ('below_five_scale', lambda: fast_decay_bounds(6, 1, F(1, 6))),
        ('nonboolean_split', lambda: uniform_child_laws(3, 1)),
        ('wrong_weight_count', lambda: verify_child_mixture(3, weights[:4], laws)),
        ('float_weight', lambda: verify_child_mixture(3, [0.2]*5, laws)),
        ('unnormalized_weights', lambda: verify_child_mixture(3, [F(1, 4)]*5, laws)),
        ('negative_weight', lambda: verify_child_mixture(3, [-1, 2, 0, 0, 0], laws)),
        ('wrong_child_count', lambda: verify_child_mixture(3, weights, laws[:4])),
        ('unsupported_child', lambda: verify_child_mixture(3, weights, unsupported)),
        ('violated_child_cap', lambda: verify_child_mixture(3, weights, concentrated)),
        ('outside_five_projection', lambda: layout_average_lower_bound(1, {(1, 5): F(1)})),
        ('outside_five_center', lambda: coherent_layout(1, 5)),
    ]
    rejected = []
    for name, operation in cases:
        try:
            operation()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('malformed input accepted: '+name)
    return rejected


def self_check():
    structure = [source_control(height) for height in range(3, 7)]
    mixtures = []
    for height in (3, 6):
        laws = uniform_child_laws(height, split_duplicates=True)
        choices = [[F(int(i == column)) for i in range(5)] for column in range(5)]
        choices += [[F(1, 5)]*5, [F(1, 3), F(1, 6), F(1, 12), F(1, 4), F(1, 6)]]
        for weights in choices:
            result = verify_child_mixture(height, weights, laws)
            mixtures.append({'height': height, 'root_weights': result['root_weights'],
                             'row1_mass': result['row1_mass'], 'dual_average': result['dual_average']})
        verify_child_mixture(height, choices[-1], laws, constant=F(2), ratio=F(1, 4))
    threshold = five_decay_bounds(6)
    family.need(threshold['cost_lower'] == F(307459328, 48828125), 'height-six lower bound')
    family.need(threshold['ceiling_six_gap_lower'] == F(14490578, 48828125) > 0,
                'height-six ceiling-six obstruction')
    family.need(threshold['target_gap_lower'] == F(11344881362, 35595703125),
                'height-six finite-target gap')
    return {'scope': 'conditional child-decay interface obstruction; not unrestricted source minimax',
            'source_controls': structure, 'mixture_controls': mixtures,
            'literal_layout_point_checks': literal_average_controls(),
            'rejected': malformed_controls(), 'threshold': threshold}


if __name__ == '__main__':
    print(json.dumps(family.jsonable(self_check()), indent=2, sort_keys=True))
