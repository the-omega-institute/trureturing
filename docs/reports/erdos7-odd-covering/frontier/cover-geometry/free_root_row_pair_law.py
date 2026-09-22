#!/usr/bin/env python3
"""Common laws from full/pair prefix caps, without prescribed root geometry.

Report 422 proves the general all-phase interface and an all-height
consumer with a single +2 centre and four recursive clean seed sources.
Its selected pair laws need no monochromatic private columns. Exact
checks retain actual support, independent original phases, and one law.
Standard library only; running this file writes no files.
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
import five_decay_root_mixture_obstruction as fast_obstruction
import prefix_local_row_transport as transport
import single_surplus_source_common_law as previous

ALPHA = F(5, 11)
PAIR_WEIGHT = F(2, 11)
REFERENCE_ROOT = F(4)
REFERENCE_LIMIT = F(507, 88)
SIMPLE_ERROR_CONSTANT = F(2125, 198)


def reference_bound(height):
    family.integer(height, 1, 'height')
    return REFERENCE_ROOT + sum(((2*j+1)*(ALPHA/F(5**j)
                       + 3*(1-ALPHA)/F(3**j)) for j in range(2, height+1)), F())


def verify_interface(height, actual_source, full, pairs):
    """Validate actual support and prefix caps; no root pattern is required."""
    family.integer(height, 1, 'height')
    actual_source = family.points(height, actual_source)
    full = family.probability(height, full)
    family.need(set(full) <= actual_source, 'full law has unsupported mass')
    for j in range(1, height+1):
        pure, _ = family.prefix_masses(full, j)
        family.need(max(pure.values()) <= F(1, 5**j), 'full prefix cap')
    family.need(type(pairs) is dict and set(pairs) == set(family.PAIRS),
                'three non-row-one pair laws required')
    selected = {}
    for pair in family.PAIRS:
        law = family.probability(height, pairs[pair])
        family.need(set(law) <= actual_source and all(r in pair for r, _ in law),
                    'pair law has unsupported or outside-row mass')
        for j in range(1, height+1):
            pure, _ = family.prefix_masses(law, j)
            family.need(max(pure.values()) <= F(1, 3**j), 'pair prefix cap')
        selected[pair] = law
    components = [(ALPHA, full)]+[(PAIR_WEIGHT, selected[p]) for p in family.PAIRS]
    nu = family.mixture(height, components)
    family.need(set(nu) <= actual_source, 'common law has unsupported mass')
    coupling = {(r, 1, y): w for (r, y), w in full.items()}
    relabel = transport.prefix_mismatch_profile(height, coupling)
    error = ALPHA*relabel['uniform_layout_difference_bound']
    return {'law': nu, 'full_mismatch_profile': relabel['prefix_mismatch'],
            'transport_error': error, 'reference_upper': reference_bound(height),
            'all_phase_upper': reference_bound(height)+error,
            'reference_root_upper': REFERENCE_ROOT}


def root_controls():
    """Use top-five/full and top-three/pair root costs for each layout."""
    maxima = defaultdict(F)
    lines = set()
    checked = 0
    for a, c, s, d in product(range(5), range(7), range(5), range(7)):
        phases = (0, a, c, d+7*((s-d)*3 % 5))
        costs = {(r, y): family.layout_api.literal_layout_cost(1, phases, (r, y))
                 for r, y in product(family.ROWS, range(7))}
        full_columns = sorted(range(7), key=lambda y: (-costs[1, y], y))[:5]
        full_cost = sum((F(costs[1, y], 5) for y in full_columns), F())
        pair_cost = F()
        attaining = defaultdict(F)
        for y in full_columns:
            attaining[1, y] += F(1, 11)
        for pair in family.PAIRS:
            pair_columns = sorted(range(7), key=lambda y: (-max(costs[r, y] for r in pair), y))[:3]
            for y in pair_columns:
                row = max(pair, key=lambda r: (costs[r, y], -r))
                pair_cost += F(costs[row, y], 9)
                attaining[row, y] += F(2, 33)
        if a in family.ROWS and s in family.ROWS:
            case = 0 if a == s == 1 else 1 if a == 1 else 2 if s == 1 else 3 if a == s else 4
            same = ((F(32, 5), F(2)), (F(5), F(28, 9)), (F(13, 5), F(40, 9)),
                    (F(8, 5), F(6)), (F(8, 5), F(5)))
            apart = ((F(6), F(2)), (F(5), F(8, 3)), (F(11, 5), F(40, 9)),
                     (F(8, 5), F(50, 9)), (F(8, 5), F(43, 9)))
            family.need((full_cost, pair_cost) == (same if c == d else apart)[case],
                        'analytic five-case root calculation')
        law = family.probability(1, dict(attaining))
        value = ALPHA*full_cost+(1-ALPHA)*pair_cost
        direct = sum((w*costs[p] for p, w in law.items()), F())
        family.need(value == direct <= REFERENCE_ROOT, 'free-root layout maximum')
        maxima[a, s] = max(maxima[a, s], value)
        lines.add((pair_cost+3, full_cost-pair_cost-F(109, 40)))
        checked += 1
    table = tuple(tuple(33*maxima[a, s] for s in family.ROWS) for a in family.ROWS)
    expected = ((132, 131, 131, 131), (119, 132, 114, 114),
                (119, 114, 132, 114), (119, 114, 114, 132))
    family.need(table == expected and max(maxima.values()) == 4, 'root row-phase table')
    family.need(len(lines) == 17, 'distinct robust root-plus-tail lines')
    active = {(F(5), F(67, 40)), (F(9), F(-57, 8))}
    family.need(active <= lines, 'two crossing lower lines missing')
    family.need(all(b+m*ALPHA <= REFERENCE_LIMIT for b, m in lines), 'coefficient upper')
    family.need(all(b+m*ALPHA == REFERENCE_LIMIT for b, m in active), 'coefficient intersection')
    return {'literal_layouts': checked, 'row_phase_table_times_33': table,
            'distinct_affine_lines': len(lines), 'selected_alpha': ALPHA,
            'robust_root_plus_tail_minimum': REFERENCE_LIMIT}


def clean_source(height, centre_row):
    """407 concentration recursion with the 413 (2,1,1,1) star seed."""
    family.integer(height, 1, 'height')
    family.need(type(centre_row) is int and centre_row in family.ROWS, 'literal centre row')
    seed = (centre_row, centre_row)+tuple(r for r in family.ROWS if r != centre_row)
    result = set()
    for digits in product(range(5), repeat=height):
        row = seed[digits[-1]] if all(d < 3 for d in digits[:-1]) else 1
        y = sum(d*7**j for j, d in enumerate(digits))
        result.add((row, y))
    return frozenset(result)


def source_children(height):
    h = family.integer(height, 3, 'height')-1
    return (family.source(h),)+tuple(clean_source(h, r) for r in family.ROWS)


def source(height):
    return frozenset((r, c+7*y) for c, child in enumerate(source_children(height))
                     for r, y in child)


def actual_components(height):
    actual = source(height)
    full, pairs = family.actual_component_laws(height, actual)
    return actual, full, pairs


def prefix_capacity(height, leaves):
    """Maximal subprobability mass with absolute prefix caps 3^-j."""
    family.integer(height, 0, 'height')
    family.need(type(leaves) in (set, frozenset, list, tuple)
                and all(type(y) is int and 0 <= y < 7**height for y in leaves),
                'literal projection leaves required')
    def visit(h, selected):
        if not selected:
            return F()
        if h == 0:
            return F(1)
        groups = defaultdict(set)
        for y in selected:
            groups[y % 7].add(y // 7)
        return min(F(1), sum((visit(h-1, child) for child in groups.values()), F())/3)
    return visit(height, set(leaves))


def source_control(height):
    children = source_children(height)
    h = height-1
    actual = source(height)
    family.need(len(actual) == 5**height+2, 'sharp source size')
    family.need(family.layout_api.contains_bary_tree({y for _, y in actual}, height, 5),
                'source full five-tree')
    for pair in combinations(family.ROWS, 2):
        family.need(family.layout_api.contains_bary_tree({y for r, y in actual if r in pair}, height, 3),
                    'source pair-ternary tree')
    rows, row_one = [], []
    for c, child in enumerate(children):
        one = {y for r, y in child if r == 1}
        other = {y for r, y in child if r != 1}
        family.need(not one & other and len(one | other) == 5**h, 'unambiguous row-one projection')
        row_one.append(F(len(one), 5**h))
        if c:
            good = {pair for pair in combinations(family.ROWS, 2)
                    if family.layout_api.contains_bary_tree({y for r, y in child if r in pair}, h, 3)}
            family.need(good == {pair for pair in combinations(family.ROWS, 2) if c in pair},
                        'actual clean star signature')
            measured = tuple(prefix_capacity(h, {y for r, y in child if r == s}) for s in family.ROWS)
            expected = tuple(F(1) if s == 1 else F(2 if s == c else 1, 3) for s in family.ROWS)
            family.need(measured == expected, 'actual clean row capacities')
            rows.append(measured)
    old_bound = fast_obstruction.five_decay_bounds(height)
    family.need(min(row_one) == old_bound['row1_lower'], 'all-root-weight concentration bound')
    return {'height': height, 'source_points': len(actual), 'clean_capacity_matrix': rows,
            'five_decay_conditional_row1_masses': row_one,
            'all_five_decay_root_mixtures_cost_lower': old_bound['cost_lower']}


def analytic_bound(height):
    family.integer(height, 3, 'height')
    d = previous.actual_profile_formula(height)
    exact_error = 3*ALPHA*sum(((2*j+1)*v for j, v in enumerate(d)), F())
    simple_error = SIMPLE_ERROR_CONSTANT*F(3, 5)**height
    family.need(exact_error <= simple_error, 'simple transport error')
    family.need(reference_bound(height) <= REFERENCE_LIMIT, 'reference tail ceiling')
    target = family.layout_api.default_target(height)
    return {'height': height, 'full_mismatch_profile': d,
            'profile_upper': reference_bound(height)+exact_error,
            'simple_upper': REFERENCE_LIMIT+simple_error,
            'target': target, 'simple_margin': target-REFERENCE_LIMIT-simple_error}


def generic_controls():
    full = {(4 if c == 6 else 1, c): F(1, 5) for c in range(2, 7)}
    pair_columns = {(2, 3): (0, 3, 6), (2, 4): (1, 2, 5), (3, 4): (0, 4, 6)}
    pairs = {p: {(p[0], c): F(1, 3) for c in pair_columns[p]} for p in family.PAIRS}
    actual = set(full).union(*(set(p) for p in pairs.values()))
    checked = verify_interface(1, actual, full, pairs)
    _, profile = previous.profile_bound(1, checked['law'])
    for phases in product(range(1), range(5), range(7), range(35)):
        cost = sum((w*family.layout_api.literal_layout_cost(1, phases, p)
                    for p, w in checked['law'].items()), F())
        family.need(cost <= checked['all_phase_upper'] and cost <= profile, 'generic all-phase bound')
    bad_pair = deepcopy(pairs)
    bad_pair[(2, 3)][2, 0] += F(1, 12)
    bad_pair[(2, 3)][2, 3] -= F(1, 12)
    bad_full = deepcopy(full)
    bad_full[1, 2] += F(1, 10)
    bad_full[1, 3] -= F(1, 10)
    outside = deepcopy(pairs)
    outside[(2, 3)][4, 0] = outside[(2, 3)].pop((2, 0))
    cases = [
        ('boolean_height', 'height must', lambda: verify_interface(True, actual, full, pairs)),
        ('unsupported_full', 'unsupported', lambda: verify_interface(1, actual-{(1, 2)}, full, pairs)),
        ('pair_root_cap', 'pair prefix cap', lambda: verify_interface(1, actual, full, bad_pair)),
        ('full_root_cap', 'full prefix cap', lambda: verify_interface(1, actual, bad_full, pairs)),
        ('outside_pair_row', 'outside-row', lambda: verify_interface(1, actual | {(4, 0)}, full, outside)),
        ('deeper_full_cap', 'full prefix cap', lambda: verify_interface(2, actual, full, pairs)),
    ]
    rejected = []
    for name, reason, operation in cases:
        try:
            operation()
        except ValueError as error:
            family.need(reason in str(error), 'wrong rejection reason for '+name)
            rejected.append(name)
        else:
            raise ValueError('malformed interface accepted: '+name)
    return {'literal_layouts': 1225, 'unprescribed_component_root_columns': True, 'rejected': rejected}


def self_check():
    expected = {3: F(13271, 2475), 4: F(601363, 111375), 5: F(203039, 37125),
                6: F(27503599, 5011875), 7: F(688102709, 125296875)}
    finite = []
    for k, value in expected.items():
        control = source_control(k)
        actual, full, pairs = actual_components(k)
        checked = verify_interface(k, actual, full, pairs)
        family.need(checked['full_mismatch_profile'] == previous.actual_profile_formula(k),
                    'new seed source has the stated exact disagreement profile')
        profile, upper = previous.profile_bound(k, checked['law'])
        target = family.layout_api.default_target(k)
        family.need(upper == value and target-upper > F(1, 20), 'finite uniform target margin')
        finite.append({'source': control, 'profile': profile, 'profile_upper': upper,
                       'target_margin': target-upper})
    threshold = analytic_bound(8)
    family.need(threshold['simple_margin'] == F(99823733, 1804275000) > F(1, 20),
                'all-height threshold arithmetic')
    return {'scope': 'actual full/pair prefix-cap interface without prescribed root geometry; one law on every recursive seed source K>=3; ordinary proof, no Lean certification',
            'root': root_controls(), 'generic': generic_controls(),
            'finite_actual_sources': finite, 'height_eight_threshold': threshold}


if __name__ == '__main__':
    print(json.dumps(family.jsonable(self_check()), indent=2))
