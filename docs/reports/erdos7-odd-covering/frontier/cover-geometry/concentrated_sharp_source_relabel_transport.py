#!/usr/bin/env python3
"""Actual concentrated sharp sources and same-Y row-relabel transport.

Uses the sibling source/signature and original-divisor APIs, exact rational
arithmetic, and explicit runtime validation which remains active under -O.
The all-height estimate is analytic; finite source controls do not prove it
by enumeration. Running this file prints exact controls and writes no files.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import copy
import json

import prime_layout_mixture_certificate as layout_api
import row_summary_interface_obstructions as signature_api

ROWS = (1, 2, 3, 4)
PAIRS = ((2, 3), (2, 4), (3, 4))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, lower, name):
    need(type(value) is int and value >= lower,
         name + ' must be a literal integer >= ' + str(lower))
    return value


def rational(value, name):
    need(type(value) in (int, F), name + ' must be an integer or Fraction')
    return F(value)


def point(height, value):
    need(type(value) is tuple and len(value) == 2
         and type(value[0]) is int and value[0] in ROWS
         and type(value[1]) is int and 0 <= value[1] < 7**height,
         'literal point outside four-row carrier')
    return value


def points(height, values):
    integer(height, 0, 'height')
    need(type(values) in (tuple, list, set, frozenset) and values,
         'nonempty finite source required')
    result = frozenset(point(height, p) for p in values)
    need(len(result) == len(values), 'duplicate source points')
    return result


def probability(height, law):
    integer(height, 0, 'height')
    need(type(law) is dict and law, 'nonempty exact probability dictionary required')
    checked = {point(height, p): rational(w, 'mass') for p, w in law.items()}
    need(all(w > 0 for w in checked.values()), 'stored masses must be positive')
    need(sum(checked.values(), F()) == 1, 'probability must have total mass one')
    return checked


def prefix_masses(law, depth):
    integer(depth, 0, 'depth')
    pure, joint = defaultdict(F), defaultdict(F)
    for (r, y), mass in law.items():
        pure[y % 7**depth] += mass
        joint[r, y % 7**depth] += mass
    return dict(pure), dict(joint)


def mixture(height, components):
    result, total = defaultdict(F), F()
    for weight, law in components:
        weight = rational(weight, 'mixture coefficient')
        need(weight >= 0, 'nonnegative mixture coefficient required')
        total += weight
        for p, mass in probability(height, law).items():
            result[p] += weight * mass
    need(total == 1, 'mixture coefficients must sum to one')
    return probability(height, {p: w for p, w in result.items() if w})


def clean_source(height, row):
    integer(height, 0, 'height')
    need(type(row) is int and row in ROWS, 'literal clean signature row required')
    if height == 0:
        return frozenset({(row, 0)})
    return frozenset(signature_api.signature_source(height, 'star', row, 1))


def one_surplus_source(height, missing):
    integer(height, 0, 'height')
    need(type(missing) in (tuple, list) and len(missing) == 2
         and all(type(r) is int and r in ROWS for r in missing)
         and missing[0] != missing[1], 'two distinct missing-pair rows required')
    result = {(r, 0) for r in ROWS if r not in missing}
    for h in range(1, height + 1):
        result = {(r, 7*y) for r, y in result}
        for c in ROWS:
            result.update((r, c+7*y) for r, y in clean_source(h-1, c))
    return frozenset(result)


def source(height):
    """Construct the concentrated two-one-surplus sharp family at any K>=2."""
    integer(height, 2, 'height')
    h = height - 1
    result = {(r, 7*y) for r, y in one_surplus_source(h, (1, 2))}
    result.update((r, 1+7*y) for r, y in one_surplus_source(h, (1, 3)))
    for c, row in ((2, 1), (3, 2), (4, 3)):
        result.update((r, c+7*y) for r, y in clean_source(h, row))
    return frozenset(result)


def uniform_tree_law(height, actual_source, allowed_rows, branching):
    """Select the least good child columns, then the least allowed leaf row."""
    actual_source = points(height, actual_source)
    need(type(allowed_rows) in (tuple, list) and allowed_rows
         and all(type(r) is int and r in ROWS for r in allowed_rows)
         and len(set(allowed_rows)) == len(allowed_rows), 'distinct allowed rows required')
    need(type(branching) is int and 1 <= branching <= 7, 'branching must be in 1..7')

    def visit(selected, depth):
        if depth == 0:
            return [(min(r for r, _ in selected), 0)] if selected else None
        children = defaultdict(list)
        for r, y in selected:
            children[y % 7].append((r, y // 7))
        good = []
        for c, child in sorted(children.items()):
            leaves = visit(child, depth-1)
            if leaves is not None:
                good.append((c, leaves))
        if len(good) < branching:
            return None
        return [(r, c+7*y) for c, leaves in good[:branching] for r, y in leaves]

    selected = visit([p for p in actual_source if p[0] in allowed_rows], height)
    need(selected is not None, 'source lacks requested row-restricted tree')
    return probability(height, {p: F(1, branching**height) for p in selected})


def actual_component_laws(height, actual_source=None):
    """Return the supported full-five law and the three supported pair laws."""
    integer(height, 2, 'height')
    actual_source = source(height) if actual_source is None else points(height, actual_source)
    full = uniform_tree_law(height, actual_source, ROWS, 5)
    pairs = {pair: uniform_tree_law(height, actual_source, pair, 3) for pair in PAIRS}
    return full, pairs


def four_component_mixture(height, full, pairs):
    need(type(pairs) is dict and set(pairs) == set(PAIRS), 'three named pair laws required')
    return mixture(height, [(F(5, 13), full)] + [(F(8, 39), pairs[p]) for p in PAIRS])


def common_law(height):
    """Construct the fixed four-component probability on the actual source."""
    full, pairs = actual_component_laws(height)
    return four_component_mixture(height, full, pairs)


def coupling_marginals(height, coupling):
    integer(height, 0, 'height')
    need(type(coupling) is dict and coupling, 'nonempty same-Y coupling required')
    left, right = defaultdict(F), defaultdict(F)
    mismatch = F()
    for key, value in coupling.items():
        need(type(key) is tuple and len(key) == 3, 'coupling key must be (row, row_bar, Y)')
        r, s, y = key
        point(height, (r, y))
        point(height, (s, y))
        mass = rational(value, 'coupling mass')
        need(mass > 0, 'stored coupling masses must be positive')
        left[r, y] += mass
        right[s, y] += mass
        if r != s:
            mismatch += mass
    return probability(height, dict(left)), probability(height, dict(right)), mismatch


def row_relabel_shell_bound(height, branching, mismatch):
    """Arithmetic RHS of the same-Y lemma; hypotheses checked by its caller."""
    integer(height, 0, 'height')
    need(type(branching) is int and 1 <= branching <= 7, 'branching must be in 1..7')
    mismatch = rational(mismatch, 'mismatch')
    need(0 <= mismatch <= 1, 'mismatch must lie in [0,1]')
    return sum((3*(2*j+1)*min(mismatch, F(1, branching**j))
                for j in range(height+1)), F())


def verify_same_y_transport(height, branching, left, right, coupling):
    """Check actual coupling hypotheses and return the uniform all-layout bound."""
    left, right = probability(height, left), probability(height, right)
    coupled_left, coupled_right, mismatch = coupling_marginals(height, coupling)
    need(left == coupled_left and right == coupled_right, 'coupling marginals do not match laws')
    bound = row_relabel_shell_bound(height, branching, mismatch)
    for j in range(height+1):
        marginal, _ = prefix_masses(left, j)
        need(max(marginal.values()) <= F(1, branching**j), 'seven-adic prefix cap violated')
    return {'mismatch': mismatch, 'uniform_layout_difference_bound': bound}


def comparison_couplings(height, full, pairs):
    """Keep all Y coordinates, changing only full labels and two pair endpoints."""
    integer(height, 2, 'height')
    probability(height, full)
    need(type(pairs) is dict and set(pairs) == set(PAIRS), 'three named pair laws required')
    full_coupling = {(r, 1, y): mass for (r, y), mass in full.items()}
    pair_couplings = {}
    for pair in PAIRS:
        law = probability(height, pairs[pair])
        need(all(r in pair for r, y in law), 'pair law has an outside row')
        for y in (0, 1):
            terminal = [(r, m) for (r, z), m in law.items() if z == y]
            need(len(terminal) == 1 and terminal[0][1] == F(1, 3**height),
                 'one actual uniform terminal point required in each exceptional column')
        coupling = defaultdict(F)
        for (r, y), mass in law.items():
            if y in (0, 1):
                for s in pair:
                    coupling[r, s, y] += mass/2
            else:
                coupling[r, r, y] += mass
        pair_couplings[pair] = dict(coupling)
    _, full_bar, _ = coupling_marginals(height, full_coupling)
    pairs_bar = {p: coupling_marginals(height, pair_couplings[p])[1] for p in PAIRS}
    return full_bar, pairs_bar, full_coupling, pair_couplings


def family_certificate(height):
    """Construct actual probabilities and explicit comparison couplings."""
    actual_source = source(height)
    full, pairs = actual_component_laws(height, actual_source)
    full_bar, pairs_bar, full_coupling, pair_couplings = comparison_couplings(height, full, pairs)
    return {'height': height, 'source': actual_source, 'full': full, 'pairs': pairs,
            'nu': four_component_mixture(height, full, pairs), 'full_bar': full_bar,
            'pairs_bar': pairs_bar, 'full_coupling': full_coupling, 'pair_couplings': pair_couplings}


def ideal_root_table():
    table = {(1, c): F(1, 13) for c in range(5)}
    table.update({(r, c): F(8, 117) for r, c in product((2, 3, 4), (0, 1))})
    table[2, 3], table[3, 4] = F(16, 117), F(8, 117)
    return table


def root_controls():
    """Evaluate original CRT divisor phases directly, including inactive choices."""
    table, values = ideal_root_table(), []
    for a, b, s, d in product(range(5), range(7), range(5), range(7)):
        mixed_phase = d+7*((s-d)*3 % 5)
        phases = (0, a, b, mixed_phase)
        value = sum((w*layout_api.literal_layout_cost(1, phases, p) for p, w in table.items()), F())
        values.append((value, (a, b, s, d)))
    largest = max(v for v, _ in values)
    attainers = {p for v, p in values if v == largest}
    expected = ((432, 425, 409, 409), (373, 432, 368, 368),
                (349, 352, 360, 344), (325, 328, 320, 336))
    measured = tuple(tuple(117*max(v for v, p in values if p[0] == a and p[2] == s)
                           for s in ROWS) for a in ROWS)
    need(largest == F(48, 13), 'wrong independent root maximum')
    need(attainers == {(1, 0, 1, 0), (1, 1, 1, 1), (2, 3, 2, 3)}, 'wrong root attainers')
    need(measured == expected, 'wrong root row-phase table')
    return {'layouts': len(values), 'maximum': largest, 'attainers': sorted(attainers), 'row_table_times_117': measured}


def analytic_bounds(height):
    """Evaluate the proved family estimates without constructing 5**K leaves."""
    integer(height, 2, 'height')
    delta = F(3, 5)**(height-2)-F(7, 5**height)
    transport = F(5, 13)*row_relabel_shell_bound(height, 5, delta)
    transport += F(8, 13)*row_relabel_shell_bound(height, 3, F(1, 3**height))
    exact_shell_upper = F(587, 104)+transport
    simple_upper = F(149, 26)+F(135, 13)*F(3, 5)**(height-2)+F(24*(height+1)**2, 13*3**height)
    target = layout_api.default_target(height)
    need(exact_shell_upper <= simple_upper, 'shell simplification failed')
    return {'height': height, 'full_mismatch': delta, 'shell_upper': exact_shell_upper,
            'simple_upper': simple_upper, 'target': target, 'simple_margin': target-simple_upper}


def verify_family_certificate(certificate):
    expected = {'height', 'source', 'full', 'pairs', 'nu', 'full_bar', 'pairs_bar', 'full_coupling', 'pair_couplings'}
    need(type(certificate) is dict and set(certificate) == expected, 'complete family certificate schema required')
    K = integer(certificate['height'], 2, 'height')
    actual_source = points(K, certificate['source'])
    need(actual_source == source(K), 'certificate source is not the stated sharp family')
    need(len(actual_source) == 5**K+2, 'wrong sharp source size')
    need(layout_api.contains_bary_tree({y for _, y in actual_source}, K, 5), 'source lacks full five-tree')
    for pair in combinations(ROWS, 2):
        need(layout_api.contains_bary_tree({y for r, y in actual_source if r in pair}, K, 3),
             'source lacks one of six pair trees')
    full = probability(K, certificate['full'])
    pairs, pairs_bar, pair_couplings = (certificate[k] for k in ('pairs', 'pairs_bar', 'pair_couplings'))
    need(all(type(d) is dict and set(d) == set(PAIRS) for d in (pairs, pairs_bar, pair_couplings)),
         'three matching named pair components required')
    for rows, branching, law in [(ROWS, 5, full)] + [(p, 3, pairs[p]) for p in PAIRS]:
        law = probability(K, law)
        need(set(law) <= actual_source and all(r in rows for r, _ in law), 'component law is not actually supported')
        need(len(law) == branching**K and all(w == F(1, branching**K) for w in law.values()),
             'component is not an actual uniform tree law')
        need(len({y for _, y in law}) == len(law)
             and layout_api.contains_bary_tree({y for _, y in law}, K, branching), 'component projection is not one complete tree')
    nu = probability(K, certificate['nu'])
    need(nu == four_component_mixture(K, full, pairs), 'actual common mixture mismatch')
    need(set(nu) <= actual_source, 'common law has unsupported mass')
    full_check = verify_same_y_transport(K, 5, full, certificate['full_bar'], certificate['full_coupling'])
    pair_checks = {p: verify_same_y_transport(K, 3, pairs[p], pairs_bar[p], pair_couplings[p]) for p in PAIRS}
    bounds = analytic_bounds(K)
    need(full_check['mismatch'] == bounds['full_mismatch'], 'wrong full relabelling mismatch')
    need(all(c['mismatch'] == F(1, 3**K) for c in pair_checks.values()), 'wrong terminal mismatch')
    counts = tuple(5**K*sum((w for (r, _), w in full.items() if r == a), F()) for a in ROWS)
    need(counts == (5**K-25*3**(K-2)+7, 10*3**(K-2)-2, 10*3**(K-2)-2, 5*3**(K-2)-3),
         'wrong actual full-five row counts')
    ideal = four_component_mixture(K, certificate['full_bar'], pairs_bar)
    need(prefix_masses(ideal, 1)[1] == ideal_root_table(), 'wrong comparison root table')
    for j in range(1, K+1):
        pure, joint = prefix_masses(ideal, j)
        need(max(pure.values()) <= F(5, 13*5**j)+F(8, 13*3**j), 'comparison pure prefix cap failed')
        need(max(joint.values()) <= F(16, 39*3**j), 'comparison joint prefix cap failed')
    return {'height': K, 'source_size': len(actual_source), 'six_pair_trees': True,
            'actual_four_component_law': True, 'full_row_counts': counts,
            'full_transport': full_check, 'pair_transport': [pair_checks[p] for p in PAIRS], 'bounds': bounds}


def small_height_failure_control():
    """One literal layout refutes success of this fixed recipe at height two."""
    phases = (0, 2, 3, 17, 3, 52)
    nu = common_law(2)
    cost = sum((w*layout_api.literal_layout_cost(2, phases, p)
                for p, w in nu.items()), F())
    target = layout_api.default_target(2)
    need(cost == F(10483, 1755), "wrong height-two literal lower witness")
    need(cost-target == F(1513, 1755) > 0, "height-two recipe failure witness lost")
    return {"height": 2, "original_divisors": layout_api.original_divisors(2),
            "phases": phases, "literal_cost": cost, "target": target,
            "excess": cost-target, "scope": "failure of this fixed law; no source obstruction or maximum claim"}


def expect_rejection(name, operation):
    try:
        operation()
    except ValueError:
        return name
    raise ValueError('malformed control was accepted: '+name)


def malformed_controls():
    sample = family_certificate(2)
    cases = [('boolean_height', lambda: source(True)),
             ('repeated_missing_row', lambda: one_surplus_source(1, (1, 1))),
             ('out_of_range_mismatch', lambda: row_relabel_shell_bound(2, 5, F(3, 2))),
             ('false_projection_cap', lambda: verify_same_y_transport(1, 5, {(1, 0): F(1)},
                 {(1, 0): F(1)}, {(1, 1, 0): F(1)}))]
    floating = copy.deepcopy(sample)
    p = next(iter(floating['nu']))
    floating['nu'][p] = float(floating['nu'][p])
    cases.append(('floating_common_mass', lambda: verify_family_certificate(floating)))
    unsupported = copy.deepcopy(sample)
    p, w = unsupported['nu'].popitem()
    outside = next(z for z in product(ROWS, range(49)) if z not in unsupported['source'])
    unsupported['nu'][outside] = w
    cases.append(('unsupported_common_mass', lambda: verify_family_certificate(unsupported)))
    wrong_marginal = copy.deepcopy(sample)
    coupling = wrong_marginal['full_coupling']
    (r, s, y), w = coupling.popitem()
    coupling[r, 2 if s == 1 else 1, y] = w
    cases.append(('wrong_coupling_marginal', lambda: verify_family_certificate(wrong_marginal)))
    cases.append(('coupling_changes_Y', lambda: coupling_marginals(1, {(1, 1, 0, 1): F(1)})))
    return [expect_rejection(name, operation) for name, operation in cases]


def self_check():
    root = root_controls()
    family = [verify_family_certificate(family_certificate(K)) for K in range(2, 6)]
    base = analytic_bounds(10)
    need(base['simple_margin'] == F(3623071823, 39981093750), 'wrong K10 threshold arithmetic')
    need(base['simple_margin'] > F(9, 100), 'K10 misses the uniform nine-hundredths margin')
    return {'root': root, 'family_controls': family, 'threshold_base': base,
            'small_height_failure': small_height_failure_control(),
            'malformed_controls_rejected': malformed_controls(),
            'scope': 'actual constructors and exact finite checks; all-height monotonicity is proved in the companion report'}


def jsonable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [jsonable(v) for v in value]
    return value


if __name__ == '__main__':
    print(json.dumps(jsonable(self_check()), indent=2, sort_keys=True))
