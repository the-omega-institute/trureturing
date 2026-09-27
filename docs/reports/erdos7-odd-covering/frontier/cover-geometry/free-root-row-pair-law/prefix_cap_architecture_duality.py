#!/usr/bin/env python3
"""Exact dual prices for full-five plus all six pair-ternary cap laws.

The source, seven component families, and full original-layout mixture
are common to every calculation. Components range over all probabilities
with the prescribed pure prefix caps, not just uniform complete trees.
Greedy laminar bases and an independent threshold-capacity formula give
the minimum price in each entire component polytope.

With no arguments, run exact implementation and boundary controls.
With a JSON path, read height, source=[[row,residue],...], layouts as in
prime_layout_mixture_certificate.py, and an optional exact target.
Output is one lower certificate for the restricted architecture. A value
at or below the target does not certify that the architecture succeeds.
Only standard-library arithmetic is used; no files are written.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import json
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

import prime_layout_mixture_certificate as layouts
from free_root_row_pair_law import prefix_capacity as ternary_prefix_capacity

ROWS = layouts.ROWS
FAMILIES = ((ROWS, 5),) + tuple((pair, 3) for pair in combinations(ROWS, 2))
need = layouts.require


def _source(height, source):
    layouts.original_divisors(height)
    need(type(source) in (tuple, list, set, frozenset) and source,
         'nonempty actual source required')
    need(all(type(p) in (tuple, list) and len(p) == 2
             and type(p[0]) is int and p[0] in ROWS
             and type(p[1]) is int and 0 <= p[1] < 7**height for p in source),
         'literal source point outside the carrier')
    result = tuple(sorted(tuple(p) for p in source))
    need(len(set(result)) == len(result), 'duplicate source points')
    return result


def prefix_capacity(height, branching, leaves):
    """Maximal subprobability mass with absolute pure caps branching**(-j).

This is normalized laminar rank, not the Boolean complete-tree predicate.
The ternary case directly reuses report 422's existing capacity routine.
"""
    layouts.original_divisors(height)
    need(type(branching) is int and 1 <= branching <= 7, 'branching must be in 1..7')
    need(type(leaves) in (tuple, list, set, frozenset)
         and all(type(y) is int and 0 <= y < 7**height for y in leaves),
         'literal projection leaves required')
    if branching == 3:
        return ternary_prefix_capacity(height, leaves)

    def visit(h, selected):
        if not selected:
            return F()
        if h == 0:
            return F(1)
        children = defaultdict(set)
        for y in selected:
            children[y % 7].add(y // 7)
        return min(F(1), sum((visit(h-1, child) for child in children.values()), F()) / branching)

    return visit(height, set(leaves))


def cap_minimum(height, source, allowed_rows, branching, prices):
    """Minimize arbitrary exact point prices over one whole cap polytope.

Return a uniform laminar basis attaining the minimum, and independently
evaluate the threshold-capacity formula. The returned basis need not be
the leaves of a complete branching-ary tree.
"""
    source = _source(height, source)
    need(type(allowed_rows) in (tuple, list) and allowed_rows
         and all(type(r) is int and r in ROWS for r in allowed_rows)
         and len(set(allowed_rows)) == len(allowed_rows), 'distinct allowed rows required')
    need(type(prices) is dict and set(prices) == set(source), 'one price per actual source point required')
    prices = {p: layouts.exact(v, 'point price') for p, v in prices.items()}
    support = tuple(p for p in source if p[0] in allowed_rows)
    need(prefix_capacity(height, branching, {y for _, y in support}) == 1,
         'component cap probability is infeasible')
    caps = tuple(branching**(height-j) for j in range(height+1))
    counts = defaultdict(int)
    basis = []
    for point in sorted(support, key=lambda p: (prices[p], p)):
        path = tuple((j, point[1] % 7**j) for j in range(height+1))
        if all(counts[key] < caps[key[0]] for key in path):
            basis.append(point)
            for key in path:
                counts[key] += 1
    need(len(basis) == branching**height, 'greedy failed to produce a full laminar basis')
    value = sum((prices[p] for p in basis), F()) / branching**height
    levels = sorted({prices[p] for p in support})
    layers = tuple((t, prefix_capacity(height, branching,
                                     {y for r, y in support if prices[r, y] <= t})) for t in levels)
    integral = levels[-1] - sum(((u-t)*capacity for (t, capacity), (u, _) in zip(layers, layers[1:])), F())
    need(value == integral, 'greedy and threshold-capacity prices disagree')
    return {'rows': tuple(allowed_rows), 'branching': branching,
            'value': value, 'basis': tuple(basis), 'mass_per_point': F(1, branching**height),
            'threshold_layers': layers, 'threshold_integral': integral}


def audit_architecture_dual(height, source, components, target=None):
    """Audit one actual layout mixture against every permitted component law.

Strict lower > target refutes this architecture on this same admissible
source. It does not refute the unrestricted supported-law problem.
"""
    source = _source(height, source)
    need(all(layouts.contains_bary_tree({y for r, y in source if r in rows}, height, b)
             for rows, b in FAMILIES), 'actual source must satisfy all seven complete-tree premises')
    target = layouts.default_target(height) if target is None else layouts.exact(target, 'target')
    carrier_prices = layouts.evaluate_layout_mixture(height, components)
    prices = {p: carrier_prices[p] for p in source}
    minima = tuple(cap_minimum(height, source, rows, b, prices) for rows, b in FAMILIES)
    lower = min(item['value'] for item in minima)
    return {'height': height, 'source': source, 'original_divisors': layouts.original_divisors(height),
            'target': target, 'default_target': layouts.default_target(height),
            'component_minima': minima, 'architecture_lower_bound': lower,
            'strict_architecture_obstruction': lower > target,
            'default_target_obstruction': lower > layouts.default_target(height),
            'prices': tuple((r, y, prices[r, y]) for r, y in source),
            'scope': 'one complete-layout mixture; all actual cap components and free convex weights; no unrestricted source-minimax claim'}


def strict_architecture_loss():
    """Refute equality of the full cap architecture and unrestricted laws.

This is not an obstruction at the default target. Both exact oracles
below retain all independent original phases for the comparison law.
"""
    from recursive_minimum_source_common_law import law
    from actual_root_tail_obstruction import exact_height_two
    from independent_layout_tree_dp import IndependentLayoutTreeDP

    source = set(law(2))
    mixture = [(F(611 if r < 4 else 971, 23020), layouts._aligned_layout(2, r, r+7*d))
               for r in ROWS for d in range(5)]
    mixture += [(F(3000, 23020), (0, r, 0, r, 0, 56*r)) for r in (1, 2, 3)]
    result = audit_architecture_dual(2, source, mixture)
    lower = F(21021, 4604)
    need({item['value'] for item in result['component_minima']} == {lower},
         'all seven exact component minima')
    expected_prices = {(r, y): F(25037 if y == 0 else 19037 if y % 7 == 0 and r < 4
                                else 12917 if y % 7 == 0 else 21013 if r < 4 else 23053, 4604)
                       for r, y in source}
    need({(r, y): v for r, y, v in result['prices']} == expected_prices,
         'literal layout mixture disagrees with price table')
    weights = {(r, y): 280 if y == 0 else 530 if y % 7 == 0 and r < 4
               else 575 if y % 7 == 0 else 348 if r < 4 else 355 for r, y in source}
    need(sum(weights.values()) == 10000, 'unrestricted comparison probability')
    enumerated = exact_height_two(weights)
    points = tuple(sorted(source))
    separated = IndependentLayoutTreeDP(2, points).separate(tuple(weights[p] for p in points))
    upper = F(4549, 1000)
    need(enumerated['value'] == separated['value'] == upper < lower < layouts.default_target(2),
         'independent exact architecture-loss certificate')
    need(not result['default_target_obstruction'], 'loss below the default target is not a target obstruction')
    return {'height': 2, 'source_points': len(source), 'complete_layouts_in_dual': len(mixture),
            'seven_component_minima': tuple(item['value'] for item in result['component_minima']),
            'unrestricted_law_maximum': upper, 'strict_loss_lower_bound': lower-upper,
            'target': layouts.default_target(2), 'default_target_obstruction': result['default_target_obstruction'],
            'comparison_law_denominator': 10000, 'comparison_root_layouts': enumerated['root_layouts'],
            'comparison_attaining_layout': enumerated['layout']}


def self_check():
    # Exhaust every basis and every binary price on a small laminar carrier.
    # Two row labels share some Y leaves: leaf capacity must count them together.
    source = {(1, a+7*d) for a in range(3) for d in range(2)} | {(2, 0), (2, 8)}
    points = tuple(sorted(source))
    bases = tuple(chosen for chosen in combinations(points, 4)
                  if len({y for _, y in chosen}) == 4
                  and all(sum(y % 7 == a for _, y in chosen) <= 2 for a in range(7)))
    need(bases, 'independent exhaustive basis list')
    count = 0
    for values in product((0, 1), repeat=len(points)):
        prices = dict(zip(points, values))
        result = cap_minimum(2, source, (1, 2), 2, prices)
        brute = min(sum((F(prices[p]) for p in basis), F()) / 4 for basis in bases)
        need(result['value'] == brute, 'greedy disagrees with exhaustive bases')
        count += 1
    prices = {p: F((i*i+3*i) % 11-5, i % 3+1) for i, p in enumerate(points)}
    rational = cap_minimum(2, source, (1, 2), 2, prices)
    need(rational['value'] == min(sum((prices[p] for p in basis), F()) / 4 for basis in bases),
         'signed rational-price basis comparison')
    zero = cap_minimum(0, {(1, 0), (2, 0)}, (1, 2), 5, {(1, 0): F(2), (2, 0): F(-1)})
    need(zero['value'] == -1 and zero['basis'] == ((2, 0),), 'height-zero parallel leaf control')

    leaves = {a+7*d for a, n in enumerate((2, 2, 2, 2, 1)) for d in range(n)}
    non_tree = {(1, y) for y in leaves}
    basis = cap_minimum(2, non_tree, (1, 2), 3, {p: F(p[1]) for p in non_tree})
    need(len(basis['basis']) == 9 and prefix_capacity(2, 3, leaves) == 1
         and not layouts.contains_bary_tree(leaves, 2, 3), 'cap basis must not be replaced by a complete tree')
    need(F(1, 9) / F(2, 9) == F(1, 2) > F(1, 3), 'conditioning changes the inherited cap budget')

    # Reuse report 400's constant-price layout mixture, including all labels.
    carrier = set(product(ROWS, range(7)))
    mixture = [(F(1, 28), layouts._aligned_layout(1, r, y)) for r, y in sorted(carrier)]
    audit = audit_architecture_dual(1, carrier, mixture, F(2))
    boundary = audit_architecture_dual(1, carrier, mixture, F(5, 2))
    default = audit_architecture_dual(1, carrier, mixture)
    need({item['value'] for item in audit['component_minima']} == {F(5, 2)}
         and audit['strict_architecture_obstruction'] and not audit['default_target_obstruction']
         and not boundary['strict_architecture_obstruction'] and not default['strict_architecture_obstruction'],
         'custom/default and strict/equality certificate semantics')
    incompatible = audit_architecture_dual(1, carrier, [(1, (0, 1, 0, 6))])
    actual_prices = {(r, y): v for r, y, v in incompatible['prices']}
    need(actual_prices[1, 0] == actual_prices[1, 6] == 9, 'independent incompatible phases were changed')

    malformed = [
        lambda: prefix_capacity(True, 3, {0}),
        lambda: prefix_capacity(1, True, {0}),
        lambda: prefix_capacity(1, 3, {7}),
        lambda: cap_minimum(1, [(1, 0), (1, 0)], (1, 2), 3, {(1, 0): 0}),
        lambda: cap_minimum(0, {(1, 0)}, (1, 1), 3, {(1, 0): 0}),
        lambda: cap_minimum(0, {(1, 0)}, (1,), 3, {(1, 0): 0.5}),
        lambda: cap_minimum(0, {(1, 0)}, (1,), 3, {}),
        lambda: cap_minimum(1, {(1, 0)}, (1,), 3, {(1, 0): 0}),
        lambda: audit_architecture_dual(2, non_tree, [(1, (0, 1, 0, 1, 0, 1))]),
        lambda: audit_architecture_dual(1, carrier, [(1, (0, 1, 0))]),
        lambda: audit_architecture_dual(1, carrier, [(F(1, 2), (0, 1, 0, 1))]),
        lambda: audit_architecture_dual(1, carrier, [(-1, (0, 1, 0, 1)), (2, (0, 2, 0, 2))]),
    ]
    for operation in malformed:
        try:
            operation()
        except ValueError:
            continue
        raise ValueError('malformed control was accepted')
    return {'scope': 'implementation and countermodel controls; no universal architecture bound established',
            'binary_price_assignments': count, 'independently_enumerated_bases': len(bases),
            'signed_rational_minimum': rational['value'], 'height_zero_minimum': zero['value'],
            'non_tree_cap_basis': {'root_leaf_counts': (2, 2, 2, 2, 1), 'leaves': tuple(sorted(leaves)),
                                   'capacity': prefix_capacity(2, 3, leaves), 'complete_ternary_tree': False,
                                   'two_leaf_child_conditional_mass': F(1, 2)},
            'reused_constant_layout_mixture_minimum': audit['architecture_lower_bound'],
            'strict_architecture_loss': strict_architecture_loss(),
            'malformed_controls': len(malformed)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', help='exact JSON certificate; omit for controls')
    args = parser.parse_args()
    if args.input is None:
        result = self_check()
    else:
        payload = json.loads(Path(args.input).read_text())
        need(type(payload) is dict and {'height', 'source', 'layouts'} <= set(payload)
             and set(payload) <= {'height', 'source', 'layouts', 'target'}, 'JSON certificate fields')
        need(type(payload['layouts']) is list, 'JSON layouts must be a list')
        components = []
        for item in payload['layouts']:
            need(type(item) is dict and set(item) == {'weight', 'phases'}, 'JSON layout fields')
            components.append((layouts._json_exact(item['weight'], 'weight'), item['phases']))
        target = layouts._json_exact(payload['target'], 'target') if 'target' in payload else None
        result = audit_architecture_dual(payload['height'], payload['source'], components, target)
    print(json.dumps(layouts._jsonable(result), indent=2))


if __name__ == '__main__':
    main()
