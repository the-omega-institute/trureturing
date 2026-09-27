#!/usr/bin/env python3
"""Classify literal 65/63 equality sources and construct one private law.

The ordinary theorem gives an original-label LCM upper bound 25/3 for any
source containing the certified private skeleton. These exact controls do
not certify Lean, arithmetic residual realization, or unrestricted #7.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked_source(source):
    points = list(source)
    require(points and all(type(p) in (tuple, list) and len(p) == 3
                           and all(type(v) is int for v in p) for p in points),
            'literal integer source triples')
    points = [tuple(p) for p in points]
    require(len(points) == len(set(points)), 'distinct source triples')
    require(all(0 <= r < 5 and 0 <= c < 5 and 0 <= y < 49 for r, c, y in points),
            'source lies in Z/25 times Z/49')
    return set(points)


def describe_private(private):
    """Validate the actual skeleton shape, without imposing a public column."""
    require(type(private) is dict and private, 'nonempty private skeleton')
    require(all(type(key) is tuple and len(key) == 2
                and all(type(v) is int and 0 <= v < 5 for v in key)
                and type(leaves) in (set, frozenset) and leaves
                and all(type(y) is int and 0 <= y < 49 for y in leaves)
                for key, leaves in private.items()), 'literal private fibres')
    roots = sorted({r for r, c in private})
    children = {r: sorted(c for rr, c in private if rr == r) for r in roots}
    require(sorted(map(len, children.values())) == [4, 5, 5, 5],
            'private skeleton occupancy 4555')
    columns = {r: {y % 7 for c in children[r] for y in private[r, c]} for r in roots}
    require(all(len(v) == 1 for v in columns.values())
            and len(set.union(*columns.values())) == 4, 'four distinct private columns')
    gap = next(r for r in roots if len(children[r]) == 4)
    for r in roots:
        if r != gap:
            require(all(len(private[r, c]) == 1 for c in children[r])
                    and len(set().union(*(private[r, c] for c in children[r]))) == 5,
                    'five distinct private leaves at every full root')
    require(sorted(len(private[gap, c]) for c in children[gap]) == [1, 2, 2, 2],
            'gap private cardinalities 1222')
    singleton = next(c for c in children[gap] if len(private[gap, c]) == 1)
    z = next(iter(private[gap, singleton]))
    edges = [private[gap, c] for c in children[gap] if c != singleton]
    require(all(z not in e for e in edges) and len({frozenset(e) for e in edges}) == 3,
            'three distinct two-element sets avoid the singleton')
    require(len({z} | set().union(*edges)) >= 5,
            'gap private union including singleton has at least five leaves')
    degrees = sorted(Counter(y for edge in edges for y in edge).values())
    kinds = {(1, 1, 1, 3): 'star', (1, 1, 2, 2): 'path',
             (1, 1, 1, 1, 2): 'two_edge_path_and_edge',
             (1, 1, 1, 1, 1, 1): 'three_disjoint_edges'}
    require(tuple(degrees) in kinds, 'three-edge forest classification')
    return {'roots': roots, 'children': children, 'gap': gap, 'singleton': singleton,
            'columns': {r: next(iter(v)) for r, v in columns.items()},
            'kind': kinds[tuple(degrees)]}


def classify_equality_source(source):
    """Find the exact public/private decomposition from report449.

    This is a shape recognizer, not a general max-flow or arithmetic solver.
    The ordinary necessity proof identifies this shape with the existence
    of a 65/63 cut under the stated literal and standalone-tree premises.
    """
    points = checked_source(source)
    keys = sorted({(r, c) for r, c, y in points})
    for public in range(7):
        private = {key: {y for r, c, y in points if (r, c) == key and y % 7 != public}
                   for key in keys}
        try:
            description = describe_private(private)
        except ValueError:
            continue
        common = {key: {y for r, c, y in points if (r, c) == key and y % 7 == public}
                  for key in keys}
        if len(set.union(*common.values())) < 5:
            continue
        children = description['children']
        selections = {r: list(combinations(children[r], len(children[r])-2))
                      for r in description['roots']}
        checks, valid = 0, True
        for r, s in combinations(description['roots'], 2):
            for left, right in product(selections[r], selections[s]):
                leaves = set.union(*(common[r, c] for c in left),
                                   *(common[s, c] for c in right))
                checks += 1
                if len(leaves) < 3:
                    valid = False
        if valid:
            require(checks == 480, 'all actual pair/subset common conditions')
            return {**description, 'public': public, 'private': private,
                    'common': common, 'common_subset_checks': checks}
    raise ValueError('source has no certified equality decomposition')


def private_skeleton_law(source, private):
    """A single law on actual points, valid also on arbitrary supersources."""
    points = checked_source(source)
    description = describe_private(private)
    require(all((r, c, y) in points for (r, c), leaves in private.items() for y in leaves),
            'every private skeleton incidence is an actual source point')
    gap, singleton = description['gap'], description['singleton']
    units = {(r, c, y): 3 for (r, c), leaves in private.items()
             if r != gap or c == singleton for y in leaves}
    edge_children = [c for c in description['children'][gap] if c != singleton]
    edges = [sorted(private[gap, c]) for c in edge_children]
    # Each edge receives four units and each endpoint at most three total.
    # The four forest shapes prove existence; this small search constructs it.
    for splits in product(range(1, 4), repeat=3):
        leaf_totals = Counter()
        for edge, left in zip(edges, splits):
            leaf_totals[edge[0]] += left
            leaf_totals[edge[1]] += 4-left
        if max(leaf_totals.values()) <= 3:
            for c, edge, left in zip(edge_children, edges, splits):
                units[gap, c, edge[0]] = left
                units[gap, c, edge[1]] = 4-left
            break
    else:
        raise ValueError('three-edge Hall allocation failed')
    require(sum(units.values()) == 60 and len(units) == 22, 'one 60-unit private law')
    law = {p: F(value, 60) for p, value in units.items()}
    require(set(law) <= points and sum(law.values(), F()) == 1, 'one actual supported law')
    return law


def original_label_caps(law):
    """Keep all numerical labels, with one law preceding all phase choices."""
    require(law and sum(law.values(), F()) == 1 and all(w > 0 for w in law.values()),
            'positive normalized law')
    crt = {}
    for (r, c, y), mass in law.items():
        five = r+5*c
        x = five+25*(((y-five)*pow(25, -1, 49)) % 49)
        require(0 <= x < 1225 and x % 25 == five and x % 49 == y, 'literal CRT identity')
        require(x not in crt, 'injective CRT carrier')
        crt[x] = mass
    labels = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
    caps = {}
    for d in labels:
        masses = [F() for _ in range(d)]
        for x, mass in crt.items():
            masses[x % d] += mass
        caps[d] = max(masses)
    expected = dict(zip(labels, (F(1), F(1, 4), F(1, 4), F(1, 15), F(1, 4),
                                 F(1, 20), F(1, 15), F(1, 20), F(1, 20))))
    require(caps == expected, 'all exact original-label cylinder maxima')
    upper = sum((caps[lcm(d, e)] for d, e in product(labels, repeat=2)), F())
    require(upper == F(25, 3) < 9, 'same-law complete LCM upper bound')
    return {'caps': {str(d): str(caps[d]) for d in labels}, 'LCM_upper': str(upper),
            'cylinder_checks': sum(labels), 'ordered_pair_checks': len(labels)**2,
            'law': [{'residue': x, 'mass': str(mass)} for x, mass in sorted(crt.items())]}


def _example_private(singleton, edges):
    private = {(r, c): {r+1+7*c} for r in (2, 3, 4) for c in range(5)}
    private[1, 0] = {2+7*singleton}
    for c, edge in enumerate(edges, 1):
        private[1, c] = {2+7*y for y in edge}
    return private


def _example_source(private):
    # No common points at the gap root; each full-root child has just one.
    return sorted({(r, c, y) for (r, c), leaves in private.items() for y in leaves}
                  | {(r, c, 1+7*c) for r in (2, 3, 4) for c in range(5)})


def _literal_checks(source):
    choices = tuple(combinations(range(5), 3))
    def tree(leaves, branching):
        return sum(sum(y % 7 == g for y in leaves) >= branching for g in range(7)) >= branching
    projection = {(r, cs): {y for rr, c, y in source if rr == r and c in cs}
                  for r in (1, 2, 3, 4) for cs in choices}
    count = 0
    for r, s in combinations((1, 2, 3, 4), 2):
        for left, right in product(choices, repeat=2):
            require(tree(projection[r, left] | projection[s, right], 3), 'literal product test')
            count += 1
    require(tree({y for r, c, y in source}, 5), 'standalone five-ary projection')
    return count


def controls():
    shapes, examples, rejected_triangles = Counter(), {}, 0
    # Exhaust all labelled gap shapes; unordered edge-children suffice because
    # the constructor and proof retain, but do not prefer, their labels.
    for z in range(7):
        for edges in combinations(tuple(combinations([y for y in range(7) if y != z], 2)), 3):
            private = _example_private(z, edges)
            if len(set.union(*(set(e) for e in edges))) < 4:
                try:
                    describe_private(private)
                except ValueError as error:
                    require(str(error).startswith('gap private union'), 'triangle premise rejection')
                    rejected_triangles += 1
                else:
                    raise ValueError('triangle accepted as a five-leaf gap')
                continue
            description = describe_private(private)
            skeleton = sorted((r, c, y) for (r, c), leaves in private.items() for y in leaves)
            law = private_skeleton_law(skeleton, private)
            caps = original_label_caps(law)
            kind = description['kind']
            shapes[kind] += 1
            if kind not in examples:
                source = _example_source(private)
                classified = classify_equality_source(source)
                require(classified['kind'] == kind and len(source) == 37, 'sparse equality source')
                examples[kind] = {'source': source, 'points': len(source),
                                  'literal_product_checks': _literal_checks(source),
                                  'common_subset_checks': classified['common_subset_checks'],
                                  'gap_singleton': z, 'gap_edges': edges, **caps}
    require(dict(shapes) == {'star': 420, 'path': 1260, 'two_edge_path_and_edge': 1260,
                            'three_disjoint_edges': 105}, 'all labelled forest types')
    require(rejected_triangles == 140 and sum(shapes.values()) == 3045,
            'exhaustive labelled gap shapes, including rejected triangles')
    base = examples['path']['source']
    classified = classify_equality_source(base)
    private = classified['private']
    frozen_private = {key: frozenset(leaves) for key, leaves in private.items()}
    require(private_skeleton_law(base, frozen_private) == private_skeleton_law(base, private),
            'immutable and mutable private fibre sets give the same law')
    extra = sorted(set(base) | {(1, 0, 48)})
    law = private_skeleton_law(extra, private)
    require(original_label_caps(law)['LCM_upper'] == '25/3', 'supersource keeps the same law')
    negative = []
    for name, source in [('extra point breaks exact shape', extra),
                         ('common pair loses its third leaf', [p for p in base if p != (2, 0, 1)])]:
        try:
            classify_equality_source(source)
        except ValueError as error:
            require(str(error) == 'source has no certified equality decomposition', 'shape rejection')
            negative.append(name)
        else:
            raise ValueError('invalid equality shape accepted')
    missing = [p for p in base if p != (2, 0, 3)]
    try:
        private_skeleton_law(missing, private)
    except ValueError as error:
        require(str(error) == 'every private skeleton incidence is an actual source point',
                'no phantom private point')
        negative.append('missing actual private point')
    else:
        raise ValueError('phantom private incidence accepted')
    # A common arithmetic translation changes coordinates and the witness
    # together; it does not permit branch-specific phase choices.
    def translate(point):
        r, c, y = point
        five = (r+5*c+253) % 25
        return five % 5, five//5, (y+253) % 49
    translated = sorted(map(translate, base))
    translated_private = defaultdict(set)
    for (r, c), leaves in private.items():
        for y in leaves:
            rr, cc, yy = translate((r, c, y))
            translated_private[rr, cc].add(yy)
    translated_shape = classify_equality_source(translated)
    translated_law = private_skeleton_law(translated, dict(translated_private))
    translated_caps = original_label_caps(translated_law)
    require(translated_shape['kind'] == 'path', 'translated exact source shape')
    return {'labelled_gap_shapes': dict(shapes), 'gap_laws_checked': sum(shapes.values()),
            'rejected_triangle_shapes': rejected_triangles, 'examples': examples,
            'supersource_points': len(extra), 'supersource_LCM_upper': '25/3',
            'rejection_controls': negative,
            'translated_source': translated, 'translated_law': translated_caps,
            'scope': 'One actual private law controls all original numerical labels and phases. '
                     'Equality classification is ordinary mathematics; no Lean certification, '
                     'arithmetic residual realization, or unrestricted noncoverage is asserted.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(controls(), indent=2)+'\n'
    if args.output:
        args.output.write_text(payload, encoding='utf-8')
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
