#!/usr/bin/env python3
"""Exact literal-blocking source with child-network minimum cut 65/63.

The 117-point source has child incidence (4,5,5,5). Its explicit matching
flow, after normalization, still has original-label LCM moment upper 107/13.
Neither a covering-system realization nor a moment obstruction is asserted.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _children():
    return {1: tuple(range(4)), **{r: tuple(range(5)) for r in (2, 3, 4)}}


def _private_leaves():
    private = {}
    for r, children in _children().items():
        for c in children:
            digits = ((0,), (1, 2), (2, 3), (3, 4))[c] if r == 1 else (c,)
            private[r, c] = {r + 1 + 7*h for h in digits}
    return private


def boundary_source():
    """Return sorted actual triples (first-five root, child, seven leaf)."""
    public = {1 + 7*h for h in range(5)}
    return sorted((r, c, y) for (r, c), leaves in _private_leaves().items()
                  for y in leaves | public)


def boundary_flow():
    """Return an unnormalized Fraction-valued actual-bridge flow of 65/63."""
    flow = {(r, c, y): F(2, 63)
            for (r, c), leaves in _private_leaves().items() for y in leaves}
    for h in range(3):
        flow[1, 0, 1 + 7*h] = F(1, 63)
    for r in (2, 3, 4):
        for c in range(3):
            flow[r, c, 1 + 7*c] = F(2, 63)
    return flow


def _contains_tree(leaves, branching):
    return sum(sum(g + 7*h in leaves for h in range(7)) >= branching
               for g in range(7)) >= branching


def _network(source):
    """Return directed capacities and the explicit source-side cut nodes."""
    start = ('source',)
    source_side = {start}
    capacities = {}

    def edge(left, right, capacity):
        require((left, right) not in capacities, 'unique directed network edge')
        capacities[left, right] = capacity

    private = _private_leaves()
    for r, children in _children().items():
        source_side.add(('root', r))
        edge(start, ('root', r), F(1, 3))
        for c in children:
            source_side.add(('private', r, c, 0, 0))
            edge(('root', r), ('private', r, c, 0, 0), F(1, 9))
            for b in (1, 2):
                for v in range(7**b):
                    node = ('private', r, c, b, v)
                    if b == 1 or v not in private[r, c]:
                        source_side.add(node)
                    edge(('private', r, c, b-1, v % 7**(b-1)), node,
                         F(2, 7 * 3**b))
    for b in (1, 2):
        for v in range(7**b):
            node = ('public', b, v)
            if v % 7 == 1:
                source_side.add(node)
            edge(node, ('public', b-1, v % 7**(b-1)), F(1, 3**b))
    for r, c, y in source:
        edge(('private', r, c, 2, y), ('public', 2, y), F(2))
    return capacities, source_side


def _flow_path(point):
    r, c, y = point
    return [('source',), ('root', r), ('private', r, c, 0, 0),
            ('private', r, c, 1, y % 7), ('private', r, c, 2, y),
            ('public', 2, y), ('public', 1, y % 7), ('public', 0, 0)]


def _normalized_original_label_caps(flow):
    total = sum(flow.values(), F())
    crt_law = defaultdict(F)
    for (r, c, y), mass in flow.items():
        five = r + 5*c
        residue = five + 25 * (((y-five) * pow(25, -1, 49)) % 49)
        require(0 <= residue < 1225 and residue % 25 == five and residue % 49 == y,
                'same actual point under CRT')
        crt_law[residue] += mass / total
    require(sum(crt_law.values(), F()) == 1, 'one normalized CRT law')
    labels = [d for d in range(1, 1226) if 1225 % d == 0]
    require(labels == [1, 5, 7, 25, 35, 49, 175, 245, 1225],
            'all nine original divisor labels')
    caps = {}
    for d in labels:
        cylinder_masses = [sum((mass for x, mass in crt_law.items() if x % d == a), F())
                           for a in range(d)]
        caps[d] = max(cylinder_masses)
    expected = {1: F(1), 5: F(17, 65), 7: F(21, 65), 25: F(5, 65),
                35: F(14, 65), 49: F(7, 65), 175: F(4, 65),
                245: F(4, 65), 1225: F(2, 65)}
    require(caps == expected, 'exact normalized-law original-label cylinder maxima')
    upper = sum((caps[lcm(d, e)] for d, e in product(labels, repeat=2)), F())
    require(upper == F(107, 13) < 9, 'same normalized-law complete LCM moment upper')
    return {
        'normalized_original_label_caps': {str(d): str(caps[d]) for d in labels},
        'original_label_cylinder_checks': sum(labels),
        'ordered_original_label_pair_checks': len(labels)**2,
        'normalized_original_label_LCM_upper': str(upper),
        'normalized_CRT_law': [{'residue': x, 'mass': str(mass)}
                               for x, mass in sorted(crt_law.items())]
    }


def controls():
    """Check the source, its literal cut, matching flow, and normalized law."""
    source = boundary_source()
    source_set = set(source)
    flow = boundary_flow()
    children = _children()
    require(len(source) == len(source_set) == 117, '117 distinct actual points')
    require({r for r, c, y in source} == {1, 2, 3, 4}, 'empty first-five root zero')
    require(all(y % 7 != 0 and r + 5*c != 21 for r, c, y in source),
            'empty first-seven root zero and second-five child 21')
    occupancy = [len({c for rr, c, y in source if rr == r}) for r in children]
    require(occupancy == [4, 5, 5, 5], 'actual occupied-child counts')
    incidence = {r: [len({c for rr, c, y in source if rr == r and y % 7 == g})
                     for g in range(7)] for r in children}
    incidence_maxima = [max(incidence[r]) for r in children]
    require(incidence_maxima == [4, 5, 5, 5], 'high child incidence')

    choices = tuple(combinations(range(5), 3))
    projections = {(r, choice): {y for rr, c, y in source if rr == r and c in choice}
                   for r in children for choice in choices}
    literal_checks = 0
    for r, s in combinations(children, 2):
        for left, right in product(choices, repeat=2):
            require(_contains_tree(projections[r, left] | projections[s, right], 3),
                    'literal pair/triple product-tree blocking')
            literal_checks += 1
    require(literal_checks == 600, 'all 600 original literal pair/triple predicates')
    require(_contains_tree({y for r, c, y in source}, 5),
            'standalone complete five-ary seven tree')

    capacities, source_side = _network(source)
    start, sink = ('source',), ('public', 0, 0)
    require(start in source_side and sink not in source_side, 'source/sink cut')
    crossing = [(left, right, capacity) for (left, right), capacity in capacities.items()
                if left in source_side and right not in source_side]
    cut_capacity = sum((capacity for left, right, capacity in crossing), F())
    bridge_crossings = [edge for edge in crossing
                        if edge[0][0] == 'private' and edge[1][0] == 'public']
    require(not bridge_crossings, 'no actual bridge crosses the cut')
    private_crossings = [edge for edge in crossing if edge[1][0] == 'private']
    public_crossings = [edge for edge in crossing if edge[0][0] == 'public']
    require(len(private_crossings) == 22 and len(public_crossings) == 1,
            '22 private leaf cuts and one public first-prefix cut')
    require(all(right[3] == 2 and capacity == F(2, 63)
                for left, right, capacity in private_crossings), 'private leaf-cut capacities')
    require(sum((capacity for left, right, capacity in public_crossings), F()) == F(1, 3),
            'exact public cut cost')
    require(cut_capacity == F(65, 63), 'exact actual cut capacity')

    require(set(flow) <= source_set and all(mass > 0 for mass in flow.values()),
            'positive flow on actual bridges')
    edge_flow = defaultdict(F)
    for point, mass in flow.items():
        path = _flow_path(point)
        for left, right in zip(path, path[1:]):
            require((left, right) in capacities, 'flow follows actual network edges')
            edge_flow[left, right] += mass
    balance = defaultdict(F)
    bridge_checks = 0
    for (left, right), capacity in capacities.items():
        mass = edge_flow[left, right]
        require(0 <= mass <= capacity, 'every network flow capacity, including bridges')
        balance[left] -= mass
        balance[right] += mass
        if left[0] == 'private' and right[0] == 'public':
            bridge_checks += 1
    total = sum(flow.values(), F())
    require(total == F(65, 63) and len(flow) == 34, 'matching flow value and support')
    require(balance[start] == -total and balance[sink] == total,
            'matching source and sink flow values')
    require(all(net == 0 for node, net in balance.items() if node not in (start, sink)),
            'conservation at every internal network node')
    require(total == cut_capacity and bridge_checks == len(source),
            'exact matching cut/flow certificate and every actual bridge checked')

    private = _private_leaves()
    result = {
        'source_points': len(source),
        'occupancy': occupancy,
        'incidence': incidence_maxima,
        'child_incidence_counts_by_first7root': incidence,
        'literal_product_tree_checks': literal_checks,
        'standalone_fiveary_seven_tree': True,
        'private_cut_leaf_counts': [[len(private[r, c]) for c in children[r]] for r in children],
        'public_cut_cost': '1/3',
        'cut_capacity': str(cut_capacity),
        'matching_unnormalized_flow_value': str(total),
        'matching_flow_support': len(flow),
        'network_edge_capacity_checks': len(capacities),
        'actual_bridge_capacity_checks': bridge_checks,
        'internal_flow_conservation_checks': len(balance)-2,
        'source': source,
        'matching_flow': [{'point': point, 'mass': str(mass)} for point, mass in sorted(flow.items())],
        'cut_crossing_edges': [{'from': left, 'to': right, 'capacity': str(capacity)}
                               for left, right, capacity in crossing],
        'scope': ('Literal product blocking and a standalone five-ary tree allow minimum cut '
                  '65/63 when incidence is unrestricted. The same normalized matching flow '
                  'has LCM moment upper 107/13<9, so network sharpness is not a moment '
                  'obstruction. No covering-system realization is asserted.')
    }
    result.update(_normalized_original_label_caps(flow))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(controls(), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload, encoding='utf-8')
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
