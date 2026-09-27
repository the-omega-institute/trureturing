#!/usr/bin/env python3
"""Exact partial-full-root cut70 control for Report449.

Only the active profile (4,4,5,5), common cost3/9 and private cost21 is
covered. The ordinary support proof, not these finite checks, supplies
its universal quantifier. No original odd-cover realization is asserted.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
from math import lcm
from pathlib import Path
import argparse
import importlib.util
import json


def require(value, message):
    if not value:
        raise ValueError(message)


def profile():
    active = (4, 4, 5, 5)
    arity = (2, 3, 3, 3)
    def lower(n, q, p):
        return p + (n-q)*((p+q-1)//q)
    vectors = []
    for ps in product(range(22), repeat=4):
        if any(ps[r]+ps[s] < 6 for r, s in combinations(range(4), 2)):
            continue
        cost = sum(lower(n, q, p) for n, q, p in zip(active, arity, ps))
        if cost <= 21:
            vectors.append((ps, cost))
    require(vectors == [((3, 3, 3, 3), 21)], 'unique lower-cost vector')
    shapes = []
    for n, q, cost in zip(active, arity, (7, 4, 5, 5)):
        choices = [s for s in combinations_with_replacement(range(cost+1), n)
                   if sum(s) == cost and sum(s[:q]) == 3]
        require(len(choices) == 1, 'unique private shape')
        shapes.append(choices[0])
    require(shapes == [(1, 2, 2, 2), (1, 1, 1, 1),
                       (1, 1, 1, 1, 1), (1, 1, 1, 1, 1)], 'private costs')
    # Fix the singleton leaf0. All labelled pairwise-distinct two-sets on
    # the other six leaves have a system of distinct representatives.
    hall_controls = 0
    for sets in combinations(tuple(combinations(range(1, 7), 2)), 3):
        require(any(len(set(xs)) == 3 for xs in product(*sets)), 'Hall control')
        hall_controls += 1
    return {'active': active, 'p_vectors': vectors, 'private_shapes': shapes,
            'three_two_set_controls_up_to_child_permutation': hall_controls}


def verify(directory):
    specification = importlib.util.spec_from_file_location(
        'saturated_transport', directory/'height_two_saturated_block_transport.py')
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    n = (4, 5, 5, 5)
    q = (2, 3, 3, 3)
    common = {(0, h) for h in range(5)}
    fibres = {(r, c): common | {(r, c)}
              for r in range(1, 4) for c in range(5)}
    fibres[1, 4] = set(product(range(7), repeat=2))
    private = {(0, 0): {(4, 0)}}
    for c, hs in enumerate(((1, 2), (2, 3), (3, 4)), 1):
        private[0, c] = {(4, h) for h in hs}
    for r in range(1, 4):
        for c in range(4 if r == 1 else 5):
            private[r, c] = {(r, c)}
    for c in range(4):
        fibres[0, c] = common | private[0, c]
    source = {(r, c, g, h) for (r, c), ys in fibres.items() for g, h in ys}
    require(len(source) == 160, 'source cardinality')
    def tree(ys, k):
        return sum(sum(g == j for g, h in ys) >= k for j in range(7)) >= k
    require(tree({(g, h) for r, c, g, h in source}, 5), 'standalone five-tree')
    pair_tests = 0
    for r, s in combinations(range(4), 2):
        for rc in combinations(range(n[r]), q[r]):
            for sc in combinations(range(n[s]), q[s]):
                ys = set().union(*(fibres[r, c] for c in rc),
                                 *(fibres[s, c] for c in sc))
                require(tree(ys, 3), 'literal pair/subset tree')
                pair_tests += 1
    literal_tests = 0
    for roots in combinations(range(5), 3):
        for children in product(tuple(combinations(range(5), 3)), repeat=3):
            ys = set().union(*(fibres.get((r, c), set())
                               for r, cs in zip(roots, children) for c in cs))
            require(tree(ys, 3), 'full literal product test')
            literal_tests += 1
    require((pair_tests, literal_tests) == (480, 10000), 'test counts')

    caps = {}
    source_node, sink = ('source',), ('sink',)
    def edge(u, v, cap):
        require((u, v) not in caps, 'unique network edge')
        caps[u, v] = cap
    for r in range(4):
        edge(source_node, ('root', r), 21)
        for c in range(n[r]):
            edge(('root', r), ('child', r, c), 7)
            for g in range(7):
                edge(('child', r, c), ('private col', r, c, g), 6)
                for h in range(7):
                    edge(('private col', r, c, g), ('private leaf', r, c, g, h), 2)
    for g in range(7):
        edge(('public col', g), sink, 21)
        for h in range(7):
            edge(('public leaf', g, h), ('public col', g), 7)
    for r, c, g, h in sorted(source):
        edge(('private leaf', r, c, g, h), ('public leaf', g, h), 126)
    nodes = {node for uv in caps for node in uv}
    ids = {node: i for i, node in enumerate(sorted(nodes))}
    network = module.Dinic(len(ids))
    refs = {uv: network.add(ids[uv[0]], ids[uv[1]], cap)
            for uv, cap in caps.items()}
    value = network.flow(ids[source_node], ids[sink], 1000)
    require(value == 70, 'integral maximum70')
    balance = defaultdict(int)
    atoms = []
    for (u, v), (i, j, cap) in refs.items():
        f = cap - network.g[i][j][1]
        require(0 <= f <= cap, 'flow capacity')
        balance[u] -= f
        balance[v] += f
        if u[0] == 'private leaf' and v[0] == 'public leaf' and f:
            atoms.append([*u[1:], f])
    require(balance[source_node] == -70 and balance[sink] == 70 and
            all(v == 0 for u, v in balance.items() if u not in (source_node, sink)),
            'flow conservation')
    require(sum(row[-1] for row in atoms) == 70, 'actual bridge total')
    # Explicit desired cut; no claim that a solver's selected mincut has
    # this profile is needed.
    inside = {source_node} | {('root', r) for r in range(4)}
    inside |= {('public col', 0)} | {('public leaf', 0, h) for h in range(7)}
    for r, c in private:
        inside.add(('child', r, c))
        for g in range(7):
            inside.add(('private col', r, c, g))
            for h in range(7):
                if (g, h) not in private[r, c]:
                    inside.add(('private leaf', r, c, g, h))
    cut = [(u, v, cap) for (u, v), cap in caps.items() if u in inside and v not in inside]
    parts = defaultdict(int)
    for u, v, cap in cut:
        parts[u[0]] += cap
    require(dict(parts) == {'root': 7, 'private col': 42, 'public col': 21},
            'explicit desired cut profile')
    require(sum(cap for u, v, cap in cut) == value, 'primal/dual equality')

    chosen = [(r, c, 4 if r == 0 else r, c)
              for r in range(4) for c in range(4 if r < 2 else 5)]
    require(len(chosen) == 18 and set(chosen) <= source, 'actual uniform18 law')
    def crt(x, y):
        return x + 25*((y-x)*pow(25, -1, 49) % 49)
    law = {crt(r+5*c, g+7*h): Q(1, 18) for r, c, g, h in chosen}
    require(len(law) == 18 and sum(law.values()) == 1, 'law normalization')
    divs = sorted(5**a*7**b for a, b in product(range(3), repeat=2))
    measured = {}
    for d in divs:
        masses = [sum(v for x, v in law.items() if x % d == a) for a in range(d)]
        expected = Q(1) if d == 1 else Q(5 if d in (5, 7, 35) else 1, 18)
        require(max(masses) == expected, 'all literal cylinder caps')
        measured[d] = max(masses)
    bound = sum(measured[lcm(d, e)] for d, e in product(divs, repeat=2))
    require(bound == Q(79, 9), 'full81-pair upper bound')
    return {'profile': profile(), 'source_points': len(source), 'source': sorted(source),
            'pair_tests': pair_tests, 'literal_product_tests': literal_tests,
            'standalone_five_tree': True, 'network_edges': len(caps),
            'flow_units': value, 'positive_bridge_flow': sorted(atoms),
            'cut_units': value, 'cut_parts': dict(parts), 'cut_edges': cut,
            'law_residues': sorted(law), 'law_atoms': len(law),
            'caps': {str(d): str(v) for d, v in measured.items()},
            'cylinders_checked': sum(divs), 'ordered_lcm_pairs': len(divs)**2,
            'gamma_upper': str(bound),
            'scope': 'One exact cut70 partial-full-root source. The universal fixed-profile proof is in Report449; this is not all cut70 profiles or an original odd covering.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    data = json.dumps(verify(Path(__file__).parent), indent=2)+'\n'
    args.output.write_text(data, encoding='utf-8')
    print(data, end='')


if __name__ == '__main__':
    main()
