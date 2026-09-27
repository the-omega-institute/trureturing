#!/usr/bin/env python3
"""Exact actual-source controls for sparse, partial and full cut71 profiles.

Finite controls accompany universal support arguments; they do not prove
profile exhaustiveness, all cut71, or an unrestricted odd-cover statement.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_dinic(path=None):
    path = Path(path) if path else Path(__file__).with_name('height_two_saturated_block_transport.py')
    spec = spec_from_file_location('_existing_cut71_dinic', path)
    require(spec is not None and spec.loader is not None, 'existing Dinic module')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.Dinic


OCCUPANCY = (4, 5, 5, 5)
CHILDREN = {(r, c) for r in range(4) for c in range(OCCUPANCY[r])}


def templates():
    result = []
    for repeated in (False, True):
        gap = (0, 0, 1, 2) if repeated else (0, 1, 2, 3)
        fibres = {(0, c): {(0, gap[c])} for c in range(4)}
        common = set(product((1, 2, 3), range(7)))
        fibres.update({(r, c): set(common) for r in (1, 2, 3) for c in range(5)})
        fibres[1, 0] |= set(product((0, 4), range(7)))
        result.append({'name': '4000_repeated' if repeated else '4000_distinct',
                       'active_counts': (4, 0, 0, 0), 'public_columns': (), 'public_leaves': (),
                       'private': {(0, c): {(0, gap[c])} for c in range(4)}, 'fibres': fibres,
                       'law_kind': 'punctured_mix', 'universal_gamma': Q(33, 4) if repeated else Q(112, 13)})
    fibres = {(0, c): set(product(range(7), repeat=2)) for c in range(4)}
    private = {(1, c): {(0, c)} for c in range(5)}
    private.update({(2, c): {(1, c), (2, c)} for c in range(5)})
    private.update({(3, c): {(1, c), (3, c)} for c in range(5)})
    fibres.update(private)
    result.append({'name': '0555', 'active_counts': (0, 5, 5, 5), 'public_columns': (),
                   'public_leaves': (), 'private': private, 'fibres': fibres,
                   'law_kind': 'uniform_private', 'universal_gamma': Q(41, 5)})
    for active_counts in ((3, 5, 5, 5), (4, 4, 5, 5)):
        public = set(product((0,), range(7))) | {(4, 6)}
        private = {(r, c): {(4 if r == 0 else r, c)}
                   for r in range(4) for c in range(active_counts[r])}
        fibres = {child: public | private[child] if child in private else set(product(range(7), repeat=2))
                  for child in CHILDREN}
        result.append({'name': ''.join(map(str, active_counts)), 'active_counts': active_counts,
                       'public_columns': (0,), 'public_leaves': ((4, 6),), 'private': private,
                       'fibres': fibres, 'law_kind': 'uniform_private', 'universal_gamma': Q(79, 9)})
    for zero_child in ((0, 0), (1, 0)):
        public_leaves = ((4, 0), (4, 1)) if zero_child[0] == 0 else ((4, 0), (1, 0))
        public = set(product((0,), range(7))) | set(public_leaves)
        private = {}
        for r, c in CHILDREN:
            if (r, c) == zero_child:
                private[r, c] = set()
            elif r == 0:
                private[r, c] = {(4, c + 1)}
            else:
                private[r, c] = {(r, c)}
        fibres = {child: public | private[child] for child in CHILDREN}
        result.append({'name': 'fullk5_0111' if zero_child[0] == 0 else 'fullk5_01111',
                       'active_counts': OCCUPANCY, 'public_columns': (0,), 'public_leaves': public_leaves,
                       'private': private, 'fibres': fibres, 'law_kind': 'uniform_private',
                       'universal_gamma': Q(79, 9)})
    full_shapes = (
        '0333/11111/11111/11112', '1222/01222/11111/11112',
        '1222/01223/11111/11111', '1222/02222/11111/11111',
        '1222/11111/11111/11123', '1222/11111/11111/11222',
        '1222/11111/11112/11113', '1222/11111/11112/11122',
        '1222/11112/11112/11112', '1223/01222/11111/11111',
        '1223/11111/11111/11113', '1223/11111/11111/11122',
        '1223/11111/11112/11112', '1233/11111/11111/11112',
        '1333/11111/11111/11111', '2222/01222/11111/11111',
        '2222/11111/11111/11113', '2222/11111/11111/11122',
        '2222/11111/11112/11112', '2223/11111/11111/11112',
        '2233/11111/11111/11111')
    private_labels = {
        '0333': ((), (0, 1, 2), (2, 3, 4), (4, 5, 6)),
        '1222': ((0,), (1, 2), (2, 3), (3, 4)),
        '1223': ((0,), (1, 2), (2, 3), (4, 5, 6)),
        '1233': ((0,), (1, 2), (3, 4, 5), (4, 5, 6)),
        '1333': ((0,), (1, 2, 3), (2, 3, 4), (4, 5, 6)),
        '2222': ((0, 1), (1, 2), (2, 3), (3, 4)),
        '2223': ((0, 1), (1, 2), (2, 3), (4, 5, 6)),
        '2233': ((0, 1), (1, 2), (2, 3, 4), (4, 5, 6)),
        '01222': ((), (0,), (1, 2), (2, 3), (3, 4)),
        '01223': ((), (0,), (1, 2), (2, 3), (4, 5, 6)),
        '02222': ((), (0, 1), (1, 2), (2, 3), (3, 4)),
        '11111': ((0,), (1,), (2,), (3,), (4,)),
        '11112': ((0,), (1,), (2,), (3,), (4, 5)),
        '11113': ((0,), (1,), (2,), (3,), (4, 5, 6)),
        '11122': ((0,), (1,), (2,), (3, 4), (4, 5)),
        '11123': ((0,), (1,), (2,), (3, 4), (4, 5, 6)),
        '11222': ((0,), (1,), (2, 3), (3, 4), (4, 5))}
    for index, shape in enumerate(full_shapes, 1):
        for use_whole in ((False, True) if '3' in shape else (False,)):
            private, whole = {}, set()
            for r, row in enumerate(shape.split('/')):
                for c, hs in enumerate(private_labels[row]):
                    require(len(hs) == int(row[c]), 'literal sorted private shape')
                    g = 4 if r == 0 else r
                    if use_whole and len(hs) == 3:
                        private[r, c] = {(g, h) for h in range(7)}
                        whole.add((r, c))
                    else:
                        private[r, c] = {(g, h) for h in hs}
            public = set(product((0,), range(7)))
            fibres = {child: public | private[child] for child in CHILDREN}
            result.append({'name': 'fullk3_%02d' % index + ('_whole' if use_whole else ''),
                           'shape': shape, 'active_counts': OCCUPANCY, 'public_columns': (0,),
                           'public_leaves': (), 'private': private, 'whole_private': whole,
                           'fibres': fibres, 'law_kind': 'uniform_eighteen', 'universal_gamma': Q(79, 9)})
    for item in result:
        item.setdefault('whole_private', set())
        item['source'] = {(r, c, g, h) for (r, c), ys in item['fibres'].items() for g, h in ys}
    return result


def literal_checks(template):
    fibres = template['fibres']
    def projection(children):
        return set().union(*(fibres.get(child, set()) for child in children))
    def tree(ys, k):
        return sum(len({h for g, h in ys if g == j}) >= k for j in range(7)) >= k
    require(set(fibres) == CHILDREN and all(fibres.values()), 'literal occupancy4555')
    require(tree(projection(fibres), 5), 'actual standalone five-tree')
    pair_tests = 0
    for r, s in combinations(range(4), 2):
        for aa in combinations(range(OCCUPANCY[r]), OCCUPANCY[r] - 2):
            for bb in combinations(range(OCCUPANCY[s]), OCCUPANCY[s] - 2):
                require(tree(projection({(r, c) for c in aa} | {(s, c) for c in bb}), 3), 'selected pair tree')
                pair_tests += 1
    literal_tests = 0
    for roots in combinations(range(5), 3):
        for choices in product(tuple(combinations(range(5), 3)), repeat=3):
            require(tree(projection({(r, c) for r, cs in zip(roots, choices) for c in cs}), 3), 'full literal tree')
            literal_tests += 1
    require((pair_tests, literal_tests) == (480, 10000), 'literal test counts')
    return {'pair_tests': pair_tests, 'full_literal_tests': literal_tests, 'standalone_five_tree': True}


def actual_network(template, dinic):
    source_node, sink = ('source',), ('sink',)
    caps = {}
    def add(u, v, cap):
        require((u, v) not in caps, 'unique network arc')
        caps[u, v] = cap
    for r, nr in enumerate(OCCUPANCY):
        add(source_node, ('r', r), 21)
        for c in range(nr):
            add(('r', r), ('c', r, c), 7)
            for g in range(7):
                add(('c', r, c), ('pg', r, c, g), 6)
                for h in range(7):
                    add(('pg', r, c, g), ('ph', r, c, g, h), 2)
    for g in range(7):
        add(('cg', g), sink, 21)
        for h in range(7):
            add(('ch', g, h), ('cg', g), 7)
    for r, c, g, h in sorted(template['source']):
        add(('ph', r, c, g, h), ('ch', g, h), 126)
    nodes = sorted({node for uv in caps for node in uv})
    ids = {node: i for i, node in enumerate(nodes)}
    graph = dinic(len(ids))
    refs = {uv: graph.add(ids[uv[0]], ids[uv[1]], cap) for uv, cap in caps.items()}
    value = graph.flow(ids[source_node], ids[sink], 1000)
    balance, flow = defaultdict(int), {}
    atoms = []
    for (u, v), (i, j, cap) in refs.items():
        amount = cap - graph.g[i][j][1]
        require(0 <= amount <= cap, 'every actual edge capacity')
        flow[u, v] = amount
        balance[u] -= amount
        balance[v] += amount
        if u[0] == 'ph' and v[0] == 'ch' and amount:
            atoms.append([*u[1:], amount])
    require(value == 71, 'actual maximum flow71')
    require(balance[source_node] == -value and balance[sink] == value and
            all(v == 0 for u, v in balance.items() if u not in (source_node, sink)), 'flow conservation')
    reachable = {ids[source_node]}
    queue = deque(reachable)
    while queue:
        u = queue.popleft()
        for v, cap, rev in graph.g[u]:
            if cap and v not in reachable:
                reachable.add(v)
                queue.append(v)
    minimum_side = {node for node, i in ids.items() if i in reachable}
    minimum_cut = [(u, v, cap) for (u, v), cap in caps.items() if u in minimum_side and v not in minimum_side]
    require(sum(cap for u, v, cap in minimum_cut) == 71, 'residual minimum cut71')
    inside = {source_node}
    for g in template['public_columns']:
        inside.add(('cg', g))
        inside.update(('ch', g, h) for h in range(7))
    inside.update(('ch', g, h) for g, h in template['public_leaves'])
    for r, a in enumerate(template['active_counts']):
        if a:
            inside.add(('r', r))
        for c in range(a):
            inside.add(('c', r, c))
            whole_g = next(iter(template['private'][r, c]))[0] if (r, c) in template['whole_private'] else None
            for g in range(7):
                if g == whole_g:
                    continue
                inside.add(('pg', r, c, g))
                for h in range(7):
                    if (g, h) not in template['private'][r, c]:
                        inside.add(('ph', r, c, g, h))
    cut = [(u, v, cap) for (u, v), cap in caps.items() if u in inside and v not in inside]
    require(not any(u[0] == 'ph' for u, v, cap in cut), 'no actual bridge crosses prescribed cut')
    require(sum(cap for u, v, cap in cut) == 71, 'prescribed cut71')
    require(all(flow[u, v] == cap for u, v, cap in cut), 'prescribed cut saturation')
    require(all(flow[u, v] == 0 for u, v in caps if u not in inside and v in inside), 'no backward cut flow')
    return {'maximum_flow': value, 'minimum_cut': 71, 'actual_flow_atoms': atoms,
            'prescribed_cut': [[list(u), list(v), cap] for u, v, cap in cut],
            'computed_minimum_cut': [[list(u), list(v), cap] for u, v, cap in minimum_cut]}


def construct_law(template, dinic):
    if template['law_kind'] == 'uniform_eighteen':
        source_node, sink = ('selector source',), ('selector sink',)
        leaves = sorted({p[2:] for p in template['source']})
        nodes = [source_node, sink] + [('child', *p) for p in sorted(CHILDREN)]
        nodes += [('leaf', *p) for p in leaves] + [('column', g) for g in range(7)]
        ids = {node: i for i, node in enumerate(nodes)}
        graph = dinic(len(ids))
        for child in sorted(CHILDREN):
            graph.add(ids[source_node], ids['child', *child], 1)
        refs = {p: graph.add(ids['child', *p[:2]], ids['leaf', *p[2:]], 1) for p in sorted(template['source'])}
        for g, h in leaves:
            graph.add(ids['leaf', g, h], ids['column', g], 1)
        for g in range(7):
            graph.add(ids['column', g], ids[sink], 5)
        require(graph.flow(ids[source_node], ids[sink], 18) == 18, 'actual child-leaf-column matching18')
        points = [p for p, (u, k, cap) in refs.items() if cap - graph.g[u][k][1]]
        require(len(points) == len({p[:2] for p in points}) == len({p[2:] for p in points}) == 18,
                'eighteen actual points with distinct children and full leaves')
        require(max(Counter(p[2] for p in points).values()) <= 5, 'selected first-seven column cap5')
        return {point: Q(1, 18) for point in points}
    if template['law_kind'] == 'uniform_private':
        points = {(r, c, g, h) for (r, c), ys in template['private'].items() for g, h in ys}
        return {point: Q(1, len(points)) for point in points}
    gap_points = sorted(point for point in template['source'] if point[0] == 0)
    repeated = len({p[2:] for p in gap_points}) < 4
    if repeated:
        pair = next((p, q) for p, q in combinations(gap_points, 2) if p[2:] == q[2:])
        psi_weight, gap_weight = Q(1), Q(0)
    else:
        pair = gap_points[:2]
        psi_weight, gap_weight = Q(35, 39), Q(4, 39)
    removed = {p[2:] for p in pair}
    law = defaultdict(Q)
    for r in (1, 2, 3):
        for children in combinations(range(5), 3):
            owners = defaultdict(list)
            for c in children:
                for leaf in template['fibres'][r, c]:
                    owners[leaf].append((r, c, *leaf))
            union = set(owners) | removed
            branches = [g for g in range(7) if sum(gg == g for gg, h in union) >= 3][:3]
            require(len(branches) == 3, 'actual puncturable ternary witness')
            tree = {(g, h) for g in branches for h in sorted(hh for gg, hh in union if gg == g)[:3]}
            remaining = sorted(tree - removed)
            require(len(remaining) >= (8 if repeated else 7), 'punctured tree size')
            for leaf in remaining:
                require(owners[leaf], 'every retained leaf has actual selected owner')
                law[min(owners[leaf])] += psi_weight / (30 * len(remaining))
    for point in gap_points:
        law[point] += gap_weight / 4
    return {point: weight for point, weight in law.items() if weight}


def check_law(template, law):
    require(set(law) <= template['source'] and all(weight > 0 for weight in law.values()), 'actual positive atoms')
    require(sum(law.values()) == 1, 'single normalized law')
    def crt(r, c, g, h):
        x, y = r + 5 * c, g + 7 * h
        return x + 25 * ((y - x) * pow(25, -1, 49) % 49)
    divisors = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
    if template['name'] == '4000_distinct':
        cap_values = (Q(1), Q(35, 117), Q(19, 39), Q(7, 39), Q(5, 39), Q(2, 13), Q(1, 13), Q(5, 117), Q(1, 39))
    elif template['name'] == '4000_repeated':
        cap_values = (Q(1), Q(1, 3), Q(3, 8), Q(1, 5), Q(1, 8), Q(1, 8), Q(3, 40), Q(1, 24), Q(1, 40))
    elif template['name'] == '0555':
        cap_values = tuple(Q(x, 25) for x in (25, 10, 10, 2, 5, 2, 1, 1, 1))
    else:
        cap_values = tuple(Q(x, 18) for x in (18, 5, 5, 1, 5, 1, 1, 1, 1))
    caps = dict(zip(divisors, cap_values))
    maxima, total = {}, 0
    for d in divisors:
        counts = defaultdict(Q)
        for point, weight in law.items():
            counts[crt(*point) % d] += weight
        for a in range(d):
            require(counts[a] <= caps[d], 'every original numerical cylinder under universal cap')
            total += 1
        maxima[d] = max(counts.values())
    gamma = sum(maxima[lcm(d, e)] for d, e in product(divisors, repeat=2))
    bound = sum(caps[lcm(d, e)] for d, e in product(divisors, repeat=2))
    require(total == 1767 and gamma <= bound == template['universal_gamma'] < 9, 'same-law81 original LCM terms')
    return {'atoms': [[*point, str(weight)] for point, weight in sorted(law.items())],
            'cylinder_maxima': {str(d): str(v) for d, v in maxima.items()},
            'universal_caps': {str(d): str(v) for d, v in caps.items()},
            'cylinders_checked': total, 'ordered_lcm_pairs': 81,
            'gamma_envelope': str(gamma), 'universal_gamma_bound': str(bound)}


def verify(dinic):
    controls = []
    for template in templates():
        controls.append({'name': template['name'], 'active_counts': template['active_counts'],
                         'source': sorted(template['source']), 'source_points': len(template['source']),
                         'public_columns': template['public_columns'], 'public_leaves': template['public_leaves'],
                         'shape': template.get('shape'), 'whole_private_children': sorted(template['whole_private']),
                         'private': [[*child, sorted(ys)] for child, ys in sorted(template['private'].items())],
                         **literal_checks(template), 'network': actual_network(template, dinic),
                         'law': check_law(template, construct_law(template, dinic))})
    require(len([c for c in controls if c['shape'] is not None and not c['whole_private_children']]) == 21,
            'all twenty-one fullk3 finite-private shapes')
    require(len(controls) == 41 and sum(bool(c['whole_private_children']) for c in controls) == 13,
            'seven sparse/partial/fullk5 controls plus21 finite and13 whole fullk3 controls')
    require(all(c['network']['minimum_cut'] == 71 for c in controls), 'all fixed controls have exact minimum cut71')
    return {'controls': controls, 'scope': 'Exact actual-source controls for4000 (distinct/repeated gap leaves),0555,3555,4455, the two surviving fullk5 shapes, all twenty-one fullk3 finite-private shapes and their all-cost3-whole-column variants. Uniform or punctured-mixture laws use one original source. Finite controls do not establish the universal profile classification or all cut71, and make no Lean or unrestricted odd-cover claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module', type=Path, help='existing saturated-block file; default is adjacent')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    out = verify(load_dinic(args.base_module))
    args.output.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    for item in out['controls']:
        print(json.dumps({'name': item['name'], 'points': item['source_points'], 'mincut': item['network']['minimum_cut'],
                          'gamma_envelope': item['law']['gamma_envelope'], 'universal_gamma': item['law']['universal_gamma_bound']}))


if __name__ == '__main__':
    main()
