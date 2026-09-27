#!/usr/bin/env python3
"""Exact actual-source controls for cut70 Families B and F.

These finite templates exercise the ordinary support proofs. They do not
replace their universal quantifiers or certify the complete profile list.
Only standard-library code is used; Dinic is loaded from the earlier
adjacent saturated-block constructor, without executing its controls.
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
    spec = spec_from_file_location('_existing_cut70_dinic', path)
    require(spec is not None and spec.loader is not None, 'existing Dinic module')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.Dinic


def make_template(name, family, sets, whole=()):
    """sets maps each active child to(g, fine-label tuple); whole marks column cuts."""
    occupancy = (4, 5, 5, 5)
    active = {(r, c) for r in range(4) for c in range(occupancy[r])}
    if family == 'B':
        active.remove((0, 3))
    y = (1, 0) if name.startswith('F9') else (4, 0)
    public = {(0, h) for h in range(7)}
    if family == 'F':
        public.add(y)
    whole = set(whole)
    require(set(sets) == active and whole <= active, 'all active children have an explicit cut shape')
    fibres, private, costs = {}, {}, {}
    for r in range(4):
        for c in range(occupancy[r]):
            child = (r, c)
            if child not in active:
                fibres[child] = set(product(range(7), repeat=2))
                continue
            g, hs = sets[child]
            require(0 <= g < 7 and len(set(hs)) == len(hs), 'literal private labels')
            require(all(type(h) is int and 0 <= h < 7 for h in hs), 'private fine digits')
            if child in whole:
                require(len(hs) == 3, 'only a cost3 child becomes a whole-column cut')
                private[child] = {(g, h) for h in range(7)}
                costs[child] = 3
            else:
                private[child] = {(g, h) for h in hs}
                costs[child] = len(hs)
            fibres[child] = public | private[child]
    require(sum(costs.values()) == 21, 'unweighted private cut total21')
    source = {(r, c, g, h) for (r, c), ys in fibres.items() for g, h in ys}
    return {'name': name, 'family': family, 'occupancy': occupancy, 'active': active,
            'public': public, 'public_y': y if family == 'F' else None,
            'private': private, 'whole': whole, 'costs': costs, 'fibres': fibres, 'source': source}


def templates():
    def clean():
        return {(r, c): (r, (c,)) for r in (1, 2, 3) for c in range(5)}
    result = []
    b_specs = [
        ('B033', [(), (0, 1, 2), (3, 4, 5)], None),
        ('B122', [(0,), (1, 2), (3, 4)], [(0,), (1,), (2,), (3,), (4, 5)]),
        ('B123', [(0,), (1, 2), (3, 4, 5)], None),
        ('B222', [(0, 1), (1, 2), (2, 3)], None),
    ]
    for name, gap, exceptional in b_specs:
        spec = clean()
        spec.update({(0, c): (4, hs) for c, hs in enumerate(gap)})
        if exceptional is not None:
            spec.update({(1, c): (1, hs) for c, hs in enumerate(exceptional)})
        result.append(make_template(name, 'B', spec))
        if name == 'B033':
            result.append(make_template(name + '_whole', 'B', spec, ((0, 1), (0, 2))))
        if name == 'B123':
            result.append(make_template(name + '_whole', 'B', spec, ((0, 2),)))
    f_specs = [
        ('F1_0222', [(), (1, 2), (3, 4), (5, 6)], {}),
        ('F2_1111_01222', [(1,), (2,), (3,), (4,)],
            {1: [(), (0,), (1, 2), (3, 4), (5, 6)]}),
        ('F3_1111_11113', [(1,), (2,), (3,), (4,)],
            {1: [(0,), (1,), (2,), (3,), (4, 5, 6)]}),
        ('F4_1111_11122', [(1,), (2,), (3,), (4,)],
            {1: [(0,), (1,), (2,), (3, 4), (5, 6)]}),
        ('F5_1111_11112_11112', [(1,), (2,), (3,), (4,)],
            {1: [(0,), (1,), (2,), (3,), (4, 5)], 2: [(0,), (1,), (2,), (3,), (4, 5)]}),
        ('F6_1112_11112', [(1,), (2,), (3,), (4, 5)],
            {1: [(0,), (1,), (2,), (3,), (4, 5)]}),
        ('F7_1113', [(1,), (2,), (3,), (4, 5, 6)], {}),
        ('F8_1122', [(1,), (2,), (3, 4), (5, 6)], {}),
        ('F9_1222_01111', [(0,), (1, 2), (3, 4), (5, 6)],
            {1: [(), (1,), (2,), (3,), (4,)]}),
    ]
    for name, gap, exceptional in f_specs:
        spec = clean()
        spec.update({(0, c): (4, hs) for c, hs in enumerate(gap)})
        for r, sets in exceptional.items():
            spec.update({(r, c): (r, hs) for c, hs in enumerate(sets)})
        result.append(make_template(name, 'F', spec))
        if name.startswith('F3'):
            result.append(make_template(name + '_whole', 'F', spec, ((1, 4),)))
        if name.startswith('F7'):
            result.append(make_template(name + '_whole', 'F', spec, ((0, 3),)))
    return result


def literal_checks(template):
    fibres = template['fibres']
    def projection(children):
        return set().union(*(fibres.get(child, set()) for child in children))
    def tree(ys, k):
        return sum(len({h for g, h in ys if g == j}) >= k for j in range(7)) >= k
    require(tree(projection(fibres), 5), 'actual standalone five-tree')
    count = 0
    n = template['occupancy']
    for r, s in combinations(range(4), 2):
        for aa in combinations(range(n[r]), n[r] - 2):
            for bb in combinations(range(n[s]), n[s] - 2):
                selected = {(r, c) for c in aa} | {(s, c) for c in bb}
                require(tree(projection(selected), 3), 'actual selected pair tree')
                count += 1
    full = 0
    for roots in combinations(range(5), 3):
        for choices in product(tuple(combinations(range(5), 3)), repeat=3):
            selected = {(r, c) for r, cs in zip(roots, choices) for c in cs}
            require(tree(projection(selected), 3), 'complete literal product tree')
            full += 1
    require((count, full) == (480, 10000), 'full literal coverage')
    return {'pair_tests': count, 'full_literal_tests': full, 'standalone_five_tree': True}


def actual_network(template, dinic):
    source_node, sink = ('source',), ('sink',)
    caps = {}
    def add(u, v, cap):
        require((u, v) not in caps, 'unique actual network arc')
        caps[u, v] = cap
    for r, nr in enumerate(template['occupancy']):
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
        balance[u] -= amount; balance[v] += amount
        if u[0] == 'ph' and v[0] == 'ch' and amount:
            atoms.append([*u[1:], amount])
    require(balance[source_node] == -value and balance[sink] == value and
            all(v == 0 for u, v in balance.items() if u not in (source_node, sink)), 'actual flow conservation')
    require(sum(row[-1] for row in atoms) == value, 'actual bridge mass')
    reachable = {ids[source_node]}; queue = deque(reachable)
    while queue:
        u = queue.popleft()
        for v, cap, rev in graph.g[u]:
            if cap and v not in reachable:
                reachable.add(v); queue.append(v)
    minimum_side = {node for node, i in ids.items() if i in reachable}
    minimum_cut = [(u, v, cap) for (u, v), cap in caps.items() if u in minimum_side and v not in minimum_side]
    require(sum(cap for u, v, cap in minimum_cut) == value, 'computed primal/minimum-cut equality')
    # The prescribed B/F profile is a separate literal cut witness.
    inside = {source_node} | {('r', r) for r in range(4)}
    inside |= {('cg', 0)} | {('ch', 0, h) for h in range(7)}
    if template['public_y'] is not None:
        inside.add(('ch', *template['public_y']))
    for r, c in template['active']:
        inside.add(('c', r, c))
        private = template['private'][r, c]
        whole_g = next(iter(private))[0] if (r, c) in template['whole'] else None
        for g in range(7):
            if g == whole_g:
                continue
            inside.add(('pg', r, c, g))
            for h in range(7):
                if (g, h) not in private:
                    inside.add(('ph', r, c, g, h))
    cut = [(u, v, cap) for (u, v), cap in caps.items() if u in inside and v not in inside]
    require(not any(u[0] == 'ph' for u, v, cap in cut), 'no actual bridge crosses prescribed cut')
    require(sum(cap for u, v, cap in cut) == 70, 'prescribed profile cut70')
    if value == 70:
        require(all(flow[u, v] == cap for u, v, cap in cut), 'prescribed forward cut saturated')
        require(all(flow[u, v] == 0 for u, v in caps if u not in inside and v in inside), 'prescribed backward cut zero')
    return {'network_edges': len(caps), 'maximum_flow': value, 'minimum_cut': value,
            'status': 'exact_mincut70' if value == 70 else 'smaller_mincut_not_a_cut70_control',
            'actual_flow_atoms': atoms, 'prescribed_cut_capacity': 70,
            'prescribed_cut': [[list(u), list(v), cap] for u, v, cap in cut],
            'computed_minimum_cut': [[list(u), list(v), cap] for u, v, cap in minimum_cut]}


def choose_eighteen(template, dinic):
    source_node, sink = ('selector source',), ('selector sink',)
    active_source = {p for p in template['source'] if p[:2] in template['active']}
    children = sorted({p[:2] for p in active_source}); leaves = sorted({p[2:] for p in active_source})
    nodes = [source_node, sink] + [('child', *p) for p in children] + [('leaf', *p) for p in leaves] + [('column', g) for g in range(7)]
    ids = {node: i for i, node in enumerate(nodes)}; graph = dinic(len(ids))
    for child in children:
        graph.add(ids[source_node], ids['child', *child], 1)
    refs = {p: graph.add(ids['child', *p[:2]], ids['leaf', *p[2:]], 1) for p in sorted(active_source)}
    for g, h in leaves:
        graph.add(ids['leaf', g, h], ids['column', g], 1)
    for g in range(7):
        graph.add(ids['column', g], ids[sink], 5)
    value = graph.flow(ids[source_node], ids[sink], 18)
    require(value == 18, 'actual child/leaf/column matching supplies18')
    chosen = [p for p, (u, k, cap) in refs.items() if cap - graph.g[u][k][1]]
    require(len(chosen) == 18 and set(chosen) <= active_source, '18 actual active-child points')
    require(len({p[:2] for p in chosen}) == 18 and len({p[2:] for p in chosen}) == 18, 'distinct children and full seven leaves')
    columns = Counter(g for r, c, g, h in chosen)
    require(max(columns.values()) <= 5, 'first-seven column cap5')
    require(max(Counter(r for r, c, g, h in chosen).values()) <= 5, 'first-five root cap5')
    def crt(r, c, g, h):
        x, y = r + 5 * c, g + 7 * h
        return x + 25 * ((y - x) * pow(25, -1, 49) % 49)
    residues = [crt(*p) for p in chosen]
    require(len(set(residues)) == 18, '18 distinct original residues')
    divisors = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
    maxima = {}; total = 0
    for d in divisors:
        counts = Counter(x % d for x in residues)
        cap = 18 if d == 1 else 5 if d in (5, 7, 35) else 1
        for a in range(d):
            require(counts[a] <= cap, 'every original numerical cylinder')
            total += 1
        maxima[d] = Q(max(counts.values()), 18)
    upper = sum(maxima[lcm(d, e)] for d, e in product(divisors, repeat=2))
    require(total == 1767 and upper <= Q(79, 9), 'all81 LCM terms under one actual law')
    return {'points': chosen, 'residues_mod1225': residues, 'probability_per_point': '1/18',
            'selected_inactive_children': 0, 'column_counts': dict(sorted(columns.items())),
            'cylinder_maxima': {str(d): str(v) for d, v in maxima.items()},
            'cylinders_checked': total, 'ordered_lcm_pairs': 81, 'gamma_upper': str(upper)}


def verify(dinic):
    controls = []
    for template in templates():
        literal = literal_checks(template)
        actual = actual_network(template, dinic)
        selection = choose_eighteen(template, dinic)
        shape = [''.join(str(template['costs'][r, c]) for rr, c in sorted(template['active']) if rr == r)
                 for r in range(4)]
        controls.append({'name': template['name'], 'family': template['family'], 'private_shape': shape,
                         'source_points': len(template['source']), 'source': sorted(template['source']),
                         'active_children': sorted(template['active']), 'public_y': template['public_y'],
                         'whole_private_columns': sorted(template['whole']),
                         **literal, 'network': actual, 'uniform18_law': selection})
    stats = Counter(control['network']['status'] for control in controls)
    require(len(controls) == 17, 'four B and nine F shapes plus four whole-column variants')
    require(stats == Counter({'exact_mincut70': 17}), 'all fixed actual-source controls have exact minimum cut70')
    return {'controls': controls, 'counts': {'templates': len(controls), **dict(stats)},
            'scope': 'Actual-source construction controls for four partial-gap B and nine fully-active G+y F shapes, with four cost3 whole-column variants. Each law uses one actual source and all original numerical labels. These finite controls do not prove profile exhaustiveness or the universal support implications, do not classify four-public-leaf F realizability, and make no Lean, original odd-cover, or cofactor-lifting claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module', type=Path, help='existing saturated-block file; default is adjacent')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    out = verify(load_dinic(args.base_module))
    args.output.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(out['counts']))
    for item in out['controls']:
        print(json.dumps({'name': item['name'], 'points': item['source_points'],
                          'mincut': item['network']['minimum_cut'],
                          'gamma_upper': item['uniform18_law']['gamma_upper']}))


if __name__ == '__main__':
    main()
