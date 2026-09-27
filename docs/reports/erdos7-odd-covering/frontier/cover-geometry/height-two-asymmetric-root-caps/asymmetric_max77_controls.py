#!/usr/bin/env python3
"""Exact actual-source controls for asymmetric root capacities; no universal theorem claim."""
from argparse import ArgumentParser
from collections import Counter, defaultdict, deque
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from pathlib import Path
import hashlib
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def generated_sources():
    for kind in (1, 2):
        for extra in ('H', 'L', 'K', 'M'):
            yield f'TN{kind}_{extra}', tn(kind, extra, False), 77
    yield 'TN2_K_four_owner', tn(2, 'K', True), 77
    f = {(0, 0): {(0, 0)}, (0, 1): {(0, 1)}}
    for c in range(2, 5):
        f[0, c] = {(0, c), (1, 0)}
    for c in range(5):
        f[1, c] = {(1, c), (2, c)}
    f.update({(r, c): set(product(range(7), repeat=2))
              for r in (2, 3) for c in range(5 if r == 2 else 4)})
    yield 'no_anchor459', flatten(f), 77
    for whole in (False, True):
        fibres = {(0, c): {(0, c)} for c in range(3)}
        fibres[0, 3] = {(0, 3), (0, 4)}
        fibres[0, 4] = {(0, h) for h in (range(7) if whole else (4, 5, 6))}
        fibres.update({(1, c): {(1, c), (2, c)} for c in range(5)})
        fibres.update({(r, c): set(product(range(7), repeat=2))
                       for r in (2, 3) for c in range(5 if r == 2 else 4)})
        yield 'FD_whole' if whole else 'FD_finite', flatten(fibres), 78


def flatten(fibres):
    return {(r, c, g, h) for (r, c), leaves in fibres.items() for g, h in leaves}


def tn(kind, extra, high):
    H, K, L, M, D, E, T = range(7)
    f = {(0, 0): {(L, 0)}, (0, 1): {(L, 1)}, (1, 0): {(H, 0)}}
    if kind == 1:
        for c in (2, 3):
            f[0, c] = {(L, c), (K, 0)}
        bonus = {'H': (H, 6), 'L': (L, 5), 'K': (K, 5), 'M': (M, 0)}[extra]
        f[0, 4] = {(L, 4), (K, 0), bonus}
        for c in range(1, 5):
            f[1, c] = {(H, c), (K, c)}
    else:
        for c in range(2, 5):
            f[0, c] = {(L, c), (K, 0)}
        for c in range(1, 4):
            f[1, c] = {(H, c), (K, c)}
        bonus = {'H': (H, 5), 'L': (L, 6), 'K': (K, 0 if high else 5), 'M': (M, 0)}[extra]
        f[1, 4] = {(H, 4), (K, 4), bonus}
    for c in range(5):
        f[2, c] = set(product(range(7), repeat=2)) if high else {(D, c), (E, c)}
    for c in range(4):
        f[3, c] = set(product(range(7), repeat=2))
    return flatten(f)


def source_checks(source):
    fibres = defaultdict(set)
    for r, c, g, h in source:
        require(0 <= r < 4 and 0 <= c < 5 and 0 <= g < 7 and 0 <= h < 7,
                'literal coordinates')
        fibres[r, c].add((g, h))
    children = {r: sorted(c for rr, c in fibres if rr == r) for r in range(4)}
    require(sorted(map(len, children.values())) == [4, 5, 5, 5], 'literal4555 occupancy')
    def tree(points, k):
        return sum(len({h for g, h in points if g == j}) >= k for j in range(7)) >= k
    require(tree({(g, h) for r, c, g, h in source}, 5), 'standalone five-tree')
    tests = 0
    for r, s in combinations(range(4), 2):
        for a in combinations(children[r], len(children[r]) - 2):
            for b in combinations(children[s], len(children[s]) - 2):
                points = set().union(*(fibres[r, c] for c in a), *(fibres[s, c] for c in b))
                require(tree(points, 3), 'actual pairwise ternary tree')
                tests += 1
    require(tests == 480, 'complete pair inventory')
    monochromatic = sum(len({g for c in cs for g, h in fibres[r, c]}) == 1
                        for r in range(4)
                        for cs in combinations(children[r], len(children[r])-2))
    return children, tests, monochromatic


class Network:
    def __init__(self, source, children, dinic):
        self.Dinic = dinic
        self.source = source
        self.edges = []
        self.ids = {}
        self.names = []
        self.S = self.node(('S',))
        self.T = self.node(('T',))
        for r in range(4):
            self.edge(('S',), ('r', r), 21)
            for c in children[r]:
                self.edge(('r', r), ('c', r, c), 7)
                for g in range(7):
                    self.edge(('c', r, c), ('pg', r, c, g), 6)
                    for h in range(7):
                        self.edge(('pg', r, c, g), ('ph', r, c, g, h), 2)
        for g in range(7):
            self.edge(('cg', g), ('T',), 21)
            for h in range(7):
                self.edge(('ch', g, h), ('cg', g), 7)
        for r, c, g, h in sorted(source):
            self.edge(('ph', r, c, g, h), ('ch', g, h), 126)

    def node(self, name):
        if name not in self.ids:
            self.ids[name] = len(self.names)
            self.names.append(name)
        return self.ids[name]

    def edge(self, u, v, cap):
        self.edges.append((self.node(u), self.node(v), cap))

    def solve(self, caps, inactive=None):
        d = self.Dinic(len(self.names))
        refs = []
        for u, v, cap in self.edges:
            if u == self.S:
                cap = caps[self.names[v][1]]
            refs.append(d.add(u, v, cap))
        # Pin the exact inactive-root set. 1000 exceeds every unpinned cut.
        if inactive is not None:
            for r in range(4):
                if r in inactive:
                    d.add(self.ids['r', r], self.T, 1000)
                else:
                    d.add(self.S, self.ids['r', r], 1000)
        value = d.flow(self.S, self.T, 10000)
        reach = {self.S}
        queue = deque([self.S])
        while queue:
            u = queue.popleft()
            for v, cap, _ in d.g[u]:
                if cap and v not in reach:
                    reach.add(v)
                    queue.append(v)
        require(self.T not in reach, 'complete maximum flow')
        flow = [cap - d.g[u][k][1] for u, k, cap in refs]
        cut = []
        balance = [0] * len(self.names)
        for idx, ((u, v, _), (ru, rk, cap), f) in enumerate(zip(self.edges, refs, flow)):
            require(0 <= f <= cap, 'every original arc capacity')
            balance[u] -= f
            balance[v] += f
            if u in reach and v not in reach:
                cut.append((idx, cap))
        cost = sum(cap for _, cap in cut)
        actual_inactive = sorted(r for r in range(4) if self.ids['r', r] not in reach)
        require(cost == value, 'constrained cut uses no pin edge')
        if inactive is None:
            require(balance[self.S] == -value and balance[self.T] == value and
                    all(x == 0 for i, x in enumerate(balance) if i not in (self.S, self.T)),
                    'original flow conservation')
        else:
            require(set(actual_inactive) == set(inactive), 'exact pinned inactive set')
        # Pinned runs certify cuts; pin-edge flow need not be original flow.
        roots = {self.names[v][1]: flow[i] for i, (u, v, cap) in enumerate(self.edges) if u == self.S}
        return {'maximum': value, 'inactive_roots': actual_inactive,
                'root_flow': roots, 'cut_capacity': cost,
                'cut_arc_counts': dict(sorted(Counter(cap for _, cap in cut).items())),
                'cut_indices': [idx for idx, cap in cut], 'reachable_vertices': sorted(reach)}


def original_cut(net, reach):
    inactive = sorted(r for r in range(4) if net.ids['r', r] not in reach)
    cost = sum(cap for u, v, cap in net.edges if u in reach and v not in reach)
    return {'capacity': cost, 'inactive_roots': inactive}


def suppliers(rec, allow_singleton):
    n, cap = len(rec['inactive_roots']), rec['capacity']
    if n == 2 and cap == 77:
        return 'TA'
    if n == 3 and cap <= 78:
        return 'IA'
    if allow_singleton and n == 1 and cap == 77:
        return 'singleton77'
    return None


def actual_uncrossing(net, modified_runs):
    candidates = []
    for size, target in ((1, 77), (2, 78)):
        for inactive in combinations(range(4), size):
            C = net.solve([21] * 4, inactive)
            if C['maximum'] == target:
                candidates.append((list(inactive), target, set(C['reachable_vertices']),
                                   'minimum_with_fixed_root_mask'))
    # The TN and no-anchor examples also have this specified NONMINIMUM cut78.
    # Every unselected private leaf stub is source-side; every public node is sink-side.
    if len([p for p in net.source if p[0] in (0, 1)]) == 18:
        reach = {net.S}
        for idx, node in enumerate(net.names):
            if node[0] in ('r', 'c', 'pg') and node[1] in (0, 1):
                reach.add(idx)
            if node[0] == 'ph' and node[1] in (0, 1) and tuple(node[1:]) not in net.source:
                reach.add(idx)
        rec = original_cut(net, reach)
        require(rec == {'capacity': 78, 'inactive_roots': [2, 3]}, 'complete specified private18 cut78')
        candidates.append(([2, 3], 78, reach, 'specified_private18_cut78'))
    controls = []
    for inactive, target, cset, kind in candidates:
        size = len(inactive)
        for r in inactive:
            D = modified_runs[r]
            if D['maximum'] == 77:
                controls.append({'C_inactive': inactive, 'C_capacity': target,
                                 'C_kind': kind, 'selected_root': r,
                                 'branch': 'asymmetric77_exactC'})
                continue
            require(D['maximum'] <= 76, 'integer perturbation failure')
            dset = set(D['reachable_vertices'])
            dc = original_cut(net, dset)
            require(dc['capacity'] == D['maximum'] + len(set(dc['inactive_roots'])-{r}),
                    'actual original versus modified cut identity')
            meet = original_cut(net, cset & dset)
            join = original_cut(net, cset | dset)
            require(meet['capacity'] + join['capacity'] <= target + dc['capacity'],
                    'actual directed-cut submodularity')
            require(set(meet['inactive_roots']) == set(inactive) | set(dc['inactive_roots']) and
                    set(join['inactive_roots']) == set(inactive) & set(dc['inactive_roots']),
                    'actual inactive masks under uncrossing')
            require(min(meet['capacity'], join['capacity']) >= 77, 'original max77 cut floor')
            supplied = [label+':'+suppliers(rec, size == 2)
                        for label, rec in [('D', dc), ('intersection', meet), ('union', join)]
                        if suppliers(rec, size == 2)]
            require(supplied, 'actual failed perturbation reaches an existing supplier')
            controls.append({'C_inactive': inactive, 'C_capacity': target,
                             'C_kind': kind, 'selected_root': r, 'branch': 'actual_uncrossing',
                             'modified_D_capacity': D['maximum'], 'original_D': dc,
                             'intersection': meet, 'union': join, 'suppliers': supplied})
    return controls


def compact(rec):
    return {k: v for k, v in rec.items() if k not in ('cut_indices', 'reachable_vertices')}


def audit_source(name, source, expected, Dinic):
    children, tests, monochromatic = source_checks(source)
    if name == 'no_anchor459':
        require(monochromatic == 0 and len(source) == 459, 'no-anchor459 source identity')
    net = Network(source, children, Dinic)
    original = net.solve([21] * 4)
    require(original['maximum'] == expected, name + ' original max')
    modifications = []
    modified_runs = []
    capped20 = net.solve([20] * 4)
    for r in range(4):
        caps = [20] * 4
        caps[r] = 21
        modified = net.solve(caps)
        modified_runs.append(modified)
        require(modified['maximum'] <= expected, 'lowered network monotonicity')
        # All source cuts with r inactive and at most one companion.
        exact = []
        pin_results = []
        for inactive in ({r}, *({r, s} for s in range(4) if s != r)):
            rec = net.solve(caps, inactive)
            pin_results.append({'inactive_roots': sorted(inactive), 'minimum_capacity': rec['maximum']})
            if modified['maximum'] == 77 and rec['maximum'] == 77:
                exact.append(rec)
                reach = set(rec['reachable_vertices'])
                require(net.ids['r', r] not in reach, 'selected root crosses exact C')
                # Inspect a genuine maximum flow, not the auxiliary pinned flow.
                require(modified['root_flow'][r] == 21, 'exact C forces selected-root saturation in observed flow')
        # If the root could have <=20 in any value77 flow, this maxflow would retain77.
        if exact:
            require(capped20['maximum'] == 76, 'all value77 flows require root21')
        modifications.append({'selected_root': r, 'modified': compact(modified),
                              'root_at_most20_maximum': capped20['maximum'],
                              'pinned_inactive_cut_minima': pin_results,
                              'exact77_C': [compact(rec) for rec in exact],
                              'exact_C_condition_met': bool(exact),
                              'all_value77_flows_root21_verified': True if exact else None})
    payload = json.dumps(sorted(source), separators=(',', ':')).encode()
    return {'name': name, 'points': len(source), 'source_sha256': hashlib.sha256(payload).hexdigest(),
            'occupancy': [len(children[r]) for r in range(4)], 'pair_tests': tests,
            'standalone_five_tree': True, 'monochromatic_legal_restrictions': monochromatic, 'vertices': len(net.names), 'arcs': len(net.edges),
            'original': compact(original), 'all_roots20': compact(capped20), 'asymmetric': modifications,
            'actual_uncrossing': actual_uncrossing(net, modified_runs) if expected == 77 else [],
            'original_max77_premise': expected == 77}


def integer_uncrossing():
    roots = frozenset(range(4))
    subsets = [frozenset(c) for n in range(5) for c in combinations(roots, n)]
    results = []
    for branch, size, cC in [('singleton77', 1, 77), ('pair78', 2, 78)]:
        counts = Counter()
        outcomes = Counter()
        for C in subsets:
            if len(C) != size:
                continue
            for r in C:
                for D in subsets:
                    j = len(D - {r})
                    for cD in range(77, 77 + j):
                        counts['lowered_cut_candidates'] += 1
                        if cD < 21 * len(D):
                            counts['four_inactive_capacity_exclusions'] += 1
                            continue
                        U, V = C | D, C & D
                        feasible = []
                        for cu in range(max(77, 21 * len(U)), cC + cD - 76):
                            for cv in range(max(77, 21 * len(V)), cC + cD - cu + 1):
                                # C∩D source-side has inactive set U; C∪D has V.
                                targets = [(D, cD, 'D'), (U, cu, 'intersection'), (V, cv, 'union')]
                                choices = []
                                for S, cap, label in targets:
                                    if len(S) == 2 and cap == 77:
                                        choices.append(label + ':TA')
                                    if len(S) == 3 and cap <= 78:
                                        choices.append(label + ':IA')
                                    if branch == 'pair78' and len(S) == 1 and cap == 77:
                                        choices.append(label + ':singleton77')
                                require(choices, 'uncrossing has no prior supplier')
                                feasible.append((cu, cv))
                                outcomes[';'.join(choices)] += 1
                        if not feasible:
                            counts['uncrossing_capacity_exclusions'] += 1
                        else:
                            counts['surviving_lowered_cuts'] += 1
                            counts['surviving_assignments'] += len(feasible)
        results.append({'branch': branch, 'counts': dict(counts),
                        'supplier_assignment_histogram': dict(sorted(outcomes.items()))})
    return {'scope': 'Exhaustive four-root integer cut interface only; no actual-source realization inferred.',
            'enumeration': 'All labelled C masks of size1 or2; each selected r in C; all16 D masks; original D capacity77 through76+j, j=|D\\{r}|; all integer uncrossed capacities with each >=max(77,21*inactive roots) and sum <=c(C)+c(D).',
            'branches': results}


def main():
    p = ArgumentParser(description=__doc__)
    p.add_argument('--geometry-root', type=Path, required=True,
                   help='Repository frontier/cover-geometry directory')
    p.add_argument('--extra-source', type=Path, action='append', default=[],
                   help='Optional JSON with source list and expected_maximum (or minimum_cut)')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    fixture = a.geometry_root / 'height-two-cut72-full-k4'
    dinic_path = fixture / 'height_two_saturated_block_transport.py'
    spec = spec_from_file_location('existing_dinic', dinic_path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    sources = []
    inputs = []
    for name, fn, key in [('actual68', 'height_two_cut77_actual_bad_neighborhood.json', None),
                          ('actual164', 'height_two_cut77_forced_twenty.json', None),
                          ('actual192', 'height_two_cut77_complement_transport.json', 'actual_nonrobust192_source')]:
        path = fixture / fn
        data = json.loads(path.read_text())
        if key:
            data = data[key]
        sources.append((name, set(map(tuple, data['source'])), 77))
        inputs.append({'relative_path': str(path.relative_to(a.geometry_root)),
                       'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    sources.extend(generated_sources())
    for path in a.extra_source:
        data = json.loads(path.read_text())
        sources.append((data.get('name', path.stem), set(map(tuple, data['source'])),
                        data.get('expected_maximum', data.get('minimum_cut'))))
        inputs.append({'extra_source': path.name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    controls = [audit_source(*source, module.Dinic) for source in sources]
    exact_count = sum(len(r['exact77_C']) for s in controls for r in s['asymmetric'])
    result = {'result': 'PASS', 'scope': 'Exact finite actual-source flow/cut controls and separate integer uncrossing interface. Not Lean, no universal selected-repair proof, no unrestricted Erdos7 conclusion.',
              'input_files': inputs, 'dinic_sha256': hashlib.sha256(dinic_path.read_bytes()).hexdigest(),
              'summary': {'actual_sources': len(controls),
                          'original_max77_sources': sum(s['original_max77_premise'] for s in controls),
                          'original_max78_boundary_controls': sum(not s['original_max77_premise'] for s in controls),
                          'pair_tests': sum(s['pair_tests'] for s in controls),
                          'asymmetric_networks': 4*len(controls), 'exact77_selected_cut_witnesses': exact_count,
                          'exact77_selected_cut_witnesses_with_original_max77': sum(len(r['exact77_C']) for s in controls if s['original_max77_premise'] for r in s['asymmetric']),
                          'actual_cut_branch_controls': sum(len(s['actual_uncrossing']) for s in controls),
                          'actual_failed_perturbation_uncrossings': sum(c['branch'] == 'actual_uncrossing' for s in controls for c in s['actual_uncrossing'])},
              'actual_source_controls': controls, 'integer_uncrossing': integer_uncrossing()}
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['summary'], indent=2))
    print(json.dumps([r['counts'] for r in result['integer_uncrossing']['branches']], indent=2))


if __name__ == '__main__':
    main()
