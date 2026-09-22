#!/usr/bin/env python3
"""Exact height-two common-law bound 46/9 for any seven fixed cap laws.

Regenerate all 3276 integer full-law row quotas, 20 original-phase
orbits, and all row words. Exact integral cap flows are certified by
residual potentials. A retained finite decision DAG covers every pair
row quota and supplies rational upper certificates for the common
layout-mixture LP. No numerical optimizer or third-party package is used.

The accompanying ordinary proof supplies the extremal-law reduction,
orbit and aggregation arguments, and finite minimax quantifiers. This
program is not Lean certification. Only stdout is written.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json

ROWS = tuple(range(4))
PAIRS = tuple(combinations(ROWS, 2))
TARGET = F(46, 9)
DEFAULT_CERTIFICATES = Path(__file__).with_name('height_two_phase_orbit_certificates.json')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def phase_orbits():
    """Root partitions of P1,M1,parent(P2),parent(M2), plus leaf equality."""
    def partitions(word=(0,)):
        if len(word) == 4:
            yield word
        else:
            for value in range(max(word)+2):
                yield from partitions(word+(value,))
    result = tuple((roots, same) for roots in partitions()
                   for same in ((True, False) if roots[2] == roots[3] else (False,)))
    require(len(result) == 20, 'phase orbit count')
    return result


ORBITS = phase_orbits()


def phase_groups(orbit):
    """Equal-cost leaf groups: root, root multiplicity, leaf count, P2, M2."""
    require(orbit in ORBITS, 'invalid phase orbit')
    roots, same = orbit
    count = max(roots)+1
    groups = []
    for root in range(count):
        marked = []
        if roots[2] == root:
            marked.append((1, int(roots[3] == root and same)))
        if roots[3] == root and not (roots[2] == root and same):
            marked.append((0, 1))
        groups.extend((root, 1, 1, pure, mixed) for pure, mixed in marked)
        groups.append((root, 1, 7-len(marked), 0, 0))
    groups.append((count, 7-count, 7, 0, 0))
    require(sum(mult*leaves for _, mult, leaves, _, _ in groups) == 49,
            'aggregated leaf count')
    return tuple(groups)


def cap_price_numerator(branching, row_count, word, orbit, quotas):
    """Exact maximum times branching**2, with fixed integer row quotas.

A word entry equal to row_count denotes a mixed label outside the
allowed rows. Unused rows with identical costs may be combined into one
row. Every returned value has an integral feasible flow and an equal
upper certificate from an exact residual potential.
"""
    b = branching
    require(type(b) is int and b in (3, 5), 'branching must be 3 or 5')
    require(type(row_count) is int and 1 <= row_count <= 4, 'row count')
    require(len(word) == 3 and all(type(r) is int and 0 <= r <= row_count for r in word), 'row word')
    require(len(quotas) == row_count and all(type(q) is int and q >= 0 for q in quotas)
            and sum(quotas) == b*b, 'integer row quotas')
    groups = phase_groups(orbit)
    roots, _ = orbit
    root_ids = tuple(sorted({g[0] for g in groups}))
    count = 2+row_count+len(groups)+len(root_ids)
    source, sink = count-2, count-1
    adjacency = [[] for _ in range(count)]
    original = []

    def edge(u, v, capacity, cost):
        original.append((u, len(adjacency[u]), v, capacity, cost))
        adjacency[u].append([v, len(adjacency[v]), capacity, cost])
        adjacency[v].append([u, len(adjacency[u])-1, 0, -cost])

    for r, quota in enumerate(quotas):
        edge(source, r, quota, 0)
    for i, (root, multiplicity, leaves, pure, mixed) in enumerate(groups):
        for r in range(row_count):
            load = (1+(r == word[0])+(root == roots[0])
                    +((root == roots[1]) and r == word[1])
                    +pure+(mixed and r == word[2]))
            edge(r, row_count+i, b*b, load*load)
        edge(row_count+i, row_count+len(groups)+root_ids.index(root), multiplicity*leaves, 0)
    for root in root_ids:
        multiplicity = next(g[1] for g in groups if g[0] == root)
        edge(row_count+len(groups)+root_ids.index(root), sink, b*multiplicity, 0)

    flow, value = 0, 0
    while flow < b*b:
        distance, previous = [None]*count, [None]*count
        distance[source] = 0
        for _ in range(count-1):
            changed = False
            for u, edges in enumerate(adjacency):
                if distance[u] is None:
                    continue
                for i, (v, _, capacity, cost) in enumerate(edges):
                    if capacity and (distance[v] is None or distance[v] < distance[u]+cost):
                        distance[v], previous[v] = distance[u]+cost, (u, i)
                        changed = True
            if not changed:
                break
        require(distance[sink] is not None, 'cap flow is infeasible')
        amount, vertex, path = b*b-flow, sink, []
        while vertex != source:
            require(len(path) < count and previous[vertex] is not None, 'invalid augmenting path')
            u, i = previous[vertex]
            path.append((u, i))
            amount = min(amount, adjacency[u][i][2])
            vertex = u
        require(amount > 0, 'zero augmentation')
        require(sum(adjacency[u][i][3] for u, i in path) == distance[sink], 'path cost')
        for u, i in path:
            v, reverse, _, _ = adjacency[u][i]
            adjacency[u][i][2] -= amount
            adjacency[v][reverse][2] += amount
        flow += amount
        value += amount*distance[sink]

    potential = [0]*count
    for iteration in range(count):
        changed = False
        for u, edges in enumerate(adjacency):
            for v, _, capacity, cost in edges:
                if capacity and potential[v] < potential[u]+cost:
                    potential[v] = potential[u]+cost
                    changed = True
        if not changed:
            break
        require(iteration < count-1, 'positive residual cycle')
    balance = [0]*count
    direct_value, upper = 0, b*b*(potential[sink]-potential[source])
    for u, i, v, capacity, cost in original:
        used = capacity-adjacency[u][i][2]
        require(0 <= used <= capacity, 'flow edge capacity')
        balance[u] -= used
        balance[v] += used
        direct_value += used*cost
        upper += capacity*max(0, cost-potential[v]+potential[u])
    require(balance[source] == -b*b and balance[sink] == b*b
            and all(balance[u] == 0 for u in range(count) if u not in (source, sink)), 'flow conservation')
    require(value == direct_value == upper, 'flow and upper certificate disagree')
    return value


def row_weights(word):
    labels = [(j, None) for j in range(3)]+list(enumerate(word))
    weights = [[0]*3 for _ in ROWS]
    for (i, r), (j, s) in product(labels, repeat=2):
        depth = max(i, j)
        if r is None and s is not None:
            weights[s][depth] += 1
        elif r is not None and (s is None or r == s):
            weights[r][depth] += 1
    for j, selected in enumerate(word):
        for r in ROWS:
            expected = (2*j+3+2*word[:j].count(selected))*(selected == r)+2*word[:j].count(r)
            require(weights[r][j] == expected, 'original-label row coefficient')
    return weights


def full_row_quotas():
    return tuple((a, b, c, 25-a-b-c) for a in range(26)
                 for b in range(26-a) for c in range(26-a-b))


def verify_certificates(path=DEFAULT_CERTIFICATES):
    data = json.loads(Path(path).read_text())
    require(data['height'] == 2 and data['target'] == str(TARGET), 'certificate scope')
    require(data['branching'] == list(range(10)) and data['beta_denominator'] == 25
            and data['pair_denominator'] == 9, 'quota domains')
    betas, words = full_row_quotas(), tuple(product(ROWS, repeat=3))
    require(len(betas) == 3276 and len(data['roots']) == len(betas), 'full beta domain')
    columns = tuple((word, orbit) for word in words for orbit in ORBITS)
    width = len(columns)
    require(width == 1280, 'complete original word/orbit domain')
    order = tuple(tuple(int(word[0] == r)-int(word[0] == r+1) for word, _ in columns) for r in range(3))
    old_prices = tuple(tuple(25*(27*(word[0] == s)
                         +3*(row_weights(word)[r][1]+row_weights(word)[s][1])
                         +row_weights(word)[r][2]+row_weights(word)[s][2]) for word, _ in columns)
                       for r, s in PAIRS)
    pair_cache = {}
    for word in product(range(3), repeat=3):
        for orbit in ORBITS:
            pair_cache[word, orbit] = tuple(cap_price_numerator(3, 2, word, orbit, (k, 9-k)) for k in range(10))
    pair_prices = tuple(tuple(tuple(25*pair_cache[
        tuple(0 if a == r else 1 if a == s else 2 for a in word), orbit][k]
        for word, orbit in columns) for k in range(10)) for r, s in PAIRS)

    prepared = []
    for entry in data['certificates']:
        modes, y = tuple(entry['modes']), tuple(map(F, entry['multipliers']))
        require(len(modes) == 6 and all(type(k) is int and -1 <= k <= 9 for k in modes), 'pair certificate modes')
        require(len(y) == 10 and min(y) >= 0 and sum(y[:6])+y[9] == 1, 'nonnegative normalized dual')
        tau = TARGET-F(23, 9)*sum(y[p] for p in range(6) if modes[p] == -1)
        denominator = lcm(*(x.denominator for x in y), tau.denominator)
        integers = tuple(int(x*denominator) for x in y)
        prepared.append((modes, integers, int(225*tau*denominator)))
    nodes = data['nodes']
    for i, node in enumerate(nodes):
        if node[0] == 'leaf':
            require(len(node) == 2 and type(node[1]) is int and 0 <= node[1] < len(prepared), 'leaf certificate address')
        else:
            require(node[0] == 'branch' and len(node) == 3 and type(node[1]) is int and 0 <= node[1] < 6,
                    'branch pair address')
            require(len(node[2]) == 10 and all(type(child) is int and 0 <= child < i for child in node[2]),
                    'complete acyclic ten-way branch')
    full_cache, seen_nodes, seen_certificates = {}, set(), set()
    counts = {'nodes': 0, 'leaves': 0, 'exact_columns': 0}

    def full_prices(word, beta):
        active = tuple(dict.fromkeys(word))
        canonical = tuple(active.index(r) for r in word)
        quotas = tuple(beta[r] for r in active)+(25-sum(beta[r] for r in active),)
        key = canonical, quotas
        if key not in full_cache:
            full_cache[key] = tuple(cap_price_numerator(5, len(quotas), canonical, orbit, quotas) for orbit in ORBITS)
        return full_cache[key]

    def visit(node_id, chosen, full_units):
        require(type(node_id) is int and 0 <= node_id < len(nodes), 'decision root address')
        counts['nodes'] += 1
        seen_nodes.add(node_id)
        node = nodes[node_id]
        if node[0] == 'branch':
            p = node[1]
            require(chosen[p] == -1, 'pair quota branched twice')
            for k, child in enumerate(node[2]):
                visit(child, chosen[:p]+(k,)+chosen[p+1:], full_units)
            return
        cert_id = node[1]
        seen_certificates.add(cert_id)
        modes, y, constant = prepared[cert_id]
        require(all(mode == -1 or chosen[p] == mode for p, mode in enumerate(modes)), 'certificate outside its quota branch')
        active_pairs = tuple((y[p], old_prices[p] if modes[p] == -1 else pair_prices[p][modes[p]])
                             for p in range(6) if y[p])
        active_orders = tuple((225*y[6+r], order[r]) for r in range(3) if y[6+r])
        for j in range(width):
            slack = (constant+sum(n*col[j] for n, col in active_orders)
                     -sum(n*col[j] for n, col in active_pairs)-y[9]*full_units[j])
            require(slack >= 0, f'negative layout column: certificate={cert_id}, column={j}')
        counts['leaves'] += 1
        counts['exact_columns'] += width+1

    for beta, root_id in zip(betas, data['roots']):
        full_units = tuple(9*v for word in words for v in full_prices(word, beta))
        visit(root_id, (-1,)*6, full_units)
    require(counts == data['counts'], 'expanded coverage counts')
    require(len(seen_nodes) == len(nodes) and len(seen_certificates) == len(prepared), 'unused certificate data')
    flow_prices = len(pair_cache)*10+len(full_cache)*20
    require(flow_prices == data['flow_prices'], 'exact cap-price coverage')
    return {'height': 2, 'target': TARGET, 'full_row_quotas': len(betas), 'pair_quotas_each': 10,
            'phase_orbits': len(ORBITS), 'original_word_orbit_columns': width,
            'exact_cap_prices': flow_prices, 'distinct_duals': len(prepared),
            'retained_decision_nodes': len(nodes), **counts,
            'scope': 'any seven fixed actual cap laws; one convex mixture before every independent original phase'}


def sharp_fixed_component_game():
    """A real seven-component game attains 46/9; no source-optimality claim."""
    divisors = (1, 5, 7, 35, 49, 245)
    layouts = []
    for row, center in ((1, 0), (2, 1), (3, 2)):
        phases = []
        for j in range(3):
            m = 7**j
            phases.extend((center % m, next(a for a in range(5*m) if a % 5 == row and a % m == center % m)))
        layouts.append(tuple(phases))
    points = tuple(product(range(1, 5), range(49)))
    prices = {}
    for row, leaf in points:
        crt = leaf+49*((row-leaf)*4 % 5)
        prices[row, leaf] = F(sum(sum(crt % d == a for d, a in zip(divisors, layout))**2 for layout in layouts), 3)
    families = ((tuple(range(1, 5)), 5),)+tuple((pair, 3) for pair in combinations(range(1, 5), 2))
    expected = tuple(map(F, ('26/5', '20/3', '20/3', '46/9', '20/3', '46/9', '46/9')))
    inactive_laws, values = [], []
    for (allowed, b), want in zip(families, expected):
        selected, leaves, roots = [], set(), [0]*7
        for point in sorted((p for p in points if p[0] in allowed), key=lambda p: (-prices[p], p)):
            leaf = point[1]
            if leaf not in leaves and roots[leaf % 7] < b:
                selected.append(point)
                leaves.add(leaf)
                roots[leaf % 7] += 1
                if len(selected) == b*b:
                    break
        require(len(selected) == b*b, 'sharp witness cap basis')
        value = sum((prices[p] for p in selected), F())/(b*b)
        require(value == want, 'sharp component price')
        values.append(value)
        if len(allowed) == 2 and 4 in allowed:
            active = next(r for r in allowed if r != 4)
            require(set(selected) == {(active, a+7*c) for a, c in product(range(3), repeat=2)}, 'sharp product component')
            inactive_laws.extend(selected)
    require(min(values) == TARGET and len(set(inactive_laws)) == 27, 'sharp minimax lower witness')
    actual = sum((sum((leaf+49*((row-leaf)*4 % 5)) % d == a for d, a in zip(divisors, layouts[0]))**2
                  for row, leaf in inactive_laws), F())/27
    require(actual == TARGET, 'sharp product law attaining layout')
    return {'three_layouts': layouts, 'weights': ('1/3',)*3, 'seven_component_prices': values,
            'fixed_component_game_value': TARGET,
            'scope': 'sharpness for prescribed components; not sharpness of unrestricted laws on the source'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates', type=Path, default=DEFAULT_CERTIFICATES, help='exact decision certificate JSON')
    parser.add_argument('--compact', action='store_true', help='emit one-line JSON')
    args = parser.parse_args()
    result = {'universal_upper': verify_certificates(args.certificates), 'sharp_game': sharp_fixed_component_game(),
              'verification': 'integer cap flows with equal dual values and exact rational layout inequalities; ordinary proof, not Lean'}
    print(json.dumps(result, default=str, indent=None if args.compact else 2, sort_keys=True))


if __name__ == '__main__':
    main()
