#!/usr/bin/env python3
"""Exact sharp295 transport on a5x7 actual support of mass21.

The proof is the minimal-support/minimum-cut case analysis in Report449.
Finite controls check the constructor, not the universal quantifier. This
module is import-safe and reuses Dinic from the earlier saturated-block
module; it neither changes that implementation nor runs its controls.
"""
from collections import Counter, deque
from fractions import Fraction as Q
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from pathlib import Path
import argparse
import json
import random


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_dinic(path=None):
    path = Path(path) if path else Path(__file__).with_name('height_two_saturated_block_transport.py')
    spec = spec_from_file_location('_sharp_transport_existing_dinic', path)
    require(spec is not None and spec.loader is not None, 'existing Dinic module spec')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.Dinic


def support(edges):
    edges = set(edges)
    require(all(type(i) is int and type(j) is int and 0 <= i < 5 and 0 <= j < 7
                for i, j in edges), 'literal5x7 support')
    return edges


def network(edges, dinic, limit=30, column_caps=None):
    """Return an integral flow and residual reachable cut; cut valid at maxflow."""
    edges = support(edges)
    caps = [7] * 7 if column_caps is None else list(column_caps)
    require(len(caps) == 7 and all(type(v) is int and v >= 0 for v in caps), 'column caps')
    graph = dinic(14)
    source, sink = 12, 13
    refs = {}
    for i in range(5):
        graph.add(source, i, 6)
    for j, cap in enumerate(caps):
        graph.add(5 + j, sink, cap)
    for i, j in sorted(edges):
        refs[i, j] = graph.add(i, 5 + j, 2)
    total = graph.flow(source, sink, limit)
    law = {e: cap - graph.g[u][k][1] for e, (u, k, cap) in refs.items()}
    reachable = {source}
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v, cap, _ in graph.g[u]:
            if cap and v not in reachable:
                reachable.add(v)
                queue.append(v)
    inside_rows = {i for i in range(5) if i in reachable}
    inside_columns = {j for j in range(7) if 5 + j in reachable}
    return total, law, inside_rows, inside_columns


def margins(law):
    return ([sum(law.get((i, j), 0) for j in range(7)) for i in range(5)],
            [sum(law.get((i, j), 0) for i in range(5)) for j in range(7)])


def check(law, edges, mass=21, bound=None, column_caps=None):
    require(set(law) <= edges, 'supported on the allowed actual cells')
    require(all(type(v) in (int, Q) and 0 <= v <= 2 for v in law.values()), 'exact rational entry caps')
    rr, cc = margins(law)
    caps = [7] * 7 if column_caps is None else column_caps
    require(sum(law.values()) == mass, 'exact total')
    require(max(rr) <= 6 and all(c <= cap for c, cap in zip(cc, caps)), 'row and column caps')
    charges = [20 * rr[i] + 20 * cc[j] + 25 * law.get((i, j), 0)
               for i in range(5) for j in range(7)]
    if bound is not None:
        require(all(v <= bound for v in charges), 'all35 cells meet charge bound')
    return max(charges)


def allocate017(degrees, eligible):
    k = len(eligible)
    require(k in (4, 5), 'at least4 eligible common-column rows')
    if k == 5:
        return {i: Q(7, 5) for i in eligible}
    high = {i for i in eligible if degrees[i] == 2}
    require(len(high) <= 3, 'at most3 high-degree eligible rows')
    if not high:
        return {i: Q(7, 4) for i in eligible}
    return {i: 2 - Q(1, len(high)) if i in high else Q(2) for i in eligible}


def allocate114(degrees):
    require(len(degrees) == 4 and sum(degrees.values()) == 4 and max(degrees.values()) <= 2,
            'four crossing edges with degree at most2')
    high = {i for i, d in degrees.items() if d == 2}
    if not high:
        return {i: Q(7, 4) for i in degrees}
    require(len(high) in (1, 2), 'one or two high-degree rows')
    return {i: 2 - Q(1, len(high)) if i in high else Q(2) for i in degrees}


def serialize(law):
    return [[i, j, str(v)] for (i, j), v in sorted(law.items()) if v]


def construct(edges, initial=None, dinic=None):
    dinic = load_dinic() if dinic is None else dinic
    edges = support(edges)
    if initial is None:
        total, base, _, _ = network(edges, dinic, limit=21)
        if total < 21:
            return None
    else:
        base = dict(initial)
    check(base, edges, bound=310)
    minimal = set(edges)
    for edge in sorted(edges):
        trial = minimal - {edge}
        if network(trial, dinic)[0] >= 21:
            minimal = trial
    total, old, inside_rows, inside_columns = network(minimal, dinic)
    require(total in (21, 22), 'minimal-support maxflow21 or22')
    require(all(network(minimal - {edge}, dinic)[0] <= 20 for edge in minimal),
            'every retained edge essential for21')
    law = {}
    cut = None
    if total == 22:
        require(len(minimal) == 11 and all(old[e] == 2 for e in minimal), 'eleven saturated edges at22')
        require(max(sum(i == r for i, j in minimal) for r in range(5)) <= 3
                and max(sum(j == c for i, j in minimal) for c in range(7)) <= 3,
                'minimal22 degrees at most3')
        law = {e: Q(21, 11) for e in minimal}
        case = 'M22'
    else:
        crossing = {(i, j) for i, j in minimal if i in inside_rows and j not in inside_columns}
        a, b, c = 5 - len(inside_rows), len(inside_columns), len(crossing)
        require(6 * a + 7 * b + 2 * c == 21, 'residual cut capacity21')
        require((a, b, c) in ((0, 3, 0), (0, 1, 7), (1, 1, 4)), 'feasible minimum-cut type')
        rr, cc = margins(old)
        require(all(rr[i] == 6 for i in set(range(5)) - inside_rows), 'outside rows saturated')
        require(all(cc[j] == 7 for j in inside_columns), 'inside columns saturated')
        require(all(old[e] == 2 for e in crossing), 'crossing entries saturated')
        require(all(old.get((i, j), 0) == 0 for i in set(range(5)) - inside_rows for j in inside_columns),
                'backward cut flow zero')
        cut = {'type': [a, b, c], 'inside_rows': sorted(inside_rows), 'inside_columns': sorted(inside_columns),
               'crossing_edges': sorted(crossing), 'capacity': 21}
        case = f'cut{a}{b}{c}'
        if (a, b, c) == (0, 3, 0):
            for j in inside_columns:
                neighbors = {i for i, jj in minimal if jj == j}
                require(len(neighbors) >= 4, 'inside column has at least4 neighbors')
                for i in neighbors:
                    law[i, j] = Q(7, len(neighbors))
        elif (a, b, c) == (0, 1, 7):
            jstar = next(iter(inside_columns))
            degrees = {i: sum(ii == i for ii, j in crossing) for i in range(5)}
            require(sum(degrees.values()) == 7 and max(degrees.values()) <= 3, 'seven crossing degrees')
            eligible = {i for i in range(5) if (i, jstar) in minimal and degrees[i] <= 2}
            law = {e: Q(2) for e in crossing}
            law.update({(i, jstar): v for i, v in allocate017(degrees, eligible).items()})
        else:
            rstar = next(iter(set(range(5)) - inside_rows))
            jstar = next(iter(inside_columns))
            degrees = {i: sum(ii == i for ii, j in crossing) for i in inside_rows}
            require(all((i, jstar) in minimal for i in inside_rows), 'all four common-column edges exist')
            law = {e: Q(2) for e in crossing}
            law.update({(i, j): Q(v) for (i, j), v in old.items() if i == rstar and v})
            law.update({(i, jstar): v for i, v in allocate114(degrees).items()})
    sharp_max = check(law, edges, bound=295)
    mixed = {e: Q(3, 4) * law.get(e, 0) + Q(1, 4) * base.get(e, 0) for e in edges}
    mixed_max = check(mixed, edges, bound=Q(1195, 4))
    initial_positive = {e for e, v in base.items() if v > 0}
    mixed_positive = {e for e, v in mixed.items() if v > 0}
    require(initial_positive <= mixed_positive <= edges, 'initial positive entries preserved')
    if initial_positive == edges:
        require(mixed_positive == edges, 'exact same positive support')
    return {'case': case, 'minimal_support': sorted(minimal), 'maxflow_on_minimal_support': total,
            'cut': cut, 'initial': serialize(base), 'sharp_law': serialize(law), 'mixed_law': serialize(mixed),
            'sharp_max': str(sharp_max), 'mixed_max': str(mixed_max),
            'cells_checked_per_law': 35, 'initial_positive_cells': len(initial_positive),
            'mixed_positive_cells': len(mixed_positive),
            'exact_same_positive_support': initial_positive == mixed_positive}


def degree_controls():
    n017 = n114 = 0
    for ds in product(range(4), repeat=5):
        if sum(ds) != 7:
            continue
        eligible = [i for i, d in enumerate(ds) if d <= 2]
        for k in (4, 5):
            for rows in combinations(eligible, k):
                values = allocate017(dict(enumerate(ds)), set(rows))
                require(sum(values.values()) == 7, '017 common-column total')
                for i, d in enumerate(ds):
                    v = values.get(i, 0)
                    require(0 <= v <= 2 and 2 * d + v <= 6, '017 entry and row caps')
                    require(20 * (2 * d + v) + 140 + 25 * v <= 295, '017 common-column scores')
                n017 += 1
    for ds in product(range(3), repeat=4):
        if sum(ds) != 4:
            continue
        values = allocate114(dict(enumerate(ds)))
        require(sum(values.values()) == 7, '114 common-column total')
        col_cap = 6 if ds.count(2) == 2 else 7
        for i, d in enumerate(ds):
            v = values[i]
            require(0 <= v <= 2 and 2 * d + v <= 6, '114 entry and row caps')
            require(20 * (2 * d + v) + 140 + 25 * v <= 290, '114 common-column scores')
            if d:
                require(20 * (2 * d + v) + 20 * col_cap + 50 <= 290, '114 crossing scores')
        n114 += 1
    require((n017, n114) == (275, 19), 'complete finite degree controls')
    return {'cut017_degree_and_eligibility_cases': n017, 'cut114_degree_cases': n114}


def sharp_control(dinic):
    edges = {(0, 0), (0, 1), (0, 2), (1, 0), (1, 3), (3, 0), (3, 1), (3, 4),
             (4, 0), (4, 1), (4, 4)}
    law = {e: Q(2) for e in edges}
    for i in (0, 3, 4):
        law[i, 0] = Q(5, 3)
    require(check(law, edges, bound=295) == 295, 'sharp witness upper295')
    require(len({e for e in edges if e[1] != 0}) == 7, 'sharp cut is7+7*2=21')
    require(network(edges, dinic)[0] == 21, 'sharp witness maximum21')
    require(Q(220) + 45 * Q(5, 3) == 295, 'pigeonhole lower295')
    ans = construct(edges, initial=law, dinic=dinic)
    require(ans['sharp_max'] == '295' and ans['mixed_max'] == '295', 'constructor attains sharp295')
    return {'edges': sorted(edges), 'attaining_law': serialize(law), 'lower_bound': '295',
            'lower_bound_certificate': 'Cut A7 + seven outside entry arcs2 forces outside entries2 and A total7. The low row contributes at most2 to A, so three high rows contribute at least5; one has v>=5/3 and score220+45v>=295.',
            'constructor': ans}


def unique20_control(dinic):
    law = {(0, 0): 2, (0, 1): 2, (0, 2): 2, (1, 0): 2, (1, 1): 2,
           (2, 0): 2, (2, 1): 2, (4, 0): 1, (4, 1): 1, (4, 3): 2, (4, 4): 2}
    edges = set(law)
    require(check(law, edges, mass=20) == 310, 'mass20 countercontrol score310')
    require(network(edges, dinic)[0] == 20, 'mass20 exact maximum')
    crossing = {e for e in edges if e[0] != 4}
    require(len(crossing) == 7 and all(law[e] == 2 for e in crossing), 'row4 plus7 entries cut20')
    room = {j: min(2, 7 - sum(law.get((i, j), 0) for i in range(4))) for j in (0, 1, 3, 4)}
    require(room == {0: 1, 1: 1, 3: 2, 4: 2} and sum(room.values()) == 6,
            'row4 saturation forces unique rational completion')
    require(all(law[4, j] == cap for j, cap in room.items()), 'unique completion matches law')
    caps = [7, 7, 7, 7, 7, 6, 7]
    check(law, edges, mass=20, column_caps=caps)
    require(network(edges, dinic, column_caps=caps)[0] == 20, 'flagged unused column does not help')
    return {'edges': sorted(edges), 'unique_law': serialize(law), 'maximum_flow': 20,
            'cut': {'outside_row': 4, 'row_capacity': 6, 'crossing_edges': sorted(crossing), 'capacity': 20},
            'remaining_row4_bounds': [[j, cap] for j, cap in room.items()],
            'forced_score': 310, 'flagged_column_with_cap6': 5,
            'scope': 'Local same-positive-support transport obstruction, not a literal full-source or good-law counterexample.'}


def controls(dinic):
    fixtures = {
        'M22': {(i, i) for i in range(5)} | {(i, (i + 1) % 5) for i in range(5)} | {(0, 2)},
        'cut030': {(i, j) for i in range(4) for j in range(3)},
        'cut017': {(0, 0), (0, 1), (0, 2), (1, 0), (1, 3), (3, 0), (3, 1), (3, 4), (4, 0), (4, 1), (4, 4)},
        'cut114': {(i, 0) for i in range(4)} | {(0, 1), (0, 2), (1, 1), (1, 2), (4, 3), (4, 4), (4, 5)},
    }
    fixture_results = {}
    counts, cases = Counter(), Counter()
    worst = Q(0)

    def exercise(edges):
        nonlocal worst
        ans = construct(edges, dinic=dinic)
        counts['supports'] += 1
        if ans is None:
            counts['infeasible'] += 1
            return None
        counts['feasible'] += 1
        cases[ans['case']] += 1
        worst = max(worst, Q(ans['sharp_max']))
        positive = {(i, j): Q(v) for i, j, v in ans['initial']}
        preserved = construct(set(positive), initial=positive, dinic=dinic)
        require(preserved is not None and preserved['exact_same_positive_support'], 'separate positive-support run')
        counts['positive_support_runs'] += 1
        cases[preserved['case']] += 1
        worst = max(worst, Q(preserved['sharp_max']))
        return ans

    for expected, edges in fixtures.items():
        ans = exercise(edges)
        require(ans is not None and ans['case'] == expected, f'actual fixture exercises {expected}')
        fixture_results[expected] = {'edges': sorted(edges), **ans}
    patterns = [set(range(5))] + [set(range(5)) - {i} for i in range(5)]
    for neighborhoods in product(patterns, repeat=3):
        edges = {(i, j) for j, rows in enumerate(neighborhoods) for i in rows}
        require(exercise(edges) is not None, 'three-column support feasible')
        counts['three_column_supports'] += 1
    rng = random.Random(20260928)
    for numerator in (1, 2, 3):
        for _ in range(32):
            edges = {(i, j) for i in range(5) for j in range(7) if rng.randrange(4) < numerator}
            exercise(edges)
            counts['seeded_supports'] += 1
    require(counts['three_column_supports'] == 216 and counts['seeded_supports'] == 96, 'bounded finite controls')
    require(set(fixtures) <= set(cases), 'all four mathematical constructor cases exercised')
    require(construct({(0, 0)}, dinic=dinic) is None, 'infeasible support returns None')
    try:
        construct({(0, 0)}, initial={(0, 0): Q(21)}, dinic=dinic)
    except ValueError:
        pass
    else:
        raise ValueError('invalid supplied initial law must fail')
    return {'counts': dict(counts), 'constructor_case_counts_including_positive_support_runs': dict(cases),
            'seed': 20260928, 'maximum_tested_sharp_charge': str(worst), 'case_fixtures': fixture_results}


def verify(dinic):
    return {'sharp_transport_bound': '295', 'positive_support_mixture_bound': '1195/4',
            'finite_controls': controls(dinic), 'degree_controls': degree_controls(),
            'sharp295_control': sharp_control(dinic), 'unique20_countercontrol': unique20_control(dinic),
            'scope': 'Exact constructor and finite controls; the minimum-cut case proof supplies the universal bound. The sharp21 and unique20 witnesses are local transport statements. No general cut77, original odd-cover realization, outside-cofactor lifting, or Lean claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module', type=Path, help='existing saturated-block module; default is adjacent file')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    result = verify(load_dinic(args.base_module))
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'counts': result['finite_controls']['counts'],
                      'cases': result['finite_controls']['constructor_case_counts_including_positive_support_runs'],
                      'degree_controls': result['degree_controls'],
                      'sharp_bound': result['sharp_transport_bound'], 'mixed_bound': result['positive_support_mixture_bound'],
                      'counter20_score': result['unique20_countercontrol']['forced_score']}))


if __name__ == '__main__':
    main()
