#!/usr/bin/env python3
"""Exact rational constructor for three-row-neighborhood mass20 transport.

The written minimum-cut proof supplies the universal claim; the controls
exercise the constructor with exact arithmetic. Standard-library only.
Helpers are loaded lazily, so importing this module performs no I/O.
"""
from fractions import Fraction as Q
from itertools import combinations
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_helpers(sharp_module=None, base_module=None):
    """Load the adjacent sharp helper and its adjacent Dinic by default."""
    sharp_path = (Path(sharp_module) if sharp_module is not None else
                  Path(__file__).with_name('height_two_sharp_block_transport.py'))
    base_path = (Path(base_module) if base_module is not None else
                 sharp_path.with_name('height_two_saturated_block_transport.py'))
    spec = spec_from_file_location('_mass20_existing_sharp_transport', sharp_path)
    require(spec is not None and spec.loader is not None, 'sharp helper module spec')
    sharp = module_from_spec(spec)
    spec.loader.exec_module(sharp)
    return sharp, sharp.load_dinic(base_path)


def neighborhoods_ok(edges):
    return all(len({j for i, j in edges if i in rows}) >= 3
               for rows in combinations(range(5), 3))


def construct(edges, flag=None, initial=None, *, sharp_module=None,
              base_module=None, _helpers=None):
    """Return an exact supported mass20 law and its7/8+1/8 mixture.

    `initial`, when supplied, is a mapping(i,j)->int or Fraction, must itself
    be a feasible mass20 law, and is the actual1/8 term of the mixture.
    It is not replaced by a freshly computed law. If omitted, use a feasible
    mass20 flow from the network (trim one unit when the first flow has21).
    Return None for a support whose maximum is below20. All inputs and output
    laws are checked even under Python-O. The result includes serialized
    initial, constructed and mixed laws for independent use.
    """
    sharp, dinic = load_helpers(sharp_module, base_module) if _helpers is None else _helpers
    edges = sharp.support(edges)
    require(flag is None or (type(flag) is int and 0 <= flag < 7), 'optional flag in0,...,6')
    require(neighborhoods_ok(edges), 'every three rows have at least three neighboring columns')
    caps = [6 if j == flag else 7 for j in range(7)]
    base = None if initial is None else dict(initial)
    if base is not None:
        sharp.check(base, edges, mass=20, bound=310, column_caps=caps)
    m, old, inside_rows, inside_cols = sharp.network(edges, dinic, limit=21, column_caps=caps)
    if m < 20:
        require(base is None, 'validated initial law contradicts network infeasibility')
        return None
    if base is None:
        base = {e: Q(v) for e, v in old.items()}
        if m == 21:
            edge = next(e for e in sorted(base) if base[e] > 0)
            require(base[edge] >= 1, 'integral21 flow permits removing one unit')
            base[edge] -= 1
        sharp.check(base, edges, mass=20, bound=310, column_caps=caps)
    if m == 21:
        law = {e: Q(v * 20, 21) for e, v in old.items()}
        case = 'M>=21'
    else:
        a = 5 - len(inside_rows)
        f = int(flag in inside_cols)
        b = len(inside_cols) - f
        crossing = {(i, j) for i, j in edges if i in inside_rows and j not in inside_cols}
        c = len(crossing)
        require(6*a + 7*b + 6*f + 2*c == 20, 'residual cut capacity20')
        case = f'cut_a{a}_b{b}_f{f}_c{c}'
        degrees = {i: sum(ii == i for ii, j in crossing) for i in inside_rows}
        col_degrees = {j: sum(jj == j for i, jj in crossing) for j in range(7)}
        law = {e: Q(v) for e, v in old.items()}
        if b == 2:
            require(a == 0, 'three-row condition excludes two inside columns and an outside row')
            if f == 0:
                require(c == 3 and len({i for i, j in crossing}) == 3,
                        'three crossing edges occupy three distinct rows')
            else:
                require(c == 0, 'two ordinary inside columns plus flag exhaust cut20')
            law = {e: Q(2) for e in crossing}
            for j in sorted(inside_cols):
                rows = {i for i, jj in edges if jj == j}
                for i in rows:
                    law[i, j] = Q(caps[j], len(rows))
        elif f == 1:
            require(b == 0 and (a, c) in ((0, 7), (1, 4)),
                    'feasible flagged-only cut; three-row condition excludes(a,c)=(2,1)')
            sharp.check(law, edges, mass=20, bound=290, column_caps=caps)
        elif a == 1:
            bad = {j for i, j in crossing if degrees[i] == 3 and col_degrees[j] == 3}
            if bad:
                require(len(bad) == 1, 'only one degree3 crossing column can meet a degree3 row')
                bad_col = next(iter(bad))
                outside = next(iter(set(range(5)) - inside_rows))
                candidates = sorted(j for i, j in edges if i == outside and j != bad_col)
                require(len(candidates) >= 3, 'outside row has three neighbors avoiding the bad column')
                law = {e: Q(2) for e in crossing}
                law.update({(outside, j): Q(2) for j in candidates[:3]})
        elif a in (2, 3):
            outside = set(range(5)) - inside_rows
            graph = dinic(14)
            refs = {}
            for i in sorted(outside):
                graph.add(12, i, 3)
            for j in range(7):
                require(3-col_degrees[j] >= 0, 'nonnegative residual half-capacity')
                graph.add(5+j, 13, 3-col_degrees[j])
            for i, j in sorted(edges):
                if i in outside:
                    refs[i, j] = graph.add(i, 5+j, 1)
            total = graph.flow(12, 13, 3*a)
            require(total == 3*a, 'even-capacity replacement supplies all outside rows')
            law = {e: Q(2) for e in crossing}
            law.update({e: Q(2 * (cap - graph.g[u][k][1])) for e, (u, k, cap) in refs.items()})
        else:
            require((a, b, f, c) == (0, 0, 0, 10), 'remaining unflagged cut is ten entry arcs')
    max_score = sharp.check(law, edges, mass=20, bound=Q(6200, 21), column_caps=caps)
    if m == 20:
        require(max_score <= Q(1175, 4), 'stronger minimum-cut20 score bound')
    mixed = {e: Q(7, 8)*law.get(e, 0) + Q(1, 8)*base.get(e, 0) for e in edges}
    mixed_max = sharp.check(mixed, edges, mass=20, bound=Q(3565, 12), column_caps=caps)
    require(all(mixed[e] > 0 for e in edges if base.get(e, 0) > 0), 'initial positive support preserved')
    return {'case': case, 'flag': flag, 'score': str(max_score), 'law': sharp.serialize(law),
            'initial_source': 'provided' if initial is not None else 'network',
            'initial': sharp.serialize(base), 'mixed_law': sharp.serialize(mixed),
            'mixed_score': str(mixed_max)}


def controls(sharp_module=None, base_module=None):
    helpers = load_helpers(sharp_module, base_module)
    sharp, _ = helpers
    fixtures = {
      'all_entries': {(i, i) for i in range(5)} | {(i, (i+1) % 5) for i in range(5)},
      'one_outside_row': {(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,4),(4,5),(4,6)},
      'two_outside_rows': {(0,0),(0,1),(1,2),(2,3)} | {(i,j) for i in (3,4) for j in (4,5,6)},
      'three_outside_rows': {(0,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4),(4,5),(4,6)},
      'two_inside_columns': {(i,j) for i in range(5) for j in (0,1)} | {(0,2),(1,3),(2,4)},
      'flag_and_seven': {(i,0) for i in range(5)} | {(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,5)},
      'flag_and_four': {(i,0) for i in range(4)} | {(0,1),(0,2),(1,1),(2,3),(4,4),(4,5),(4,6)},
      'three_inside_columns': {(i,j) for i in range(5) for j in (0,1,2)},
      'complete': {(i,j) for i in range(5) for j in range(7)},
    }
    results = {}
    supplied_initial_runs = 0
    for name, edges in fixtures.items():
        require(neighborhoods_ok(edges), f'fixture neighborhood condition:{name}')
        for flag in (None, *range(7)):
            # An independent, everywhere-positive rational input exercises
            # actual supplied-law mixing specifically in the M>=21 branch.
            initial = {e: Q(4, 7) for e in edges} if name == 'complete' else None
            ans = construct(edges, flag, initial, _helpers=helpers)
            if initial is not None:
                require(ans is not None and ans['case'] == 'M>=21', 'supplied input exercises M>=21')
                require(ans['initial'] == sharp.serialize(initial), 'caller initial retained exactly')
                mixed = {(i, j): Q(v) for i, j, v in ans['mixed_law']}
                law = {(i, j): Q(v) for i, j, v in ans['law']}
                require(all(mixed[e] == Q(7,8)*law.get(e,0) + Q(1,8)*initial[e]
                            for e in edges), 'pointwise supplied-law mixture')
                require(set(mixed) == edges, 'full positive caller support preserved')
                supplied_initial_runs += 1
            results[f'{name}/flag={flag}'] = ans
    # Bounded two-inside-column patterns:4 or5 neighbors per common column;
    # three external edges meet rows0,1,2 and one, two, or three extra columns.
    patterns = [set(range(5))] + [set(range(5)) - {i} for i in range(5)]
    extra_columns = [(2,2,2), (2,2,3), (2,3,4)]
    count = 0
    for left in patterns:
        for right in patterns:
            for extra in extra_columns:
                edges = {(i,0) for i in left} | {(i,1) for i in right}
                edges |= {(i,j) for i,j in enumerate(extra)}
                if not neighborhoods_ok(edges):
                    continue
                for flag in (None, *range(7)):
                    ans = construct(edges, flag, _helpers=helpers)
                    count += 1
                    if ans is not None:
                        require(Q(ans['score']) < 300, 'bounded control strict threshold')
    require((len(results), count, supplied_initial_runs) == (72, 864, 8), 'control inventory')
    # Reject an invalid supplied total even with Python-O.
    try:
        construct(fixtures['complete'], initial={(0,0): Q(1)}, _helpers=helpers)
    except ValueError:
        pass
    else:
        raise ValueError('invalid supplied initial was not rejected')
    return {'uniform_bound': '6200/21', 'M20_bound': '1175/4',
            'positive_mixture_bound': '3565/12', 'fixture_runs': len(results),
            'bounded_two_column_runs': count, 'supplied_initial_runs': supplied_initial_runs,
            'invalid_initial_rejected': True, 'results': results,
            'scope': 'Finite exact constructor controls, not a replacement for the written mincut proof; no literal-source or general cut77 claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sharp-module', type=Path, help='sharp helper; default is adjacent module')
    parser.add_argument('--base-module', type=Path, help='Dinic helper; default is adjacent to sharp helper')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    data = controls(args.sharp_module, args.base_module)
    args.output.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in data.items() if k != 'results'}))


if __name__ == '__main__':
    main()
