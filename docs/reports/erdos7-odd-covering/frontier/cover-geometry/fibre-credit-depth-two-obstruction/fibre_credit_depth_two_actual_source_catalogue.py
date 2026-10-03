#!/usr/bin/env python3
"""Replay actual315 source groups and their complete convex-query envelopes."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import subprocess


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


DEPENDENCIES = {
    'fibre_credit_depth_two_old23_full_height.json':
    'ca998ef3ce5e1043cbd1a78a4f9cd4306b12cfb781b219729aa916f0ba016ede',
}


def calculate():
    directory = Path(__file__).resolve().parent
    for name, digest in DEPENDENCIES.items():
        need(sha256((directory / name).read_bytes()).hexdigest() == digest,
             'pinned source dependency: ' + name)
    inherited = json.loads((directory / 'fibre_credit_depth_two_old23_full_height.json').read_text())['rows'][0]
    native = directory / 'fibre_credit_depth_two_actual_source_catalogue.cpp'
    # Every count is bounded by17 cells,12 query slots and6 live roots.
    # Query-pair counts use uint64_t; arithmetic counts stay below10000.
    with TemporaryDirectory(prefix='e7_actual_source_catalogue_') as temporary:
        temp = Path(temporary)
        executable = temp / 'catalogue'
        raw_result = temp / 'result.json'
        subprocess.run(['c++', '-std=c++17', '-O2', '-fsanitize=undefined',
                        '-fno-sanitize-recover=all', str(native), '-o', str(executable)],
                       check=True, capture_output=True)
        subprocess.run([str(executable), str(raw_result)], check=True, capture_output=True)
        raw = json.loads(raw_result.read_text())
    need((raw['layouts'], raw['color_partitions'], raw['total_cases'], raw['source_vectors'])
         == (4760, 52, 247520, 19324), 'complete actual source catalogue')
    need(len(raw['rows']) == 192 and sum(r['source_vector_count'] for r in raw['rows']) == 19324,
         'every actual source belongs to one group')
    rows = []
    for row in raw['rows']:
        n, m = row['N'], row['M']
        hinges = [F(v, n) for v in row['hinge_numerators']] + [F(0), F(0)]
        need(77 <= n <= 94 and row['source_vector_count'] > 0, 'actual group size')
        need(hinges[0] - hinges[1] == 1 and hinges[1] == F(m, n),
             'mean and size belong to the same source group')
        need(all(hinges[t] <= F(inherited['hinge_bounds'][t]) for t in range(12)),
             'actual envelope respects inherited D2 bound')
        law = {y: hinges[y - 1] - 2 * hinges[y] + hinges[y + 1] for y in range(1, 13)}
        need(min(law.values()) >= 0 and sum(law.values()) == 1, 'positive comparison law')
        need(all(sum(p * max(y - t, 0) for y, p in law.items()) == hinges[t]
                 for t in range(14)), 'comparison law recovers the whole integer profile')
        rows.append({**row, 'nonunit_mean': str(hinges[1]),
                     'hinge_bounds': list(map(str, hinges[:12])),
                     'comparison_law': [{'value': y, 'probability': str(p)}
                                        for y, p in law.items() if p]})

    exceptional = raw['exceptional_sources']
    need(len(exceptional) == 28 and sum(r['M'] == 185 for r in exceptional) == 6
         and sum(r['M'] == 184 for r in exceptional) == 22,
         'complete two exceptional source groups')
    need(len({tuple(r['b']) for r in exceptional}) == 28, 'distinct source vectors')
    points = [x for x in range(45) if all(x % d != a for d, a in
              ((3, 0), (9, 4), (5, 0), (15, 1), (45, 37)))]
    mods = (3, 5, 9, 15, 45)
    masks = {}
    for d in mods:
        phases = {}
        for a in range(d):
            mask = tuple(int(x % d == a) for x in points)
            if any(mask):
                phases.setdefault(mask, a)
        masks[d] = phases
    layouts = []
    for choice in product(*(masks[d] for d in mods)):
        values = tuple(1 + sum(mask[i] for mask in choice) for i in range(17))
        phases = [masks[d][mask] for d, mask in zip(mods, choice)]
        layouts.append((values, phases))
    need(len(layouts) == 4760, 'literal old query inventory')
    target = next(r['hinge_numerators'] for r in rows if (r['N'], r['M']) == (86, 185))
    sharp = []
    for source in exceptional:
        need(sum(6 - b for b in source['b']) == 86, 'source mass matches its vector')
        if source['M'] != 185:
            continue
        found = None
        for values, phases in layouts:
            # All positive-seven query slots use the untouched live row.
            counts = {v: sum((5 - b) * int(a == v) + int(2 * a == v)
                             for a, b in zip(values, source['b'])) for v in range(1, 13)}
            if [sum(count * max(v - t, 0) for v, count in counts.items())
                for t in range(12)] == target:
                found = {'b': source['b'], 'old45_query_phases': phases,
                         'query_load_counts': {str(v): c for v, c in counts.items() if c}}
                break
        need(found is not None, 'one actual query attains every sharp group hinge')
        need(found['query_load_counts'] == {'1': 5, '2': 38, '3': 14, '4': 18,
                                          '6': 8, '8': 2, '12': 1},
             'same attained convex comparison law')
        sharp.append(found)
    return {'scope': 'Exact additionally pruned first315 source catalogue,192 genuine convex '
            'comparison laws and six sharp same-source query laws. Ordinary arithmetic, not Lean.',
            'dependency_hashes': DEPENDENCIES, 'native_source_sha256': sha256(native.read_bytes()).hexdigest(),
            'layouts': 4760, 'color_partitions': 52, 'source_configurations': 247520,
            'source_vectors': 19324, 'group_count': 192, 'ordered_query_pairs': 22657600,
            'rows': rows, 'exceptional_sources': exceptional, 'sharp_sources': sharp,
            'inherited_D2_replayed': False, 'complete_native_enumeration_replayed': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with complete actual source catalogue')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
