#!/usr/bin/env python3
"""Rebuild all six effective padded actual315 source/query catalogues.

Requires the standard Python library and clang++. The native enumeration
uses global cylinder phases and root partitions, with UBSan enabled.
This is exact finite arithmetic, not Lean verification.
"""
from hashlib import sha256
from math import prod
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import subprocess


def check(value, message):
    if not value:
        raise ValueError(message)


def calculate():
    directory = Path(__file__).resolve().parent
    source = directory / 'fibre_credit_depth_two_actual_joint_catalogue.cpp'
    with TemporaryDirectory(prefix='e7_joint_catalogue_', dir='/tmp') as name:
        temporary = Path(name)
        binary, output = temporary / 'catalogue', temporary / 'result.json'
        subprocess.run(['clang++', '-std=c++17', '-O3', '-fsanitize=undefined',
                        '-fno-sanitize-recover=undefined', str(source),
                        '-o', str(binary)], check=True, capture_output=True)
        subprocess.run([str(binary), str(output)], check=True, capture_output=True)
        result = json.loads(output.read_text())
    counts = (19324, 20279, 20080, 18025, 17769, 17416)
    groups = (451, 320, 522, 630, 457, 813)
    pairs = ((1, 37), (1, 11), (1, 2), (11, 2), (11, 1), (11, 37))
    check(len(result['rows']) == 6, 'all six normalized source shapes')
    for shape, row in enumerate(result['rows']):
        check(row['shape_index'] == shape, 'canonical source order')
        check((row['a15'], row['a45']) == pairs[shape], 'same old45 normalization')
        points = [x for x in range(45) if x % 3 and x % 9 != 4 and x % 5
                  and x % 15 != row['a15'] and x != row['a45']]
        check(row['old45_points'] == points, 'actual old45 survivors')
        check(row['distinct_b_vectors'] == counts[shape], 'complete source inventory')
        check(len(row['joint_groups']) == groups[shape], 'complete joint cost groups')
        check(sum(g[4] for g in row['joint_groups']) == counts[shape],
              'multiplicities account for every actual source')
        check(row['raw_phase_color_cases'] == 52 * prod(row['effective_cylinders']),
              'all effective phases and root equality partitions')
        check(row['query_count'] == prod(row['effective_cylinders']),
              'all effective old45 query layouts')
        check(row['unordered_query_pairs'] == row['query_count'] *
              (row['query_count'] + 1) // 2, 'complete unordered query pairs')
        check(row['H6_numerator'] == 10, 'exact uniform sixth hinge')
        for n, m, k, j4, multiplicity, b in row['joint_groups']:
            check(len(b) == len(points) and all(0 <= v <= 5 for v in b),
                  'one actual surviving-row vector')
            check(n == sum(6 - v for v in b) and multiplicity > 0,
                  'same-source denominator and nonempty group')
            check(min(m, k, j4) > 0, 'positive paired query costs')
        check(all(case['H4_numerator'] == 29 for case in row['exceptional_hinge4']),
              'exceptional fourth hinges are actual sharp maxima')
    result['dependency_hashes'] = {source.name: sha256(source.read_bytes()).hexdigest()}
    result['actual_source_count'] = sum(counts)
    result['paired_group_count'] = sum(groups)
    result['unordered_query_pair_count'] = sum(r['unordered_query_pairs'] for r in result['rows'])
    check(result['unordered_query_pair_count'] == 64105860, 'complete six-shape query count')
    result['exceptional_source_count'] = sum(len(r['exceptional_hinge4']) for r in result['rows'])
    check(result['exceptional_source_count'] == 116, 'literal exceptional source count')
    result['source_scope'] = 'Effective padded actual sources selected inside original survivors; not every raw unpadded source vector.'
    result['lean_verification'] = False
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, sort_keys=True, separators=(',', ':')) + '\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
              'retained result agrees with complete actual catalogue')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
