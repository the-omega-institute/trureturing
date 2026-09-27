#!/usr/bin/env python3
"""Exact necessary rawcut71 profiles, retaining all labelled root positions.

Sorted private costs are quotiented only by permutations of full roots
with the same active count. This is arithmetic classification, not actual
source realizability or a proof of the moment bound.
"""
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
import argparse
import json

N = (4, 5, 5, 5)
Q = (2, 3, 3, 3)


def require(ok, message):
    if not ok:
        raise ValueError(message)


@lru_cache(None)
def row_domain(active, selected, public_cost):
    if not active:
        return (((), 0, 0),)
    return tuple((row, sum(row), sum(row[:selected]))
                 for row in combinations_with_replacement(range(1 if public_cost == 0 else 0, 4), active))


def sorted_shapes(active, public_cost, total_private):
    domains = [row_domain(a, q, public_cost) for a, q in zip(active, Q)]
    result = []
    def visit(root, rows, total, minima):
        if root == 4:
            if total == total_private:
                result.append('/'.join(''.join(map(str, row)) if row else '-' for row in rows))
            return
        for row, cost, minimum in domains[root]:
            if total + cost > total_private:
                continue
            if active[root] and 7 * (N[root] - active[root]) + 2 * cost >= 21:
                continue
            if active[root] and any(active[j] and minimum + minima[j] < 9 - public_cost for j in range(root)):
                continue
            if root > 0 and any(active[j] == active[root] and rows[j] > row for j in range(1, root)):
                continue
            visit(root + 1, rows + (row,), total + cost, minima + (minimum,))
    visit(0, (), 0, ())
    return result


def profile_key(active, k, z):
    return ''.join(map(str, active)) + '_k%d_Z%d' % (k, z)


def verify():
    profiles, shapes = [], {}
    for active in product((0, 2, 3, 4), (0, 3, 4, 5), (0, 3, 4, 5), (0, 3, 4, 5)):
        top = sum(3 if a == 0 else n - a for a, n in zip(active, N))
        for public_cost in range(max(0, 11 - top)):
            remainder = 71 - 7 * (top + public_cost)
            if remainder < 0 or remainder % 2:
                continue
            private_total = remainder // 2
            if active == N and public_cost + private_total < 15:
                continue
            candidates = sorted_shapes(active, public_cost, private_total)
            if not candidates:
                continue
            key = profile_key(active, public_cost, private_total)
            profiles.append({'key': key, 'active': active, 'T': top, 'k': public_cost,
                             'Z': private_total, 'shape_count': len(candidates)})
            shapes[key] = candidates
    expected_counts = {'0555_k0_Z25': 1, '2555_k3_Z18': 2, '3555_k4_Z18': 1,
                       '4000_k0_Z4': 1, '4455_k4_Z18': 1, '4545_k4_Z18': 1, '4554_k4_Z18': 1,
                       '4555_k1_Z32': 4, '4555_k3_Z25': 21, '4555_k5_Z18': 13}
    require({p['key']: p['shape_count'] for p in profiles} == expected_counts,
            'exact ten labelled profiles and private-shape counts')
    require(sum(len(ss) for ss in shapes.values()) == 46, 'forty-six labelled-profile sorted shapes')
    require(shapes['0555_k0_Z25'] == ['-/11111/22222/22222'] and
            shapes['2555_k3_Z18'] == ['03/11111/11111/11111', '12/11111/11111/11111'] and
            shapes['3555_k4_Z18'] == ['111/11111/11111/11111'] and
            shapes['4000_k0_Z4'] == ['1111/-/-/-'], 'sparse and gap-private shape guards')
    canonical = {}
    for item in profiles:
        active = (item['active'][0], *sorted(item['active'][1:]))
        key = profile_key(active, item['k'], item['Z'])
        if key not in canonical:
            canonical[key] = {'key': key, 'active': active, 'T': item['T'], 'k': item['k'], 'Z': item['Z'],
                              'shape_count': item['shape_count'], 'labelled_keys': []}
        require(canonical[key]['shape_count'] == item['shape_count'], 'root permutations preserve shape count')
        canonical[key]['labelled_keys'].append(item['key'])
    require(len(canonical) == 8 and sum(p['shape_count'] for p in canonical.values()) == 44,
            'eight root-permutation families and forty-four canonical shapes')
    require(len(canonical['4455_k4_Z18']['labelled_keys']) == 3 and
            all(len(v['labelled_keys']) == 1 for k, v in canonical.items() if k != '4455_k4_Z18'),
            'only the partial full-root location has multiplicity three')
    return {'rawcut': 71, 'labelled_profile_count': 10, 'canonical_profile_count': 8,
            'profiles': profiles, 'canonical_profiles': list(canonical.values()), 'shapes': shapes,
            'scope': 'Exact solutions of bounded private-cost, pair, root-node-minimal and full-activity standalone necessary inequalities. Ten labelled profiles, eight families under full-root permutations. Sorted private shapes quotient equal active full-root roles. These arithmetic possibilities are not claims of actual realizability or universal same-law bounds.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    out = verify()
    args.output.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'labelled_profiles': out['labelled_profile_count'], 'canonical_families': out['canonical_profile_count'],
                      'canonical_shape_counts': {p['key']: p['shape_count'] for p in out['canonical_profiles']}}))


if __name__ == '__main__':
    main()
