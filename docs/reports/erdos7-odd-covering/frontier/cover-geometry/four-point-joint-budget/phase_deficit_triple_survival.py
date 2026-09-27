"""Consume a phase-cell deficit in the same-source triple survivor inequality.

Exact rational arithmetic supports report512's ordinary proof. This is not
Lean verification or a certificate for unrestricted Erdős #7.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from math import prod
import argparse
import hashlib
import json


ROOT = Path(__file__).resolve().parent
INPUTS = {
    'integer_selector_tail_interface_certificate.json':
        '66f155d2d9f65b044017e0c033c1d3e8f9999cea100eabce1b8aa049810ecb5a',
    'integer_selector_tail_interface.json':
        '4681c5b6da42138625dfa6c21e680522edf60ed400a3ae83c817d94bfcf9e4f4',
    'two_region_triple_survival.json':
        'aada38719d5029f778ea663739a52d9312e7957a1672a7c11d11b71c6f240365',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def det(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def vertices(rows):
    points = {}
    for ids in combinations(range(len(rows)), 3):
        matrix = [rows[i][0] for i in ids]
        rhs = [rows[i][1] for i in ids]
        den = det(matrix)
        if not den:
            continue
        point = tuple(F(det([[rhs[i] if j == k else matrix[i][j]
                              for j in range(3)] for i in range(3)]), den)
                      for k in range(3))
        if all(dot(normal, point) <= bound for normal, bound in rows):
            points.setdefault(point, ids)
    return points


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--certificate', type=Path,
                        default=ROOT / 'phase_deficit_triple_survival_certificate.json')
    parser.add_argument('--write-certificate', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    sources = {}
    for name, digest in INPUTS.items():
        raw = (args.input_dir / name).read_bytes()
        need(hashlib.sha256(raw).hexdigest() == digest, 'pinned source ' + name)
        sources[name] = json.loads(raw)
    source = sources['integer_selector_tail_interface_certificate.json']
    actual = sources['integer_selector_tail_interface.json']['axis_realizations'][0]
    previous = sources['two_region_triple_survival.json']
    profiles = ((4, 2, -4, 1, 2, 1, 1), (5, -2, 4, 1, 1, 1, 1),
                (-5, -3, -2, 1, 1, 1, 1))
    need(all(tuple(map(tuple, rows)) == profiles for rows in
             (source['cases'][0]['profiles'], actual['profiles'], previous['profiles'])),
         'same original three profiles')
    need(source['old_primes'] == [3, 5, 7, 11, 13, 17, 19], 'same prime axes')
    weight, target, second_weight = (17, 9, 8), (17, 16, 13), (9, 16, 9)
    boxes = []
    for profile in profiles:
        shapes = (tuple(max(1, x) for x in profile[:3]) + profile[3:],
                  tuple(max(1, -x) for x in profile[:3]) + profile[3:])
        boxes.append(tuple(set(product(*(range(x) for x in shape))) for shape in shapes))
    labels = []
    for exponent in set().union(*(a | b for a, b in boxes)):
        d = prod(p ** e for p, e in zip(source['old_primes'], exponent))
        need(actual['old_carrier'] % d == 0, 'original old label divides carrier')
        masks = [[int(point % d == centre % d) for point in actual['old_points']]
                 for centre in actual['old_centres']]
        need(masks == [[int(exponent in pair[j]) for pair in boxes] for j in (0, 1)],
             'literal CRT and profile masks agree')
        scores = [dot(weight, mask) for mask in masks]
        maximum = max(scores)
        gaps = [maximum - value for value in scores if value < maximum]
        labels.append({'d': d, 'masks': masks, 'scores': scores, 'maximum': maximum,
                       'maximizing_selectors': [j for j, value in enumerate(scores) if value == maximum],
                       'gap': min(gaps) if gaps else None})
    labels.sort(key=lambda item: item['d'])
    need(len(labels) == len({item['d'] for item in labels}) == 51, '51 original labels')
    block = [item for item in labels
             if all(item['masks'][j][1] for j in item['maximizing_selectors'])]
    block_labels = [1, 3, 9, 21, 27, 63, 81, 147, 189, 441, 567,
                    1029, 1323, 3087, 3969, 9261, 27783]
    need([item['d'] for item in block] == block_labels, 'exact forced point2 block')
    need(sum(item['maximum'] for item in block) == 229
         and min(item['gap'] for item in block if item['gap'] is not None) == 1,
         'block ceiling and nonmaximizing selector regret')
    need(min(item['maximum'] for item in block) >= 1, 'absent labels lose at least one')
    tied = next(item for item in labels if item['d'] == 5)
    need(tied['scores'] == [17, 17] and not all(mask[1] for mask in tied['masks']),
         'label5 must not be counted as forcing point2')
    alpha, beta = F(4180, 207), F(3052, 261)
    need(23 * (1 - alpha / 22) == F(17, 9)
         and 29 * (1 - beta / 28) == F(152, 9), 'loss threshold normalization')
    a = [F(1), F(8, 9)] + [F(0)] * 21
    b = [F(1)] * 16 + [F(8, 9)] + [F(0)] * 12
    products = sorted((x * y for x in a for y in b), reverse=True)
    prefixes = [sum(products[:k], F()) for k in range(18)]
    need(all(prefixes[k] == k - F(1, 9) * max(k - 16, 0) for k in range(18)),
         'packed top-k for the whole block')
    losses = [F(c) + 9 * (17 - c - prefixes[17 - c]) for c in range(18)]
    need(min(losses) == 1, 'every selector-count branch loses at least one')

    def capacity(v):
        return sum(max(dot(v, mask) for mask in item['masks']) for item in labels)

    directions = ((1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 1),
                  (0, 1, 1), (1, 1, 1), (1, 1, 2), (1, 2, 1), (2, 1, 1))
    capacities = [capacity(v) for v in directions]
    need(capacities == [22, 21, 39, 30, 45, 42, 58, 85, 78, 79], 'ten axis budgets')
    need(capacity(weight) == 671 and capacity(second_weight) == 662
         and capacity(target) == 892, 'same unmodified mixed capacities')

    def constraints(height, extra=()):
        rows = [(normal, F(n)) for normal, n in zip(directions, capacities)]
        for i in range(3):
            unit = tuple(int(i == j) for j in range(3))
            rows.extend([(unit, F(height)), (tuple(-x for x in unit), F(0))])
        return rows + [(normal, F(rhs)) for normal, rhs in extra]

    first = (((1, 0, 0), 20),)
    trows, urows = constraints(22, first), constraints(28)
    vt, vu = vertices(trows), vertices(urows)
    good = F(41) + F(616, 667)
    regions = []
    specifications = [
        ('base_first', trows, urows, vt, vu, weight, 15, 22, F(41)),
        ('bad_t2', constraints(22, first + (((0, 1, 0), alpha),)), urows,
         None, vu, weight, 15, 22, F(8821, 207)),
        ('bad_u2', trows, constraints(28, (((0, 1, 0), beta),)),
         vt, None, weight, 15, 10, F(1269, 29)),
        ('base_second', constraints(22, (((-1, 0, 0), -20),)), urows,
         None, vu, second_weight, 12, 22, F(92)),
    ]
    for name, tr, ur, tv, uv, v, nt, nu, expected in specifications:
        tv, uv = tv if tv is not None else vertices(tr), uv if uv is not None else vertices(ur)
        n = capacity(v)
        need((len(tv), len(uv)) == (nt, nu), 'complete vertices for ' + name)
        values = [(sum(vi * (22 - ti) * (28 - ui) for vi, ti, ui in zip(v, t, u)) - n, t, u)
                  for t in tv for u in uv]
        minimum = min(value for value, _, _ in values)
        need(minimum == expected, 'exact minimum for ' + name)
        if name != 'base_first':
            need(minimum > good, 'complementary/second region exceeds new bound')
        regions.append({'region': name, 'weight': v, 'capacity': n,
                        'minimum': str(minimum), 'vertex_pairs': len(values),
                        'minimizers': [{'t': list(map(str, t)), 'u': list(map(str, u))}
                                       for value, t, u in values if value == minimum],
                        't_constraints': [{'normal': a, 'rhs': str(rhs)} for a, rhs in tr],
                        'u_constraints': [{'normal': a, 'rhs': str(rhs)} for a, rhs in ur],
                        't_vertices': [{'point': list(map(str, t)), 'active_rows': ids}
                                       for t, ids in sorted(tv.items())],
                        'u_vertices': [{'point': list(map(str, u)), 'active_rows': ids}
                                       for u, ids in sorted(uv.items())]})
    need([item['minimum'] for item in previous['branches']] == ['41', '92']
         and previous['old_fixed_objective_minimum'] == '32', 'old results stay unchanged')
    need(all(sum(v) == 34 and all(0 <= x <= y for x, y in zip(v, target))
             for v in (weight, second_weight)), 'branchwise weight transport and sum34')
    mixed_upper = F(671, 616) - F(229, 667) + F(228, 667)
    need(mixed_upper == F(671, 616) - F(1, 667), 'subtract block deficit exactly once')
    certificate = {'inputs': INPUTS, 'profiles': profiles, 'old_primes': source['old_primes'],
                   **{k: actual[k] for k in ('old_carrier', 'old_centres', 'old_points')},
                   'first_weight': weight, 'target_weight': target, 'second_weight': second_weight,
                   'literal_labels': labels, 'phase_block': block, 'excluded_tied_label_d5': tied,
                   'axis_directions': directions, 'axis_capacities': capacities,
                   'good_thresholds': list(map(str, (alpha, beta))),
                   'packed_top_k': list(map(str, prefixes)), 'selector_loss_branches': list(map(str, losses)),
                   'block_ceiling': '229/667', 'good_block_union_upper': '228/667',
                   'good_mixed_union_upper': str(mixed_upper), 'regions': regions,
                   'uniform_numerator': str(good), 'max_survivor_lower': str(good / (616 * 34))}
    certificate = json.loads(json.dumps(certificate))
    if args.write_certificate:
        args.certificate.write_text(json.dumps(certificate, indent=2) + '\n')
    need(certificate == json.loads(args.certificate.read_text()), 'retained certificate differs')
    out = {'certificate_sha256': hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
           'inputs': INPUTS, 'literal_label_count': len(labels), 'block_labels': block_labels,
           'block_ceiling': '229/667', 'good_block_union_upper': '228/667',
           'good_thresholds': list(map(str, (alpha, beta))),
           'regions': [{k: item[k] for k in ('region', 'minimum', 'vertex_pairs', 'minimizers')}
                       for item in regions], 'vertex_pairs_checked': sum(item['vertex_pairs'] for item in regions),
           'uniform_numerator': str(good), 'gain_over_41': str(good - 41),
           'weighted_survivor_lower': str(good / 616), 'max_survivor_lower': str(good / (616 * 34)),
           'scope': 'Same three-point/two-centre interface and actual finite families, with full uniform product new fibres. Ordinary proof and exact arithmetic, not arithmetic sharpness, a new Boolean edge, a global source-mass improvement, or Lean verification.'}
    if args.output:
        args.output.write_text(json.dumps(out, indent=2) + '\n')
    else:
        need(out == json.loads(Path(__file__).with_suffix('.json').read_text()), 'retained result differs')
    print(json.dumps({k: out[k] for k in ('literal_label_count', 'vertex_pairs_checked',
                                        'uniform_numerator', 'max_survivor_lower')}, indent=2))


if __name__ == '__main__':
    main()
