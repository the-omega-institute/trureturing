#!/usr/bin/env python3
"""Fixed actual counterexample to sufficiency of separate depth marginals.

Checks two supplied six-class cores on their complete period 315. This is
not a phase search, an all-family enumeration, or Lean verification.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    period = 315
    pure = ((3, 1), (9, 3), (5, 1), (7, 1))
    parent = (15, 12)
    children = {'A': (63, 9), 'B': (63, 2)}
    private_common = {3: 280, 9: 210, 5: 126, 7: 225, 15: 252}
    private_child = {'A': 135, 'B': 65}
    checks = {}

    def require(name, condition):
        checks[name] = bool(condition)
        if not condition:
            raise ValueError(name)

    def hit(point, original):
        d, phase = original
        return point % d == phase

    source = tuple(x for x in range(period) if not any(hit(x, c) for c in pure))
    require('complete_common_pure_source', len(source) == 120)
    source_cells = [F(sum(x % 9 == j for x in source), len(source)) for j in range(9)]
    expected_cells = [F(1, 5) if j in (0, 2, 5, 6, 8) else F(0) for j in range(9)]
    require('complete_nine_cell_source_profile', source_cells == expected_cells)
    results = {}
    for name, child in children.items():
        core = pure+(parent, child)
        require(name+'_six_distinct_odd_labels',
                len({d for d, _ in core}) == 6 and all(d > 1 and d % 2 for d, _ in core))
        require(name+'_one_complete_period', all(period % d == 0 for d, _ in core))
        require(name+'_normalized_phases', all(0 <= a < d for d, a in core))
        private_points = []
        for d, phase in core:
            point = private_child[name] if d == 63 else private_common[d]
            hits = [k for k, a in core if point % k == a]
            require(name+'_private_point_'+str(d), hits == [d])
            private_points.append({'label': d, 'phase': phase, 'point': point,
                                   'crt_coordinates': [point % 9, point % 5, point % 7],
                                   'hit_labels': hits})
        require(name+'_zero_survives_all_originals', not any(hit(0, c) for c in core))
        joint = [[F(sum(hit(x, parent) == bool(i) and hit(x, child) == bool(j)
                        for x in source), len(source)) for j in range(2)] for i in range(2)]
        first = sum(joint[1])
        second = joint[0][1]+joint[1][1]
        intersection = joint[1][1]
        union = 1-joint[0][0]
        actual_survivor = tuple(x for x in range(period) if not any(hit(x, c) for c in core))
        require(name+'_full_survivor_matches_joint_complement',
                F(len(actual_survivor), len(source)) == joint[0][0])
        require(name+'_first_depth_mass', first == F(1, 10))
        require(name+'_second_depth_mass', second == F(1, 30))
        require(name+'_intersection', intersection == (F(1, 120) if name == 'A' else 0))
        require(name+'_union', union == (F(1, 8) if name == 'A' else F(2, 15)))
        results[name] = {
            'originals': [{'label': d, 'phase': a} for d, a in core],
            'private_point_certificates': private_points,
            'first_depth_mass': str(first), 'second_depth_mass': str(second),
            'joint_indicator_law': [[str(v) for v in row] for row in joint],
            'intersection_mass': str(intersection), 'mixed_union_mass': str(union),
            'additional_second_depth_mass': str(second-intersection),
            'full_survivor_count': len(actual_survivor),
        }
    require('same_separate_depth_marginals',
            all(results['A'][k] == results['B'][k]
                for k in ('first_depth_mass', 'second_depth_mass')))
    require('different_actual_joint_union',
            F(results['B']['mixed_union_mass'])-F(results['A']['mixed_union_mass']) == F(1, 120))
    require('different_full_survivors',
            results['A']['full_survivor_count'] != results['B']['full_survivor_count'])
    result = {
        'scope': 'fixed counterexample to sufficiency of common source cells and separate depth laws',
        'complete_period': period, 'common_pure_source_count': len(source),
        'common_pure_originals': [{'label': d, 'phase': a} for d, a in pure],
        'common_nine_cell_law': [str(v) for v in source_cells],
        'families': results,
        'claim_refuted': 'common pure source and separate depth event laws determine mixed union mass',
        'conclusion_boundary': 'the common law is the pure product source; full conditioned survivors differ',
        'checks': checks, 'passed_count': len(checks),
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'passed_count': len(checks), 'source_count': len(source),
                      'union_A': results['A']['mixed_union_mass'],
                      'union_B': results['B']['mixed_union_mass'], 'result': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
