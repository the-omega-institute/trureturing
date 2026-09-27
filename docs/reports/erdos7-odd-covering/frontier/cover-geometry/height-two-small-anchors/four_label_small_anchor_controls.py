#!/usr/bin/env python3
"""Exact finite controls for four-label 211/1111 actual anchor law."""
import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def subsets(values):
    values = tuple(values)
    return [frozenset(v for j, v in enumerate(values) if mask >> j & 1)
            for mask in range(1, 1 << len(values))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='Write JSON results to this path.')
    args = parser.parse_args()
    types = {'211': (0, 0, 1, 2), '1111': (0, 1, 2, 3)}
    deletion_result = {}
    for name, columns in types.items():
        checks = 0
        patterns = set()
        for tree_columns in itertools.combinations(range(7), 3):
            eligible = [j for j, col in enumerate(columns) if col in tree_columns]
            for mask in range(1 << len(eligible)):
                deleted = [eligible[j] for j in range(len(eligible)) if mask >> j & 1]
                d = tuple(sum(columns[label] == col for label in deleted) for col in tree_columns)
                remaining = tuple(3 - a for a in d)
                require(min(remaining) >= 1, 'a branch vanishes')
                require(sum(min(2, r) for r in remaining) >= 5, 'five-leaf truncation fails')
                patterns.add(d)
                checks += 1
        deletion_result[name] = {
            'column_selection_and_deleted_subset_cases': checks,
            'distinct_ordered_deletion_patterns': len(patterns),
            'minimum_truncated_survivors': min(sum(min(2, 3 - d) for d in p) for p in patterns),
        }
    owner_cases = 0
    incidence_subsets = subsets(range(4))
    owner_counts = Counter()
    for n in (2, 3):
        for fibres in itertools.product(incidence_subsets, repeat=n):
            if frozenset.union(*fibres) != frozenset(range(4)):
                continue
            # Replay the proof's actual assignment and its only possible repair.
            assignment = [next(i for i, f in enumerate(fibres) if label in f) for label in range(4)]
            if len(set(assignment)) == 1:
                other = next(i for i in range(n) if i != assignment[0])
                label = min(fibres[other])
                assignment[label] = other
            require(all(label in fibres[assignment[label]] for label in range(4)), 'nonactual ownership')
            require(max(Counter(assignment).values()) <= 3, 'owner exceeds three labels')
            for columns in types.values():
                child_column = Counter((assignment[label], columns[label]) for label in range(4))
                require(max(child_column.values()) <= 2, 'child-column exceeds two labels')
            owner_cases += 1
            owner_counts[n] += 1
    psi = [Q(1), Q(1,3), Q(2,5), Q(1,5), Q(2,15), Q(1,5), Q(2,25), Q(1,15), Q(1,25)]
    eta = [Q(1), Q(1), Q(1,2), Q(3,4), Q(1,2), Q(1,4), Q(1,2), Q(1,4), Q(1,4)]
    t = Q(25,29)
    caps = [Q(1)] + [t*psi[i]+(1-t)*eta[i] if i == 2 else
                    max(t*psi[i], (1-t)*eta[i]) for i in range(1,9)]
    expected = [Q(1), Q(25,87), Q(12,29), Q(5,29), Q(10,87), Q(5,29), Q(2,29), Q(5,87), Q(1,29)]
    require(caps == expected, 'common mixture cap mismatch')
    total = sum(c*v for c,v in zip((1,3,3,5,9,5,15,15,25), caps))
    require(total == Q(250,29) and total < 9, 'charge mismatch')
    require(sum(min(2,3-d) for d in (2,2,0)) == 4, 'type22 boundary replay')
    result = {
        'status': 'PASS',
        'scope': 'exact rational caps and finite structural controls; no Lean verification',
        'allowed_anchor_column_types': list(types),
        'deletion_controls': deletion_result,
        'complete_projection_owner_families': owner_cases,
        'owner_family_counts': dict(owner_counts),
        'common_law_caps': list(map(str,caps)),
        'ordered_lcm_charge': str(total),
        'type22_deleted_220_truncated_survivors': 4,
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
