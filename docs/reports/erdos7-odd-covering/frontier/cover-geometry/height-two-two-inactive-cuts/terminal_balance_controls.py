#!/usr/bin/env python3
"""Exact arithmetic controls for the terminal-balance transport interfaces.

Checks local cut types and all stated redistribution parameters, one sharp
local matrix, and the conditional consumer constants. No source enumeration,
terminal-cap feasibility, four-block avoidance, or Lean claim is made.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pure19_cut_types():
    shapes = [(a, b, c) for a in range(6) for b in range(8)
              for c in range(36) if 6*a+7*b+2*c == 19]
    require(shapes == [(0, 1, 6), (1, 1, 3), (2, 1, 0)], 'all three cut shapes')
    require(2*(5-2) < 7, 'third cut type cannot fill its inside column')
    require(Q(19, 20)*310 == Q(589, 2) < 295, 'mass20 scaling case')
    return dict(shapes=shapes, excluded_shape=[2, 1, 0],
                excluded_inside_entry_capacity=6, scaled_mass20_score='589/2')


def zero_outside_rows():
    families = Counter()
    maxima = {}
    count = 0
    for degrees in product(range(4), repeat=5):
        if sum(degrees) != 6:
            continue
        for k in (4, 5):
            for neighbors in combinations(range(5), k):
                if any(degrees[i] > 2 for i in neighbors):
                    continue
                h = sum(degrees[i] == 2 for i in neighbors)
                allocation = [Q(0)]*5
                for i in neighbors:
                    if k == 5:
                        allocation[i] = Q(7, 5)
                    elif h == 0:
                        allocation[i] = Q(7, 4)
                    else:
                        allocation[i] = Q(2)-Q(1, h) if degrees[i] == 2 else Q(2)
                rows = [2*d+v for d, v in zip(degrees, allocation)]
                require(sum(allocation) == 7 and 2*sum(degrees)+7 == 19, 'preserved total')
                require(max(allocation) <= 2 and max(rows) <= 6, 'entry and row caps')
                inside = [20*r+140+25*v for r, v in zip(rows, allocation)]
                require(max(inside) <= 295, 'all inside-column cells')
                require(max(20*r+120+50 for r in rows) <= 290, 'outside positive-cell bound')
                require(max(20*r+140 for r in rows) <= 260, 'zero-cell bound')
                key = (k, h)
                families[key] += 1
                maxima[key] = max(maxima.get(key, Q(0)), max(inside))
                count += 1
    require(set(families) == {(4, 0), (4, 1), (4, 2), (4, 3),
                              (5, 1), (5, 2), (5, 3)}, 'all feasible k,h combinations')
    require(max(maxima.values()) == 295, 'redistribution attains sharp arithmetic ceiling')
    return dict(cut_shape=[0, 1, 6], degree_neighbor_cases=count,
                parameter_cases=[dict(k=k, h=h, count=families[k, h],
                                      max_inside_score=str(maxima[k, h]))
                                 for k, h in sorted(families)])


def one_outside_row():
    count = 0
    column_cases = 0
    maxima = dict(inside=Q(0), outside=Q(0))
    degree_patterns = []
    for degrees in product(range(3), repeat=4):
        if sum(degrees) != 3:
            continue
        high = [i for i, d in enumerate(degrees) if d == 2]
        require(len(high) <= 1, 'at most one degree-two row')
        allocation = [Q(1) if i in high else Q(2) for i in range(4)] if high else [Q(7, 4)]*4
        rows = [2*d+v for d, v in zip(degrees, allocation)]
        require(sum(allocation) == 7 and max(rows) <= 6 and max(allocation) <= 2, 'inside caps')
        inside_scores = [20*r+140+25*v for r, v in zip(rows, allocation)]+[Q(260)]
        require(max(inside_scores) <= 270, 'inside and outside-row zero A cell')
        maxima['inside'] = max(maxima['inside'], max(inside_scores))
        positive_rows = [i for i, d in enumerate(degrees) if d]
        for e in range(len(positive_rows)+1):
            for crossings in combinations(positive_rows, e):
                for outside_entry in range(3):
                    column_mass = 2*e+outside_entry
                    if column_mass > 7:
                        continue
                    scores = [20*rows[i]+20*column_mass+(50 if i in crossings else 0)
                              for i in range(4)]
                    scores.append(120+20*column_mass+25*outside_entry)
                    require(max(scores) <= 290, 'every outside-column cell bound')
                    if e == 3:
                        require(all(degrees[i] == 1 for i in crossings), 'three crossings exhaust degrees')
                        require(outside_entry <= 1, 'three-crossing column residual capacity')
                        require(all(scores[i] <= 270 for i in crossings) and scores[-1] <= 285,
                                'explicit omitted outside-column case')
                    maxima['outside'] = max(maxima['outside'], max(scores))
                    column_cases += 1
        degree_patterns.append(list(degrees))
        count += 1
    require(count == 16 and max(maxima.values()) == 290, 'complete degree parameter inventory')
    return dict(cut_shape=[1, 1, 3], degree_cases=count, outside_column_cases=column_cases,
                max_inside_score=str(maxima['inside']), max_outside_score=str(maxima['outside']),
                degree_patterns=degree_patterns)


def sharp_matrix():
    x = [[Q(0) for _ in range(7)] for _ in range(5)]
    for i, columns in enumerate(((1, 2), (1, 3), (2, 3))):
        x[i][0] = Q(5, 3)
        for j in columns:
            x[i][j] = Q(2)
    x[3][0] = Q(2)
    rows = [sum(row) for row in x]
    columns = [sum(x[i][j] for i in range(5)) for j in range(7)]
    scores = [[20*rows[i]+20*columns[j]+25*x[i][j] for j in range(7)] for i in range(5)]
    require(sum(rows) == 19 and max(rows) <= 6 and max(columns) <= 7, 'sharp matrix total and caps')
    require(max(map(max, x)) <= 2 and max(map(max, scores)) == 295, 'sharp entry cap and score')
    non_A_entries = sum(x[i][j] > 0 for i in range(5) for j in range(1, 7))
    require(non_A_entries == 6 and 7+2*non_A_entries == 19, 'matching local cut')
    require(220+45*Q(7-2, 3) == 295, 'cut and pigeonhole lower bound')
    return dict(total='19', rows=list(map(str, rows)), columns=list(map(str, columns)),
                matrix=[[str(v) for v in row] for row in x], maximum_score='295',
                maximizing_cells=[[i, j] for i in range(5) for j in range(7) if scores[i][j] == 295],
                cut_capacity=19, lower_bound='295')


def balance_consumers():
    cases = [(74, 19, 19, 19, 295, (591, 580, 584, 587), Q(665, 74)),
             (75, 19, 20, 19, 310, (594, 598, 587, 590), Q(673, 75)),
             (75, 20, 19, 19, 310, (594, 598, 587, 595), Q(673, 75)),
             (76, 20, 21, 19, 310, (600, 604, 593, 601), Q(170, 19))]
    results = []
    for t, A, B, D, local, expected, target in cases:
        bounds = (3*A+3*B+9*18+315, 3*A+3*B+9*19+local,
                  3*A+3*B+9*D+299, 8*A+3*B+4*D+302)
        law = Q(1)+Q(max(bounds), t)
        require(bounds == expected and law == target and max(bounds) < 8*t, 'conditional consumer arithmetic')
        results.append(dict(total=t, coarse_caps=[A, B, D], raw_bounds=list(bounds),
                            maximum_raw=max(bounds), law_bound=str(law), gap_to_nine=str(9-law)))
    return results


def occupation_bridge():
    noncoherent = (3*20+3*21+9*20+299, 8*20+3*21+4*20+302)
    require(noncoherent == (602, 605), 'noncoherent occupation bounds')
    good, bad = Q(604), Q(3*20+3*21+9*20+310)
    threshold = (8*76-good)/(bad-good)
    occupation = Q(3, 7)
    uniform_seven = [Q(1, 7)]*7
    S = sum(uniform_seven[4:])
    require(S == occupation and 4*uniform_seven[4]+S == Q(7, 3)*S == 1, 'sorting constant equality control')
    require(2*20 > 21 and 4*20 > 76, 'distinct terminals and at most three bad blocks')
    raw = good+(bad-good)*occupation
    law = Q(1)+raw/76
    require(bad == 613 and threshold == Q(4, 9) and occupation < threshold, 'occupation threshold')
    require(raw == Q(4255, 7) and law == Q(4787, 532) and 9-law == Q(1, 532), 'common-law arithmetic')
    return dict(good_raw=str(good), bad_raw=str(bad), noncoherent=list(noncoherent),
                strict_occupation_threshold=str(threshold), minimax_sufficient_occupation=str(occupation),
                sorting_equality_weights=list(map(str, uniform_seven)),
                raw_bound=str(raw), law_bound=str(law), gap_to_nine=str(9-law))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = dict(result='PASS', pure19_cut_types=pure19_cut_types(),
                  cut_016=zero_outside_rows(), cut_113=one_outside_row(),
                  sharp_local_matrix=sharp_matrix(), conditional_consumers=balance_consumers(),
                  four_block_occupation=occupation_bridge(),
                  scope='Exact finite arithmetic interfaces and one sharp local transport support. '
                        'Not exhaustive actual-source enumeration, terminal-cap feasibility, '
                        'four-block avoidance, a general minimax proof or Lean verification.')
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(result='PASS', cut_shapes=3,
                          redistribution_cases=result['cut_016']['degree_neighbor_cases']+result['cut_113']['degree_cases'],
                          outside_column_cases=result['cut_113']['outside_column_cases'],
                          conditional_consumers=4)))


if __name__ == '__main__':
    main()
