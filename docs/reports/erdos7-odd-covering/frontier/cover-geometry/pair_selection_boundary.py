#!/usr/bin/env python3
"""Two deterministic sources refute unconditional pair-neighborhood reduction.
Exhaustively checks local pair options and disjoint-root selection only;
no claim that the sources have no successful actual probability law.
"""
from collections import Counter
from itertools import combinations, product
import json


def need(ok, message):
    if not ok:
        raise AssertionError(message)


COLS = tuple(range(7))
PAIRS = tuple(combinations(COLS, 2))
BASE = {(0,1), (0,2), (1,2)}


def review(rows):
    bad = []
    pair_options = []
    for row in rows:
        need(len(row) == 3, 'exactly three active children')
        need(all(len(ys) >= 2 for ys in row), 'all nonempty neighborhoods have degree at least two')
        bad.append({e for e in PAIRS if sum(bool(set(ys)-set(e)) for ys in row) < 3})
        options = {frozenset(ps) for ps in product(*(combinations(ys,2) for ys in row))}
        need(all(option & BASE for option in options), 'every root must consume a base pair')
        pair_options.append(options)
    need(all(bad[i].isdisjoint(bad[j]) for i,j in combinations(range(4),2)), 'source admissibility')
    need(len({y for row in rows for ys in row for y in ys}) >= 5, 'five-column projection')
    valid = 0
    def select(r, used):
        nonlocal valid
        if r == 4:
            valid += 1
            return
        for option in pair_options[r]:
            if not used & option:
                select(r+1, used | option)
    select(0, frozenset())
    need(valid == 0, 'no disjoint-root pair reduction exists')
    return dict(rows=rows, points=sum(len(ys) for row in rows for ys in row),
                bad_pairs=[sorted(bs) for bs in bad], robust_roots=sum(not bs for bs in bad),
                root_option_counts=[len(o) for o in pair_options], valid_pair_selections=valid)


def main():
    triple = (0,1,2)
    source38 = ((triple,)*3, (triple,)*3, (triple,)*3, ((0,1,2,3,4),triple,triple))
    source27 = (((0,1),(0,3),(1,4)), ((0,2),)*3, ((1,2),)*3, (triple,)*3)
    first, second = review(source38), review(source27)
    need(first['points'] == 38 and first['robust_roots'] == 4, '38-point old robust class')
    need(second['points'] == 27 and second['robust_roots'] == 1, '27-point stronger reduction boundary')
    print(json.dumps(dict(source38=first, source27=second), indent=2))


if __name__ == '__main__':
    main()
