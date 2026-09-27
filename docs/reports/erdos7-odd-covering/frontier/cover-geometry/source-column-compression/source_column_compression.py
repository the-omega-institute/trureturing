#!/usr/bin/env python3
"""Compress actual terminal-leaf neighbours without changing five-column tests.
Finite combinatorial construction and exact controls; not Lean certification.
"""
from itertools import combinations, product
from collections import Counter, defaultdict

COLUMNS = frozenset(range(7))
FIVE_SETS = tuple(frozenset(d) for d in combinations(range(7), 5))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def neighbours(height, support):
    require(type(height) is int and height >= 1, 'height must be an integer at least one')
    period = 5 ** height
    rows = defaultdict(set)
    for point in support:
        require(isinstance(point, (tuple, list)) and len(point) == 2, 'expected (leaf,column)')
        x, y = point
        require(type(x) is int and 0 <= x < period, 'leaf outside original modulus')
        require(type(y) is int and 0 <= y < 7, 'column outside original modulus')
        rows[x].add(y)
    return {x: frozenset(ys) for x, ys in sorted(rows.items())}


def contains_ternary_tree(height, leaves):
    """Prefix digits are read from the least significant five-adic digit."""
    good = set(leaves)
    for depth in range(height - 1, -1, -1):
        counts = Counter(x % (5 ** depth) for x in good)
        good = {x for x, count in counts.items() if count >= 3}
    return 0 in good


def product_tree_source(height, rows):
    # On a five-ary tree, the complement has no ternary tree iff this
    # set has a ternary tree: each parent uses the same 3-of-5 recursion.
    return all(contains_ternary_tree(height, (x for x, ys in rows.items() if ys & d))
               for d in FIVE_SETS)


def maximum_column_matching(rows):
    """Unit capacity on columns and capacity three on each actual leaf."""
    slots = {y: tuple((x, slot) for x, ys in rows.items() if y in ys
                     for slot in range(3)) for y in COLUMNS}
    occupied = {}
    def augment(column, seen):
        for slot in slots[column]:
            if slot in seen:
                continue
            seen.add(slot)
            if slot not in occupied or augment(occupied[slot], seen):
                occupied[slot] = column
                return True
        return False
    for y in sorted(COLUMNS):
        augment(y, set())
    return {y: x for (x, _), y in occupied.items()}


def compress_source(height, support):
    """Return an actual subset, retaining >= min(original column count,6)."""
    rows = neighbours(height, support)
    require(product_tree_source(height, rows), 'source fails a product-tree test')
    original_columns = set().union(*rows.values()) if rows else set()
    require(len(original_columns) >= 5, 'source needs at least five actual columns')
    matched = maximum_column_matching(rows)
    require(len(matched) >= min(len(original_columns), 6), 'matching contradicts source bound')
    retained = {x: set() for x in rows}
    for y, x in matched.items():
        retained[x].add(y)
    for x, ys in rows.items():
        for y in sorted(ys - retained[x]):
            if len(retained[x]) >= min(3, len(ys)):
                break
            retained[x].add(y)
        require(len(retained[x]) == min(3, len(ys)), 'wrong terminal degree')
    reduced = tuple((x, y) for x in sorted(retained) for y in sorted(retained[x]))
    require(set(reduced) <= {(x,y) for x,ys in rows.items() for y in ys}, 'not an actual subset')
    for d in FIVE_SETS:
        before = {x for x, ys in rows.items() if ys & d}
        after = {x for x, ys in retained.items() if ys & d}
        require(before == after, 'a full column-deletion projection changed')
    require(product_tree_source(height, retained), 'compressed source lost its tree property')
    reduced_columns = {y for x,y in reduced}
    require(len(reduced_columns) >= min(len(original_columns),6), 'lost standalone projection')
    return reduced, {'matched': tuple(sorted(matched.items())), 'original_columns':len(original_columns),
                     'retained_columns':len(reduced_columns), 'original_points':sum(map(len, rows.values())),
                     'retained_points':len(reduced)}


def direct_tree_test_height_two(rows):
    """Independent literal ternary trees; root zero is not assumed absent."""
    child_sets = tuple(combinations(range(5),3))
    for d in FIVE_SETS:
        for roots in combinations(range(5),3):
            for children in product(child_sets, repeat=3):
                if not any(rows.get(r+5*a, frozenset()) & d
                           for r, aset in zip(roots, children) for a in aset):
                    return False
    return True


def controls():
    # Both kinds of terminal fibres occur, including a source for which
    # all seven columns cannot be kept with degree at most three.
    counts = []
    for height in range(1,5):
        leaves = [sum(a*5**i for i,a in enumerate(word))
                  for word in product(range(3), repeat=height)]
        source = {(x,y) for x in leaves for y in range(3)}
        source |= {(leaves[0],y) for y in range(7)}
        reduced, info = compress_source(height, source)
        require(info['retained_columns'] == 6, 'sharp six-column retention control')
        require(info['original_points'] == 3**(height+1)+4, 'source size')
        counts.append((height,info['original_points'],len(reduced)))
    # Four nonrobust roots; each bad graph is the distinct edge {0,r}.
    source = {(r,y) for r in range(1,5) for y in (0,r)}
    source |= {(r+5*a,y) for r in range(1,5) for a in (1,2) for y in (0,1,2)}
    rows = neighbours(2,source)
    require(direct_tree_test_height_two(rows), 'literal four-nonrobust product-tree test')
    reduced,info=compress_source(2,source)
    require(set(reduced)==source and info['retained_columns']==5, 'degree-three source unchanged')
    # Sparse very high numerical labels are kept literally, without a
    # quotient relabelling or separate permutation of each root.
    source2={(4+5*x,y) for x,y in source}
    # This source lies in only one root and must fail the height-three test.
    invalid=[(0,source),(2,[(25,0)]),(2,[(1,7)]),(2,[(True,0)]),
             (3,source2),(2,[]),(1,[(x,y) for x in range(5) for y in range(4)])]
    rejected=0
    for height,bad_source in invalid:
        try:
            compress_source(height,bad_source)
        except ValueError:
            rejected+=1
        else:
            raise ValueError('invalid source accepted')
    require(rejected==len(invalid), 'invalid-input count')
    print('PASS: arbitrary-height construction; 21 projections retained per source; '
          '210000 literal depth-two tests; sharp six-column limit; invalid inputs rejected=',rejected)
    print('height/original points/reduced points:',counts)


if __name__ == '__main__':
    controls()
