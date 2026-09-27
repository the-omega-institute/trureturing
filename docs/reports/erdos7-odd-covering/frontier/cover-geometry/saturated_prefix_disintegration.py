#!/usr/bin/env python3
"""Exact finite controls for saturated first-prime fibres (report 378).

The general argument is in the report. These checks exercise nested
prefix isolation, the three-box classification and exact incidence bounds.
They are not instances of an unknown minimum odd covering system.
"""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
import json


def check(ok, message):
    if not ok:
        raise ValueError(message)


# A nonuniform complete ternary subtree in the five-ary depth-three tree.
# Digits are lowest-first, and permitted children depend on the parent.
p, q, r, depth = 5, 3, 3, 3
levels = [{()}]
for a in range(depth):
    next_level = set()
    for prefix in levels[-1]:
        shift = (sum((i+1)*v for i, v in enumerate(prefix))+a) % p
        chosen = {(shift+d) % p for d in (0, 1, 3)}
        next_level.update(prefix+(d,) for d in chosen)
    levels.append(next_level)
A = levels[-1]
check(len(A) == r**depth, 'saturated projection size')
for leaf in A:
    tree = {()}
    for a in range(depth):
        next_tree = set()
        for prefix in tree:
            if prefix == leaf[:a]:
                present = {v[-1] for v in levels[a+1] if v[:-1] == prefix}
                children = {leaf[a]} | (set(range(p))-present)
            else:
                children = set(range(q))
            check(len(children) == q, 'isolating tree branching')
            next_tree.update(prefix+(d,) for d in children)
        tree = next_tree
    check(len(tree) == q**depth and tree.intersection(A) == {leaf}, 'leaf isolation')

# All multisets of three full rows, full columns or cells in the 5x7 grid.
rectangles = []
for rows in combinations(range(5), 3):
    for columns in combinations(range(7), 5):
        rectangles.append(sum(1 << (7*a+b) for a in rows for b in columns))
boxes = [('row', a, sum(1 << (7*a+b) for b in range(7))) for a in range(5)]
boxes += [('column', b, sum(1 << (7*a+b) for a in range(5))) for b in range(7)]
boxes += [('cell', 7*a+b, 1 << (7*a+b)) for a in range(5) for b in range(7)]
blocking = []
count = 0
for indices in combinations_with_replacement(range(len(boxes)), 3):
    count += 1
    mask = 0
    for i in indices:
        mask |= boxes[i][2]
    meets_all = all(mask & rectangle for rectangle in rectangles)
    pure = (len(set(indices)) == 3 and
            (all(boxes[i][0] == 'row' for i in indices) or
             all(boxes[i][0] == 'column' for i in indices)))
    check(meets_all == pure, 'three-box classification')
    if meets_all:
        blocking.append(indices)
check(count == 18424 and len(blocking) == 45, 'classification totals')

# Truncated ternary prices; these support but do not replace the all-height proof.
incidence = []
for H in range(1, 9):
    pure_tail = sum((F(3)**(1-e) for e in range(2, H+1)), F(0))
    base = 2-pure_tail
    exception = sum((F(3)**(-j) for j in range(2, H)), F(0))
    bound = 4*base-exception
    formula = F(8) if H == 1 else F(35, 6)+F(5, 2)*F(3)**(1-H)
    check(bound == formula, 'incidence expression')
    incidence.append(dict(H=H, nonpure_tail_mass=str(base),
                          triple_exception_cap=str(exception), incidence_lower=str(bound)))
# Saturation at depth one permits a strictly better composite price.
price_controls = []
for alpha, beta in product(range(4), range(4)):
    c = F(3)**(-beta)
    old = min(F(3)**(-alpha), c)
    new = F(3)**(-min(alpha, 1))*min(F(3)**(-max(alpha-1, 0)), c)
    check(new <= old, 'price must not weaken')
    price_controls.append(dict(alpha=alpha, beta=beta, old=str(old), new=str(new)))
check(next(x for x in price_controls if x['alpha'] == x['beta'] == 1)['new'] == '1/9',
      'joint low-prefix price')
print(json.dumps(dict(saturated_leaf_count=len(A), isolation_checks=len(A),
                      grid_box_count=len(boxes), grid_rectangles=len(rectangles),
                      grid_multisets_checked=count, blocking_triples=len(blocking),
                      incidence=incidence, price_controls=price_controls,
                      scope='Finite controls of the ordinary argument; no minimum odd-cover witness'),
                 indent=2))
