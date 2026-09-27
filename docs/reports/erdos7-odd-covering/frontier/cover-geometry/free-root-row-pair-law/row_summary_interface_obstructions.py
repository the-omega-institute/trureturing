#!/usr/bin/env python3
"""Actual obstructions to two row-summary interfaces for the common-law problem.

signature_source(height, kind, centre, dominant) constructs a clean
five-tree with any specified majority signature and at most 5*3**(h-1)
leaves outside any specified dominant row.

stationary_counterexample(height, coefficient, distinguished_row=1)
constructs actual full/pair tree laws, their final-row stationary mixture,
and a literal original-divisor layout that violates the target for all
coefficients. Exact uniform coefficient and height claims are proved in
the accompanying report; these finite controls do not establish them by
sampling. No source minimax counterexample or covering conclusion follows.

Only the standard library and a sibling existing original-tree API are
used. Running without arguments prints fixed exact controls as JSON and
writes no files. Construction size grows with the requested height.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import json

ROWS = (1, 2, 3, 4)
PARTITIONS = (((1, 2), (3, 4)), ((1, 3), (2, 4)), ((1, 4), (2, 3)))
ROW_CODE = {r: tuple(1 if r in a else -1 for a, b in PARTITIONS) for r in ROWS}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def _api():
    filename = 'prime_layout_mixture_certificate.py'
    spec = importlib.util.spec_from_file_location('_signature_tree_api', Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:
        raise ImportError('cannot load sibling '+filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


API = _api()


def signature_code(kind, centre):
    require(type(kind) is str and kind in ('star', 'triangle')
            and type(centre) is int and centre in ROWS,
            'a star/triangle and literal row centre are required')
    return ROW_CODE[centre] if kind == 'star' else tuple(-x for x in ROW_CODE[centre])


def base_labels(kind, centre):
    signature_code(kind, centre)
    if kind == 'star':
        return (centre,)*5
    a, b, c = (r for r in ROWS if r != centre)
    return (a, a, b, b, c)


def signature_source(height, kind, centre, dominant):
    """Return a clean source: same signature at every recursive root.

    Three root children recursively continue the requested signature;
    the other two children are full five-trees of the dominant row.
    The height-one seed is a star or a 2,2,1 triangle colouring.
    """
    require(type(height) is int and height >= 1, 'positive integer height required')
    require(type(dominant) is int and dominant in ROWS, 'literal dominant row required')
    seed = base_labels(kind, centre)
    result = set()
    for digits in product(range(5), repeat=height):
        row = seed[digits[-1]] if all(d < 3 for d in digits[:-1]) else dominant
        residue = sum(d*7**j for j, d in enumerate(digits))
        result.add((row, residue))
    return result


def measured_signature(points, height):
    require(type(height) is int and height >= 1, 'positive integer height required')
    require(type(points) in (set, frozenset, tuple, list), 'finite clean source required')
    checked = []
    for point in points:
        require(type(point) in (tuple, list) and len(point) == 2,
                'row-residue point required')
        r, y = point
        require(type(r) is int and r in ROWS and type(y) is int and 0 <= y < 7**height,
                'point outside the literal four-row carrier')
        checked.append((r, y))
    require(len(set(checked)) == len(checked), 'duplicate clean-source points')
    leaves = {y for r, y in checked}
    require(len(leaves) == len(checked) == 5**height
            and API.contains_bary_tree(leaves, height, 5),
            'source must label each leaf of one full five-tree exactly once')
    points = checked
    result = []
    for a, b in PARTITIONS:
        left = API.contains_bary_tree({y for r, y in points if r in a}, height, 3)
        right = API.contains_bary_tree({y for r, y in points if r in b}, height, 3)
        require(left != right, 'clean complement duality failed')
        result.append(1 if left else -1)
    return tuple(result)


def signature_controls():
    controls = 0
    extremes = []
    for h in (1, 2, 4):
        maximum = 0
        for kind, centre, dominant in product(('star', 'triangle'), ROWS, ROWS):
            points = signature_source(h, kind, centre, dominant)
            projected = {y for r, y in points}
            require(len(points) == len(projected) == 5**h, 'source must have one label per leaf')
            require(API.contains_bary_tree(projected, h, 5), 'full five-tree projection')
            require(measured_signature(points, h) == signature_code(kind, centre), 'wrong actual signature')
            non_dominant = sum(r != dominant for r, y in points)
            initial = sum(r != dominant for r in base_labels(kind, centre))
            require(non_dominant == initial*3**(h-1), 'incorrect exceptional-set recurrence')
            require(non_dominant <= 5*3**(h-1), 'exceptional-set bound')
            maximum = max(maximum, non_dominant)
            controls += 1
        extremes.append({'height': h, 'leaves': 5**h, 'maximum_non_dominant_leaves': maximum})
    # Validate the full internal majority rule on mixed-signature subtrees.
    choices = [('star', 1), ('triangle', 2), ('star', 3), ('triangle', 4), ('star', 2)]
    children = [signature_source(2, kind, centre, i % 4 + 1) for i, (kind, centre) in enumerate(choices)]
    combined = {(r, i+7*y) for i, child in enumerate(children) for r, y in child}
    child_signatures = [measured_signature(child, 2) for child in children]
    majority = tuple(1 if sum(s[j] == 1 for s in child_signatures) >= 3 else -1 for j in range(3))
    require(measured_signature(combined, 3) == majority, 'coordinatewise majority rule')
    # c=1/3 endpoint: a winning-pair tree can live entirely off the dominant row.
    points = signature_source(4, 'star', 2, 1)
    ternary = {sum(d*7**j for j, d in enumerate(ds)) for ds in product(range(3), repeat=4)}
    require({(2, y) for y in ternary} <= points, 'endpoint ternary witness missing')
    for j in range(5):
        prefix_counts = Counter(y % 7**j for y in ternary)
        require(max(prefix_counts.values()) == 3**(4-j), 'endpoint uniform ternary cap')
    return {'fixed_source_controls': controls, 'heights': extremes,
            'all_eight_signatures': sorted({signature_code(k, s) for k, s in product(('star','triangle'),ROWS)}),
            'mixed_child_majority_rule': True, 'endpoint_off_dominant_ternary_law': True,
            'scope': 'construction checks; the polytope impossibility is an all-height analytic theorem'}


def _mixture(components):
    weights = defaultdict(F)
    for coefficient, law in components:
        for point, mass in law.items():
            weights[point] += coefficient*mass
    return {p: w for p, w in weights.items() if w}


def _leaves(height, branching):
    return {sum(d*7**j for j, d in enumerate(ds))
            for ds in product(range(branching), repeat=height)}


def stationary_counterexample(height, coefficient, distinguished_row=1):
    """Construct one actual supported failure family at any rational coefficient.

    coefficient is an int or Fraction in [0,1]. The distinguished row
    supports a full five-tree; every other row supports the common nested
    ternary tree. The three pairs not using the distinguished row select
    their row labels cyclically. Returned nu is computed from the actual
    component laws, not from a pointwise closed-form shortcut.
    """
    require(type(height) is int and height >= 1, 'positive integer height required')
    require(type(coefficient) in (int, F) and 0 <= coefficient <= 1,
            'coefficient must be an exact rational in [0,1]')
    require(type(distinguished_row) is int and distinguished_row in ROWS,
            'literal distinguished row required')
    coefficient = F(coefficient)
    d = distinguished_row
    others = tuple(r for r in ROWS if r != d)
    five, three = _leaves(height, 5), _leaves(height, 3)
    actual_source = {(d, y) for y in five} | {(r, y) for r in others for y in three}
    mu = {(d, y): F(1, 5**height) for y in five}
    pair_laws = {tuple(sorted((d, r))): {(d, y): F(1, 3**height) for y in three}
                 for r in others}
    a, b, c = others
    for pair, row in (((a, b), a), ((b, c), b), ((a, c), c)):
        pair_laws[pair] = {(row, y): F(1, 3**height) for y in three}
    omitted = {i: _mixture((F(1,3), law) for pair, law in pair_laws.items() if i not in pair)
               for i in ROWS}
    matrix = {i: {r: coefficient*(r == d)
                       +(1-coefficient)*sum((mass for (row,y), mass in omitted[i].items() if row == r), F(0))
                   for r in ROWS} for i in ROWS}
    beta = {r: ((2+coefficient) if r == d else (1-coefficient))/(5-2*coefficient)
            for r in ROWS}
    omega = _mixture((beta[i], omitted[i]) for i in ROWS)
    nu = _mixture(((coefficient, mu), (1-coefficient, omega)))
    modulus = 7**height
    x = modulus*(d*pow(modulus, -1, 5) % 5)
    phases = tuple(x % div for div in API.original_divisors(height))
    return {'height': height, 'coefficient': coefficient, 'distinguished_row': d,
            'source': actual_source, 'mu': mu, 'pair_laws': pair_laws,
            'omitted_laws': omitted, 'row_matrix': matrix, 'beta': beta,
            'nu': nu, 'original_phases': phases}


def stationary_control(height, coefficient, distinguished_row=1):
    data = stationary_counterexample(height, coefficient, distinguished_row)
    nu, actual_source = data['nu'], data['source']
    require(all(m > 0 for m in nu.values()) and sum(nu.values(), F(0)) == 1
            and set(nu) <= actual_source, 'actual supported probability failed')
    require(API.contains_bary_tree({y for r,y in actual_source}, height, 5), 'full five-tree')
    for pair, law in data['pair_laws'].items():
        require(set(law) <= actual_source and all(r in pair for r,y in law)
                and sum(law.values(), F(0)) == 1, 'actual pair-law support')
        require(API.contains_bary_tree({y for r,y in law}, height, 3), 'actual pair ternary tree')
    beta = data['beta']
    for row in ROWS:
        require(sum(beta[i]*data['row_matrix'][i][row] for i in ROWS) == beta[row], 'stationarity')
        require(sum((m for (r,y), m in nu.items() if r == row), F(0)) == beta[row], 'final row identity')
    actual = sum((m*API.literal_layout_cost(height, data['original_phases'], point)
                  for point,m in nu.items()), F(0))
    s3 = sum((F(2*j+1, 3**j) for j in range(height+1)), F(0))
    s5 = sum((F(2*j+1, 5**j) for j in range(height+1)), F(0))
    lam = F(coefficient)
    predicted = 4*lam*s5+(1-lam)*(11-8*lam)/(5-2*lam)*s3
    require(actual == predicted and actual > 2*s3, 'literal layout expectation or target failure')
    return {'height': height, 'coefficient': str(lam), 'distinguished_row': distinguished_row,
            'source_points': len(actual_source), 'actual_layout_expectation': str(actual),
            'target_gap': str(actual-2*s3), 'stationary_rows': {str(r):str(beta[r]) for r in ROWS},
            'original_phases': data['original_phases']}


def malformed_controls():
    tests = [lambda h=h: stationary_counterexample(h, F(1,2))
             for h in (True, False, 0, -1, 1.0, '1')]
    tests += [lambda c=c: stationary_counterexample(1, c)
              for c in (True, False, 0.5, '1/2', F(-1,2), F(3,2))]
    tests += [lambda r=r: stationary_counterexample(1, F(1,2), r)
              for r in (True, 0, 5, 1.0)]
    tests += [lambda args=args: signature_source(*args) for args in (
        (0,'star',1,1), (True,'star',1,1), (1,'other',1,1),
        (1,'star',True,1), (1,'triangle',0,1), (1,'star',1,True))]
    tests += [lambda points=points: measured_signature(points, 1) for points in (
        [(True, y) for y in range(5)], [(1, y) for y in range(5)]+[(1, 0)],
        [(1, y) for y in range(4)], [(1, y) for y in range(5)]+[(2, 0)])]
    rejected = 0
    for test in tests:
        try:
            test()
        except ValueError:
            rejected += 1
    require(rejected == len(tests), 'malformed public input accepted')
    return rejected


def self_check():
    stationary = [stationary_control(h, c) for h in (1,4) for c in (F(0), F(3,8), F(1))]
    stationary.append(stationary_control(2, F(3,8), 3))
    return {'stationary_actual_law_controls': stationary,
            'signature_controls': signature_controls(),
            'malformed_public_inputs_rejected': malformed_controls(),
            'scope': 'two explicit interface obstructions; no all-source minimax or covering conclusion'}


if __name__ == '__main__':
    print(json.dumps(self_check(), indent=2))
