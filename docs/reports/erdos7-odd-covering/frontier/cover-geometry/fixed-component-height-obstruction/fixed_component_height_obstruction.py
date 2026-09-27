#!/usr/bin/env python3
"""Exact obstruction to transporting arbitrary fixed cap components in 5-depth.

The reusable routines check actual two-coordinate laws, prefix capacities,
independently assigned original-divisor layouts, and one common layout-mixture
lower certificate. The retained example has heights (3,3), six legal forest
laws and one full-five law. Their convex hull misses the finite target even
though the same actual source has a uniform law well below that target.

Standard library only; no optimizer, no file writes, and no Lean certification.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exponent_labels(height5, height7):
    require(type(height5) is int and height5 >= 1, 'invalid 5-height')
    require(type(height7) is int and height7 >= 0, 'invalid 7-height')
    return tuple(product(range(height5+1), range(height7+1)))


def validate_law(law, height5, height7, roots):
    exponent_labels(height5, height7)
    require(law and sum(law.values(), F()) == 1, 'probability normalization')
    for (x, y), mass in law.items():
        require(type(x) is int and type(y) is int, 'integer coordinates')
        require(isinstance(mass, F) and mass > 0, 'positive exact mass')
        require(0 <= x < 5**height5 and 0 <= y < 7**height7,
                'point outside complete carrier')
        require(x % 5 in roots, 'point outside actual source')


def prefix_maximum(law, key):
    masses = defaultdict(F)
    for point, mass in law.items():
        masses[key(point)] += mass
    return max(masses.values(), default=F())


def check_coordinate_caps(law, coordinate, prime, height, base):
    require(coordinate in (0, 1) and prime > 1 and base > 1, 'cap parameters')
    maxima = []
    for depth in range(height+1):
        value = prefix_maximum(law, lambda p: p[coordinate] % prime**depth)
        require(value <= F(1, base**depth), 'coordinate prefix cap')
        maxima.append(value)
    return tuple(maxima)


def check_forest_caps(law, height5, rows):
    require(all(x % 5 in rows for x, _ in law), 'forest row support')
    maxima = []
    for depth in range(height5):
        value = prefix_maximum(law, lambda p: (
            p[0] % 5, (p[0] // 5) % 5**depth))
        require(value <= F(1, 3**depth), 'forest first-root and tail cap')
        maxima.append(value)
    return tuple(maxima)


def centered_layout(height5, height7, center):
    return {(a, b): (center[0] % 5**a, center[1] % 7**b)
            for a, b in exponent_labels(height5, height7)}


def validate_layout(layout, height5, height7):
    require(set(layout) == set(exponent_labels(height5, height7)),
            'every original divisor, including one, must occur exactly once')
    for (a, b), (u, v) in layout.items():
        require(type(u) is int and type(v) is int, 'integer phases')
        require(0 <= u < 5**a and 0 <= v < 7**b, 'phase outside its modulus')


def squared_load(point, layout):
    x, y = point
    return sum(x % 5**a == u and y % 7**b == v
               for (a, b), (u, v) in layout.items())**2


def expected_layout_price(law, layout):
    return sum((mass*squared_load(point, layout)
                for point, mass in law.items()), F())


def coordinate_marginal(law, coordinate):
    require(coordinate in (0, 1), 'marginal coordinate')
    marginal = defaultdict(F)
    for point, mass in law.items():
        marginal[point[coordinate]] += mass
    return dict(marginal)


def complete_layout_prefix_upper(law, height5, height7):
    """Bound every independent layout using its 256 (at height3) LCM pairs."""
    labels = exponent_labels(height5, height7)
    caps = {(a, b): prefix_maximum(law, lambda p: (p[0] % 5**a, p[1] % 7**b))
            for a, b in labels}
    upper = sum((caps[max(a, c), max(b, d)]
                 for (a, b), (c, d) in product(labels, repeat=2)), F())
    return caps, upper


def common_lower_certificate(laws, layouts, weights, height5, height7):
    require(len(layouts) == len(weights) and layouts, 'layout mixture size')
    require(all(isinstance(w, F) and w >= 0 for w in weights)
            and sum(weights, F()) == 1, 'layout mixture normalization')
    for layout in layouts:
        validate_layout(layout, height5, height7)
    prices = tuple(tuple(expected_layout_price(law, layout) for layout in layouts)
                   for law in laws)
    averages = tuple(sum((w*c for w, c in zip(weights, row)), F())
                     for row in prices)
    return prices, averages, min(averages)


def complete_missing_root_uniform_moment(roots, height5, height7):
    """LCM upper bound and an attaining layout on the actual complete source."""
    roots = tuple(roots)
    require(roots and len(set(roots)) == len(roots)
            and all(type(r) is int and 0 <= r < 5 for r in roots), 'actual roots')
    labels = exponent_labels(height5, height7)

    def cap5(a):
        return F(1) if a == 0 else F(1, len(roots)*5**(a-1))

    upper = sum((cap5(max(a, c))*F(1, 7**max(b, d))
                 for (a, b), (c, d) in product(labels, repeat=2)), F())
    layout = centered_layout(height5, height7, (roots[0], 0))
    points = ((r+5*t, y) for r in roots for t in range(5**(height5-1))
              for y in range(7**height7))
    source_size = len(roots)*5**(height5-1)*7**height7
    attained = F(sum(squared_load(point, layout) for point in points), source_size)
    require(attained == upper, 'uniform source bound is attained')
    return source_size, upper


def controls():
    height5 = height7 = 3
    roots = tuple(range(1, 5))
    pairs = tuple(combinations(roots, 2))
    # Any three first-5 roots meet these four roots; all later tails and
    # the entire 7 coordinate are present in the actual source.
    require(all(set(branches) & set(roots) for branches in combinations(range(5), 3)),
            'complete product-tree source condition at the first 5 root')
    forests = {}
    for pair in pairs:
        law = {(r+5*d0+25*d1, d0+7*d1+49*d2): F(1, 54)
               for r in pair for d0, d1, d2 in product(range(3), repeat=3)}
        validate_law(law, height5, height7, roots)
        check_forest_caps(law, height5, pair)
        check_coordinate_caps(law, 1, 7, height7, 3)
        forests[pair] = law
    full = {(1, d0+7*d1+49*d2): F(1, 125)
            for d0, d1, d2 in product(range(5), repeat=3)}
    validate_law(full, height5, height7, roots)
    check_coordinate_caps(full, 1, 7, height7, 5)
    require(prefix_maximum(full, lambda p: p[0] % 25) == 1,
            'the full-five component retains no nontrivial 5-tail cap')

    chain = defaultdict(F)
    for pair in ((2, 3), (2, 4), (3, 4)):
        for point, mass in forests[pair].items():
            chain[point] += mass/3
    validate_law(chain, height5, height7, roots)
    check_coordinate_caps(chain, 0, 5, height5, 3)
    check_coordinate_caps(chain, 1, 7, height7, 3)

    names = tuple(str(pair) for pair in pairs)+('full-five', 'chain-three-three')
    laws = tuple(forests[pair] for pair in pairs)+(full, chain)
    layouts = tuple(centered_layout(height5, height7, (r, 0)) for r in roots)
    weights = (F(8684, 31365),)+(F(22681, 94095),)*3
    prices, averages, lower = common_lower_certificate(
        laws, layouts, weights, height5, height7)
    for pair, row in zip(pairs, prices[:6]):
        require(row == tuple(F(454 if r in pair else 76, 27) for r in roots),
                'forest original-layout prices')
    require(prices[6] == (F(3712, 125),)+(F(232, 125),)*3, 'full original-layout prices')
    require(lower == F(99992, 10455), 'shared lower certificate')
    target = (3-F(5, 27))**2
    require(lower-target == F(4168696, 2540565), 'strict target gap')
    source_size, good = complete_missing_root_uniform_moment(roots, height5, height7)
    require(good == F(3933, 1225) and good < target, 'same source has a good law')

    marginal5, marginal7 = (coordinate_marginal(chain, i) for i in (0, 1))
    require(len(marginal5) == len(marginal7) == 27
            and set(marginal5.values()) == set(marginal7.values()) == {F(1, 27)},
            'complete chain marginals are uniform on 27 points')
    independent = {(x, y): px*py for x, px in marginal5.items()
                   for y, py in marginal7.items()}
    validate_law(independent, height5, height7, roots)
    require(len(independent) == 729, 'independent product support')
    require(coordinate_marginal(independent, 0) == marginal5
            and coordinate_marginal(independent, 1) == marginal7,
            'complete coordinate marginals must remain identical')
    chain_caps, chain_upper = complete_layout_prefix_upper(chain, height5, height7)
    independent_caps, independent_upper = complete_layout_prefix_upper(
        independent, height5, height7)
    for a, b in exponent_labels(height5, height7):
        expected = F(1, 3**b) if a == 0 else F(1, 3**(1+max(a-1, b)))
        require(chain_caps[a, b] == expected, 'correlated joint prefix maximum')
        require(independent_caps[a, b] == F(1, 3**(a+b)), 'independent joint prefix maximum')
    attaining = centered_layout(height5, height7, (2, 0))
    require(chain_upper == expected_layout_price(chain, attaining) == F(328, 27),
            'correlated exact complete-layout moment')
    require(independent_upper == expected_layout_price(independent, attaining) == target,
            'independent exact complete-layout moment')
    require(chain_upper-independent_upper == F(3080, 729), 'same-marginal moment gap')
    return {'heights': [height5, height7], 'original_divisor_labels': len(layouts[0]),
            'actual_source_size': source_size, 'common_layout_weights': weights,
            'components': {name: {'points': len(law), 'original_layout_prices': row,
                                  'common_layout_price': average}
                           for name, law, row, average in zip(names, laws, prices, averages)},
            'fixed_component_lower': lower, 'target': target, 'strict_gap': lower-target,
            'same_source_uniform_exact_moment': good,
            'same_marginal_comparison': {
                'complete_marginal_support_sizes': [len(marginal5), len(marginal7)],
                'correlated_support_size': len(chain), 'independent_support_size': len(independent),
                'correlated_exact_moment': chain_upper, 'independent_exact_moment': independent_upper,
                'moment_gap': chain_upper-independent_upper,
                'ordered_original_label_pairs': len(layouts[0])**2},
            'scope': 'arbitrary fixed components cannot be transported by weights alone; '
                     'no obstruction to free component selection or the unrestricted source target',
            'verification': 'exact ordinary certificate; no optimizer or Lean certification'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compact', action='store_true', help='emit one-line JSON')
    args = parser.parse_args()
    print(json.dumps(controls(), default=str, indent=None if args.compact else 2, sort_keys=True))


if __name__ == '__main__':
    main()
