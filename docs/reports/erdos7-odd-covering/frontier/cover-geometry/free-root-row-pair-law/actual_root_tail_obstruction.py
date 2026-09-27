#!/usr/bin/env python3
"""Exact-root / separately maximized depth-tail obstruction for report 423.

The all-height proof is analytic. These exact controls check actual source
support, all seven trees, component caps, the coefficient obstruction, and
a same-component K=2 law passing the original independent-phase game.
Standard library only; this program writes no files.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import concentrated_sharp_source_relabel_transport as family
import prime_layout_mixture_certificate as layouts
import single_surplus_source_common_law as profiles
from independent_layout_tree_dp import IndependentLayoutTreeDP


def words(branching, height):
    family.integer(height, 0, 'height')
    family.need(type(branching) is int and 1 <= branching <= 7, 'branching')
    return frozenset(sum(d*7**j for j, d in enumerate(ds))
                     for ds in product(range(branching), repeat=height))


def components(height):
    family.integer(height, 2, 'height')
    five, three = words(5, height), words(3, height)
    full = {(2 if y % 49 == 0 else 1, y): F(1, 5**height) for y in five}
    tau = {r: {(r, y): F(1, 3**height) for y in three} for r in (2, 3)}
    source = frozenset(full) | frozenset(tau[2]) | frozenset(tau[3])
    pairs = {(2, 3): tau[2], (2, 4): tau[2], (3, 4): tau[3]}
    return source, full, pairs


def common_law(height, full, pairs, alpha):
    alpha = family.rational(alpha, 'alpha')
    family.need(0 <= alpha <= 1, 'alpha outside unit interval')
    return family.mixture(height, [(alpha, full)]
                          + [((1-alpha)/3, pairs[p]) for p in family.PAIRS])


def root_marginal(law):
    result = defaultdict(F)
    for (r, y), w in law.items():
        result[r, y % 7] += w
    return dict(result)


def root_cost(root, a, c, s, d):
    return sum((w*(1+int(r == a)+int(y == c)+int(r == s and y == d))**2
                for (r, y), w in root.items()), F())


def exact_root(law):
    root = root_marginal(law)
    return max(root_cost(root, *phase)
               for phase in product(range(5), range(7), range(5), range(7)))


def separated_bound(height, law):
    law = family.probability(height, law)
    b, _ = profiles.profile_bound(height, law)
    return exact_root(law) + sum(((2*j+1)*b[j] for j in range(2, height+1)), F())


def geometric_tail(base, height):
    return sum((F(2*j+1, base**j) for j in range(2, height+1)), F())


def certificate_minimum(height):
    family.integer(height, 2, 'height')
    return F(838, 205) + F(80, 41)*geometric_tail(5, height) \
        + F(63, 41)*geometric_tail(3, height)


def source_control(height):
    source, full, pairs = components(height)
    family.need(layouts.contains_bary_tree({y for _, y in source}, height, 5),
                'full five-tree missing')
    for pair in combinations(family.ROWS, 2):
        family.need(layouts.contains_bary_tree({y for r, y in source if r in pair},
                                               height, 3), 'pair tree missing')
    for label, law, base in [('full', full, 5)] + [
            (str(pair), law, 3) for pair, law in pairs.items()]:
        family.probability(height, law)
        family.need(set(law) <= source, 'unsupported component '+label)
        for j in range(1, height+1):
            pure, _ = family.prefix_masses(law, j)
            family.need(max(pure.values()) <= F(1, base**j), 'component prefix cap')
    for pair, law in pairs.items():
        family.need(all(r in pair for r, _ in law), 'pair row support')
    family.need(sum((w for (r, _), w in full.items() if r != 1), F()) == F(1, 25),
                'full disagreement mass')
    t5, t3 = geometric_tail(5, height), geometric_tail(3, height)
    for alpha in (F(), F(1, 3), F(5, 11), F(20, 41), F(2150, 4013), F(1)):
        nu = common_law(height, full, pairs, alpha)
        b, _ = profiles.profile_bound(height, nu)
        family.need(all(b[j] == 4*alpha/F(5**j)+3*(1-alpha)/F(3**j)
                        for j in range(2, height+1)), 'exact actual tail profile')
        root = root_marginal(nu)
        family.need(root_cost(root, 1, 1, 1, 1) == 2+F(107, 25)*alpha,
                    'first root line')
        family.need(root_cost(root, 2, 0, 2, 0) == 6-F(98, 25)*alpha,
                    'second root line')
    crossing = common_law(height, full, pairs, F(20, 41))
    family.need(exact_root(crossing) == F(838, 205), 'root crossing upper')
    minimum = certificate_minimum(height)
    family.need(separated_bound(height, crossing) == minimum, 'coefficient minimum attainment')
    target = layouts.default_target(height)
    excess = F(33, 205)+F(19, 41)*F(height+2, 3**height) \
        - F(10, 41)*F(4*height+7, 5**height)
    family.need(minimum-target == excess > F(3, 205), 'uniform certificate obstruction')
    conditional = {p: w/F(24, 25) for p, w in full.items() if p[0] == 1}
    zeta = family.mixture(height, [(F(1, 3), conditional),
                                  (F(1, 3), pairs[2, 3]), (F(1, 3), pairs[3, 4])])
    family.need(set(zeta) <= source, 'successful comparison law support')
    b, upper = profiles.profile_bound(height, zeta)
    family.need(b[:2] == (F(2), F(5, 8)), 'successful root profile')
    family.need(all(b[j] == F(25, 72*5**j)+F(5, 3**(j+1))
                    for j in range(2, height+1)), 'successful tail profile')
    family.need(upper == F(31, 8)+F(25, 72)*t5+F(5, 3)*t3,
                'successful all-height bound')
    family.need(target-upper >= F(13, 54), 'successful uniform margin')
    return {'height': height, 'source_points': len(source),
            'minimum_separated_certificate': minimum, 'certificate_excess': excess,
            'other_supported_law_upper': upper, 'other_supported_law_margin': target-upper}


def exact_height_two(weights):
    """All original phases, via root enumeration and exact last-label gains.

    For each of 1,225 root layouts, optimize the pure/mixed depth-two
    labels jointly. Their phases may lie in different depth-two cells.
    Integer weights make every comparison exact.
    """
    family.need(type(weights) is dict and weights, 'nonempty integer weight map')
    family.points(2, tuple(weights))
    family.need(all(type(w) is int and w > 0 for w in weights.values()),
                'positive integer weights')
    best, witness, checked = -1, None, 0
    for a, c, s, d in product(range(5), range(7), range(5), range(7)):
        base = 0
        pure, mixed = defaultdict(int), {}
        for (r, y), w in weights.items():
            load = 1+int(r == a)+int(y % 7 == c)+int(r == s and y % 7 == d)
            base += w*load*load
            gain = w*(2*load+1)
            pure[y] += gain
            mixed[r, y] = gain
        for u in range(49):
            gain, r, v = max((b+2*weights[r, v]*int(u == v), r, v)
                             for (r, v), b in mixed.items())
            value = base+pure[u]+gain
            if value > best:
                best = value
                witness = {1: 0, 5: a, 7: c, 35: d+7*((s-d)*3 % 5),
                           49: u, 245: v+49*((r-v)*4 % 5)}
        checked += 1
    family.need(witness is not None and checked == 1225, 'root coverage')
    literal = 0
    for (r, y), w in weights.items():
        x = y+49*((r-y)*4 % 5)
        literal += w*sum(int(x % modulus == a) for modulus, a in witness.items())**2
    family.need(literal == best, 'literal CRT attaining layout')
    return {'value': F(best, sum(weights.values())), 'numerator': best,
            'denominator': sum(weights.values()), 'layout': witness,
            'root_layouts': checked}


def same_component_counterexample():
    source, full, pairs = components(2)
    alpha = F(2150, 4013)
    nu = common_law(2, full, pairs, alpha)
    weights = {p: int(4013*w) for p, w in nu.items()}
    family.need(all(F(weights[p], 4013) == w for p, w in nu.items()), 'integer law')
    family.need(len(weights) == 42 and sum(weights.values()) == 4013, 'law size')
    family.need(set(weights) <= source and weights[2, 0] == 224, 'actual merged mass')
    family.need(all(w == (86 if r == 1 else 69 if r == 3 else 224 if y == 0 else 138)
                    for (r, y), w in weights.items()), 'explicit weight recipe')
    result = exact_height_two(weights)
    family.need(result['value'] == F(20475, 4013), 'independent original maximum')
    points = tuple(sorted(weights))
    independent = IndependentLayoutTreeDP(2, points).separate([weights[p] for p in points])
    family.need(independent['value'] == result['value'], 'existing independent-layout DP')
    target = layouts.default_target(2)
    family.need(target-result['value'] == F(323, 36117), 'actual strict target margin')
    cert = separated_bound(2, nu)
    family.need(cert >= certificate_minimum(2) > target, 'same-law certificate failure')
    return {'alpha': alpha, 'positive_points': len(weights), **result,
            'target_margin': target-result['value'], 'separated_certificate': cert}


def self_check():
    controls = [source_control(k) for k in (2, 3, 4)]
    result = same_component_counterexample()
    rejected = 0
    for operation in (lambda: components(1),
                      lambda: exact_height_two({(1, 49): 1}),
                      lambda: exact_height_two({(1, 0): F(1)})):
        try:
            operation()
        except (TypeError, ValueError):
            rejected += 1
        else:
            raise ValueError('malformed control accepted')
    family.need(rejected == 3, 'malformed controls')
    return {'scope': 'exact-root plus separate-depth certificate obstruction; ordinary proof, no Lean claim',
            'all_height_formula_controls': controls,
            'same_component_original_game_counterexample': result,
            'rejected_malformed_controls': rejected}


if __name__ == '__main__':
    print(json.dumps(family.jsonable(self_check()), sort_keys=True, indent=2))
