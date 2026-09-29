"""Exact counterexample to strictness for every law satisfying the old non-strict cylinder caps.

Source and law use the direct_child_tree_caps.py carrier (root, child, y),
where y=g+7*h is a literal residue modulo49. Importing performs no work.
A different law on this same source may satisfy a strictly better bound.
"""
import argparse
import json
from pathlib import Path

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product

NORMALIZER = 63
OLD_CAPS = {
    (0, 0): F(1), (1, 0): F(1, 3), (2, 0): F(1, 9),
    (0, 1): F(1, 3), (0, 2): F(1, 9),
    (1, 1): F(4, 21), (1, 2): F(4, 63),
    (2, 1): F(2, 21), (2, 2): F(2, 63),
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def saturation_source():
    """Return 121 sorted literal triples; occupancies (4,5,5,5), incidences (2,2,2,2)."""
    source = set()
    for c, columns in enumerate(({1, 6}, {1, 6}, {2, 3}, {4, 5}, set())):
        source.update((1, c, g + 7*h) for g in columns for h in range(5))
    for r in range(2, 5):
        for c in range(5):
            digits = {0, r-1} if c == 0 else range(5)
            source.update((r, c, c+1 + 7*h) for h in digits)
        source.update((r, 2, 2 + 7*h) for h in range(5))
    return sorted(source)


def saturation_integer_weights():
    """Return 39 positive integer weights on literal triples, summing to 63."""
    weights = defaultdict(int)

    def put(r, c, g, h, value):
        weights[(r, c, g + 7*h)] += value

    for c in (0, 1):
        for h in (0, 1, 2):
            put(1, c, 1, h, 2)
        put(1, c, 6, 0, 1)
    put(1, 2, 3, 0, 2)
    put(1, 2, 3, 1, 2)
    put(1, 3, 4, 0, 2)
    put(1, 3, 4, 1, 1)
    for r in range(2, 5):
        put(r, 0, 1, 0, 1)
        put(r, 0, 1, r-1, 2)
        for c, g, h in ((1, 2, 1), (2, 3, 2), (3, 4, 2)):
            put(r, c, g, 0, 1)
            put(r, c, g, h, 2)
        put(r, 4, 5, 0, 2)
    return dict(sorted(weights.items()))


def saturation_law():
    """Return the old saturating probability as dict[triple, Fraction]."""
    return {point: F(weight, NORMALIZER)
            for point, weight in saturation_integer_weights().items()}


def cylinder_maxima(law):
    """Compute all nine literal cylinder maxima for any height-(2,2) law."""
    result = {}
    for a, b in product(range(3), repeat=2):
        masses = defaultdict(F)
        for (r, c, y), mass in law.items():
            masses[((r + 5*c) % 5**a, y % 7**b)] += mass
        result[(a, b)] = max(masses.values(), default=F())
    return result


def centered_load_distribution(law, center=1):
    """Load distribution for all nine original labels phased at center."""
    distribution = defaultdict(F)
    for (r, c, y), mass in law.items():
        load = sum((r + 5*c - center) % 5**a == 0
                   and (y - center) % 7**b == 0
                   for a, b in product(range(3), repeat=2))
        distribution[load] += mass
    return dict(sorted(distribution.items()))


def controls():
    """Check source premises, global caps, all 81 pairs, and exact moment 9."""
    source = set(saturation_source())
    law = saturation_law()
    require(len(source) == 121 and len(law) == 39, 'source/law support sizes')
    require(sum(law.values(), F()) == 1 and set(law) <= source, 'supported probability')
    occupancy = [len({c for rr, c, y in source if rr == r}) for r in range(1, 5)]
    incidence = [max(len({c for rr, c, y in source if rr == r and y % 7 == g})
                     for g in range(7)) for r in range(1, 5)]
    require(occupancy == [4, 5, 5, 5] and incidence == [2]*4, 'occupancy/incidence')
    require({y for r, c, y in source} == {g + 7*h for g in range(1, 7) for h in range(5)},
            'exact standalone six-root five-ary projection')
    require(not any(r == 0 or y % 7 == 0 or (r, c) == (1, 4) or y == 37
                    for r, c, y in source), 'missing5/7/25/49 cells')
    triples = list(combinations(range(5), 3))

    def project(r, children):
        return {y for rr, c, y in source if rr == r and c in children}

    def blocks_seven_tree(leaves):
        return sum(sum(y % 7 == g for y in leaves) >= 3 for g in range(7)) >= 3

    require(all(blocks_seven_tree(project(r, cs) | project(s, ds))
                for r, s in combinations(range(1, 5), 2)
                for cs, ds in product(triples, repeat=2)), 'all600 pair/triple tests')
    robust = [all(blocks_seven_tree(project(r, cs)) for cs in triples)
              for r in range(1, 5)]
    require(robust == [False]*4, 'four nonrobust roots')
    maxima = cylinder_maxima(law)
    require(maxima == OLD_CAPS, 'all nine global caps attained')
    labels = list(product(range(3), repeat=2))
    for (a, b), (aa, bb) in product(labels, repeat=2):
        joint = sum((mass for (r, c, y), mass in law.items()
                     if (r + 5*c - 1) % 5**a == 0 and (y - 1) % 7**b == 0
                     and (r + 5*c - 1) % 5**aa == 0 and (y - 1) % 7**bb == 0), F())
        require(joint == OLD_CAPS[(max(a, aa), max(b, bb))], 'common-center pair equality')
    distribution = centered_load_distribution(law)
    require(distribution == {z: F(v, 63) for z, v in ((1, 33), (2, 14), (3, 4),
                                                    (4, 4), (6, 6), (9, 2))},
            'exact load distribution')
    moment = sum((z*z*mass for z, mass in distribution.items()), F())
    require(moment == 9, 'old law moment')
    return {'source_points': len(source), 'law_support': len(law),
            'occupancy': occupancy, 'incidence': incidence, 'robust_flags': robust,
            'pair_triple_checks': 600, 'original_ordered_pairs': 81,
            'all_nine_caps_exact': {str(k): str(v) for k, v in maxima.items()},
            'load_distribution': {z: str(v) for z, v in distribution.items()},
            'old_law_moment': str(moment),
            'seven_depth': 2, 'normalizer': NORMALIZER,
            'literal_source': [list(point) for point in sorted(source)],
            'literal_law': [{'point': list(point), 'mass': str(mass)}
                            for point, mass in sorted(law.items())],
            'scope': 'Old-law saturation; a different law on the same source may be strict.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Write the exact JSON control result to this file.')
    args = parser.parse_args()
    result = controls()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is not None:
        args.output.write_text(rendered, encoding='utf-8')
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
