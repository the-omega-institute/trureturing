#!/usr/bin/env python3
"""Small actual-source controls, not a query optimizer or research candidate."""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import json
from pathlib import Path

DEFAULT_RESULT = Path(__file__).resolve().with_suffix('.json')


def run():
    checks = 0

    def check(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(message)

    leaves = (4, 7, 2, 5, 8)
    numerators = ((4, 1, 2), (1, 4, 0), (2, 0, 4), (0, 2, 3), (3, 1, 1))
    u = tuple(tuple(F(x, 20) for x in row) for row in numerators)
    allowed5 = tuple(y for y in range(25) if y % 5 != 2 and y != 8)
    check(len(allowed5) == 19, 'actual pure source count')
    delta, a = F(25, 19), F(5, 19)
    pi = (a, a, 1 - 2 * a)
    roots = (0, 1, 4)
    labels = (1, 3, 5, 9, 15, 25, 45, 75, 225)

    def colour(y):
        z = y % 5
        return z if z <= 1 else 2

    def prime_part(n, p):
        z = 1
        while n % p == 0:
            z *= p
            n //= p
        return z

    def crt_pair(res3, modulus3, res5, modulus5):
        # Tiny literal CRT reconstruction; no symbolic query optimization.
        hits = [x for x in range(modulus3 * modulus5)
                if x % modulus3 == res3 and x % modulus5 == res5]
        check(len(hits) == 1, 'CRT reconstruction uniqueness')
        return hits[0]

    carrier = [(crt_pair(l, 9, y, 25), l, y,
                u[li][colour(y)] / 19)
               for li, l in enumerate(leaves) for y in allowed5]
    mass = sum((row[3] for row in carrier), F(0))
    check(all(0 <= v <= F(1, 5) for row in u for v in row), 'dominated table')
    check(mass > 0, 'positive fixed-source retained mass')
    for c, root in enumerate(roots):
        check(all(y in allowed5 for y in range(root, 25, 5)), 'whole clean root')
        check(F(sum(colour(y) == c for y in allowed5), 19) == pi[c], 'colour marginal')

    bins = []
    for c in range(3):
        for r, prob in enumerate((pi[c] - a, a * F(4, 5), a * F(1, 5))):
            check(prob >= 0, 'nonnegative run bin')
            if prob:
                bins.append((c, r, prob))
        check((pi[c] - a) + a * F(4, 5) + a * F(1, 5) == pi[c], 'run bin normalization')
    check(len(bins) == 7, 'E2 ambient local bins')
    for c, r, prob in bins:
        def run_depth(y):
            return 0 if y % 5 != roots[c] else (2 if y == roots[c] else 1)
        literal_prob = F(sum(colour(y) == c and run_depth(y) == r for y in allowed5), 19)
        check(prob == literal_prob, 'actual law equals compressed bin law')

    # Prescribed examples include dead pure roots, damaged roots, live roots,
    # and independently chosen phases. There is no maximization over layouts.
    layouts = [tuple(t % n for n in labels) for t in (0, 2, 4, 8, 13, 24)]
    layouts += [tuple((seed * (i + 1) ** 2 + 7 * i + 3) % n
                     for i, n in enumerate(labels)) for seed in (1, 2, 3, 5, 8, 13)]

    def relocate_q(layout):
        moved = []
        for n, residue in zip(labels, layout):
            m3, m5 = prime_part(n, 3), prime_part(n, 5)
            replacement5 = roots[colour(residue)] if m5 > 1 else 0
            new = crt_pair(residue % m3, m3, replacement5, m5)
            if m5 > 1:
                check(colour(new) == colour(residue), 'label colour preserved')
            check(new % m3 == residue % m3, 'other phase preserved')
            moved.append(new)
        return tuple(moved)

    def literal_histogram(layout):
        hist = defaultdict(F)
        for x, _, _, weight in carrier:
            load = sum(x % n == residue for n, residue in zip(labels, layout))
            hist[load] += weight
        return {k: v for k, v in hist.items() if v}

    def compressed_histogram(layout):
        hist = defaultdict(F)
        for li, l in enumerate(leaves):
            for c, r, prob in bins:
                load = 0
                for n, residue in zip(labels, layout):
                    m3, m5 = prime_part(n, 3), prime_part(n, 5)
                    ternary_hit = l % m3 == residue % m3
                    e5 = 0 if m5 == 1 else (1 if m5 == 5 else 2)
                    prime5_hit = e5 == 0 or (colour(residue) == c and e5 <= r)
                    load += ternary_hit and prime5_hit
                hist[load] += u[li][c] * prob
        return {k: v for k, v in hist.items() if v}

    def moment(hist, cost):
        return sum((weight * cost(load) for load, weight in hist.items()), F(0))

    rows = []
    for index, layout in enumerate(layouts):
        moved = relocate_q(layout)
        before = literal_histogram(layout)
        after = literal_histogram(moved)
        compressed = compressed_histogram(moved)
        check(after == compressed, 'entire load law equals compressed integration')
        check(sum(before.values(), F(0)) == mass, 'old common-source mass')
        check(sum(after.values(), F(0)) == mass, 'new common-source mass')
        gaps = []
        for h in range(10):
            gap = moment(after, lambda t: max(t - h, 0)) - moment(before, lambda t: max(t - h, 0))
            check(gap >= 0, 'same-colour clean move hinge domination')
            gaps.append(str(gap))
        gap4 = moment(after, lambda t: t ** 4) - moment(before, lambda t: t ** 4)
        check(gap4 >= 0, 'same-colour clean move fourth-moment domination')
        rows.append({
            'index': index,
            'literal_phases': list(layout),
            'same_colour_clean_phases': list(moved),
            'hinge_nonnegative_gaps_h0_through9': gaps,
            'fourth_moment_nonnegative_gap': str(gap4),
            'compressed_load_law': [[k, str(v)] for k, v in sorted(compressed.items())],
        })
    check(any(F(g) > 0 for row in rows for g in row['hinge_nonnegative_gaps_h0_through9']),
          'nonvacuous strict finite control')
    # The depth-four actual family from826 and one new mixed original.
    # This is a restriction counterexample, not a research query evaluation.
    Q = (5, 7, 11, 13, 17, 19, 23)
    originals = [
        (3, 0), (9, 1), (15, 10), (21, 7), (45, 31),
        (33, 22), (35, 0), (39, 13), (63, 49), (51, 34),
        (57, 19), (55, 0), (105, 70), (75, 25), (69, 46),
        (65, 0), (99, 22), (77, 0), (85, 0), (117, 13),
        (95, 0), (165, 55), (91, 0), (147, 49), (225, 175),
    ]
    pure = {}
    for q in Q:
        first, spine = (2, 3) if q == 5 else (1, 2)
        pure[q] = [(q, first)] + [(q ** j, spine + q ** (j - 1)) for j in (2, 3, 4)]
    family = originals + [item for q in Q for item in pure[q]]
    check(len(family) == len({m for m, _ in family}) == 53, 'actual family numerical distinctness')
    check(375 not in {m for m, _ in family}, 'additional numerical label distinct')
    # Slice: leaf2, 5-colour{0}, nonzero colour at all remaining primes.
    # For each anchor/mixed original one of these observed coordinates
    # certifies avoidance. Pure constraints remain in the actual local laws.
    for m, residue in originals:
        m3 = prime_part(m, 3)
        excluded = (m3 <= 9 and 2 % m3 != residue % m3)
        excluded |= (m % 5 == 0 and residue % 5 != 0)
        excluded |= any(m % q == 0 and residue % q == 0 for q in Q if q > 5)
        check(excluded, 'retained categorical slice avoids every anchor/mixed original')
    for q in Q[1:]:
        pure_mass = 1 - sum((F(1, m) for m, _ in pure[q]), F(0))
        check(pure_mass > 0 and 1 - F(1, q) / pure_mass > 0,
              'common nonzero-colour factor is positive')
    actual5 = [y for y in range(625) if all(y % m != residue for m, residue in pure[5])]
    check(len(actual5) == 469, 'actual depth4 pure survivor count')
    retained5 = [y for y in actual5 if y % 5 == 0]
    # On leaf2, the new original125mod375 removes exactly0mod125.
    restricted5 = [y for y in retained5 if y % 125 != 0]
    before5 = [y for y in restricted5 if y % 125 == 25]
    after5 = [y for y in restricted5 if y % 125 == 0]
    check(275 % 3 == 125 % 3 == 2, 'literal query ternary projection unchanged')
    check(275 % 125 == 25 and 125 % 125 == 0, 'literal query depth3 projections')
    check(25 % 5 == 0 and 0 % 5 == 0, 'restriction counterexample keeps colour')
    restricted_mass = F(len(restricted5), 469)
    before_mass, after_mass = F(len(before5), 469), F(len(after5), 469)
    check(restricted_mass == F(120, 469), 'one fixed restricted normalization')
    check(before_mass == F(5, 469) and after_mass == 0, 'same-source actual restriction failure')
    before_normalized, after_normalized = before_mass / restricted_mass, after_mass / restricted_mass
    check(before_normalized == F(1, 24) and after_normalized == 0, 'normalized1over24to0')
    restriction_counterexample = {
        'original_family': [[m, residue] for m, residue in family],
        'ternary_weights_on_declared_five_leaves': ['0', '0', '1', '0', '0'],
        'retained_slice': {'ternary_leaf_mod9': 2, 'prime5_colour': [0], 'other_prime_colours': 'nonzero'},
        'retained_table': 'indicator of this categorical slice',
        'additional_original': [375, 125],
        'query_before': [375, 275],
        'query_after_same_colour_clean_move': [375, 125],
        'actual_prime5_survivor_count_mod625': len(actual5),
        'restricted_prime5_support_count': len(restricted5),
        'before_hit_count': len(before5),
        'after_hit_count': len(after5),
        'common_positive_factor': 'product of the unchanged other-prime nonzero-colour probabilities',
        'restricted_mass_without_common_factor': str(restricted_mass),
        'query_before_mass_without_common_factor': str(before_mass),
        'query_after_mass_without_common_factor': str(after_mass),
        'normalized_query_before': str(before_normalized),
        'normalized_query_after': str(after_normalized),
        'boundary': 'arbitrary additional deep originals need a new restricted-density or clean-path premise',
    }
    return {
        'schema': 'e7-clean-root-phase-compression-v1',
        'scope': '12 prescribed layouts on one fixed actual two-axis source and one actual53-original restriction counterexample; no research-candidate evaluation or optimization',
        'pure5_originals': [[5, 2], [25, 8]],
        'ternary_leaves_mod9': list(leaves),
        'retained_table_numerators_over20': [list(row) for row in numerators],
        'actual_source_points_before_zero_table': len(carrier),
        'ambient_compressed_states_before_zero_table': len(leaves) * len(bins),
        'mass': str(mass),
        'delta5': str(delta),
        'a5': str(a),
        'pi5': [str(p) for p in pi],
        'labels': list(labels),
        'layout_controls': rows,
        'restriction_counterexample': restriction_counterexample,
        'checks': checks,
        'not_claimed': ['all-layout proof from finite samples', 'a bound for the827 coherent hinge', 'prefix maximum', 'positive E7 gate', 'Lean verification'],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--result', '--compare', type=Path, default=DEFAULT_RESULT)
    parser.add_argument('--write-result', action='store_true')
    args = parser.parse_args()
    result = run()
    if args.write_result:
        args.result.write_text(json.dumps(result, indent=2) + '\n')
    elif json.loads(args.result.read_text()) != result:
        raise ValueError('saved phase-compression result mismatch')
    print(json.dumps({'status': 'tiny exact controls passed', 'checks': result['checks']}))


if __name__ == '__main__':
    main()
