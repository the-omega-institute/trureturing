"""Exact stationary first-nonzero-digit phase-sharing boundaries.

The 1190 bound concerns the reduced nozero digit cube. Unrestricted old
stationary patterns attain 1185 and the all-height limit 79/99. This does
not decide the joint J target. All inputs are embedded; checks survive -O.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


PRIMES = (5, 7, 11, 13)
AXES = {mask: tuple(i for i in range(4) if mask >> i & 1)
        for mask in range(1, 16)}
REDUCED_PATTERNS = {
    3: (3, 3), 5: (4, 3), 6: (4, 4), 7: (3, 4, 6),
    9: (4, 3), 10: (5, 4), 11: (3, 5, 6), 12: (5, 5),
    13: (4, 6, 6), 14: (6, 4, 4), 15: (3, 6, 6, 6),
}
UNRESTRICTED_PATTERNS = {
    3: (2, 2), 5: (3, 2), 6: (3, 3), 7: (2, 3, 5),
    9: (4, 2), 10: (4, 3), 11: (2, 4, 5), 12: (4, 4),
    13: (3, 5, 5), 14: (5, 3, 3), 15: (4, 6, 6, 6),
}
EXPECTED_COEFFICIENTS = {
    'reduced': [1190, 469, 274, 98, 145, 54, 32, 11,
                117, 44, 26, 9, 14, 5, 3, 1],
    'unrestricted': [1185, 469, 273, 98, 145, 54, 32, 11,
                     117, 44, 26, 9, 14, 5, 3, 1],
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pattern_hits(word, mask, digits):
    return tuple(word[i] for i in AXES[mask]) == digits


def graph_charge_control():
    edges = list(combinations(range(4), 2))
    matchings = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    for mask in range(64):
        graph = {edge for i, edge in enumerate(edges) if mask >> i & 1}
        charge = sum(a in graph and b in graph for a, b in matchings)
        charge += int((0, 1) in graph and (0, 2) in graph)
        require(max(len(graph) - 1, 0) >= charge, 'four-vertex overlap charge')
    return 64


def coefficient_control(patterns):
    require(set(patterns) == {m for m in AXES if len(AXES[m]) >= 2},
            'one mixed pattern for every support')
    for mask, digits in patterns.items():
        require(len(digits) == len(AXES[mask]) and
                all(2 <= digit < PRIMES[i] for i, digit in zip(AXES[mask], digits)),
                'pure-old-surviving nonzero digits')
    coefficients = [0] * 16
    for word in product(*[(0,) + tuple(range(2, q)) for q in PRIMES]):
        if any(pattern_hits(word, mask, digits) for mask, digits in patterns.items()):
            continue
        zero_mask = sum(1 << i for i, digit in enumerate(word) if digit == 0)
        coefficients[zero_mask] += 1
    remaining = set(product(*(range(2, q) for q in PRIMES)))
    additions = {}
    for size in (2, 3, 4):
        removed = {word for word in remaining
                   if any(len(AXES[mask]) == size and pattern_hits(word, mask, digits)
                          for mask, digits in patterns.items())}
        additions[str(size)] = len(removed)
        remaining -= removed
    require(len(remaining) == coefficients[0], 'nozero count agrees with coefficients')
    return coefficients, additions


def finite_counts(coefficients, heights):
    require(len(heights) == 4 and all(h >= 1 for h in heights), 'positive finite heights')
    weights = [(q**h - 1) // (q - 1) for q, h in zip(PRIMES, heights)]
    survivors = sum(count * prod(weights[i] for i in range(4) if not (mask >> i & 1))
                    for mask, count in enumerate(coefficients))
    pure_survivors = prod(1 + (q - 2)*w for q, w in zip(PRIMES, weights))
    return dict(heights=heights, complete_core_period=prod(q**h for q, h in zip(PRIMES, heights)),
                original_moduli=prod(h + 1 for h in heights) - 1,
                nonzero_digit_weights=weights, survivor_count=survivors,
                pure_survivor_count=pure_survivors,
                conditional_survival=F(survivors, pure_survivors),
                below_1190_over_1485=F(survivors, pure_survivors) < F(1190, 1485))


def literal_family(patterns, heights):
    originals = []
    for exponents in product(*(range(h + 1) for h in heights)):
        mask = sum(1 << i for i, exponent in enumerate(exponents) if exponent)
        if not mask:
            continue
        digits = (1,) if len(AXES[mask]) == 1 else patterns[mask]
        pairs = [(PRIMES[i]**exponents[i], digit*PRIMES[i]**(exponents[i] - 1))
                 for i, digit in zip(AXES[mask], digits)]
        modulus = prod(m for m, _ in pairs)
        residue = sum(a*(modulus // m)*pow(modulus // m, -1, m) for m, a in pairs) % modulus
        require(all(residue % m == a for m, a in pairs), 'literal CRT residue')
        originals.append((modulus, residue))
    require(len(originals) == len({m for m, _ in originals}) == prod(h + 1 for h in heights) - 1,
            'one original for each nonunit divisor')
    require(all(m > 1 and m % 2 and 0 <= a < m for m, a in originals), 'distinct odd nonunit originals')
    return originals


def literal_height_one_control(patterns, coefficients):
    heights = (1, 1, 1, 1)
    originals = literal_family(patterns, heights)
    period = prod(PRIMES)
    survivor_count = pure_count = 0
    for integer in range(period):
        digits = tuple(integer % q for q in PRIMES)
        pure_survival = all(digit != 1 for digit in digits)
        symbolic_survival = pure_survival and not any(
            pattern_hits(digits, mask, word) for mask, word in patterns.items())
        actual_survival = not any(integer % m == a for m, a in originals)
        require(actual_survival == symbolic_survival, 'literal originals agree with digit partition')
        survivor_count += actual_survival
        pure_count += pure_survival
    expected = finite_counts(coefficients, heights)
    require(survivor_count == expected['survivor_count'] and pure_count == expected['pure_survivor_count'],
            'literal counts agree with the weighted polynomial')
    return dict(height=1, original_moduli=originals, literal_residue_checks=period,
                survivor_count=survivor_count, pure_survivor_count=pure_count)


def control():
    require(prod(q - 2 for q in PRIMES) == 1485, 'nozero cube size')
    pair_area = sum(prod(PRIMES[i] - 2 for i in range(4) if i not in support)
                    for support in combinations(range(4), 2))
    triple_area = sum(q - 2 for q in PRIMES)
    require(pair_area == 274 and triple_area == 28, 'original support cylinder sizes')
    families = {}
    for name, patterns in (('reduced', REDUCED_PATTERNS), ('unrestricted', UNRESTRICTED_PATTERNS)):
        coefficients, additions = coefficient_control(patterns)
        require(coefficients == EXPECTED_COEFFICIENTS[name], 'exact zero-mask coefficients')
        require(additions == {'2': 266 if name == 'reduced' else 271, '3': 28, '4': 1},
                'attaining pair, triple and quadruple contributions')
        if name == 'reduced':
            require(all(digit >= 3 for digits in patterns.values() for digit in digits),
                    'reduced patterns contain no new-pure digit 2')
        finite = [finite_counts(coefficients, (h,)*4) for h in (1, 2, 3, 4)]
        families[name] = dict(mixed_patterns=[dict(mask=mask, digits=digits) for mask, digits in sorted(patterns.items())],
                              nozero_survivors=coefficients[0], union_additions_by_support_size=additions,
                              zero_mask_coefficients=coefficients, finite_heights=finite,
                              literal_height_one=literal_height_one_control(patterns, coefficients))
    height_three = families['unrestricted']['finite_heights'][2]
    require(height_three['survivor_count'] == 51897928602 and
            height_three['pure_survivor_count'] == 64864962448 and
            height_three['conditional_survival'] == F(1996074177, 2494806248) and
            height_three['below_1190_over_1485'], 'finite-height obstruction to an unrestricted 1190 bound')
    require(F(1185, 1485) == F(79, 99), 'attained all-height limiting bound')
    return dict(schema='erdos7-stationary-phase-sharing-boundary-v1', primes=PRIMES,
                pure_old_digit=1, normalized_new_pure_digit=2,
                scope='1190 is sharp on the reduced nozero digit cube; unrestricted stationary old phases attain 1185 and limiting conditional survival 79/99. The universal J target remains unsettled.',
                joint_reduction_threshold='c < 2; preserve the sign of sum w(x)(g(x)+1_(g(x)>0)-c)',
                nozero_cells=1485, pair_area_sum=pair_area, triple_area_sum=triple_area,
                quadruple_area=1, reduced_overlap_credit=8, unrestricted_overlap_credit=3,
                four_vertex_graph_checks=graph_charge_control(),
                families=families, literal_residue_checks_total=2*prod(PRIMES),
                attained_unrestricted_limit=F(79, 99))


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(encode(control()), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
