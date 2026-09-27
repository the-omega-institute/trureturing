#!/usr/bin/env python3
"""Check a literal original-class obstruction to a universal low-excess law.

Only the two explicit --input/--output paths are read/written.  The input
contains numerical modulus/residue pairs, with no projected phase labels.
All substantive checks remain enabled under python -O.
"""

import argparse
import hashlib
import json
from fractions import Fraction
from itertools import product
from math import lcm, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def split_modulus(modulus):
    retained, outside, powers = 1, modulus, []
    for prime in (3, 5, 7):
        power = 1
        while outside % prime == 0:
            outside //= prime
            retained *= prime
            power *= prime
        if power != 1:
            powers.append((prime, power))
    return retained, outside, powers


def crt(residues, moduli):
    result, period = 0, 1
    for residue, modulus in zip(residues, moduli):
        result += period * (((residue - result) * pow(period, -1, modulus)) % modulus)
        period *= modulus
    return result


def evaluate(originals):
    require(len(originals) == 452, 'expected 452 complete original classes')
    require(len({m for m, _ in originals}) == len(originals), 'repeated numerical modulus')
    require(all(type(m) is int and type(a) is int and m > 1 and m % 2 == 1
                and 0 <= a < m for m, a in originals), 'illegal original class')
    primes = (11, 13, 17, 19)
    outside_period = prod(primes)
    outside_only, decoded, weights, cofactors = [], [], {}, {}
    for modulus, residue in originals:
        retained, outside, powers = split_modulus(modulus)
        if retained == 1:
            outside_only.append((outside, residue))
            continue
        require(residue % retained != 0, 'zero retained coordinate is covered')
        conditions = tuple((p, residue % p) for p in primes if outside % p == 0)
        require(prod(p for p, _ in conditions) == outside, 'outside cofactor is not squarefree in A')
        weight = prod((Fraction(p - 1, (p - 2) * power) for p, power in powers),
                      start=Fraction(1))
        weights[retained] = weight
        cofactors.setdefault(retained, set()).add(outside)
        decoded.append((retained, residue % retained, conditions))
    require(sorted(outside_only) == [(p, 0) for p in primes], 'outside-only originals differ')
    require(len(weights) == 28, 'expected 28 retained numerical rows')
    require(all(len(bs) == 16 and 1 in bs for bs in cofactors.values()), 'missing original cofactor')
    points = tuple(product(*(range(1, p) for p in primes)))
    require(len(points) == 34560, 'wrong complete outside survivor count')
    numeric_points = [crt(point, primes) for point in points]
    require(len(set(numeric_points)) == len(points), 'CRT is not injective on carrier')
    require(set(numeric_points) == {y for y in range(outside_period)
                                   if all(y % p != 0 for p in primes)}, 'incomplete outside carrier')
    coordinate_masks = {(p, a): 0 for p in primes for a in range(1, p)}
    for index, point in enumerate(points):
        bit = 1 << index
        for prime, residue in zip(primes, point):
            coordinate_masks[prime, residue] |= bit
    full = (1 << len(points)) - 1
    phase_masks = {}
    for retained, phase, conditions in decoded:
        mask = full
        for prime, residue in conditions:
            mask &= coordinate_masks.get((prime, residue), 0)
        key = retained, phase
        phase_masks[key] = phase_masks.get(key, 0) | mask
    require(all(phase_masks.get((d, 1)) == full for d in weights), 'missing permanent phase 1')
    denominator = lcm(*(weight.denominator for weight in weights.values()))
    integer_weights = {d: int(weight * denominator) for d, weight in weights.items()}
    loads = [0] * len(points)
    for (retained, phase), mask in phase_masks.items():
        if phase == 1:
            continue
        while mask:
            bit = mask & -mask
            loads[bit.bit_length() - 1] += integer_weights[retained]
            mask ^= bit
    by_numeric_point = sorted(zip(numeric_points, loads))
    minimum = min(loads)
    minimum_value = Fraction(minimum, denominator)
    minimizers = [y for y, load in by_numeric_point if load == minimum]
    require(minimum_value == Fraction(256, 735), 'different exact minimum')
    require(minimizers == [19802], 'different complete minimum set')
    require(3 * minimum > denominator, 'no pointwise obstruction to strict PE3 reverse')
    require(all(weight <= Fraction(16, 5 * d) for d, weight in weights.items()), 'weight comparison fails')
    retained_period = lcm(*weights)
    original_period = lcm(*(m for m, _ in originals))
    hole = crt((0, 1), (retained_period, outside_period))
    require(original_period == retained_period * outside_period, 'wrong full period')
    require(hole == 64366265250 and all(hole % m != a for m, a in originals), 'literal hole fails')
    result = {
        'status': 'PASS',
        'scope': 'A noncover refutes an unconditional low-excess supplier; Erdős #7 remains open.',
        'original_count': len(originals),
        'retained_count': len(weights),
        'retained_period': retained_period,
        'outside_period': outside_period,
        'outside_survivor_count': len(points),
        'original_period': original_period,
        'literal_integer_hole': hole,
        'weight_denominator': denominator,
        'minimum_numerator': minimum,
        'minimum_FS': str(minimum_value),
        'margin_above_one_third': str(minimum_value - Fraction(1, 3)),
        'minimum_survivors': minimizers,
        'pointwise_FH_lower_from_FS': str(Fraction(5, 16) * minimum_value),
        'margin_above_five_forty_eighths': str(Fraction(5, 16) * minimum_value - Fraction(5, 48)),
        'numeric_survivor_score_sha256': hashlib.sha256(
            json.dumps(by_numeric_point, separators=(',', ':')).encode()).hexdigest(),
    }
    return result, by_numeric_point


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(args.input.resolve() != args.output.resolve(), 'input and output must differ')
    raw_bytes = args.input.read_bytes()
    data = json.loads(raw_bytes)
    require(isinstance(data, dict) and set(data) == {'originals'}, 'unexpected input fields')
    require(all(isinstance(row, dict) and set(row) == {'modulus', 'residue'}
                for row in data['originals']), 'expected only numerical original pairs')
    originals = [(row['modulus'], row['residue']) for row in data['originals']]
    result, _ = evaluate(originals)
    result['input_sha256'] = hashlib.sha256(raw_bytes).hexdigest()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
