#!/usr/bin/env python3
"""Verify an irredundant, divisor-closed obstruction to low phase excess.

The input supplies only literal numerical moduli, residues, private integers
and one uncovered integer. No solver, projected labels or author helper is
used. Only the two explicit --input/--output paths are read or written.
All mathematical checks remain active under Python -O.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from math import isqrt, lcm, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def split_modulus(modulus):
    outside = modulus
    powers = []
    for prime in (3, 5, 7):
        power = 1
        while outside % prime == 0:
            outside //= prime
            power *= prime
        if power > 1:
            powers.append((prime, power))
    return modulus // outside, outside, powers


def nonunit_divisors(modulus):
    divisors = {modulus}
    for d in range(2, isqrt(modulus) + 1):
        if modulus % d == 0:
            divisors.add(d)
            divisors.add(modulus // d)
    return divisors


def evaluate(data):
    require(isinstance(data, dict) and set(data) == {'hole', 'originals'},
            'expected only the literal hole and original records')
    rows = data['originals']
    require(isinstance(rows, list) and len(rows) == 463, 'expected 463 originals')
    fields = {'modulus', 'residue', 'private_point'}
    require(all(isinstance(row, dict) and set(row) == fields for row in rows),
            'unexpected original fields')
    require(all(type(row[key]) is int for row in rows for key in fields),
            'original data must be integers')
    originals = [(row['modulus'], row['residue']) for row in rows]
    moduli = {m for m, _ in originals}
    require(len(moduli) == len(originals), 'duplicate numerical modulus')
    require(originals == sorted(originals), 'originals must be in numerical order')
    require(all(m > 1 and m % 2 == 1 and 0 <= a < m for m, a in originals),
            'illegal numerical class')
    period = lcm(*moduli)
    require(period == 481225870125, 'unexpected original period')
    require(all(nonunit_divisors(m) <= moduli for m in moduli),
            'numerical inventory is not nonunit-divisor-closed')
    primes = (3, 5, 7, 11, 13, 17, 19)
    residual = period
    for prime in primes:
        require((prime, 0) in originals, 'missing normalized original prime class')
        while residual % prime == 0:
            residual //= prime
    require(residual == 1, 'unexpected support prime')

    hole = data['hole']
    require(type(hole) is int and 0 <= hole < period, 'illegal literal hole')
    require(all(hole % m != a for m, a in originals), 'hole is covered')
    for row in rows:
        witness = row['private_point']
        require(0 <= witness < period, 'private integer outside period')
        hits = [m for m, a in originals if witness % m == a]
        require(hits == [row['modulus']], 'private integer does not have its unique owner')

    pair_count = 0
    for i, (m, a) in enumerate(originals):
        for n, b in originals[i + 1:]:
            pair_count += 1
            require(n % m != 0 or b % m != a, 'proper class containment')

    outside_only, decoded, weights = [], [], {}
    for m, a in originals:
        retained, outside, powers = split_modulus(m)
        if retained == 1:
            outside_only.append((outside, a))
            continue
        weights[retained] = prod(
            (Fraction(p - 1, (p - 2) * power) for p, power in powers),
            start=Fraction(1))
        decoded.append((retained, 1 << (a % retained), outside, a % outside))
    require(len(weights) == 28 and len(outside_only) == 15,
            'unexpected retained/outside inventories')
    retained_period = lcm(*weights)
    outside_period = lcm(*(b for _, _, b, _ in decoded), *(b for b, _ in outside_only))
    require(retained_period == 10418625 and outside_period == 46189,
            'unexpected original carriers')
    require(period == retained_period * outside_period, 'carriers do not give the original period')
    denominator = lcm(*(weight.denominator for weight in weights.values()), *weights)
    require(denominator == retained_period, 'unexpected common integer denominator')
    source_weights = {d: int(denominator * w) for d, w in weights.items()}
    haar_weights = {d: denominator // d for d in weights}
    scores = []
    min_source = min_haar = None
    source_minimizers, haar_minimizers = [], []
    for y in range(outside_period):
        if any(y % b == a for b, a in outside_only):
            continue
        phases = {d: 0 for d in weights}
        for d, phase_bit, b, a in decoded:
            if y % b == a:
                phases[d] |= phase_bit
        excess = {d: max(mask.bit_count() - 1, 0) for d, mask in phases.items()}
        source_score = sum(source_weights[d] * count for d, count in excess.items())
        haar_score = sum(haar_weights[d] * count for d, count in excess.items())
        scores.append((y, source_score, haar_score))
        if min_source is None or source_score < min_source:
            min_source, source_minimizers = source_score, [y]
        elif source_score == min_source:
            source_minimizers.append(y)
        if min_haar is None or haar_score < min_haar:
            min_haar, haar_minimizers = haar_score, [y]
        elif haar_score == min_haar:
            haar_minimizers.append(y)
    require(len(scores) == 33458, 'unexpected complete outside survivor count')
    source_min = Fraction(min_source, denominator)
    haar_min = Fraction(min_haar, denominator)
    require(source_min == Fraction(256, 735) and source_minimizers == [19802],
            'source-excess minimum differs')
    require(haar_min == Fraction(29222, 212625) and haar_minimizers == [25022],
            'Haar-excess minimum differs')
    require(source_min > Fraction(1, 3) and haar_min > Fraction(5, 48),
            'no universal strict low-excess obstruction')
    return {
        'status': 'PASS',
        'scope': 'An actual irredundant noncover with divisor-closed distinct odd numerical moduli refutes the two low-excess suppliers even under these structural restrictions. No unrestricted Erdos #7 or Lean conclusion.',
        'original_count': len(originals),
        'private_point_checks': len(rows),
        'private_point_original_incidence_checks': len(rows) * len(rows),
        'proper_containment_pair_checks': pair_count,
        'nonunit_divisor_closed': True,
        'normalized_original_primes': list(primes),
        'original_period': period,
        'literal_integer_hole': hole,
        'retained_moduli': sorted(weights),
        'retained_period': retained_period,
        'outside_period': outside_period,
        'outside_only_originals': [{'modulus': m, 'residue': a} for m, a in outside_only],
        'outside_survivor_count': len(scores),
        'integer_weight_denominator': denominator,
        'minimum_FS': str(source_min),
        'minimum_FS_survivors': source_minimizers,
        'minimum_FH': str(haar_min),
        'minimum_FH_survivors': haar_minimizers,
        'margin_FS_over_one_third': str(source_min - Fraction(1, 3)),
        'margin_FH_over_five_forty_eighths': str(haar_min - Fraction(5, 48)),
        'complete_outside_score_sha256': hashlib.sha256(
            json.dumps(scores, separators=(',', ':')).encode()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(args.input.resolve() != args.output.resolve(), 'input and output must differ')
    raw = args.input.read_bytes()
    result = evaluate(json.loads(raw))
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
