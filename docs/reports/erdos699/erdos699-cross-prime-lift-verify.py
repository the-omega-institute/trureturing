#!/usr/bin/env python3
"""Verify the entire conditional 11/23 periodic exclusion certificate.

Domain reconstruction and arithmetic are independent of the producer.
Verification establishes the periodic square obstruction under the
mathematical interface in theory sections 43--46. The implication from
the original predicate to that interface remains ASSUMED-UNVERIFIED.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def coprime(a: int, b: int) -> bool:
    while b:
        a, b = b, a % b
    return a == 1


def is_prime(q: int) -> bool:
    if q < 2:
        return False
    divisor = 2
    while divisor * divisor <= q:
        if q % divisor == 0:
            return False
        divisor += 1
    return True


def unique_object(pairs: list) -> dict:
    result = {}
    for key, value in pairs:
        check(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def verify(data: dict) -> dict:
    check(type(data) is dict, 'certificate must be an object')
    check(set(data) == {'schema_version', 'period', 'class_modulus',
                       'square_expression', 'witness_primes', 'domains', 'total', 'rows'},
          'unexpected certificate metadata')
    for key, expected in (('schema_version', 1), ('period', 27720),
                          ('class_modulus', 110), ('total', 8064)):
        check(type(data[key]) is int and data[key] == expected, f'invalid {key}')
    check(data['square_expression'] == '1+4*x*(c*2^N-1)*(c*2^N-2)/D',
          'incorrect square expression')
    primes = [5, 7, 13, 17, 19, 29, 31, 37, 41, 43, 61, 67, 71, 73,
              109, 113, 181, 199, 241, 353, 397, 463]
    check(type(data['witness_primes']) is list and
          all(type(q) is int for q in data['witness_primes']) and
          data['witness_primes'] == primes, 'incorrect witness prime set')
    squares = {}
    for q in primes:
        check(is_prime(q), 'composite witness modulus')
        check(pow(2, 27720, q) == 1, 'invalid exponent period')
        squares[q] = {pow(t, 2, q) for t in range(q)}

    # Reconstruct the reversed orientation from c and the permitted 3 factor.
    # Test every N and x in the interval rather than using a producer stream.
    specifications = []
    for c in (1, 3):
        for D in ((11, 33) if c == 1 else (11,)):
            numerators = [x for x in range(1, D) if 4*x > D and coprime(x, D)]
            specifications.append((c, D, 11 if c == 1 else 3, numerators))
    # With neither endpoint at n-2, x=1 forces N=55; x=2 forces N=77.
    for x in (1, 2):
        specifications.append((1, 3, 55 if x == 1 else 77, [x]))

    reconstructed = {}
    metadata = []
    domain_counts = []
    for case_id, (c, D, r, numerators) in enumerate(specifications):
        count = 0
        for N in range(27720):
            if N % 110 != r:
                continue
            for x in numerators:
                reconstructed[(case_id, N, x)] = (c, D)
                count += 1
        domain_counts.append(count)
        metadata.append({'case_id': case_id, 'c': c, 'D': D, 'N_mod110': r,
                         'numerators': numerators, 'count': count})
    check(domain_counts == [2016, 3528, 2016, 252, 252] and
          len(reconstructed) == 8064, 'domain reconstruction failed')
    check(type(data['domains']) is list and len(data['domains']) == 5,
          'invalid domain metadata length')
    for provided, expected in zip(data['domains'], metadata):
        check(type(provided) is dict and set(provided) == set(expected),
              'unexpected domain fields')
        check(all(type(provided[k]) is int for k in expected if k != 'numerators'),
              'noninteger domain metadata')
        check(type(provided['numerators']) is list and
              all(type(x) is int for x in provided['numerators']),
              'noninteger numerator metadata')
        check(provided == expected, 'incorrect mathematical domain metadata')

    check(type(data['rows']) is list and len(data['rows']) == len(reconstructed),
          'missing or extra certificate rows')
    seen = set()
    counts = [0] * 5
    for row in data['rows']:
        check(type(row) is dict and set(row) == {'case_id', 'N', 'x', 'q', 'residue'},
              'unexpected witness row fields')
        check(all(type(value) is int for value in row.values()), 'noninteger witness row')
        key = (row['case_id'], row['N'], row['x'])
        check(key in reconstructed, 'extra domain tuple')
        check(key not in seen, 'duplicate domain tuple')
        seen.add(key)
        c, D = reconstructed[key]
        q = row['q']
        check(q in squares and is_prime(q), 'invalid witness prime')
        check(coprime(D, q) and pow(2, 27720, q) == 1,
              'invalid witness coprimality or period')
        n = c * pow(2, row['N'], q)
        inverse = pow(D, q-2, q)
        check(D * inverse % q == 1, 'modular inverse failed')
        value = (D + 4 * row['x'] * (n-1) * (n-2)) * inverse % q
        check(0 <= row['residue'] < q and row['residue'] == value,
              'incorrect witness residue')
        check(value not in squares[q], 'witness is a quadratic residue')
        counts[row['case_id']] += 1
    check(seen == set(reconstructed), 'incomplete domain coverage')
    check(counts == domain_counts, 'incorrect verified domain counts')
    return {'verified_rows': len(seen), 'domain_counts': counts, 'period': 27720,
            'witness_prime_count': len(primes),
            'scope': 'conditional periodic square obstruction; original-to-interface bridge unverified'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).with_name('erdos699-cross-prime-lift-certificate.json'))
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text(encoding='utf-8'), object_pairs_hook=unique_object)
    print(json.dumps(verify(data), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
