#!/usr/bin/env python3
"""Exact finite-Q consumer of pinned fixed-period, common-law core seeds.

No source producer, geometry enumeration, third-party module, or Lean checker
is run. All checks remain active under -O. The extension and analytic-tail
proofs, including their inherited source premises, are ordinary mathematics.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial, isqrt, prod
from pathlib import Path

QUERY_SHA = '44f871684942eb7dceb37c55880c9f9a49244d8bdd60134670ad80d10a3c587d'
SEVEN_SHA = '2ff88432077332183296e76c9119791e6fa6e05cbf8476454489069c249f2e63'
FIRST = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)


def need(ok, why):
    if not ok:
        raise ValueError(why)


def read_pinned(path, digest):
    raw = path.read_bytes()
    need(sha256(raw).hexdigest() == digest, str(path) + ': SHA256 mismatch')
    return json.loads(raw)


def extension(A, density, primes, pure_mode='arbitrary'):
    need(primes == tuple(sorted(set(primes))), 'distinct increasing new primes')
    need(all(q > 2 and all(q % d for d in range(2, isqrt(q) + 1))
             for q in primes), 'odd primes')
    need(pure_mode in ('arbitrary', 'absent'), 'pure mode')
    a = [F(q - 2, q - 1) if pure_mode == 'arbitrary' else F(1) for q in primes]
    b = [1 / ((q - 1) * aq) for q, aq in zip(primes, a)]
    P = prod((1 + x for x in b), start=F(1))
    S = sum(b, F(0))
    mass = A + 2 + S - (A + 1) * P
    # Independent subset grouping retains every d=1 multi-prime class.
    grouped = F(0)
    for mask in range(1, 1 << len(primes)):
        terms = [b[i] for i in range(len(b)) if mask & (1 << i)]
        grouped += (A if len(terms) == 1 else A + 1) * prod(terms)
    need(1 - grouped == mass, 'complete exponent-support grouping')
    haar = mass * prod(a, start=F(1)) / density
    if pure_mode == 'arbitrary':
        need(prod(a, start=F(1)) * P == 1, 'worst-pure mass-density identity')
        need(haar == mass / (density * P), 'same-seed Haar conversion')
    return {'new_primes': primes, 'pure_mode': pure_mode, 'P': P, 'S': S,
            'mass_lower_expression': mass, 'Haar_lower_expression': haar,
            'criterion_positive': mass > 0}


def encoded(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encoded(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encoded(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--query-seed', type=Path, required=True)
    parser.add_argument('--seven-seed', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    query = read_pinned(args.query_seed, QUERY_SHA)
    seven = read_pinned(args.seven_seed, SEVEN_SHA)
    need('One law serves all its query phases' in query['scope'], 'query one-law scope')
    need('One law serves all layouts at a fixed finite period.' in seven['scope'],
         'seven-core one-law scope')
    seeds = {row['core_count']: (F(row['nonunit_layout_bound']),
                               F(row['normalized_Haar_density_cap']))
             for row in query['summaries'] if row['core_count'] in (5, 6)}
    seeds[7] = (F(seven['seven_core_query_R_upper']), F(seven['normalized_density_cap']))
    need(set(seeds) == {5, 6, 7}, 'required seed core sizes')
    need(seeds[5] == (F(354268696184847779107405, 37639127656852367739093),
                     F(84375000000, 1812390307)), 'five-core constants')
    need(seeds[6] == (F(8034293665870716452955503975561029997134562974,
                       581858869356700257567944700688463416886232987),
                     F(10125000000000, 68006602781)), 'six-core constants')
    need(seeds[7] == (F(70874, 3375), F(455625)), 'seven-core constants')

    B, ell = 1000000, 12
    need(B >= 286 and ell >= 4 and 3**ell <= B, 'Chapter33 applicability')
    c = F(2 * ell**2 + 1, 2 * ell**2 - 1)
    need(c == F(289, 287), 'Chapter33 product constant')
    series = sum((F(factorial(7), factorial(7 - j) * ell**j) for j in range(8)), F(0))
    tau = c**7 / B * F(B, B - 3)**2 * series
    settings = (
        (5, (43, 47, 53, 59, 61), F(1, 6000), F(1, 10000),
         F(1446009325937, 74029529600), F(35015347, 3685915), F(19, 2),
         F(758925898988086401704759981, 4254306957863460122625000000000)),
        (6, (53, 59, 61, 67), F(1, 12000), F(1, 100000),
         F(16830979471677, 788155596800), F(1236442, 88335), F(14),
         F(20780797372750944435897944289447648087106979923,
           245640385728810904867359431593980664170000000000000)),
    )
    positives = []
    for k, new, simple_head, simple_live, expected_M2, expected_critical, rounded_A, expected_haar in settings:
        A, density = seeds[k]
        row = extension(A, density, new)
        head = FIRST[:k] + new
        need(len(head) == len(set(head)) == 10, 'ten distinct head primes')
        haar = row['Haar_lower_expression']
        need(row['criterion_positive'] and haar == expected_haar and haar > simple_head,
             'exact and rounded ten-prime Haar lower bounds')
        critical = (1 + row['S']) / (row['P'] - 1) - 1
        need(critical == expected_critical and A < critical < rounded_A,
             'critical query constant and unsafe rounding')
        rounded = extension(rounded_A, density, new)['mass_lower_expression']
        need(rounded < 0, 'rounding query bound loses positive mass')
        M2 = prod(F(p * (p + 1), (p - 1)**2) for p in head)
        need(M2 == expected_M2, 'ten-prime Haar moment product')
        loss = M2 * tau
        need(haar - loss > simple_live and simple_head - loss > simple_live,
             'Chapter33 positive margin, including rounded head mass')
        row.update({'core_count': k, 'reference_head_primes': head,
                    'strict_simple_head_Haar_lower': simple_head, 'critical_query_A': critical,
                    'unsafe_rounded_query_A': rounded_A, 'unsafe_rounded_mass_expression': rounded,
                    'M2': M2, 'tail_loss_upper': loss, 'exact_remaining_live_mass_lower': haar - loss,
                    'rounded_head_remaining_live_mass_lower': simple_head - loss,
                    'strict_simple_remaining_live_mass_lower': simple_live})
        positives.append(row)

    controls = []
    supports = ((FIRST[:5] + (43, 47, 53, 59, 61), (5,)),
                (FIRST[:6] + (53, 59, 61, 67), (6,)),
                (FIRST[:5] + (37, 41, 43, 47), (5, 7)))
    for support, successful in supports:
        rows = []
        for k, (A, density) in seeds.items():
            row = extension(A, density, support[k:])
            need(row['criterion_positive'] == (k in successful), 'contrasting split sign')
            rows.append({'core_count': k, 'mass_lower_expression': row['mass_lower_expression'],
                         'Haar_lower_expression': row['Haar_lower_expression']})
        controls.append({'support': support, 'splits': rows})

    small_supports = []
    for n in (9, 10):
        rows = []
        for mode in ('arbitrary', 'absent'):
            for k, (A, density) in seeds.items():
                mass = extension(A, density, FIRST[k:n], mode)['mass_lower_expression']
                need(mass < 0, 'first-prime support remains outside sufficient criterion')
                rows.append({'core_count': k, 'pure_mode': mode, 'mass_lower_expression': mass})
        small_supports.append({'support': FIRST[:n], 'splits': rows})

    result = {
        'scope': 'Exact finite arithmetic consumer of fixed-period common-law seeds. Generic extension, prime transport, and Chapter33 tail proofs retain their attributed source premises; no source rerun or new Lean certification.',
        'input_sha256': {'query_stoploss_completion.json': QUERY_SHA,
                         'seven_core_last_stage_bridge.json': SEVEN_SHA},
        'seeds': {k: {'query_A': A, 'normalized_Haar_density_cap': d} for k, (A, d) in seeds.items()},
        'formulas': {'general': 'b_q=1/((q-1)*a_q); P=product(1+b_q); S=sum(b_q); m=A+2+S-(A+1)*P; Haar_lower=m*product(a_q)/density',
                     'arbitrary_pure': 'a_q=(q-2)/(q-1); b_q=1/(q-2); Haar_lower=m/(density*P)',
                     'scope': 'Subtract only pure single-prime terms; retain every old-cofactor-one multi-prime class.'},
        'tail_parameters': {'B': B, 'ell': ell, '3^ell': 3**ell, 'c': c,
                            'tau7_series': series, 'tau7': tau,
                            'seed': 'Haar restricted to actual head avoid-set, unnormalized, joint density at most one.',
                            'remaining_mass_scope': 'Positive mass in the distorted tail law; not a final Haar-density lower bound.'},
        'ten_prime_families': positives,
        'contrasting_splits': controls,
        'first_prime_support_controls': small_supports,
        'nonpositive_expression_scope': 'Failure of this scalar sufficient criterion only; not a covering example or an all-law obstruction.',
    }
    text = json.dumps(encoded(result), indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
        print('PASS: pinned common-law seeds, finite-Q grouping, ten-prime bounds, split controls, and exact Chapter33 tails.')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
