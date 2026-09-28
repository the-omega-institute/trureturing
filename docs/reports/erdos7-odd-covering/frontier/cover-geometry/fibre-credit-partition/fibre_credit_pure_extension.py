"""Same-law pure-outside continuation of the height-one common query.

Every original has v3(m)<=1 and uses the first eleven odd primes.
Other heights and all original residues are arbitrary in the main result.
The optional finite profiles are upper height bounds, not main premises.
This consumes the checked source/query pair without rebuilding it.
Ordinary proof and exact arithmetic; no Lean verification is claimed.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import argparse
import json


QUERY_HASH = '019e8321d1c11458be92ba5b8ede28ff2dad998cd050846ac42870571ea9ba83'
OUTSIDE = (29, 31, 37)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def record(value):
    return {'exact': str(value), 'decimal': float(value)}


def extend(source, finite_outside):
    bound = F(source['query_upper'])
    alpha = F(source['alpha_lower'])
    bs = tuple(F(p**3 - 1, (p - 2)*p**3 + 1) if finite_outside
               else F(1, p - 2) for p in OUTSIDE)
    caps = tuple(1 + b for b in bs)
    price = prod(caps) - 1
    mixed_unit = price - sum(bs, F(0))
    expense = bound * price + mixed_unit
    b1, b2, b3 = bs
    expanded = bound * (b1 + b2 + b3) + (bound + 1) * (
        b1*b2 + b1*b3 + b2*b3 + b1*b2*b3)
    need(expense == expanded, 'singleton and mixed outside supports')
    reserve = 1 - expense
    need(reserve > 0, 'positive same-law continuation reserve')
    full_cap = F(source['full_product_mean']) / alpha * prod(caps)
    haar = reserve / full_cap
    need(haar > F(1, 700), 'strict full Haar survivor bound')
    return {'old_query_upper': record(bound), 'old_source_alpha_lower': str(alpha),
            'outside_height_bounds': [3, 3, 3] if finite_outside else None,
            'outside_pure_source_caps': list(map(str, caps)),
            'outside_inventory_bounds': list(map(str, bs)),
            'nonunit_outside_price': record(price),
            'unit_mixed_outside_price': record(mixed_unit),
            'forbidden_union_upper': record(expense),
            'supported_probability_reserve': record(reserve),
            'full_haar_density_upper': record(full_cap),
            'full_haar_survivor_lower': record(haar),
            'strict_surplus_over_1_over_700': str(haar - F(1, 700))}


def verify(package):
    raw = (package / 'fibre_credit_truncated_query.json').read_bytes()
    need(sha256(raw).hexdigest() == QUERY_HASH, 'pinned source/query certificate')
    data = json.loads(raw)
    need(data['core_primes'] == [3, 5, 7, 11, 13, 17, 19, 23]
         and data['outside_primes'] == list(OUTSIDE), 'original prime inventory')
    unlimited = extend(data['arbitrary_nonternary_heights'], False)
    old_finite = extend(data['whole_cover_height_profile'], False)
    finite = extend(data['whole_cover_height_profile'], True)
    need(F(unlimited['nonunit_outside_price']['exact']) == F(3, 29), 'complete outside price')
    need(F(unlimited['unit_mixed_outside_price']['exact']) == F(92, 27405), 'unit mixed price')
    need(F(unlimited['full_haar_density_upper']['exact']) == F(1751777280, 62133457), 'joint density cap')
    need(F(unlimited['full_haar_survivor_lower']['exact']) == F(
        88016430921103672032820067404610465617466941,
        61115611972512329206704300212201763057254400000), 'arbitrary-height positive bound')
    b23, b29 = F(1, 21), F(1, 27)
    need((1 - b23*b29) / (b23 + b29 + b23*b29) == F(566, 49), 'existing two-prime interface')
    nonternary = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    no3_b = tuple(F(1, p - 2) for p in nonternary)
    no3_cap = prod(1 + b for b in no3_b)
    no3_reserve = 2 + sum(no3_b, F(0)) - no3_cap
    no3_haar = no3_reserve / no3_cap
    need(no3_haar == F(29127751, 173015040) > F(1, 700), 'empty-core nonternary continuation')
    return {'scope': __doc__, 'query_certificate_sha256': QUERY_HASH,
            'core_primes': data['core_primes'], 'outside_primes': list(OUTSIDE),
            'whole_family_ternary_height_upper': 1,
            'arbitrary_nonternary_heights': unlimited,
            'finite_old_profile_arbitrary_outside_heights': old_finite,
            'finite_old_and_outside_profiles': finite,
            'without3_empty_core': {'first_11_nonternary_primes': nonternary,
                'source_density_cap': str(no3_cap), 'remaining_mass_lower': str(no3_reserve),
                'haar_survivor_lower': str(no3_haar)},
            'boundary': 'One old actual survivor law and three actual pure-outside masks are fixed before the remaining union is deleted. Only unit labels with singleton outside support vanish for free. The main result needs no global minimality or finite nonternary height bounds. Deeper ternary originals and unrestricted prime support are not settled.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = json.dumps(verify(args.package), sort_keys=True, indent=2) + '\n'
    if args.output is None:
        print(output, end='')
    else:
        args.output.write_text(output)
