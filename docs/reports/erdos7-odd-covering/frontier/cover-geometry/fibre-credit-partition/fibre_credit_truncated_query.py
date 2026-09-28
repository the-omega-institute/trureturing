"""Exact complete-query bounds when all old ternary exponents are at most one.

The arbitrary-nonternary-height result reuses the eight-core source certificate.
The finite-profile result reuses the existing64-partition reduction with a
new eight-core profile. Only multiplier atoms through6 and full first moments
are needed; the real-threshold optimum follows from the two exact slopes.
Outside deletion additionally requires whole-family ternary height at most1.
The computed HC7/HC9 profile requires a whole cover globally minimal first
in cardinality, then in the sum of numerical moduli, as in Report385.
These are upper comparisons, not actual cover enumeration or Lean results.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path
import argparse
import json
import runpy


CORE = (3, 5, 7, 11, 13, 17, 19, 23)
OUTSIDE = (29, 31, 37)
CERT_HASH = 'ae84f5c3df9ca167c7768dc561f958392631cb3cf092803445321d3e989e37e4'
SOURCE_HASH = '0022be7af152b4b13748589ed98177e157cc490a1656d39d4b64a26e1ad72a16'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pinned(path, expected):
    raw = path.read_bytes()
    need(sha256(raw).hexdigest() == expected, 'pinned dependency: ' + path.name)
    return raw


def multiplier(caps, heights):
    low, mean = {1: F(1, 2), 2: F(1, 2)}, F(3, 2)
    factors = []
    for p, cap, height in zip(CORE[1:], caps, heights):
        atoms = {1: 1 - cap / p}
        for m in range(2, 7):
            atoms[m] = (cap * F(p - 1, p ** m) if height is None or m <= height
                        else cap / p ** height if m == height + 1 else F(0))
        factor_mean = 1 + cap / (p - 1) * (1 if height is None else 1 - F(1, p ** height))
        need(all(w >= 0 for w in atoms.values()) and sum(atoms.values()) <= 1, 'positive auxiliary law')
        if height is not None:
            need(height <= 5 and sum(atoms.values()) == 1, 'complete finite-height law')
            need(factor_mean == cap, 'finite factor mean equals pure-source cap')
        nxt = {}
        for a, b in product(low, atoms):
            if a * b <= 6:
                nxt[a * b] = nxt.get(a * b, F(0)) + low[a] * atoms[b]
        low, mean = nxt, mean * factor_mean
        factors.append({'prime': p, 'height': height, 'cap': str(cap),
                        'atoms_through6': {str(m): str(w) for m, w in atoms.items()},
                        'full_mean': str(factor_mean)})
    return low, mean, factors


def ledger(alpha, caps, heights, outside_heights):
    low, mean, factors = multiplier(caps, heights)
    tail_ge6 = 1 - sum((w for m, w in low.items() if m < 6), F(0))
    tail_gt6 = tail_ge6 - low.get(6, F(0))
    need(tail_ge6 > alpha > tail_gt6 >= 0, 'strict real-threshold optimum at6')
    hinge6 = mean - 6 + sum((F(6 - m) * w for m, w in low.items() if m < 6), F(0))
    need(hinge6 >= 0, 'positive full hinge expectation')
    upper = 5 + hinge6 / alpha
    price = prod(1 + (F(1, p - 1) if height is None else
                       sum((F(1, p ** e) for e in range(1, height + 1)), F(0)))
                 for p, height in zip(OUTSIDE, outside_heights)) - 1
    margin = 1 - price * (1 + upper)
    need(margin < 0, 'this upper comparison still does not certify survival')
    return {'alpha_lower': str(alpha), 'coordinate_laws': factors,
            'product_atoms_through6': {str(m): str(w) for m, w in sorted(low.items())},
            'full_product_mean': str(mean), 'hinge6': str(hinge6),
            'tail_ge6': str(tail_ge6), 'tail_gt6': str(tail_gt6),
            'left_slope_at6': str(1 - tail_ge6 / alpha),
            'right_slope_at6': str(1 - tail_gt6 / alpha),
            'unique_optimal_real_threshold': 6, 'query_upper': str(upper),
            'query_upper_decimal': float(upper), 'outside_height_caps': outside_heights,
            'outside_price': str(price), 'comparison_margin': str(margin),
            'comparison_margin_decimal': float(margin),
            'pre_normalization_deficit': str(-alpha * margin)}


def verify(root):
    old = json.loads(pinned(root / 'fibre_credit_partition.json', CERT_HASH))
    rows = old['partition_numerators']
    need(len(rows) == old['partition_count'] == 64, 'all retained source partitions')
    alpha = F(min(row[1] for row in rows), old['partition_denominator'])
    need(alpha == F(2142533, 15904350), 'existing eight-core source margin')
    infinite = ledger(alpha, tuple(F(p - 1, p - 2) for p in CORE[1:]), (None,) * 7, (None,) * 3)
    need(F(infinite['outside_price']) == F(3023, 30240), 'full outside inventory')
    need(F(infinite['query_upper']) == F(25585241677563810650651525265027348808464564,
                                        2768452210966647080721479752700688323091875), 'ternary-only truncated query')

    source = root / 'fibre_credit_height_partition.py'
    pinned(source, SOURCE_HASH)
    compare = runpy.run_path(str(source))['compare']
    support_size = len(CORE) + len(OUTSIDE)
    bound = lambda p: min(5 if p <= 7 else 4, 2 + (5 * support_size - 9) // (p - 2))
    heights = tuple(map(bound, CORE[1:]))
    outside_heights = tuple(map(bound, OUTSIDE))
    need(heights == (5, 5, 4, 4, 4, 4, 4) and outside_heights == (3, 3, 3), 'shared HC7/HC9 profile')
    profile = compare(CORE, heights)
    alpha_finite = F(profile['minimum_comparison'])
    need(profile['partition_count'] == 64 and profile['minimizing_partitions_containing_5'] == [[5]],
         'complete finite source partition reduction')
    need(alpha_finite == F(7869166022025963372126998610755, 58313734905966118372203626202336),
         'finite-height source lower comparison')
    caps = tuple(map(F, profile['source_caps']))
    finite = ledger(alpha_finite, caps, heights, outside_heights)
    need(F(finite['full_product_mean']) == F(3, 2) * prod(caps), 'finite mean equals predeletion Haar cap')
    need(F(finite['query_upper']) == F(72644530810195793920671528681368, 7869166022025963372126998610755),
         'finite-profile query bound')
    need(F(finite['comparison_margin']) == F(-5752216770187904734900111181430100674522,
                                            252493113440094170651284888859573040475255), 'finite-profile negative screen')
    return {'scope': __doc__, 'core_primes': CORE, 'outside_primes': OUTSIDE,
            'pinned_source_certificate_sha256': CERT_HASH, 'pinned_profile_program_sha256': SOURCE_HASH,
            'ternary_query_height': 1, 'arbitrary_nonternary_heights': infinite,
            'whole_cover_height_profile': finite, 'finite_source_partition_profile': profile,
            'boundary': 'The same actual survivor law supports only the stated query family. Outside deletion requires whole-family v3(m)<=1, including later originals. The finite source/query requires the shared original height bounds; their HC7/HC9 derivation additionally assumes a whole cover globally minimal first in cardinality and then in the sum of numerical moduli. Negative margins do not exhibit a cover or show an actual survivor mass is negative.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(verify(args.package), sort_keys=True, indent=2) + '\n'
    if args.output is None:
        print(text, end='')
    else:
        args.output.write_text(text)
