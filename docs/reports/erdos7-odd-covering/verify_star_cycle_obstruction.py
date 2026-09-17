#!/usr/bin/env python3
"""Exact odd-CRT counterexample to composing individually zero-loss clusters.

One actual uniform 357 source, with pure 11/13/17/19 extensions. No optimizer,
abstract Gram relaxation, external numerical package, or Lean verification.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def compute():
    period = 1575
    forbidden = [(3, 0), (5, 0), (7, 0), (9, 4), (15, 4), (21, 19),
                 (25, 14), (35, 18), (45, 26), (63, 1), (75, 71),
                 (105, 83), (175, 23), (225, 199), (315, 262),
                 (525, 383), (1575, 754)]
    divisors = [d for d in range(1, period + 1) if period % d == 0]
    labels = divisors[1:]
    require([d for d, residue in forbidden] == labels, 'complete original old modulus inventory')
    require(all(d > 1 and d % 2 and 0 <= residue < d for d, residue in forbidden),
            'literal distinct odd congruences')
    source = [x for x in range(period) if all(x % d != residue for d, residue in forbidden)]
    require(len(source) == 382, 'literal survivor cardinality')
    size = len(source)
    counts = {d: Counter(x % d for x in source) for d in divisors}
    maxima = {d: max(counts[d].values()) for d in divisors}
    argmax = {d: {r for r, count in counts[d].items() if count == maxima[d]} for d in divisors}

    # All possible central-unary stars, including every pair neighbor.
    # Every pair (d,e) has max mass maxima[lcm(d,e)] / size.
    star_witnesses = {}
    for d in labels:
        candidates = set(argmax[d])
        for multiple in divisors:
            if multiple % d == 0:
                candidates &= {r % d for r in argmax[multiple]}
        require(candidates, 'a nonzero full central-unary star')
        star_witnesses[d] = min(candidates)
        for e in labels:
            if e != d:
                require(any(r % d == star_witnesses[d] for r in argmax[lcm(d, e)]),
                        'central label cannot attain this original pair maximum')

    # Every edge separately attains both endpoint unaries and its pair maximum.
    edge_witnesses = []
    for d, e in combinations(labels, 2):
        multiple = lcm(d, e)
        candidates = [r for r in argmax[multiple]
                      if r % d in argmax[d] and r % e in argmax[e]]
        require(candidates, 'a nonzero two-ended edge cluster')
        edge_witnesses.append([d, e, min(candidates)])
    require(len(edge_witnesses) == 136, 'all original edge clusters')
    require(not any(all(x % d in argmax[d] for d in labels) for x in source),
            'a common global maximizing state unexpectedly exists')

    cluster = [5, 21, 35]
    require({d: sorted(argmax[d]) for d in cluster} ==
            {5: [2], 21: [8, 17], 35: [2, 3, 27, 32]}, 'triangle domains')
    pair_tables = {}
    for d, e in combinations(cluster, 2):
        table = [[0 for _ in range(e)] for _ in range(d)]
        for x in source:
            table[x % d][x % e] += 2
        pair_tables[d, e] = table
    independent = 3 * sum(maxima[d] for d in cluster)
    independent += 2 * sum(maxima[lcm(d, e)] for d, e in combinations(cluster, 2))
    best = -1
    maximizers = []
    restricted_best = -1
    for residues in product(*(range(d) for d in cluster)):
        selected = dict(zip(cluster, residues))
        value = 3 * sum(counts[d][selected[d]] for d in cluster)
        value += sum(table[selected[d]][selected[e]] for (d, e), table in pair_tables.items())
        if value > best:
            best = value
            maximizers = [list(residues)]
        elif value == best:
            maximizers.append(list(residues))
        if all(selected[d] in argmax[d] for d in cluster):
            restricted_best = max(restricted_best, value)
    require(independent == 725 and best == 716 and maximizers == [[2, 2, 2]],
            'full six-factor triangle maximum')
    require(independent - restricted_best == 30, 'unary-only domain restriction price')
    require(counts[21][2] == 47 and maxima[21] == 50,
            'attaining triangle layout pays the true unary loss')

    # Product extension: the same actual law, now through pure AP11/13/17/19.
    extension_primes = [11, 13, 17, 19]
    extended_forbidden = forbidden + [(p, 0) for p in extension_primes]
    full_period = period * prod(extension_primes)
    full_labels = sorted(d * prod(p for p, bit in zip(extension_primes, bits) if bit)
                         for d in divisors for bits in product((0, 1), repeat=4))
    require(len(full_labels) == len(set(full_labels)) == 288, 'all full original test labels')
    require(len({d for d, residue in extended_forbidden}) == 21, '21 distinct original forbidden moduli')
    require(lcm(*(d for d, residue in extended_forbidden)) == full_period, 'actual common period')
    # Every new prime only removes root zero: subsequent mixed masks are absent.
    # Hence no assigned bad mass and physical/killed laws are the same products.
    normalizer = size * prod(p - 1 for p in extension_primes)
    require(normalizer == 13201920, 'actual final survivor count')
    full_core_parts = {d: gcd(d, period) for d in full_labels}
    projection_maxima = {(d, e): {r % d for r in argmax[lcm(d, e)]}
                         for d in divisors for e in divisors}
    core_edge_compatible = {(d, e): any(r % d in argmax[d] and r % e in argmax[e]
                                      for r in argmax[lcm(d, e)])
                            for d in divisors for e in divisors}
    for d in full_labels[1:]:
        core = full_core_parts[d]
        witness = 0 if core == 1 else star_witnesses[core]
        for e in full_labels[1:]:
            if d != e:
                require(witness in projection_maxima[core, full_core_parts[e]],
                        'pure-extension central-unary star')
    for d, e in combinations(full_labels[1:], 2):
        require(core_edge_compatible[full_core_parts[d], full_core_parts[e]],
                'pure-extension two-ended edge')

    return {
        'schema': 'actual-odd-crt-zero-stars-zero-edges-v1',
        'source_period': period,
        'source_forbidden': [list(item) for item in forbidden],
        'source_survivors': source,
        'source_survivor_count': size,
        'original_old_test_labels': divisors,
        'marginal_maximum_counts': {str(d): maxima[d] for d in divisors},
        'marginal_maximizer_residues': {str(d): sorted(argmax[d]) for d in divisors},
        'full_central_unary_star_witnesses': {str(d): r for d, r in star_witnesses.items()},
        'two_ended_edge_witnesses': edge_witnesses,
        'common_maximizing_state_exists': False,
        'triangle': {
            'original_labels': cluster,
            'complete_residue_assignments': prod(cluster),
            'independent_envelope': str(Fraction(independent, size)),
            'maximum': str(Fraction(best, size)),
            'maximizers': maximizers,
            'loss': str(Fraction(independent - best, size)),
            'loss_if_unary_maximizers_are_imposed': str(Fraction(independent - restricted_best, size)),
            'L1_loss_comparison_coefficient': 15,
        },
        'pure_extension': {
            'primes': extension_primes,
            'full_forbidden': [list(item) for item in extended_forbidden],
            'period': full_period,
            'full_original_test_labels': full_labels,
            'final_survivor_count': normalizer,
            'actual_nu13_survivor_count': size * 10 * 12,
            'charge17': '0',
            'charge19_physical17': '0',
            'final_killed_mass': '1',
            'all_full_original_stars_and_two_ended_edges_zero': True,
            'triangle_loss_for_full_signed_pair_envelope': '9/382',
        },
        'scope': 'Exact actual-family obstruction to zero local clusters implying global saturation. '
                 'Product extension justified in the accompanying proof; no unrestricted numeric bound or Lean verification.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/star_cycle_obstruction_certificate.json'))
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = compute()
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2) + '\n')
    else:
        supplied = json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique)
        require(supplied == result, 'certificate differs from literal reconstruction')
    print('PASS actual 1575-source obstruction: all 17 central-unary stars and 136 two-ended edges vanish; '
          'full triangle loss 9/382; 288-label pure-extension scope as stated.')
