"""Consume retained source margins and compute seven-core completion constants.

This checks certificate arithmetic, not source geometry, arbitrary-height
comparison, common-law existence, or transport proofs. No producer is run.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from math import ceil, prod
from pathlib import Path
import json


CERTIFICATE_SHA256 = 'a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac'
ARCHIVE_SHA256 = '9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c'
PHASE_COUNTS = dict(basic=16, basic75=4, mixed=420, anchor=184,
                    coarse=25840, spatial=1003, pure3=506, closing=28)


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def certificate_summary(path):
    raw = path.read_bytes()
    require(sha256(raw).hexdigest() == CERTIFICATE_SHA256, 'certificate identity')
    data = json.loads(raw)
    require(data['mass_denominator'] == 135000, 'integer-to-Haar denominator')
    require(data['row_format'] == ['phase', 'configuration', 'reserve_lower', 'loss_upper'],
            'row shape')
    rows = data['rows']
    require(len(rows) == 28001, 'terminal row count')
    seen, margins, phases = set(), [], Counter()
    for phase, configuration, reserve, loss in rows:
        key = (phase, json.dumps(configuration, separators=(',', ':')))
        require(key not in seen, 'duplicate terminal row')
        seen.add(key)
        require(type(reserve) is int and type(loss) is int, 'integer entries')
        require(reserve - loss >= 4, 'uniform terminal margin')
        margins.append(reserve - loss)
        phases[phase] += 1
    require(min(margins) == 4, 'sharp retained minimum')
    require(phases == PHASE_COUNTS, 'phase coverage')

    delta, beta, threshold = Q(4, 1000), 10, 12
    mass = delta / 135
    epsilon = beta * delta / 135
    query_bound = threshold - 1 + beta - epsilon
    cap = prod((Q(3, 2), Q(5, 3), Q(3, 2), Q(2), Q(9, 5)))
    density = cap / mass
    require((mass, epsilon, query_bound, cap, density) ==
            (Q(1, 33750), Q(1, 3375), Q(70874, 3375), Q(27, 2), Q(455625)),
            'common-ledger bridge constants')

    parent = 23
    capacity = Q(parent) - Q(parent, parent - 1)
    level = Q(parent, parent - 1) * (21 - epsilon / 2)
    expected = Q(parent, parent - 1) * query_bound
    probability = 1 - expected / level
    haar_mass, gap = probability / density, capacity - level
    require((probability, haar_mass, gap) ==
            (Q(1, 141749), Q(1, 64584388125), Q(23, 148500)),
            'actual good-set constants')

    tail_density = 65000000000
    require(haar_mass > Q(1, tail_density), 'rounded good-set density cap')
    primes = (3, 5, 7, 11, 13, 17, 19)
    moment1 = prod(Q(p, p - 1) for p in primes)
    moment2 = prod(Q(p * (p + 1), (p - 1)**2) for p in primes)
    cutoff = ceil(tail_density * moment2)
    require((moment1, moment2, cutoff) ==
            (Q(323323, 110592), Q(2263261, 110592), 1330222484448),
            'height-independent tail constants')
    numerator = 324 * tail_density * moment1
    require(numerator == Q(123140595703125, 2), 'weighted tail numerator')
    require(numerator < 3**6 * cutoff**3, 'tail below 3^-250 at the stated cutoff')
    require(Q(1, 3**250) < gap, 'tail fits the pointwise core margin')

    return dict(
        scope='Exact consumer of retained integer margins and derived constants. '
              'Source geometry and arbitrary-height comparison are attributed premises; '
              'the common-law extraction and prime transport are separate ordinary proofs. '
              'One law serves all layouts at a fixed finite period. No Lean certification.',
        certificate_sha256=CERTIFICATE_SHA256, source_doi='10.5281/zenodo.22759614',
        source_edition='1.0.1', source_archive_sha256=ARCHIVE_SHA256,
        source_producer_rerun=False, geometry_enumeration_rerun=False,
        terminal_rows=len(rows), phase_counts=dict(phases), minimum_integer_surplus=min(margins),
        cell_units_per_haar_unit=135, integer_units_per_cell_unit=1000,
        source_ledger_gap_cell_units=delta, seven_core_live_mass_lower=mass,
        seven_core_unnormalized_density_cap=cap, seven_core_query_R_upper=query_bound,
        query_gap_below21=epsilon, normalized_density_cap=density,
        parent_lower_bound=parent, completion_mean_upper=expected, good_load_level=level,
        good_probability_lower=probability, good_haar_mass_lower=haar_mass,
        pointwise_parent_margin=gap, tail_density=tail_density, J1=moment1, J2=moment2,
        N=cutoff, tail_cutoff=f'3^256 * {cutoff}^3', weighted_tail_numerator=numerator)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True,
                        help='integer_certificate.json from Schroeder edition 1.0.1')
    parser.add_argument('--output', type=Path, help='summary path; default JSON on stdout')
    args = parser.parse_args()
    encoded = json.dumps(certificate_summary(args.certificate), indent=2, default=str) + '\n'
    if args.output:
        args.output.write_text(encoded)
        print('PASS: 28001 retained terminal margins and seven-core completion constants.')
    else:
        print(encoded, end='')


if __name__ == '__main__':
    main()
