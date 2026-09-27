#!/usr/bin/env python3
"""Exact relative-ledger consumer of the pinned original terminal certificate.

The source's stagewise screening domination, common functional and vertex
interpolation remain ordinary proof premises. No source producer, geometry,
cached geometry evaluator, external package or Lean checker is imported.
"""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

CERTIFICATE_SHA = 'a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac'
EXPECTED_PHASES = {
    'basic': 16, 'basic75': 4, 'mixed': 420, 'anchor': 184,
    'coarse': 25840, 'spatial': 1003, 'pure3': 506, 'closing': 28,
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    need(sha256(raw).hexdigest() == CERTIFICATE_SHA, 'original certificate SHA256 mismatch')
    certificate = json.loads(raw)
    need(certificate['mass_denominator'] == 135000, 'source mass denominator')
    need(certificate['row_format'] == ['phase', 'configuration', 'reserve_lower', 'loss_upper'],
         'terminal aggregate schema')
    rows = certificate['rows']
    need(len(rows) == 28001, 'complete terminal row count')
    identities = set()
    phases = Counter()
    ratios = []
    gaps = []
    for row in rows:
        need(isinstance(row, list) and len(row) == 4, 'terminal row shape')
        phase, configuration, reserve, loss = row
        need(phase in EXPECTED_PHASES and isinstance(configuration, list), 'phase and configuration')
        need(all(type(x) in (int, str) for x in configuration), 'configuration key types')
        need(type(reserve) is int and type(loss) is int, 'integer aggregate bounds')
        need(reserve > 0 and 0 <= loss < reserve and reserve - loss >= 4,
             'positive rounded terminal ledger')
        identity = (phase, tuple(configuration))
        need(identity not in identities, 'duplicate terminal identity')
        identities.add(identity)
        phases[phase] += 1
        ratios.append(Fraction(loss, reserve))
        gaps.append(reserve - loss)
    need(phases == EXPECTED_PHASES and len(identities) == 28001, 'complete phase coverage')
    need(min(gaps) == 4, 'minimum integer surplus')
    rho = max(ratios)
    attainers = [
        {'phase': row[0], 'configuration': row[1], 'reserve_lower': row[2],
         'loss_upper': row[3], 'integer_surplus': row[2] - row[3]}
        for row, ratio in zip(rows, ratios) if ratio == rho
    ]
    need(rho == Fraction(16873, 16875) and len(attainers) == 4, 'exact maximum aggregate ratio')
    need(all(x['phase'] == 'coarse' and x['reserve_lower'] == 33750
             and x['loss_upper'] == 33746 for x in attainers), 'maximizing terminal bounds')
    query_bound = 11 + 10 * rho
    old_bound = Fraction(70874, 3375)
    need(query_bound == Fraction(70871, 3375) == 21 - Fraction(4, 3375),
         'relative-ledger query consequence')
    need(old_bound - query_bound == Fraction(1, 1125), 'strict improvement')
    need(Fraction(9, 10) < rho < 1, 'relative-ledger comparison boundary')
    result = {
        'scope': 'Exact arithmetic of all retained terminal aggregate rows. The maximum below is loss_upper/reserve_lower, not the actual maximum of the stage23/D7 ratio or the actual query invariant.',
        'certificate_sha256': CERTIFICATE_SHA,
        'source_row_format': certificate['row_format'],
        'mass_denominator': 135000,
        'cell_units_per_Haar_unit': 135,
        'integer_units_per_cell_unit': 1000,
        'row_count': len(rows),
        'unique_terminal_count': len(identities),
        'phase_counts': dict(phases),
        'minimum_integer_surplus': min(gaps),
        'maximum_aggregate_loss_reserve_ratio': str(rho),
        'maximum_attainer_count': len(attainers),
        'maximum_attainers': attainers,
        'query_bound_conditional_on_source_bridge': str(query_bound),
        'query_gap_below21': str(21 - query_bound),
        'previous_query_bound': str(old_bound),
        'improvement_from_previous_bound': str(old_bound - query_bound),
        'common_functional_consequence': 'For nonnegative common bounds S=sum(stage7,...,stage19 losses), U=L23 and common reserve R, screening and interpolation imply S+U<=rho*R. Then D7=R-S>0 and U/D7<=(rho*R-S)/(R-S)<=rho. The established query bridge gives R_query<=11+10*rho.',
        'inherited_proof_obligations': [
            'Every terminal screen uses the same fixed caps and bounds the same completed-family common functional; its reserve is no larger and each stage-loss upper bound is no smaller than the corresponding common quantity.',
            'If a screen ignores a budget, its bounds hold uniformly over that budget; all required joint vertices are covered by the retained hierarchy.',
            'The common reserve is affine in the source interpolation and each stage-loss upper function is convex with the same nonnegative vertex coefficients. Therefore rho*R-sum(stage losses) interpolates as a concave lower ledger.',
            'The existing fixed-law final-stage bridge controls every query using the same live measure: R_query<=11+10*L23/D7. No query-dependent law or stagewise parameter reselection is introduced.',
        ],
        'unresolved_stagewise_information': 'These rows store only reserve and total loss. They do not supply the individual stage23 loss or D7. The aggregate maximum does not establish the stage23/D7<9/10 criterion for R_query<20.',
        'source_producer_rerun': False,
        'geometry_rerun': False,
        'lean_certification': False,
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
        print('PASS: pinned 28001-row terminal aggregates, unique identities, exact relative maximum and conditional query improvement.')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
