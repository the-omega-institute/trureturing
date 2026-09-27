#!/usr/bin/env python3
"""Exact same-source fees for releasing secondary pair endpoints.

Read the completed canonical Reports 626 and 625 certificates, retain all
query costs, and price each of the eighty possible released labels once.
This standard-library computation does not rerun the source scans or
constitute Lean verification. See the accompanying ordinary proof.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    'unanchored_square_source_certificate.json': 'b8c38f05cbcd65607e25bc138ecc5a20961cd5bb786b18ad41df5583986bb1a4',
    'unanchored_square_source_certificate.py': 'fdde856e6317ad315fce3f48f75be95ec41a9b59595e41454db9450045f1847b',
    'unanchored_square_source_certificate.cpp': '61e9553d1fc15a87df6493be00f6c98c36b35612edc884e4347f433121e2ceb9',
    'unanchored_square_source_certificate_conditional.cpp': '49ee101c7664b8e68eb78c02115ceef2c78102271d4a037800821585676d7ab4',
    'arbitrary_pure_network_extensions.json': 'ae50c6a2f6edc9bd30db3531882bf13c0b0b11f1760e7ebcd711e56f11c285fa',
    'arbitrary_pure_network_extensions.py': '553f6b014d4ca30f6d5e31e60acf27e85eae8e6cd6a3fac1182f1785128744df',
    'actual_pair_activation_certificate.json': '2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f',
}
QS = (7, 11, 13, 17, 19)
CORE = (3, 5) + QS
CHECKS = {}


def ck(name, condition):
    if not condition:
        raise ArithmeticError(name)
    CHECKS[name] = True


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=HERE,
                        help='Directory containing the canonical input certificates')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    directory = args.source_dir.resolve()
    for name, pin in PINS.items():
        ck('dependency_pin_' + name, digest(directory / name) == pin)
    data626 = json.loads((directory / 'unanchored_square_source_certificate.json').read_text())
    data625 = json.loads((directory / 'arbitrary_pure_network_extensions.json').read_text())
    data604 = json.loads((directory / 'actual_pair_activation_certificate.json').read_text())
    ck('626_complete_twenty_sources', data626['complete'] is True
       and data626['complete_cases'] == list(range(20)))
    ck('625_pass', data625['status'] == 'PASS' and all(data625['checks'].values()))
    for field, filename in [('producer_sha256', 'unanchored_square_source_certificate.py'),
                            ('kernel_sha256', 'unanchored_square_source_certificate.cpp'),
                            ('conditional_kernel_sha256', 'unanchored_square_source_certificate_conditional.cpp')]:
        ck('626_' + field, data626[field] == PINS[filename])
    ck('625_producer_pin', data625['producer_sha256'] == PINS['arbitrary_pure_network_extensions.py'])
    for name, pin in data626['local_intervals']['dependencies'].items():
        ck('626_inherited_pin_' + name, digest(directory / name) == pin)
    gamma = F(data626['gate_lower'])
    alpha = F(data626['Haar_factor'])
    c = F(data604['constants']['continuation_c'])
    g = 1 - c
    ck('gamma', gamma == F(190452499219361, 189995609279692800))
    ck('alpha', alpha == F(2673, 110656) == F(data625['constants']['alpha']))
    ck('626_head_conversion', alpha * gamma == F(data626['haar_lower']))
    ck('continuation_c', c == F(1084133, 201247200) and 0 < c < 1)
    loss = list(map(F, data604['complete_coefficients']['loss']))
    query = list(map(F, data604['complete_coefficients']['weighted_nonunit_query']))
    ck('all_512_query_costs_retained', len(loss) == len(query) == 512
       and min(loss + query) >= 0 and loss[0] == query[0] == 0)

    r = {q: F(1, q - 1) for q in QS}
    square = {q: F(1, q * (q - 2)) for q in QS}
    zmin = {q: 1 - 5 * r[q] - 2 * square[q] for q in QS}
    ck('global_box_positive', min(zmin.values()) == F(23, 210))
    central = {(0, 0): F(14, 15), (1, 0): F(2, 3),
               (0, 1): F(4, 15), (1, 1): F(8, 45)}
    ck('live_mask_minimum', (1 - F(2, 3)) * (1 - 3 * F(4, 15)) == F(1, 15))
    ck('central_cap_sum', sum(central.values()) == F(92, 45))
    ck('central_product_cap', central[1, 1] == central[1, 0] * central[0, 1])

    labels, edges, orientations = [], [], []
    primary_labels = set()
    for q, s in combinations(QS, 2):
        remaining = tuple(u for u in QS if u not in (q, s))
        hcap = 1 - sum(r[u] * r[v] for u, v in combinations(remaining, 2))
        ck(f'three_vertex_hcap_positive_{q}_{s}', hcap > 0)
        # Each derivative is the two-vertex polynomial Z_u Z_v-r_u r_v.
        for u, v in combinations(remaining, 2):
            ck(f'positive_box_derivative_{q}_{s}_{u}_{v}', zmin[u] * zmin[v] > r[u] * r[v])
        corner_values = []
        for bits in product(range(2), repeat=3):
            z = {u: (F(1) if bit else zmin[u]) for u, bit in zip(remaining, bits)}
            value = prod(z.values()) - sum(r[u] * r[v] * z[w]
                for u, v in combinations(remaining, 2) for w in remaining if w not in (u, v))
            corner_values.append(value)
        ck(f'all_eight_response_corners_{q}_{s}', 0 < min(corner_values)
           and max(corner_values) == hcap)
        edge_labels = []
        for eq, es in [(2, 1), (1, 2)]:
            orientation_labels = []
            outside_cap = (square[q] if eq == 2 else r[q]) * (square[s] if es == 2 else r[s])
            for a, b in product(range(2), repeat=2):
                modulus = 3**a * 5**b * q**eq * s**es
                powers = tuple({3: a, 5: b, q: eq, s: es}.get(p, 0) for p in CORE)
                raw_cap = central[a, b] * outside_cap * hcap
                ck(f'literal_factorization_{modulus}', modulus == prod(p**e for p, e in zip(CORE, powers)))
                row = {'modulus': modulus, 'exponents': list(powers), 'edge': [q, s],
                       'outside_exponents': [eq, es], 'central_exponents': [a, b],
                       'central_cap': str(central[a, b]), 'outside_cap': str(outside_cap),
                       'response_cap': str(hcap), 'raw_deletion_cap': str(raw_cap),
                       'gate_fee': str(g * raw_cap)}
                labels.append(row)
                edge_labels.append(row)
                orientation_labels.append(row)
                primary_labels.add(3**a * 5**b * q * s)
            fee = sum((F(row['gate_fee']) for row in orientation_labels), F())
            orientations.append({'edge': [q, s], 'outside_exponents': [eq, es],
                                 'moduli': [row['modulus'] for row in orientation_labels],
                                 'gate_fee': str(fee), 'remaining_gate_lower': str(gamma - fee),
                                 'positive_sufficient_bound': gamma > fee})
        raw = sum((F(row['raw_deletion_cap']) for row in edge_labels), F())
        ck(f'eight_label_formula_{q}_{s}', raw == F(92, 45) *
           (square[q] * r[s] + r[q] * square[s]) * hcap)
        edges.append({'edge': [q, s], 'response_cap': str(hcap),
                      'moduli': sorted(row['modulus'] for row in edge_labels),
                      'raw_deletion_cap': str(raw), 'gate_fee': str(g * raw),
                      'remaining_gate_lower': str(gamma - g * raw),
                      'positive_sufficient_bound': gamma > g * raw})
    ck('eighty_distinct_secondary_labels', len(labels) == len({row['modulus'] for row in labels}) == 80)
    ck('forty_disjoint_primary_labels', len(primary_labels) == 40
       and primary_labels.isdisjoint(row['modulus'] for row in labels))
    ck('ten_edges_twenty_orientations', len(edges) == 10 and len(orientations) == 20)
    total_raw = sum((F(row['raw_deletion_cap']) for row in labels), F())
    total_fee = g * total_raw
    ck('edge_and_label_sums_agree', total_raw == sum((F(row['raw_deletion_cap']) for row in edges), F()))
    ck('full_release_fee', total_fee == F(111509457942163301, 3127546913198400000))
    ck('full_release_additive_bound_insufficient', total_fee > gamma)
    chosen = next(row for row in edges if row['edge'] == [17, 19])
    B = F(chosen['raw_deletion_cap'])
    fee = g * B
    raw = gamma - fee
    head = alpha * raw
    ck('chosen_response_cap', F(chosen['response_cap']) == F(173, 180))
    ck('chosen_raw_cap', B == F(1141973, 1412802000))
    ck('chosen_fee', fee == F(32654402587313, 40617492379200000))
    ck('only_affordable_full_eight_label_edge', [row['edge'] for row in edges if row['positive_sufficient_bound']] == [[17, 19]])
    ck('chosen_head_lower', head == F(4431452026623492378483431, 924397893305270357144371200000)
       and head > F(1, 210000))
    tail = data625['large_owner_tail']
    E = F(tail['complete_tail_upper'])
    ck('only_large_owner_threshold', tail['threshold'] == 2**115 and tail['dyadic_start'] == 115)
    ck('complete_tail_formula', E == F(15, 1000) * F(4 * 117)**12 / 2**115
       == F(19740202146111572828188083, 495176015714152109959649689600))
    caps = {int(p): F(value) for p, value in data625['constants']['actual_head_caps'].items()}
    ck('ten_head_joint_caps_unchanged', caps == {3:F(2), 5:F(4,3), 7:F(7,5), 11:F(11,9),
       13:F(13,11), 17:F(17,15), 19:F(19,17), 23:F(5,3), 29:F(20,11), 31:F(2)})
    ck('head_caps_le_two', max(caps.values()) <= 2)
    V = 2**115
    ck('large_owner_cap', F(2 * (V - 1), V - 3) < 4)
    network_raw = raw - E
    network_head = alpha * network_raw
    ck('joint_release_tail_positive', network_raw > 0)
    ck('joint_release_tail_head_lower', network_head ==
       F(35599326215723254740897196090524662687, 9292674124624301561266911535067194982400000)
       and network_head > F(1, 262000))
    result = {
        'schema': 'secondary-pair-endpoint-release-v1', 'status': 'PASS',
        'scope': {
            'head': 'Exactly the Report626 literal head, arbitrary pure phases and free seven-star roots; its restricted mixed inventory remains.',
            'release': 'Any fixed subset S of the eighty listed secondary numerical labels may have arbitrary independently chosen first roots. The four primary labels and every unreleased secondary label at each edge share one endpoint pair.',
            'source': 'Keep each reference edge rectangle as an auxiliary deletion, then impose all actual released events on that same source. No actual original constraint is dropped.',
            'quantifiers': 'Every allowed finite original family with globally fixed residues and distinct numerical moduli; missing labels cost zero. The displayed B(S) sums every permitted label and is uniform in presence and phases.',
            'large_owners': 'Optional only-large-owner network: all owners >=2^115, fixed finite unions of smaller head or earlier owner parents, pure powers and assigned mixed inventories only; no small owners, private blocks or Type I blocks.',
        },
        'dependencies': PINS,
        'inherited_source_dependencies': data626['local_intervals']['dependencies'],
        'constants': {'gamma': str(gamma), 'alpha': str(alpha), 'c': str(c), 'g': str(g),
                      'central_caps': {f'{a},{b}': str(v) for (a,b),v in central.items()},
                      'central_cap_sum': str(sum(central.values())), 'E115': str(E)},
        'subset_criterion': {'B': 'Sum raw_deletion_cap over S (or only its present originals).',
                             'head': 'gamma - g B(S) > 0 implies head Haar mass >= alpha (gamma - g B(S)).',
                             'only_large_owner_network': 'gamma - g B(S) - E115 > 0 implies extendible head Haar mass > alpha (gamma - g B(S) - E115).',
                             'unit_term': 'The coefficient g=1-c uses the complete squared query load INCLUDING UNIT. Mere moment monotonicity gives only cost delta.'},
        'labels': sorted(labels, key=lambda row: row['modulus']),
        'per_edge': edges, 'per_orientation': orientations,
        'eight_17_19': {**chosen, 'head_lower': str(head), 'head_strict_lower': '1/210000',
                       'network_raw_lower': str(network_raw), 'extendible_head_lower': str(network_head),
                       'extendible_head_strict_lower': '1/262000',
                       'full_network_density_strict_lower': '1/(262000 Q_off)'},
        'all_eighty': {'raw_deletion_cap': str(total_raw), 'gate_fee': str(total_fee),
                       'remaining_gate_lower': str(gamma - total_fee),
                       'positive_sufficient_bound': False,
                       'meaning': 'Failure of this additive sufficient bound only; no covering counterexample or upper bound on actual survival.'},
        'checks': CHECKS, 'check_count': len(CHECKS),
        'inherited_large_scans_rerun': False, 'new_lean_verification': False,
        'producer_sha256': digest(Path(__file__)),
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'check_count', 'eight_17_19', 'all_eighty']}, indent=2))


if __name__ == '__main__':
    main()
