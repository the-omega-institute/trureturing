"""Finite controls for the source-branch rearrangement and plateau fields.

Reads only the adjacent pinned certificates and one explicit source program.
The all-depth theorem is the companion ordinary proof, not finite sampling.
No geometry generation, repository scan, subprocess, or Lean verification.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pinned(path, digest):
    raw = path.read_bytes()
    need(sha256(raw).hexdigest() == digest, 'pinned input: ' + path.name)
    return raw


LEAVES = (4, 13, 22, 7, 16, 25)
A = (0, 1, 4, 4, 4, 4)
B = (0, 4, 4, 1, 4, 4)
POS = (0, 6, 6, 6, 6, 6)
K = ((11, 11, 9, 6, 3), (28, 28, 28, 28, 25), (23, 23, 23, 23, 21))
MODS = (3, 5, 9, 15)
DOMAIN = tuple(product((1, 2), range(1, 5), (2, 4, 5, 7, 8), (1, 4, 7, 8, 11, 13, 14)))
LAYOUTS = tuple(product(range(-1, 2), ((-1, -1),) + tuple(product(range(2), range(2))),
                       range(-1, 6), ((-1, -1),) + tuple(product(range(6), range(2)))))


def aligned(xi):
    return xi[:2] + (7 if xi[2] == 4 else xi[2],) + xi[3:]


def score(weights, bg, field, coefficients, fixed, layout):
    h9, (h45, j45), h27, (h135, j135) = layout
    c9, c45, c27, c135, cfix = coefficients
    return sum(weights[l] * field[j] * max(0, bg[j] + cfix * (l // 3 == fixed)
               + c9 * (l // 3 == h9) + c45 * (l // 3 == h45 and j == j45)
               + c27 * (l == h27) + c135 * (l == h135 and j == j135))
               for l, j in product(range(6), range(2)))


def moved(layout):
    h9, (h45, j45), h27, (h135, j135) = layout
    return (1 if h9 >= 0 else -1, (1 if h45 >= 0 else -1, j45),
            4 if h27 >= 0 else -1, (4 if h135 >= 0 else -1, j135))


def verify(root):
    face_hash = '33ca20af85a421863ca0c3865fd903f2be1744b824aed951369ffbcaa0e9ca98'
    face = json.loads(pinned(root / 'face-tube.json', face_hash))
    geometry_hash = 'd0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
    pinned(root.parent / 'missing23-eta14' / 'geometry_replay.py', geometry_hash)
    need(F(face['uniform_face_margin_lower']) == F(116, 15625), 'old common margin')
    need(A[:3] == (0, 1, 4) and (sum(B[:3]), sum(B[3:])) == (8, 9), 'zero3 source sums')
    need(max(A[:3]) == max(A[3:]) == max(B[:3]) == max(B[3:]) == 4, 'common source peaks')
    need((sum(A[:3]), sum(A[3:])) == (5, 12), 'old source sums')
    need((sum(POS[:3]), sum(POS[3:])) == (12, 18), 'positive3 source sums')

    # All shared two-column head layouts, including heads outside these branches.
    parameters = (
        ((-16, -4), (1, 3), (7, 5, 4, 9, 6)),
        ((-3, 2), (0, 5), (1, 8, 0, 2, 3)),
        ((0, 0), (1, 1), (0, 0, 0, 0, 0)),
        ((4, -9), (4, 0), (11, 0, 5, 3, 2)),
        ((-20, 1), (2, 7), (3, 2, 17, 1, 1)),
        ((7, 13), (3, 4), (2, 4, 5, 0, 7)),
    )
    local_checks = 0
    minimum_move = minimum_source = None
    digest = sha256()
    for positive, fixed, (bg, field, coefficients) in product((False, True), range(-1, 2), parameters):
        wa, wb = (POS, POS) if positive else (A, B)
        target_fixed = -1 if fixed == -1 else 1
        for layout in LAYOUTS:
            after = moved(layout)
            before = score(wb, bg, field, coefficients, fixed, layout)
            middle = score(wb, bg, field, coefficients, target_fixed, after)
            result = score(wa, bg, field, coefficients, target_fixed, after)
            need(before <= middle <= result, 'one layout move and source comparison')
            dm, ds = middle - before, result - middle
            minimum_move = dm if minimum_move is None else min(minimum_move, dm)
            minimum_source = ds if minimum_source is None else min(minimum_source, ds)
            digest.update(f'{int(positive)},{fixed},{before},{middle},{result};'.encode())
            local_checks += 1

    crt = {(x % 27, x % 5): x for x in range(135)}
    carrier = tuple(x for x in range(135) if x % 3 and x % 9 != 1 and x % 27 != 4
                    and x % 5 and x % 15 != 2 and x % 45 != 8)
    need(len(carrier) == 44, 'actual source carrier')
    count = lambda x, xi: sum(x % m == r for m, r in zip(MODS, xi))
    fields = {xi: tuple(tuple(table[count(x, xi)] for x in range(135)) for table in K) for xi in DOMAIN}
    xi0 = tuple(xi for xi in DOMAIN if xi[2] in (2, 5, 8))
    excluded = tuple(xi for xi in DOMAIN if xi[0] == 1 and xi[2] in (4, 7)
                     and xi[3] % 3 == 1 and xi[3] % 5 == xi[1])
    extended = tuple(xi for xi in DOMAIN if xi not in excluded)
    need((len(DOMAIN), len(xi0), len(excluded), len(extended)) == (280, 168, 8, 272), 'physical domains')
    finite_field_checks = 0
    for stage, labels in enumerate((xi0, extended, extended)):
        for xi in labels:
            zeta = aligned(xi)
            need(zeta in labels, 'alignment stays in declared domain')
            need(fields[xi][stage] == fields[zeta][stage], 'one alignment preserves the entire charged field')
            finite_field_checks += 135
            for leaf, j in product(range(3), range(1, 5)):
                x, y = crt[4 + 9 * leaf, j], crt[7 + 9 * leaf, j]
                need(fields[xi][stage][x] == fields[xi][stage][y], 'common field between root1 branches')
                finite_field_checks += 1
    for xi in excluded:
        for stage in (1, 2):
            need(fields[xi][stage] != fields[aligned(xi)][stage] if xi[2] == 4
                 else fields[xi][stage] != fields[xi[:2] + (4,) + xi[3:]][stage], 'excluded plateau boundary is real')
    # The first7 field has no such plateau extension at the same labels.
    xi = (2, 1, 4, 8)
    need(xi in extended and fields[xi][0] != fields[aligned(xi)][0], 'first7 cannot use the11/13 plateau')

    # Three actual positive-comparison components where the same local move fails.
    # This checks full44-cell responses, not a maximum over all head layouts.
    obstructions = []
    current_xi = (2, 2, 2, 8)
    moduli = (3, 9, 27, 5, 15, 45, 135)
    heads = (2, 2, 2, 2, 11, 11)
    x4, x7 = crt[13, 1], crt[7, 1]
    need((x4, x7) == (121, 61) and x4 in carrier and x7 in carrier, 'native obstruction cells')
    for charged, p, threshold, m, u, xi, expected in (
        (0, 11, 4, 1, 3, (2, 1, 7, 11), F(-11, 140)),
        (1, 13, 4, 2, 1, (1, 1, 7, 1), F(-1, 10)),
        (2, 17, 8, 4, 1, (1, 1, 7, 1), F(-11, 65)),
    ):
        c = F(p - 1, p)
        coefficients = (m - c, m - c, m * (1 + u), m - c,
                        m - c, m, m * (1 + u))
        need(min(coefficients) >= 0, 'nonnegative complete obstruction coefficients')
        values = []
        for leaf in (x4, x7):
            total = F(0)
            for x in carrier:
                quinary = F(4, 5) - F(x % 5 == 1, 4) - F(x % 3 == 2 and x % 5 == 1, 5)
                field = F(K[charged][count(x, xi)], (14, 33, 26)[charged])
                load = m - threshold + c * count(x, current_xi)
                load += sum(a * (x % g == r) for a, g, r in zip(coefficients, moduli, heads + (leaf,)))
                total += quinary * field * max(0, load)
            values.append(total)
        need(values[1] - values[0] == expected < 0, 'full44-cell local head-move obstruction')
        obstructions.append({'charged_prime': (7, 11, 13)[charged], 'charged_label': xi,
            'current_prime': p, 'current_label': current_xi, 'multiplier': m,
            'positive3_depth': u, 'extra5_depth': 0, 'from_cell': x4, 'to_cell': x7,
            'complete_component_responses': list(map(str, values)), 'local_move_change': str(expected)})

    per_stage = (len(xi0), len(extended), len(extended), 280, 280, 280)
    full_count = 280 ** 6
    new_count = 1
    for n in per_stage:
        new_count *= n
    prefix = next(v for v in face['prefix_certificates_and_negative_controls'] if (v['H3'], v['H5']) == (12, 8))
    return {
        'scope': 'Fixed source chart and five-leaf face; ordinary all-depth comparison proof required. Finite controls only, no full geometry or new Lean verification.',
        'face_certificate_sha256': face_hash, 'geometry_source_sha256': geometry_hash,
        'source_leaf_order': LEAVES, 'weight_unit': '1/6', 'A': A, 'B': B, 'positive3': POS,
        'local_parameter_cases': 2 * 3 * len(parameters), 'layouts_per_case': len(LAYOUTS),
        'local_layout_checks': local_checks, 'local_values_sha256': digest.hexdigest(),
        'minimum_layout_move_gain': minimum_move, 'minimum_source_move_gain': minimum_source,
        'asymmetric_field_local_obstructions': obstructions,
        'field_incidence_checks': finite_field_checks, 'excluded11_or13_labels': excluded,
        'certified_physical_labels_per_stage': per_stage, 'certified_physical_tuples': new_count,
        'complete_physical_tuples': full_count, 'fraction_of_full_domain': str(F(new_count, full_count)),
        'earlier_all_six_fixed_domain': 168 ** 6, 'last_three_unrestricted_domain': 168 ** 3 * 280 ** 3,
        'uniform_face_margin_lower': face['uniform_face_margin_lower'],
        'raw_tube_radius': face['raw_tube_radius'], 'tube_slack_lower': face['tube_slack_lower'],
        'finite_prefix_conditions': prefix['additional_phase_conditions'], 'prefix_slack_lower': prefix['slack_lower'],
        'boundary': 'First7 modulo9 is restricted to2/5/8; each11/13 excludes8 plateau-breaking labels. Other source charts/budgets and unrestricted global forcing are not proved.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    print(json.dumps(verify(args.package), sort_keys=True, indent=2))
