#!/usr/bin/env python3
"""Independent exact verifier for Report681; stdlib only, no producer imports.

The inherited680 source table and dual witness are hash-pinned. Selector
factors are rebuilt as rational measures, with the weak deep factors kept as
four separate debit components. No1350-scaled producer representation is used.
The conclusion concerns the fixed source and the current all-depth supremum
query envelope, not every source or outside-dependent retention field.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import gcd, lcm
from pathlib import Path

PINS = {
    'clustered_global_phase_fixture.json': '4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
    'clustered_exact_actual_source.json': '31d7d2b20a4a72805222c7c7782506d3b9babd37c36f7cfb0d287260ba4b1905',
    'clustered_actual_boundary_gate_witness.json': '887cd5d78038e2375ebd63d6d43c4c1e954f848f76d4fc145bc0f44b210c32a1',
    'remaining33_global_root_exclusion_certificate.json': 'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4',
}
EXPECTED_U4 = F('970010484735106794674517936604944094739/1220679392690694067983395343197798400000000')
EXPECTED_LIMIT = F('2257007011560668856122899/411282767102882161859179315200000000')
TARGET = F(193, 100000)
I = (0, 1, 2, 4, 5)
J = tuple(m for m in range(20) if m != 5)
LIVE = [(l, m) for l in I for m in J if not (l < 3 and m < 5)]
G = F(200163067, 201247200)
COUNTS = {}


def check(ok, label):
    COUNTS[label] = COUNTS.get(label, 0) + 1
    if not ok:
        raise RuntimeError('independent check failed: ' + label)


def weight3(l):
    return F(1 if l == 4 else 2, 9)


def weight5(m):
    return F(3 if m == 10 else 4, 75)


def selector(status, address, leaf, radix, mass, deep_scale):
    # The root label is the quotient of the reference leaf index by p.
    if status == 0:
        return mass
    if status == 1:
        return mass if leaf // radix == address else F(0)
    if status == 2:
        return mass if leaf == address else F(0)
    return deep_scale if leaf == address else F(0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--report', type=Path, default=None,
                        help='Optional producer JSON to compare, never imported code')
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    data = {}
    for name, expected_hash in PINS.items():
        raw = (args.directory / name).read_bytes()
        check(hashlib.sha256(raw).hexdigest() == expected_hash, 'input SHA256 pins')
        data[name] = json.loads(raw)
    fixture = data['clustered_global_phase_fixture.json']
    source = data['clustered_exact_actual_source.json']
    witness = data['clustered_actual_boundary_gate_witness.json']
    coeff_record = data['remaining33_global_root_exclusion_certificate.json']
    check(witness['corner'] == [4, 10], 'fixed weak corner')
    check(source['source_fixture_sha256'] == PINS['clustered_global_phase_fixture.json'], 'source provenance')
    check(witness['source_sha256'] == {k: v for k, v in PINS.items() if k != 'clustered_actual_boundary_gate_witness.json'}, 'witness provenance')
    check([tuple(c) for c in witness['coordinates']] == LIVE, 'ordered80 coordinates')
    check(len(LIVE) == 80, 'coordinate count')
    check(sum(map(weight3, I), F(0)) == 1, 'ternary mass normalization')
    check(sum(map(weight5, J), F(0)) == 1, 'quinary mass normalization')
    cells = source['cells']
    check([tuple(c['cell']) for c in cells] == LIVE, 'source cell ordering')
    H = []
    for c in cells:
        table = [[F(x) for x in row] for row in c['H_by_support_and_root7']]
        check(len(table) == 32, '32 support responses per cell')
        check(table[0] == [F(c['source_mass'])], 'empty query equals source mass')
        for t, row in enumerate(table):
            check(len(row) == (6 if t & 1 else 1), 'global7 root query arity')
            for x in row:
                check(x >= 0, 'nonnegative source query response')
        H.append(table)
    source_entries = [weight3(l) * weight5(m) * H[c][0][0] for c, (l, m) in enumerate(LIVE)]
    source_mass = sum(source_entries, F(0))
    check(source_mass == F('305684996597/646498195200'), 'unchanged common source mass')
    coefficients = list(map(F, coeff_record['combined512_coefficients']))
    check(len(coefficients) == 512, 'complete512 coefficients')
    for bit, q in enumerate((11, 13, 17, 19), 1):
        coefficients[32 * 9 + (1 << bit)] += G / (q * (q - 2))
    dual = {int(k): terms for k, terms in witness['generic_dual'].items()}
    check(set(dual) == {k for k, value in enumerate(coefficients) if value}, 'dual covers every positive fee group')
    denominator = witness['dual_denominator']
    check(denominator == 2**32, 'dual dyadic denominator')
    # Component index has bit1 for weak3/deep and bit0 for weak5/deep.
    debit = [[F(0) for _ in range(4)] for _ in LIVE]
    term_count = 0
    for group, terms in dual.items():
        mode, support = divmod(group, 32)
        ex, ey = divmod(mode, 4)
        check(coefficients[group] > 0, 'positive dual budget')
        check(sum(term['numerator'] for term in terms) == denominator, 'whole query convex budget')
        for term in terms:
            term_count += 1
            numerator, root, left, right = (term[x] for x in ('numerator', 'root7', 'left', 'right'))
            check(type(numerator) is int and numerator >= 0, 'nonnegative integral dual weight')
            check(root in range(1, 7), 'one legal global7 query')
            check(left in ((0,), (0, 1), I, I)[ex], 'legal ternary selector')
            check(right in ((0,), (0, 1, 2, 3), J, J)[ey], 'legal quinary selector')
            fee = coefficients[group] * F(numerator, denominator)
            for c, (l, m) in enumerate(LIVE):
                s3 = selector(ex, left, l, 3, weight3(l), F(1))
                s5 = selector(ey, right, m, 5, weight5(m), F(4, 5))
                k = 2 * int(ex == 3 and l == 4) + int(ey == 3 and m == 10)
                outside = H[c][support][root - 1 if support & 1 else 0]
                debit[c][k] += fee * s3 * s5 * outside
    check(term_count == 564, 'inherited564 common-source terms')

    def residuals(gamma3, gamma5):
        factors = (F(1), gamma5, gamma3, gamma3 * gamma5)
        return [G * mass - sum((a * b for a, b in zip(parts, factors)), F(0))
                for mass, parts in zip(source_entries, debit)]

    generic_upper = sum((max(F(0), r) for r in residuals(F(1), F(1))), F(0))
    check(generic_upper == EXPECTED_LIMIT, 'generic limit exact reconstruction')
    originals = fixture['actual_originals']
    check(len(originals) == 101, 'unchanged101 originals')
    check(source['actual_originals'] == originals[:91], 'same91 mixed source phases')
    source_family = source['actual_originals'] + source['outside_pure_originals'] + source['central_pure_and_15']
    check([(t['modulus'], t['residue']) for t in source_family] ==
          [(t['modulus'], t['residue']) for t in originals], 'same101 source phase family')
    for item in originals:
        modulus, residue = item['modulus'], item['residue']
        check(type(modulus) is int and modulus > 1 and modulus % 2 == 1, 'original legal odd modulus')
        check(0 <= residue < modulus, 'original residue range')
        for p in (3, 5):
            check(modulus % (p**3) != 0, 'old predicates ignore higher central digits')
    depth_results = []
    final_residuals = None
    for n in range(5):
        additions = []
        capacities = []
        gammas = []
        for p, weak, weight, density in ((3, 4, F(1, 9), F(2)), (5, 2, F(1, 25), F(4, 3))):
            deleted = []
            for height in range(3, n + 3):
                residue = weak + p*p * sum(p**k for k in range(height - 3))
                entry = {'modulus': p**height, 'residue': residue, 'prime': p, 'height': height}
                deleted.append(entry)
                additions.append(entry)
                check(residue % (p*p) == weak, 'deletions stay inside weak leaf')
                digits = [(residue // p**k) % p for k in range(2, height)]
                check(digits == [1] * (height - 3) + [0], 'actual higher deletion word')
            for a in deleted:
                for b in deleted:
                    if a['modulus'] < b['modulus']:
                        check(a['residue'] != b['residue'] % a['modulus'], 'same-prime deletion cylinders disjoint')
            capacity = F(1, p*p) - sum((F(1, t['modulus']) for t in deleted), F(0))
            check(capacity > 0, 'positive actual surviving capacity')
            height = max(3, n + 2)
            total = p**height
            surviving_count = sum(all(x % t['modulus'] != t['residue'] for t in deleted)
                                  for x in range(weak, total, p*p))
            check(F(surviving_count, total) == capacity, 'capacity by finite residue enumeration')
            query = weak + 2*p*p
            for t in deleted:
                check(query % gcd(p**3, t['modulus']) != t['residue'] % gcd(p**3, t['modulus']),
                      'entire child2 query cylinder survives all deletions')
            # This one child3 separation implies every deeper cylinder on the
            # fixed integer ray survives, not merely the finite checks below.
            for e in range(3, 10):
                check(query % (p**e) == (query % (p**(e + 1))) % (p**e), 'coherent nested query residues')
                mass = (weight / capacity) * F(1, p**e)
                check(mass / (density * F(1, p**e)) == weight / (density * capacity),
                      'normalized sharp capacity along fixed query ray')
            gamma = weight / (density * capacity)
            gammas.append(gamma)
            capacities.append({'prime': p, 'weak_leaf_residue': weak, 'haar_capacity': str(capacity),
                               'fixed_leaf_mass': str(weight), 'reference_density': str(density),
                               'gamma': str(gamma), 'nested_query_residue': query})
        family = originals + additions
        check(family[:101] == originals, '101 phases retained exactly')
        check(len(family) == 101 + 2*n, 'actual original family count')
        check(len({t['modulus'] for t in family}) == len(family), 'all numerical moduli distinct')
        check(all(t['modulus'] > 1 and t['modulus'] % 2 and 0 <= t['residue'] < t['modulus'] for t in family),
              'whole family valid odd congruences')
        rs = residuals(*gammas)
        upper = sum((max(F(0), r) for r in rs), F(0))
        depth_results.append({'n': n, 'original_count': len(family), 'capacities': capacities,
                              'gamma3': str(gammas[0]), 'gamma5': str(gammas[1]),
                              'upper': str(upper), 'below_target': upper < TARGET,
                              'added_higher_pure_originals': additions})
        if n == 4:
            final_residuals = rs
            check(upper == EXPECTED_U4, 'exactU4 second implementation')
            check(gammas == [F(81, 82), F(1875, 1876)], 'exact weak leaf cap ratios')
            check(upper < TARGET, 'strict obstruction threshold')
            avoiding = 432297622003171927
            for t in family:
                check(avoiding % t['modulus'] != t['residue'], 'actual integer avoids each109 original')
            period = lcm(*(t['modulus'] for t in family))
            check(period == 1190750449028765625, 'actual109 common period')
    check([d['below_target'] for d in depth_results] == [False, False, False, False, True],
          'first tested n crossing only')
    # Complete9q² fee uses mode8 (whole5) instead of mode9 (root5).
    # For nonnegative cell fields a whole5 query dominates each root5 query.
    for l, m in LIVE:
        for left in I:
            for right in range(4):
                leaf3 = selector(2, left, l, 3, weight3(l), F(1))
                whole5 = selector(0, 0, m, 5, weight5(m), F(4, 5))
                root5 = selector(1, right, m, 5, weight5(m), F(4, 5))
                check(leaf3 * whole5 >= leaf3 * root5, 'full inventory screen pointwise domination')
    chosen = [{'cell': list(c), 'value': str(r)} for c, r in zip(LIVE, final_residuals)]
    if args.report is not None:
        reported = json.loads(args.report.read_text())
        check(reported['chosen_residuals'] == chosen, 'all80 residuals agree independently')
        for ours, theirs in zip(depth_results, reported['depth_results']):
            for key in ('n', 'original_count', 'gamma3', 'gamma5', 'upper', 'below_target'):
                check(ours[key] == theirs[key], 'each reported depth result agrees')
        check(len(reported['depth_results']) == len(depth_results), 'reported depth count')
    result = {
        'schema': 'clustered681-independent-check-v1', 'status': 'PASS',
        'new_lean_verification': False, 'optimizer_used': False,
        'method': 'Pinned680 common-source responses and dual budgets; direct rational selectors; four weak-deep debit components; stdlib Fraction arithmetic. No producer code read or imported.',
        'input_sha256': PINS, 'program_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'source_mass': str(source_mass), 'common_dual_term_count': term_count,
        'target': str(TARGET), 'generic_limit_upper': str(generic_upper),
        'depth_results': depth_results, 'chosen_residuals': chosen,
        'actual_avoiding_integer': 432297622003171927, 'actual_crt_modulus': 1190750449028765625,
        'checks': COUNTS, 'check_count': sum(COUNTS.values()),
        'scope': 'Fixed109-original source, 101 phases unchanged. Every coarse80-cell retention field0<=theta<=1 under the current all-height supremum query envelope has gate at mostU4. The ordinary finite-partition lemma separately extends to finite-depth central-only fields. Does not bound outside-dependent fields, changed sources, or depth-specific fees; not a covering counterexample.'
    }
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'status': 'PASS', 'check_count': result['check_count'], 'upper': str(EXPECTED_U4),
                      'upper_decimal': float(EXPECTED_U4), 'target': str(TARGET), 'output': str(output)}, indent=2))


if __name__ == '__main__':
    main()
