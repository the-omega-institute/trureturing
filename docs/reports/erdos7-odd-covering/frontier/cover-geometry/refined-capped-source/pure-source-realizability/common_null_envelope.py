"""Common225-cylinder envelope for four jointly chosen selected phases.

The check uses one225 carrier and12 declared reference maps. It does not
enumerate phase quadruples, optimize sources, run an LP, or verify Lean.
"""
import argparse
from collections import Counter
import json
from math import lcm, prod
from pathlib import Path

FREE = (15, 45, 75, 225)
SELECTED = (15, 21, 45, 33, 35, 39, 63, 51, 57, 55, 105, 75,
            69, 65, 99, 77, 85, 117, 95, 165, 91, 147, 225)
PERIOD = 225


def exponent(m, p):
    e = 0
    while m % p == 0:
        e += 1
        m //= p
    return e


def crt(parts):
    value, modulus = 0, 1
    for a, n in parts:
        if n > 1:
            value += modulus * (((a - value) * pow(modulus, -1, n)) % n)
            modulus *= n
    return value % modulus


def transport(m, a, reference):
    """One common prime-tree map, applied to any actual numerical label."""
    ell, colour = reference % 9, reference % 5
    e3, e5 = exponent(m, 3), exponent(m, 5)
    p3, p5 = 3 ** e3, 5 ** e5
    a3, a5 = a % p3, a % p5
    if e3 >= 2:
        leaf = a3 % 9
        a3 += {ell: 2, 2: ell}.get(leaf, leaf) - leaf
    if e5:
        digit = a5 % 5
        a5 += {colour: 1, 1: colour}.get(digit, digit) - digit
    other = m // (p3 * p5)
    return crt(((a3, p3), (a5, p5), (a % other, other)))


def cylinder(m, a):
    if PERIOD % m != 0:
        raise ValueError('label does not divide common225 period')
    return set(range(a % m, PERIOD, m))


def allowed_phases(m, envelope):
    # The complement projects to exactly the phases whose whole cylinders
    # are NOT contained in the envelope. This retains union containment.
    prohibited = {x % m for x in set(range(PERIOD)) - envelope}
    return set(range(m)) - prohibited


def compute(certificate):
    checks = 0

    def require(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(message)

    require(certificate['schema'] == 'e7-common-null-envelope-v1', 'schema')
    records = certificate['actual_reference_family']
    family = dict(records)
    require(len(records) == len(family) == 25, 'distinct25 actual numerical labels')
    require(set(family) == {3, 9, *SELECTED}, 'reference selected inventory')
    for m, a in family.items():
        require(type(m) is int and type(a) is int and m > 1 and m % 2 and 0 <= a < m, 'legal reference original')
        if m in (3, 9, 45):
            require(a == {3: 0, 9: 1, 45: 11}[m], 'literal reference anchor')
        else:
            e = exponent(m, 3)
            require(e in (0, 1, 2) and a % (m // (3 ** e)) == 0, 'complete nonternary reference')
            if e:
                require(a % (3 ** e) == (1 if e == 1 else 4), 'reference ternary role')
    fixed = {m: a for m, a in family.items() if m not in FREE}
    require(len(fixed) == 21, '19 mixed originals plus two anchors')
    require(tuple(certificate['free_labels']) == FREE, 'four unchanged numerical slots')
    require(certificate['common_period'] == PERIOD, 'common carrier')

    references = [r for r in range(45) if r % 9 in (2, 5, 8) and r % 5 != 0]
    require(references == certificate['references'], '12 common reference choices')
    base = cylinder(3, 0) | cylinder(9, 1) | cylinder(15, 10)
    bsets = {
        15: {a for a in range(15) if a % 3 == 0 or a == 10},
        45: {a for a in range(45) if a % 3 == 0 or a % 9 == 1 or a % 15 == 10},
        75: {a for a in range(75) if a % 3 == 0 or a % 15 == 10},
        225: {a for a in range(225) if a % 3 == 0 or a % 9 == 1 or a % 15 == 10}}
    for m in FREE:
        require(allowed_phases(m, base) == bsets[m], 'base cylinder-containment formula')
    require([len(bsets[m]) for m in FREE] == certificate['base_phase_counts'] == [6, 22, 30, 110], 'base counts')
    envelopes = {r: base | cylinder(45, r) for r in references}
    allowed = {}
    for r in references:
        current = {m: allowed_phases(m, envelopes[r]) for m in FREE}
        require(current[15] == bsets[15], '15 unaffected by one root2 leaf')
        require(current[75] == bsets[75], '75 requires a whole ternary root')
        require(current[45] == bsets[45] | {r}, '45 reference addition')
        require(current[225] == bsets[225] | set(range(r, 225, 45)), 'five whole225 descendants')
        require([len(current[m]) for m in FREE] == certificate['fixed_reference_phase_counts'] == [6, 23, 30, 115], 'fixed-reference counts')
        allowed[r] = current
        for m, a in fixed.items():
            require(transport(m, a, r) == a, 'common map fixes every one of21 actual cylinders')
        images = {transport(PERIOD, x, r) for x in range(PERIOD)}
        require(len(images) == PERIOD, 'one common carrier bijection')
        require({transport(PERIOD, x, r) for x in envelopes[r]} == envelopes[11], 'same reference envelope transported')
        for m in FREE:
            require(all(transport(PERIOD, x, r) % m == transport(m, x % m, r) for x in range(PERIOD)),
                    'all four numerical partitions commute with common transport')

    def reference_options(phases):
        return [r for r in references if all(phases[m] in allowed[r][m] for m in FREE)]

    possible45 = set().union(*(allowed[r][45] for r in references))
    possible225 = set().union(*(allowed[r][225] for r in references))
    per45 = {a: set().union(*(allowed[r][225] for r in references if a in allowed[r][45])) for a in possible45}
    histogram = Counter(len(values) for values in per45.values())
    require(dict(histogram) == {170: 22, 115: 12}, 'joint225 choices depend on actual45 phase')
    joint_pairs = sum(len(values) for values in per45.values())
    require(joint_pairs == certificate['joint_45_225_count'] == 5120, 'same-reference joint pair count')
    joint_quadruples = len(bsets[15]) * len(bsets[75]) * joint_pairs
    separate_product = len(bsets[15]) * len(possible45) * len(bsets[75]) * len(possible225)
    require(joint_quadruples == certificate['joint_quadruple_count'] == 921600, 'joint quadruple count')
    require(separate_product == certificate['separate_product_count'] == 1040400, 'separate-reference overcount')
    require(separate_product > joint_quadruples, 'nontrivial joint-reference constraint')

    # One full CRT witness avoids every actual original in each declared
    # finite control. It is not asserted to survive arbitrary extensions.
    full_period = lcm(*family)
    other_period = full_period // PERIOD
    witness = crt(((2, PERIOD), (1, other_period)))
    require(0 <= witness < full_period and witness % PERIOD == 2, 'finite full-carrier survivor witness')
    fixture_results = []
    for fixture in certificate['fixtures']:
        phases = dict(zip(FREE, fixture['phases']))
        require(len(fixture['phases']) == len(FREE), 'one phase per selected numerical label')
        require(all(type(a) is int and 0 <= a < m for m, a in phases.items()), 'canonical actual phases')
        actual = fixed | phases
        require(set(actual) == set(family) and len(actual) == 25, 'no added or split numerical original')
        options = reference_options(phases)
        require(options == fixture['expected_references'], 'one reference for all four actual phases')
        per_label = {str(m): [r for r in references if phases[m] in allowed[r][m]] for m in FREE}
        for r in references:
            actual_union = set().union(*(cylinder(m, a) for m, a in phases.items()))
            require((actual_union <= envelopes[r]) == (r in options), 'actual joint union matches shared-reference test')
        require(all(witness % m != a for m, a in actual.items()), 'finite fixture has an explicit survivor')
        if fixture.get('nonjoint', False):
            require(all(per_label[str(m)] for m in FREE) and not options, 'individual transport does not imply a common reference')
        fixture_results.append({'name': fixture['name'], 'phases': fixture['phases'], 'references': options,
                                'per_label_references': per_label, 'finite_survivor': witness})

    return {'schema': certificate['schema'], 'checks': checks,
            'reference_phases': references,
            'base_allowed_phases': {str(m): sorted(bsets[m]) for m in FREE},
            'fixed_reference_phase_counts': [6, 23, 30, 115],
            'joint225_count_by45_group': {'base45_count': 22, 'choices_each': 170,
                                         'reference45_count': 12, 'choices_each_when_reference_fixed': 115},
            'joint_45_225_count': joint_pairs, 'joint_quadruple_count': joint_quadruples,
            'separate_product_count': separate_product,
            'separate_product_overcount': separate_product - joint_quadruples,
            'fixed_actual_label_count': len(fixed), 'actual_selected_mixed_label_count': len(SELECTED),
            'full_finite_witness_period': full_period, 'fixtures': fixture_results,
            'scope': 'Same-reference null-envelope application of801/810/820/822/823. Auxiliary exclusions are not actual labels. Complete actual-survivor normalizations, arbitrary finite old pure families and804 support/tail remain required. No LP, atlas recomputation or Lean verification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    local = Path(__file__).resolve().parent
    parser.add_argument('--certificate', type=Path, default=local / 'common_null_envelope_certificate.json')
    parser.add_argument('--result', type=Path, default=local / 'common_null_envelope.json')
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = compute(json.loads(args.certificate.read_text()))
    if args.write_result is None:
        if result != json.loads(args.result.read_text()):
            raise ValueError('retained result mismatch')
    else:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'checks': result['checks'], 'references': 12,
                      'joint_pairs': result['joint_45_225_count'],
                      'joint_quadruples': result['joint_quadruple_count']}, sort_keys=True))


if __name__ == '__main__':
    main()
