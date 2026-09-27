#!/usr/bin/env python3
"""A common law with an arbitrary centre and controlled full-law relabelling.

Report 421 proves the general all-phase interface and the all-height S_K
consumer with a single +2 central root child and four clean children.
Exact finite checks validate actual support, one common law,
prefix profiles, and the retained height-three rational certificate.
No optimizer, external package, or Lean certification is used here.
"""
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction as F
from itertools import permutations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import five_decay_root_mixture_obstruction as source_api
import prefix_local_row_transport as transport
import root_rectangle_second_moment as root_sources

family = source_api.family
ALPHA = F(50, 113)
PAIR_WEIGHT = F(21, 113)
REFERENCE_ROOT = F(446, 113)
REFERENCE_LIMIT = F(2595, 452)
SIMPLE_ERROR_CONSTANT = F(10625, 1017)


def profile_bound(height, law):
    """Sufficient all-original-phase bound, proved by depth-pair charging."""
    law = family.probability(height, law)
    records = []
    for j in range(height+1):
        pure, joint = family.prefix_masses(law, j)
        a = {r: max(m + joint.get((r, u), F()) for u, m in pure.items())
             for r in family.ROWS}
        z = {r: max((m for (s, _), m in joint.items() if s == r), default=F())
             for r in family.ROWS}
        records.append(max(a[r]+2*z[r] for r in family.ROWS))
    return tuple(records), sum(((2*j+1)*b for j, b in enumerate(records)), F())


def profile_slack_control():
    """Attaining law for the analytic seven-point profile obstruction."""
    source = {(r+1, c) for r, c in root_sources.edges(root_sources.TEMPLATES['B'])}
    law = {p: F(1 if p[1] == 1 else 2, 11) for p in source}
    profile, upper = profile_bound(1, law)
    family.need(profile == (F(20, 11), F(8, 11)) and upper == 4,
                'seven-point exact profile optimizer')
    family.need(profile[1] > F(2, 3), 'separate depth-one target must fail')
    return {'profile': profile, 'profile_upper': upper,
            'root_budget_gain': 2-profile[0],
            'weighted_depth_one_excess': 3*(profile[1]-F(2, 3))}


def reference_bound(height):
    family.integer(height, 1, 'height')
    return REFERENCE_ROOT + sum(((2*j+1)*(ALPHA/F(5**j)
                         + 3*(1-ALPHA)/F(3**j)) for j in range(2, height+1)), F())


def verify_interface(height, actual_source, full, pairs):
    """Check actual components before phases, with no centre row-balance rule."""
    family.integer(height, 1, 'height')
    actual_source = family.points(height, actual_source)
    full = family.probability(height, full)
    family.need(set(full) <= actual_source, 'full law has unsupported mass')
    family.need(type(pairs) is dict and set(pairs) == set(family.PAIRS),
                'the three non-row-one pair laws are required')
    checked_pairs = {}
    for pair in family.PAIRS:
        law = family.probability(height, pairs[pair])
        family.need(set(law) <= actual_source and all(r in pair for r, _ in law),
                    'pair law has unsupported or outside-row mass')
        family.need(all(y % 7 in (0,)+pair for _, y in law), 'pair root columns')
        family.need(all(y % 7 == 0 or r == y % 7 for r, y in law),
                    'private pair root must have its own row')
        root, _ = family.prefix_masses(law, 1)
        family.need(root == {c: F(1, 3) for c in (0,)+pair}, 'pair root weights')
        for j in range(1, height+1):
            pure, _ = family.prefix_masses(law, j)
            family.need(max(pure.values()) <= F(1, 3**j), 'pair prefix cap')
        checked_pairs[pair] = law
    full_root, _ = family.prefix_masses(full, 1)
    family.need(full_root == {c: F(1, 5) for c in range(5)}, 'full root weights')
    for j in range(1, height+1):
        pure, _ = family.prefix_masses(full, j)
        family.need(max(pure.values()) <= F(1, 5**j), 'full prefix cap')
    coupling = {(r, 1, y): w for (r, y), w in full.items()}
    relabel = transport.prefix_mismatch_profile(height, coupling)
    nu = family.mixture(height, [(ALPHA, full)]
                        + [(PAIR_WEIGHT, checked_pairs[p]) for p in family.PAIRS])
    family.need(set(nu) <= actual_source, 'common law has unsupported mass')
    error = ALPHA*relabel['uniform_layout_difference_bound']
    return {'law': nu, 'full_mismatch_profile': relabel['prefix_mismatch'],
            'transport_error': error, 'reference_upper': reference_bound(height),
            'all_phase_upper': reference_bound(height)+error}


def actual_components(height):
    source = source_api.source(height)
    full, pairs = family.actual_component_laws(height, source)
    return source, full, pairs


def actual_profile_formula(height):
    family.integer(height, 3, 'height')
    k = height
    values = [F(70*3**(k-3)-7, 5**k), F(25*3**(k-3)-7, 5**k)]
    values.extend(max(F(5*3**(k-j-1)), F(5*3**(k-j)-7, 2))/5**k
                  for j in range(2, k))
    values.append(F(1, 5**k))
    return tuple(values)


def analytic_bound(height):
    family.integer(height, 3, 'height')
    d = actual_profile_formula(height)
    exact_error = 3*ALPHA*sum(((2*j+1)*v for j, v in enumerate(d)), F())
    simple_error = SIMPLE_ERROR_CONSTANT*F(3, 5)**height
    family.need(exact_error <= simple_error, 'simple error must dominate exact profile')
    family.need(reference_bound(height) <= REFERENCE_LIMIT, 'reference tail limit')
    target = family.layout_api.default_target(height)
    return {'height': height, 'full_mismatch_profile': d,
            'profile_upper': reference_bound(height)+exact_error,
            'simple_upper': REFERENCE_LIMIT+simple_error,
            'target': target, 'simple_margin': target-REFERENCE_LIMIT-simple_error}


def root_controls():
    """Six vertices cover every allowed centre marginal by convexity."""
    summaries, checked = [], 0
    expected_table = ((446, 446, 425, 425), (368, 416, 360, 360),
                      (333, 353, 374, 325), (305, 318, 297, 353))
    for vertex in sorted(set(permutations((2, 1, 0)))):
        table = {(1, c): F(10, 113) for c in range(5)}
        for r in (2, 3, 4):
            table[r, r] = F(14, 113)
            if vertex[r-2]:
                table[r, 0] = F(7*vertex[r-2], 113)
        family.probability(1, table)
        maxima = defaultdict(F)
        for a, b, r, c in product(range(5), range(7), range(5), range(7)):
            phases = (0, a, b, c+7*((r-c)*3 % 5))
            literal = sum((w*family.layout_api.literal_layout_cost(1, phases, p)
                           for p, w in table.items()), F())
            direct = sum((w*(1+int(s == a)+int(y == b)+int(s == r and y == c))**2
                          for (s, y), w in table.items()), F())
            family.need(literal == direct, 'root CRT and indicator costs disagree')
            maxima[a, r] = max(maxima[a, r], literal)
            checked += 1
        family.need(max(maxima.values()) == REFERENCE_ROOT, 'robust centre root maximum')
        if vertex == (2, 1, 0):
            actual = tuple(tuple(113*maxima[a, r] for r in family.ROWS) for a in family.ROWS)
            family.need(actual == expected_table, 'root row-phase table')
        summaries.append({'centre_vertex_times_113': tuple(7*v for v in vertex),
                          'exact_root_maximum': max(maxima.values())})
    return {'literal_layouts': checked, 'vertices': summaries,
            'representative_row_phase_table_times_113': expected_table}


def height_three_law(record):
    fields = {'height', 'positive_points', 'integer_weights', 'denominator', 'profile_upper'}
    family.need(type(record) is dict and set(record) == fields, 'height-three record fields')
    family.need(type(record['height']) is int and record['height'] == 3, 'height-three height')
    raw = record['positive_points']
    family.need(type(raw) is list and raw and all(type(p) is list and len(p) == 2 for p in raw),
                'height-three literal point list')
    points = family.points(3, [tuple(p) for p in raw])
    ordered = [tuple(p) for p in raw]
    family.need(points <= source_api.source(3), 'height-three unsupported point')
    weights = record['integer_weights']
    denominator = family.integer(record['denominator'], 1, 'denominator')
    family.need(type(weights) is list and len(weights) == len(ordered)
                and all(type(w) is int and w > 0 for w in weights)
                and sum(weights) == denominator, 'height-three integer weights')
    law = family.probability(3, {p: F(w, denominator) for p, w in zip(ordered, weights)})
    profile, upper = profile_bound(3, law)
    family.need(type(record['profile_upper']) is str and str(upper) == record['profile_upper'],
                'height-three exact profile mismatch')
    family.need(family.layout_api.default_target(3)-upper > F(1, 13),
                'height-three uniform target margin failed')
    return law, {'height': 3, 'positive_points': len(law), 'denominator': denominator,
                 'profile': profile, 'profile_upper': upper,
                 'target_margin': family.layout_api.default_target(3)-upper}


def generic_controls():
    full = {(1 if c else 4, c): F(1, 5) for c in range(5)}
    pairs = {p: {(p[0], 0): F(1, 3), (p[0], p[0]): F(1, 3),
                  (p[1], p[1]): F(1, 3)} for p in family.PAIRS}
    source = set(full).union(*(set(law) for law in pairs.values()))
    result = verify_interface(1, source, full, pairs)
    _, profile = profile_bound(1, result['law'])
    checked = 0
    for phases in product(range(1), range(5), range(7), range(35)):
        literal = sum((w*family.layout_api.literal_layout_cost(1, phases, p)
                       for p, w in result['law'].items()), F())
        family.need(literal <= result['all_phase_upper'] and literal <= profile,
                    'generic all-phase upper failed')
        checked += 1
    bad_support = source - {next(iter(full))}
    bad_private = deepcopy(pairs)
    bad_private[(2, 3)][3, 2] = bad_private[(2, 3)].pop((2, 2))
    bad_weights = deepcopy(pairs)
    bad_weights[(2, 3)][2, 0] += F(1, 12)
    bad_weights[(2, 3)][2, 2] -= F(1, 12)
    bad_full = {(r, (y+1) % 7): w for (r, y), w in full.items()}
    lifted_full = {(r, y): w for (r, y), w in full.items()}
    lifted_pairs = deepcopy(pairs)
    tests = [
        ('boolean_height', lambda: verify_interface(True, source, full, pairs)),
        ('unsupported_full', lambda: verify_interface(1, bad_support, full, pairs)),
        ('private_wrong_row', lambda: verify_interface(1, source | {(3, 2)}, full, bad_private)),
        ('pair_root_weights', lambda: verify_interface(1, source, full, bad_weights)),
        ('full_root_weights', lambda: verify_interface(1, source | set(bad_full), bad_full, pairs)),
        ('deeper_prefix_cap', lambda: verify_interface(2, source, lifted_full, lifted_pairs)),
    ]
    rejected = []
    for name, operation in tests:
        try:
            operation()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('malformed interface accepted: '+name)
    return {'literal_layouts': checked, 'rejected': rejected}


def self_check():
    with Path(__file__).with_name('single_surplus_source_height_three.json').open() as stream:
        record = json.load(stream)
    _, small = height_three_law(record)
    bad_records = []
    for key, value in (('denominator', record['denominator']+1),
                       ('profile_upper', str(F(record['profile_upper'])+1))):
        bad = deepcopy(record)
        bad[key] = value
        try:
            height_three_law(bad)
        except ValueError:
            bad_records.append(key)
        else:
            raise ValueError('malformed finite certificate accepted: '+key)
    expected = {4: F(17488, 3051), 5: F(733456, 127125),
                6: F(876619, 151875), 7: F(494841743, 85809375)}
    finite = [small]
    for k, value in expected.items():
        source, full, pairs = actual_components(k)
        checked = verify_interface(k, source, full, pairs)
        family.need(checked['full_mismatch_profile'] == actual_profile_formula(k),
                    'actual full mismatch profile differs from formula')
        profile, upper = profile_bound(k, checked['law'])
        target = family.layout_api.default_target(k)
        family.need(upper == value and target-upper > F(1, 13),
                    'fixed common law finite uniform target margin')
        finite.append({'height': k, 'source_points': len(source), 'profile': profile,
                       'profile_upper': upper, 'target_margin': target-upper})
    threshold = analytic_bound(8)
    family.need(threshold['simple_margin'] == F(148881233, 1853482500) > F(2, 25),
                'all-height threshold arithmetic')
    return {'scope': 'general centre interface and all-height actual S_K law; ordinary proof, not Lean certification',
            'root': root_controls(), 'generic': generic_controls(),
            'seven_point_profile_slack': profile_slack_control(),
            'finite_actual_sources': finite, 'height_eight_threshold': threshold,
            'rejected_finite_certificate_fields': bad_records}


if __name__ == '__main__':
    print(json.dumps(family.jsonable(self_check()), indent=2))
