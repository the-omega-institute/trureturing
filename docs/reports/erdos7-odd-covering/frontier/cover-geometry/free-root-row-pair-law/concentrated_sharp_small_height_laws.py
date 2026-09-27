#!/usr/bin/env python3
"""Check fixed laws on the actual report-414 source against all phases.

The sibling JSON is the default input; an optional positional path selects
another certificate with this schema and source family. Exact dynamic
programming supplies the upper bound, and an independent literal CRT
calculation checks the stored attaining original-divisor layout. These are
fixed-law results, not source-minimax values or an all-height conclusion.
Runtime checks and the malformed-input controls remain active under -O.
Only standard-library modules and same-directory retained dependencies are
used; running the checker writes no files.
"""
import argparse
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from independent_layout_tree_dp import IndependentLayoutTreeDP
import concentrated_sharp_source_relabel_transport as source_api


SCOPE = (
    'Report 414 concentrated two-one-surplus sharp source; each listed law is fixed '
    'on the actual source before all independent original-divisor phases; '
    'exact maxima for these fixed laws, with no source-minimax claim.'
)
CASE_FIELDS = {
    'height', 'positive_points', 'integer_weights', 'denominator',
    'exact_maximum', 'target', 'layout',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def literal_integer(value, lower, name):
    need(type(value) is int and value >= lower,
         name + ' must be a literal integer >= ' + str(lower))
    return value


def exact_rational(value, name):
    need(type(value) is str, name + ' must be a canonical rational string')
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(name + ' must be a canonical rational string') from error
    need(str(result) == value, name + ' must be a canonical rational string')
    return result


def original_moduli(height):
    return tuple(d for j in range(height + 1) for d in (7**j, 5*7**j))


def crt_expectation(height, points, weights, denominator, layout):
    """Evaluate the literal CRT representatives, independently of the DP."""
    q = 7**height
    inverse = pow(q, -1, 5)
    total = 0
    for (row, y), weight in zip(points, weights):
        x = y + q * (((row - y) * inverse) % 5)
        load = sum(x % divisor == phase for divisor, phase in layout.items())
        total += weight * load * load
    return Fraction(total, denominator)


def verify_case(case):
    need(type(case) is dict and set(case) == CASE_FIELDS, 'invalid case fields')
    height = literal_integer(case['height'], 2, 'height')
    raw_points = case['positive_points']
    need(type(raw_points) is list and raw_points, 'nonempty positive_points required')
    need(all(type(p) is list and len(p) == 2
             and type(p[0]) is int and p[0] in (1, 2, 3, 4)
             and type(p[1]) is int and 0 <= p[1] < 7**height
             for p in raw_points), 'literal four-row carrier points required')
    points = tuple(tuple(p) for p in raw_points)
    need(len(set(points)) == len(points), 'duplicate positive points')
    actual_source = source_api.source(height)
    need(set(points) <= actual_source, 'unsupported point outside actual report-414 source')

    weights = case['integer_weights']
    need(type(weights) is list and len(weights) == len(points),
         'weight and point lengths must match')
    need(all(type(w) is int and w > 0 for w in weights),
         'stored integer weights must be positive literal integers')
    denominator = literal_integer(case['denominator'], 1, 'denominator')
    need(sum(weights) == denominator, 'weight sum must equal denominator')

    maximum = exact_rational(case['exact_maximum'], 'exact_maximum')
    target = exact_rational(case['target'], 'target')
    expected_target = 2 * (3 - Fraction(height + 2, 3**height))
    need(target == expected_target, 'target must equal 2*(3-(K+2)/3^K)')

    raw_layout = case['layout']
    moduli = original_moduli(height)
    need(type(raw_layout) is dict and set(raw_layout) == {str(d) for d in moduli},
         'complete original-divisor phase map required')
    need(all(type(raw_layout[str(d)]) is int and 0 <= raw_layout[str(d)] < d
             for d in moduli), 'canonical literal phase residues required')
    layout = {d: raw_layout[str(d)] for d in moduli}
    witness = crt_expectation(height, points, weights, denominator, layout)
    need(witness == maximum, 'CRT witness expectation differs from exact_maximum')

    optimum = IndependentLayoutTreeDP(height, points).separate(
        weights, max_states=None, max_operations=None)
    need(optimum['value'] == maximum, 'exact DP maximum differs from exact_maximum')
    need(maximum < target, 'exact maximum must be strictly below target')
    return {
        'height': height,
        'source_size': len(actual_source),
        'positive_points': len(points),
        'denominator': denominator,
        'exact_maximum': str(maximum),
        'target': str(target),
        'target_margin': str(target - maximum),
    }


def verify_certificate(data):
    need(type(data) is dict and set(data) == {'schema_version', 'scope', 'cases'},
         'invalid top-level schema')
    need(type(data['schema_version']) is int and data['schema_version'] == 1,
         'schema_version must be literal integer 1')
    need(data['scope'] == SCOPE, 'scope must identify the report-414 fixed-law claim')
    cases = data['cases']
    need(type(cases) is list and cases, 'nonempty cases required')
    return [verify_case(case) for case in cases]


def negative_controls(data):
    """Each malformed case must be rejected for its intended defect."""
    checked = []

    def rejected(case, name, reason):
        try:
            verify_case(case)
        except ValueError as error:
            need(reason in str(error), name + ' was rejected for the wrong reason')
        else:
            raise ValueError(name + ' malformed-input control was accepted')
        checked.append(name)

    for valid in data['cases']:
        height = valid['height']
        source = source_api.source(height)
        absent = next((r, y) for y in range(7**height) for r in (1, 2, 3, 4)
                      if (r, y) not in source)
        bad = deepcopy(valid)
        bad['positive_points'][0] = list(absent)
        rejected(bad, 'K' + str(height) + ':unsupported-point', 'unsupported point')

        bad = deepcopy(valid)
        bad['denominator'] += 1
        rejected(bad, 'K' + str(height) + ':wrong-weight-sum', 'weight sum')

        bad = deepcopy(valid)
        bad['exact_maximum'] = str(Fraction(bad['exact_maximum']) + 1)
        rejected(bad, 'K' + str(height) + ':false-maximum', 'CRT witness expectation')

        bad = deepcopy(valid)
        del bad['layout'][str(5 * 7**height)]
        rejected(bad, 'K' + str(height) + ':incomplete-phases', 'complete original-divisor')
    return checked


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON object key: ' + key)
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    with args.certificate.open(encoding='utf-8') as stream:
        data = json.load(stream, object_pairs_hook=unique_object)
    results = verify_certificate(data)
    controls = negative_controls(data)
    print(json.dumps({'scope': data['scope'], 'verified_cases': results,
                      'rejected_negative_controls': controls}, indent=2))


if __name__ == '__main__':
    main()
