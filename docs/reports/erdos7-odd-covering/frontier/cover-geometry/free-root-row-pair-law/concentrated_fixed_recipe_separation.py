#!/usr/bin/env python3
"""Verify submitted exact maxima for the fixed actual law of report 414.

Supports any finite list of heights >= 2, each with its original attaining
layout and exact claimed maximum. The family constructor and validator are
reused; the supplied law is fixed before independent phases. Only the exact
separator supplies the upper bound. A separate CRT calculation checks the
attaining layout. Resource exhaustion raises an error, never a partial bound.
"""
import argparse
from fractions import Fraction as F
import json
from math import lcm
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import concentrated_sharp_source_relabel_transport as family
from concentrated_sharp_small_height_laws import crt_expectation, exact_rational, unique_object
from independent_layout_tree_dp import IndependentLayoutTreeDP


def verify_case(case, max_states=None, max_operations=None):
    family.need(type(case) is dict and set(case) == {'height', 'maximum', 'target', 'layout'},
                'height, maximum, target and layout required')
    height = family.integer(case['height'], 2, 'height')
    maximum = exact_rational(case['maximum'], 'maximum')
    target = exact_rational(case['target'], 'target')
    family.need(target == 6-F(2*(height+2), 3**height), 'wrong finite target')
    raw_layout = case['layout']
    moduli = tuple(d for j in range(height+1) for d in (7**j, 5*7**j))
    family.need(type(raw_layout) is dict and set(raw_layout) == {str(d) for d in moduli},
                'one phase per original divisor required')
    family.need(all(type(raw_layout[str(d)]) is int and 0 <= raw_layout[str(d)] < d
                    for d in moduli), 'canonical literal phases required')
    layout = {d: raw_layout[str(d)] for d in moduli}
    certificate = family.family_certificate(height)
    family.verify_family_certificate(certificate)
    law = certificate['nu']
    points = sorted(law)
    denominator = lcm(*(mass.denominator for mass in law.values()))
    weights = [int(denominator*law[point]) for point in points]
    family.need(sum(weights) == denominator and set(points) <= certificate['source'],
                'actual normalized source law required')
    witness = crt_expectation(height, points, weights, denominator, layout)
    family.need(witness == maximum, 'literal CRT witness differs from claimed maximum')
    result = IndependentLayoutTreeDP(height, points).separate(
        weights, max_states=max_states, max_operations=max_operations)
    family.need(result['value'] == maximum, 'full independent-phase maximum differs from claim')
    return {'height': height, 'source_points': len(certificate['source']),
            'positive_points': len(points), 'maximum': str(maximum), 'target': str(target),
            'margin': str(target-maximum), 'cached_states': result['cached_states'],
            'subset_operations': result['subset_operations'], 'seconds': result['seconds']}


def verify_data(data, max_states=None, max_operations=None):
    family.need(type(data) is dict and set(data) == {'schema_version', 'cases'},
                'schema_version and cases required')
    family.need(type(data['schema_version']) is int and data['schema_version'] == 1,
                'literal schema version 1 required')
    family.need(type(data['cases']) is list and data['cases'], 'nonempty case list required')
    return [verify_case(case, max_states, max_operations) for case in data['cases']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--max-states', type=int)
    parser.add_argument('--max-operations', type=int,
                        help='subset-convolution candidates only, not a memory or total-work cap')
    args = parser.parse_args()
    with args.certificate.open(encoding='utf-8') as stream:
        data = json.load(stream, object_pairs_hook=unique_object)
    print(json.dumps({'scope': 'fixed actual recipe; full original independent phases; no source-minimax claim',
                      'verified': verify_data(data, args.max_states, args.max_operations)}, indent=2))


if __name__ == '__main__':
    main()
