#!/usr/bin/env python3
"""Verify actual fixed-cap laws and a common complete-layout dual witness.

An optional JSON path supplies height, laws, theta, and optionally mixture.
The seven laws have keys full,12,13,14,23,24,34; each is a list of
[row,residue,mass]. Each theta item has weight and phases, with phases in
original-divisor order 1,5,7,35,... . Exact masses are integers or strings.
An optional seven-entry mixture, in the displayed key order, additionally
certifies an upper bound when its actual law is a product of three equally
weighted rows and a common ternary-cap residue probability.

No arguments verifies an actual height-two game of value exactly 46/9.
All seven built-in laws are uniform labelled complete trees. This is an
ordinary exact certificate, not a universal height-two theorem or a Lean
proof. No optimizer or numerical search runs; only stdout is written.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import json

ROWS = (1, 2, 3, 4)
KEYS = ('full', '12', '13', '14', '23', '24', '34')
FAMILIES = {'full': (ROWS, 5)} | {
    ''.join(map(str, pair)): (pair, 3) for pair in combinations(ROWS, 2)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    require(type(value) in (int, str, F), 'exact integer or rational string required')
    return F(value)


def original_divisors(height):
    require(type(height) is int and height >= 0, 'nonnegative integer height required')
    return tuple(d for j in range(height + 1) for d in (7**j, 5*7**j))


def validate_law(height, key, entries):
    """Check a whole probability, literal support, and every pure prefix cap."""
    allowed, branching = FAMILIES[key]
    require(type(entries) in (list, tuple) and entries, 'nonempty law entries required')
    law = {}
    for entry in entries:
        require(type(entry) in (list, tuple) and len(entry) == 3, 'law entry must be row,residue,mass')
        row, residue, mass = entry
        require(type(row) is int and row in allowed and type(residue) is int
                and 0 <= residue < 7**height, 'point outside its literal component carrier')
        mass = rational(mass)
        require(mass > 0 and (row, residue) not in law, 'positive mass and unique points required')
        law[row, residue] = mass
    require(sum(law.values()) == 1, 'component probability normalization')
    for depth in range(height + 1):
        masses = defaultdict(F)
        for (_, residue), mass in law.items():
            masses[residue % 7**depth] += mass
        require(max(masses.values()) <= F(1, branching**depth), 'whole-prefix component cap')
    return law


def square_load(divisors, phases, point):
    """Evaluate each original divisor separately, including divisor one."""
    row, residue = point
    count = 0
    for divisor, phase in zip(divisors, phases):
        if divisor % 5:
            count += residue % divisor == phase
        else:
            modulus = divisor // 5
            count += row == phase % 5 and residue % modulus == phase % modulus
    return count**2


def three_row_product_upper(height, law):
    """Validate the product premise for the analytic all-phase bound 2*S_3."""
    active = {row for row, _ in law}
    require(len(active) == 3, 'upper certificate requires three active rows')
    projected = defaultdict(F)
    for (_, residue), mass in law.items():
        projected[residue] += mass
    require(all(law.get((row, residue), F()) == mass/3
                for row in active for residue, mass in projected.items()),
            'upper certificate requires equal independent row factors')
    for depth in range(height + 1):
        masses = defaultdict(F)
        for residue, mass in projected.items():
            masses[residue % 7**depth] += mass
        require(max(masses.values()) <= F(1, 3**depth), 'common residue ternary-prefix cap')
    # At depth j the pure coefficient is 2j+1; the sum of mixed-row
    # coefficients is at most 6j+3. The latter events each have cap
    # 3^(-j)/3 under the validated product law, for arbitrary phases.
    return 2*sum((F(2*j+1, 3**j) for j in range(height + 1)), F())


def verify(payload):
    require(type(payload) is dict and {'height', 'laws', 'theta'} <= set(payload)
            and set(payload) <= {'height', 'laws', 'theta', 'mixture'}, 'certificate fields')
    height = payload['height']
    divisors = original_divisors(height)
    require(type(payload['laws']) is dict and set(payload['laws']) == set(KEYS),
            'exactly one full law and all six pair laws required')
    laws = {key: validate_law(height, key, payload['laws'][key]) for key in KEYS}
    require(type(payload['theta']) in (list, tuple) and payload['theta'], 'nonempty layout mixture')
    theta = []
    for item in payload['theta']:
        require(type(item) is dict and set(item) == {'weight', 'phases'}, 'layout fields')
        weight, phases = rational(item['weight']), item['phases']
        require(weight > 0 and type(phases) in (list, tuple) and len(phases) == len(divisors),
                'positive layout weight and every original phase required')
        require(all(type(a) is int and 0 <= a < d for a, d in zip(phases, divisors)),
                'literal phase outside its original divisor')
        theta.append((weight, tuple(phases)))
    require(sum(q for q, _ in theta) == 1, 'layout probability normalization')
    layout_prices = {key: tuple(sum((mass*square_load(divisors, phases, point)
                                    for point, mass in law.items()), F())
                               for _, phases in theta) for key, law in laws.items()}
    prices = {key: sum((q*value for (q, _), value in zip(theta, values)), F())
              for key, values in layout_prices.items()}
    lower = min(prices.values())
    target = 6-F(2*(height+2), 3**height)
    result = {'height': height, 'original_divisors': divisors,
              'component_layout_prices': layout_prices, 'component_theta_prices': prices,
              'fixed_component_game_lower': lower, 'finite_target': target,
              'strict_fixed_component_obstruction': lower > target,
              'scope': 'these seven actual fixed laws only; no free-component or source-minimax conclusion'}
    if 'mixture' in payload:
        raw = payload['mixture']
        require(type(raw) in (tuple, list) and len(raw) == len(KEYS), 'seven mixture weights required')
        weights = tuple(map(rational, raw))
        require(min(weights) >= 0 and sum(weights) == 1, 'mixture probability normalization')
        law = defaultdict(F)
        for key, weight in zip(KEYS, weights):
            if weight:
                for point, mass in laws[key].items():
                    law[point] += weight*mass
        upper = three_row_product_upper(height, law)
        require(lower <= upper, 'actual lower and certified upper disagree')
        result.update({'mixture_all_independent_phase_upper': upper,
                       'matching_bounds': lower == upper})
    return result


def boundary_payload():
    """Seven explicit uniform complete-tree laws, with no optimization data."""
    laws = {'full': [[a+1 if a < 3 else 1, a+7*d, '1/25']
                     for a, d in product(range(5), repeat=2)]}
    for r, s in combinations(ROWS, 2):
        laws[f'{r}{s}'] = [[s if s < 4 and a == s-1 else r, a+7*d, '1/9']
                           for a, d in product(range(3), repeat=2)]
    theta = []
    for row, centre in ((1, 0), (2, 1), (3, 2)):
        phases = []
        for depth in range(3):
            modulus = 7**depth
            residue = centre % modulus
            mixed = residue+modulus*((row-residue)*pow(modulus, -1, 5) % 5)
            phases.extend((residue, mixed))
        theta.append({'weight': '1/3', 'phases': phases})
    return {'height': 2, 'laws': laws, 'theta': theta,
            'mixture': [0, 0, 0, '1/3', 0, '1/3', '1/3']}


def boundary():
    result = verify(boundary_payload())
    require(tuple(result['component_theta_prices'][key] for key in KEYS)
            == (F(26, 5), F(20, 3), F(20, 3), F(46, 9), F(20, 3), F(46, 9), F(46, 9)),
            'boundary component prices')
    require(result['fixed_component_game_lower'] == result['mixture_all_independent_phase_upper']
            == F(46, 9), 'exact boundary game value')
    result['verification'] = 'exact actual probabilities and complete layouts; analytic product-law upper; not Lean'
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path)
    parser.add_argument('--compact', action='store_true')
    args = parser.parse_args()
    result = verify(json.loads(args.certificate.read_text())) if args.certificate else boundary()
    print(json.dumps(result, default=str, sort_keys=True, indent=None if args.compact else 2))


if __name__ == '__main__':
    main()
