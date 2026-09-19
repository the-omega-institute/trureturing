#!/usr/bin/env python3
"""Exact full-square numerator bound from arbitrary-cylinder endpoint caps.

The ordinary proof in note62 supplies the endpoint-family quantifiers.
This checker reconstructs all infinite sums and tests the ordered-pair
intersection identity on actual finite original-label surviving sets.
Standard library; read-only unless --output is explicitly supplied.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import gcd
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
PINS = {
    'frontier/endpoint-bounds/endpoint_linear_numerator.py': '646c6dce65185917554f77441c8c9d6373bb20021c1204cce01fd71f9a95e314',
    'certificates/source_norms/endpoint-bounds/endpoint_linear_numerator.json': 'c6d20392e71b3fb73b87d40b390b02fe50e9b92bd3245831bfa4d0b96e4875be',
    'frontier/source-budgets/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
    'certificates/source_norms/moments-survival/exact_survival_comparison_boundary.json': 'bb4b8b9246e84d93953591841f1c4f0c26024c6ab5a32358f3ffd77871bf3cfb',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, relative, name):
    path = base/relative
    require(sha256(path.read_bytes()).hexdigest() == PINS[relative], 'Pinned source: '+relative)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def geometric_weight(p, start):
    """Complete sum of (2*n+1)/p**n for n>=start."""
    mass = F(1, p**start)/(1-F(1, p))
    return mass*(2*start+1+F(2, p-1))


def raw35_cap(a, b):
    if b == 0:
        if a == 0:
            return F(1, 4)
        if a == 1:
            return F(1, 8)
        if a == 2:
            return F(1, 12)
        return F(3, 4*3**a)
    if a == 0:
        return F(1, 2*5**b)
    if a == 1:
        return F(1, 3*5**b)
    if a == 2:
        return F(1, 9*5**b)
    return F(1, 3**a*5**b)


def surviving35_cap(a, b):
    if b == 0:
        if a == 0:
            return F(3, 20)
        if a == 1:
            return F(11, 120)
        if a == 2:
            return F(2, 45)
        return F(11, 20*3**a)
    if a == 0:
        return F(1, 18) if b == 1 else F(4, 9*5**b)
    if a == 1 and b == 1:
        return F(1, 25)
    return raw35_cap(a, b)


def complete_sums():
    t3, t5, t7 = geometric_weight(3, 3), geometric_weight(5, 1), geometric_weight(7, 1)
    require((t3, t5, t7) == (F(4, 9), F(7, 8), F(5, 9)), 'Three complete weighted geometric tails')
    categories = {'unit': F(1, 4), '3': 3*F(1, 8), '9': 5*F(1, 12),
                  'deep3': F(3, 4)*t3, 'pure5': F(1, 2)*t5,
                  '3_times5': 3*F(1, 3)*t5, '9_times5': 5*F(1, 9)*t5,
                  'deep35': t3*t5}
    raw = sum(categories.values())
    losses = {'unit_mass': F(1, 4)-F(3, 20), '3': 3*F(1, 30),
              '9': 5*F(7, 180), '5': 3*F(2, 45), '15': 9*F(2, 75),
              'deep3': F(1, 5)*t3, 'deep5': F(1, 18)*geometric_weight(5, 2)}
    loss = sum(losses.values())
    zero7, factor7 = raw-loss, F(6, 5)*t7
    positive7 = factor7*raw
    full = zero7+positive7
    require(raw == F(57, 16) and loss == F(3139, 3600), 'Complete raw cap sum and all true surviving-cap losses')
    require((zero7, factor7, positive7, full) == (F(4843, 1800), F(2, 3), F(19, 8), F(4559, 900)),
            'Independent zero7 and positive7 summation')
    tails = []
    for cut in (3, 5, 9):
        raw_prefix = sum((2*a+1)*(2*b+1)*raw35_cap(a, b)
                         for a, b in product(range(cut+1), repeat=2))
        zero_prefix = sum((2*a+1)*(2*b+1)*surviving35_cap(a, b)
                          for a, b in product(range(cut+1), repeat=2))
        tail3, tail5 = geometric_weight(3, cut+1), geometric_weight(5, cut+1)
        mixed_outside = tail3*t5+(t3-tail3)*tail5
        raw_tail = F(3, 4)*tail3+F(37, 18)*tail5+mixed_outside
        zero_tail = F(11, 20)*tail3+2*tail5+mixed_outside
        seven_tail = F(6, 5)*geometric_weight(7, cut+1)
        seven_prefix = sum(F(6*(2*e+1), 5*7**e) for e in range(1, cut+1))
        require(raw_prefix+raw_tail == raw and zero_prefix+zero_tail == zero7,
                'Direct finite grid plus independent complete35 tail')
        require(seven_prefix+seven_tail == factor7, 'Complete positive-seven factor')
        prefix = zero_prefix+seven_prefix*raw_prefix
        remainder = zero_tail+seven_prefix*raw_tail+seven_tail*raw
        require(prefix+remainder == full and remainder > 0, 'Exact full exponent-box sum and omitted tail')
        tails.append({'cut': cut, 'finite_box_sum': prefix, 'complete_tail': remainder})
    return {'raw35_categories': categories, 'raw35_pair_cap_sum': raw,
            'surviving_cap_losses': losses, 'total_loss': loss,
            'zero7_square_upper': zero7, 'positive7_pair_factor': factor7,
            'positive7_square_upper': positive7, 'full_square_upper': full,
            'finite_box_and_complete_tail': tails}


def finite_pair_checks(constructor):
    height = 2
    period = 3**height*5**height*7**height
    mask = bytearray(b'\1')*period
    source_labels = []
    for a, b, e in product(range(height+1), repeat=3):
        if a+b+e == 0:
            continue
        if e == 0:
            aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
            re = 0
        elif a+b == 0:
            aa, ra, bb, rb, re = 0, 0, 0, 0, 6*7**(e-1)
        else:
            j, aa, ra, bb, rb = constructor.mixed(a, b, 'off-diagonal')
            re = j*7**(e-1)
        modulus, residue = constructor.crt(aa, ra, bb, rb, e, re)
        mask[residue::modulus] = b'\0'*len(mask[residue::modulus])
        source_labels.append(modulus)
    require(len(set(source_labels)) == len(source_labels) == 26, 'Genuine distinct original forbidden labels')
    survivors = [i for i, live in enumerate(mask) if live]
    pure_count = sum(all(z % 7**e != 6*7**(e-1) for e in range(1, height+1)) for z in range(7**height))
    denominator = 3**height*5**height*pure_count
    exponents = list(product(range(height+1), repeat=3))
    moduli = [3**a*5**b*7**e for a, b, e in exponents]
    cylinder_caps = [F(max(Counter(i % modulus for i in survivors).values()), denominator) for modulus in moduli]
    cap_by_exponent = dict(zip(exponents, cylinder_caps))
    pair_upper = sum((2*a+1)*(2*b+1)*(2*e+1)*cap_by_exponent[a, b, e] for a, b, e in exponents)
    generator = random.Random(6200916)
    results = []
    for mode in ('nested', 'independent'):
        residues = [4 % m if mode == 'nested' else generator.randrange(m) for m in moduli]
        test_masks = [sum(1 << i for i in survivors if i % m == r) for m, r in zip(moduli, residues)]
        direct = F(sum(sum(i % m == r for m, r in zip(moduli, residues))**2 for i in survivors), denominator)
        pair = F(sum((left & right).bit_count() for left in test_masks for right in test_masks), denominator)
        counts, incompatible = Counter(), 0
        compatible_upper = F(0)
        for i, j in product(range(len(exponents)), repeat=2):
            key = tuple(max(left, right) for left, right in zip(exponents[i], exponents[j]))
            counts[key] += 1
            common = (test_masks[i] & test_masks[j]).bit_count()
            if (residues[i]-residues[j]) % gcd(moduli[i], moduli[j]):
                require(common == 0, 'Incompatible original residues have empty intersection')
                incompatible += 1
            else:
                require(F(common, denominator) <= cap_by_exponent[key], 'Actual compatible intersection obeys its lcm-cylinder cap')
                compatible_upper += cap_by_exponent[key]
        require(all(counts[a, b, e] == (2*a+1)*(2*b+1)*(2*e+1) for a, b, e in exponents),
                'All ordered exponent-pair multiplicities reconstructed independently')
        require(direct == pair <= compatible_upper <= pair_upper, 'Direct square equals the exact pair expansion and obeys the grouped bound')
        require((incompatible == 0) == (mode == 'nested'), 'Independent residues exercise the nonnested branch')
        results.append({'mode': mode, 'actual_square_integral': direct, 'ordered_pair_integral': pair,
                        'compatible_pair_upper': compatible_upper, 'all_pair_upper': pair_upper,
                        'incompatible_ordered_pairs': incompatible})
    return {'source_height': height, 'period': period, 'source_labels': len(source_labels),
            'test_labels': len(exponents), 'ordered_pairs': len(exponents)**2,
            'normalized_survivor_mass': F(len(survivors), denominator), 'cases': results}


def calculate(base):
    for relative, pin in PINS.items():
        require(sha256((base/relative).read_bytes()).hexdigest() == pin, 'Current dependency hash: '+relative)
    linear = load(base, 'frontier/endpoint-bounds/endpoint_linear_numerator.py', 'endpoint_square_linear')
    old_endpoint = json.loads((base/'certificates/source_norms/endpoint-bounds/endpoint_linear_numerator.json').read_text())
    tables = linear.endpoint_tables()
    require(linear.encode(tables) == old_endpoint['endpoint'], 'Inherited59 actual-cylinder caps reconstructed')
    require(tables['new_cylinder_caps'] == {3: F(11, 120), 9: F(2, 45), 5: F(1, 18), 15: F(1, 25)}
            and max(tables['deep3_cap_coefficients']) == F(11, 20)
            and tables['pure5_deep_cap_coefficient'] == F(4, 9), 'Exact arbitrary-cylinder cap inventory')
    old = json.loads((base/'certificates/source_norms/moments-survival/exact_survival_comparison_boundary.json').read_text())
    old_margin = F(old['fixed_square_margin'])
    require(old_margin == F(5701, 3888), 'Current old square margin at the same endpoint')
    sums = complete_sums()
    margin = 45*F(3, 20)-sums['full_square_upper']
    gain = margin-old_margin
    require(margin == F(379, 225) and gain == F(21203, 97200) > 0, 'Absolute square margin strictly improves the current comparison')
    constructor = load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'endpoint_square_constructor')
    return {'schema': 'erdos7-endpoint-square-numerator-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': PINS, 'cost': 'f(v)=v^2', 'barrier': F(45), 'surviving_mass': F(3, 20),
            'complete_pair_sums': sums, 'absolute_square_margin': margin, 'old_square_margin': old_margin,
            'absolute_margin_improvement': gain, 'finite_actual_pair_checks': finite_pair_checks(constructor),
            'scope': ('Uniform ordinary theorem over all independently labelled original357 tests '
                      'at the specified source/mass/carrier endpoint, and limiting finite families. '
                      'The full square is rebuilt from actual-cylinder caps. No quantitative '
                      'neighborhood, global K replacement, or Lean verification is claimed.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        certificate = args.base/'certificates/source_norms/endpoint-bounds/endpoint_square_numerator.json'
        require(json.loads(certificate.read_text()) == result, 'Exact canonical certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS: uniform endpoint square4559/900, absolute margin379/225, improvement21203/97200.')
    print('Complete exponent tails and actual original-label ordered-pair intersections verified.')


if __name__ == '__main__':
    main()
