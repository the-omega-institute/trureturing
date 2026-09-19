#!/usr/bin/env python3
"""Complete pure3 forbidden deletion gives uniform endpoint mean16/25.

The ordinary proof supplies original-label saturation and the exact product
section on root0. This verifies all first-five source tables, complete tails,
the whole linear sum and direct exclusion of the old scalar W mean.
No conditional equality premise or uniform survival claim is introduced.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint_linear_complete_pure3_deletion.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/endpoint_linear_numerator.py': '5c83f0a6277079323120ce0a31ac220c884f92ff555506f9dcaf926d3335e133',
    'certificates/source_norms/endpoint_linear_numerator.json': '1d5c0a6a2e9ba8e4d615f6963caa717f35e803ff531ab798420929d1d39bb981',
    'certificates/source_norms/endpoint_survival_scalar_barrier.json': '7aaed60175fa7a2f556350ba47c341ec1426142a08aaf9b1a5941908d7a20d10',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('complete_pure3_linear_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    previous = read('certificates/source_norms/endpoint_linear_numerator.json')
    scalar = read('certificates/source_norms/endpoint_survival_scalar_barrier.json')
    for certificate in (previous, scalar):
        for path, pin in certificate['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    linear = module('complete_pure3_linear59', base/'frontier/endpoint_linear_numerator.py')
    old = linear.endpoint_tables()
    require(encode(old) == previous['endpoint'], 'Exact original all-cylinder endpoint caps')
    D, oldL = F(3, 20), F(1157, 1800)
    require(old['linear_numerator_upper'] == oldL and old['surviving_mass'] == D, 'Same endpoint mass and previous uniform mean')
    deep3_mass = F(1, 27)/(1-F(1, 3))
    seven_mass = F(6, 35)/(1-F(1, 7))
    coefficient = deep3_mass*seven_mass
    require((deep3_mass, seven_mass, coefficient) == (F(1, 18), F(1, 5), F(1, 90)), 'Complete two-dimensional original-cofactor tail')
    density = (F(3, 4), F(3, 4), F(1, 4), F(1, 2), F(1, 2))
    require([l for l, d in enumerate(density) if d == max(density)] == [0, 1], 'Every saturated forbidden deep3 carrier is in root0')
    qslots = tuple(map(F, ('0', '1/5', '1/5', '3/20', '1/5')))
    tables = []
    for x in linear.LATE_INTERVAL:
        _, selected = linear.slot_matrices(x)
        before = [sum(selected[l][j] for l in range(5)) for j in range(5)]
        after = [cap-coefficient*q for cap, q in zip(before, qslots)]
        require(max(after) == F(4, 75) and [j for j, cap in enumerate(after) if cap == max(after)] in ([2, 4], [4]), 'All first-five columns below4/75 along the affine source interval')
        require(min(after) >= 0, 'Nonnegative surviving slot caps')
        tables.append({'late_B_mass': x, 'old_selected_column_caps': before,
                       'pure5_complement_slot_masses': qslots, 'complete_pure3_deletion': [coefficient*q for q in qslots],
                       'new_column_caps': after})
    eta = linear.ETA
    h, h0, cell1 = sum(eta), sum(eta[:2]), eta[1]
    old_deep5_coefficient = h-(h0+cell1)/5
    new_deep5_coefficient = old_deep5_coefficient-coefficient
    require((old_deep5_coefficient, new_deep5_coefficient) == (F(4, 9), F(13, 30)), 'Raw pure5-complement coefficient retained before subtraction')
    tail5_mass = F(1, 25)/(1-F(1, 5))
    require(tail5_mass == F(1, 20), 'Complete positive-five depth tail')
    first_gain = F(1, 18)-F(4, 75)
    tail_gain = coefficient*tail5_mass
    require((first_gain, tail_gain, first_gain+tail_gain) == (F(1, 450), F(1, 1800), F(1, 360)), 'Disjoint first-five and deep-five gains')
    categories = {'unit': D, 'test3': F(11, 120), 'test9': F(2, 45),
                  'pure3_deep': F(11, 20)*deep3_mass, 'test5': F(4, 75),
                  'pure5_deep': new_deep5_coefficient*tail5_mass, 'test15': F(1, 25),
                  '3_times_deep5': F(1, 60), '9_times5': F(1, 36),
                  'deep35': F(1, 72), 'positive7': F(3, 20)}
    L = sum(categories.values())
    margin = 6*D-L
    require(L == oldL-first_gain-tail_gain == F(16, 25) and margin == F(13, 50), 'Complete improved uniform endpoint mean and barrier6 margin')
    W = [(v, F(mass)) for v, mass in scalar['laws']['W']['support']]
    Wmass = sum(mass for _, mass in W)
    Wmean = sum(v*mass for v, mass in W)
    require(Wmass == D and Wmean == oldL and Wmean-L == F(1, 360) > 0, 'The old W mean violates the new uniform theorem')
    return {'schema': 'erdos7-endpoint-linear-complete-pure3-deletion-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': used, 'mass': D, 'old_linear_upper': oldL,
            'complete_pure3_raw_tail': deep3_mass, 'complete_seven_cap_tail': seven_mass,
            'five_complement_deletion_coefficient': coefficient, 'first5_affine_endpoint_tables': tables,
            'old_deep5_coefficient': old_deep5_coefficient, 'new_deep5_coefficient': new_deep5_coefficient,
            'complete_deep5_tail_mass': tail5_mass, 'first5_gain': first_gain, 'complete_deep5_gain': tail_gain,
            'complete_test_categories': categories, 'linear_upper': L, 'signed_barrier': 6, 'signed_margin_lower': margin,
            'improvement_over59': oldL-L, 'W_mass': Wmass, 'W_linear_integral': Wmean, 'W_mean_exclusion_gap': Wmean-L,
            'scope': ('Ordinary uniform actual404 endpoint mean16/25 using complete forbidden pure3 deletion. '
                      'Original residues and all tails remain independent. The old1157/1800 saturation '
                      'premise is impossible. No quantitative neighborhood, global K, survival update or Lean claim.')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('complete_pure3_linear_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical exact complete-pure3 linear certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:exact product-section coefficient, all first-five columns, complete original tails and direct W-mean exclusion.')
    print('Uniform endpoint linear16/25; barrier6 margin13/50; improvement1/360 over59.')
    print('No linear-saturation hypothesis or unconditional survival-denominator update is asserted.')


if __name__ == '__main__':
    main()
