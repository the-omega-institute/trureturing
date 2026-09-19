#!/usr/bin/env python3
"""Whole-J identity reserve with separate complete original-family errors."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_family_error_reserve.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/j-source/j_source_labelwise_neighborhood.py': '7bc8cefd82701ec039284474ef62252191a5f0f923a2942f0ddf64cbff06e9a1',
    'certificates/source_norms/j-source/j_source_labelwise_neighborhood.json': 'f53c4461ffef8816e989c24e01c254d280aacf767328ca0d15aea840b2bf0011',
    'certificates/source_norms/j-source/j_face_alignment.json': '6874e71b0846d973fedd330f5a8a54bfa457b2cdfe896943db407b8d89bec611',
    'certificates/source_norms/j-source/j_face_surplus_transport.json': '2c64303053c544e0f5ef9aab5f4d56c6a9f75e2ab88efe347bfb88ca4a3c3a28',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original proof provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def geometric(p, first):
    return F(p, (p-1)*p**first)


def complete_axis_error(p, first, cap, drift, error):
    """Sum min(cap*p^-n, drift*p^-n+error) over every n>=first."""
    cap, drift, error = map(F, (cap, drift, error))
    require(p >= 2 and first >= 1 and 0 <= drift <= cap and error >= 0,
            'Nonnegative source drift, raw-minus-face cap and same actual residual')
    if error == 0:
        return {'prime': p, 'first_depth': first, 'cap_coefficient': cap,
                'drift_coefficient': drift, 'residual_error': error,
                'first_clipped_depth': None, 'unclipped_depths': 0,
                'finite_part': F(0), 'complete_remainder': drift*geometric(p, first),
                'value': drift*geometric(p, first)}
    n = first
    while error < (cap-drift)*F(1, p**n):
        n += 1
    finite = drift*(geometric(p, first)-geometric(p, n))+(n-first)*error
    tail = cap*geometric(p, n)
    require(error >= (cap-drift)*F(1, p**n)
            and (n == first or error < (cap-drift)*F(1, p**(n-1))),
            'Exact first crossing and its entire infinite geometric continuation')
    return {'prime': p, 'first_depth': first, 'cap_coefficient': cap,
            'drift_coefficient': drift, 'residual_error': error,
            'first_clipped_depth': n, 'unclipped_depths': n-first,
            'finite_part': finite, 'complete_remainder': tail, 'value': finite+tail}


def independent_axis_error(p, first, cap, drift, error):
    """Start with the full raw-minus-face sum and subtract finite savings."""
    cap, drift, error = map(F, (cap, drift, error))
    if error == 0:
        return drift*geometric(p, first)
    value, n = cap*geometric(p, first), first
    while (cap-drift)*F(1, p**n) > error:
        value -= (cap-drift)*F(1, p**n)-error
        n += 1
    return value


def reserve_bound(delta, rho):
    """Ordinary197 bound in136's complete actual whole-J source domain."""
    delta, rho = map(F, (delta, rho))
    require(delta >= 0 and rho >= 0 and delta+rho <= F(1, 1000),
            'Original136 whole-J source, packing and actual residual hypotheses')
    budget = rho+7*delta/36
    rows = []
    for name, modulus, face, source, price in (
            ('test3', 3, F(11, 120), F(2), F(3)),
            ('test9', 9, F(2, 45), F(2), F(3)),
            ('test5', 5, F(4, 75), F(4), F(35)),
            ('test15', 15, F(1, 25), F(3), F(30))):
        gap, actual = F(1, modulus)-face, source*delta+price*budget
        require(gap > 0, 'Raw cap strictly contains the original whole-J face cap')
        rows.append({'family': name, 'modulus': modulus, 'face_cap': face,
                     'raw_minus_face': gap, 'source_delta_price': source,
                     'actual_budget_price': price, 'unclipped_error': actual,
                     'error_upper': min(gap, actual)})
    axes = [complete_axis_error(3, 3, F(9, 20), 3*delta, 3*budget),
            complete_axis_error(5, 2, F(17, 30), 2*delta/15, budget)]
    for row in axes:
        require(row['value'] == independent_axis_error(
            row['prime'], row['first_depth'], row['cap_coefficient'],
            row['drift_coefficient'], row['residual_error']),
            'Two exact summations retain the complete axis tail')
    error = sum(r['error_upper'] for r in rows)+sum(r['value'] for r in axes)
    reserve = F(79, 1944)-54*delta-error
    return {'source_radius': delta, 'residual_radius': rho,
            'single_actual_capacity_budget_upper': budget,
            'shallow_families': rows, 'complete_axis_errors': axes,
            'unchanged_mixed_families': {'3_times_deep5': F(0), '9_times5': F(0), 'deep35': F(0)},
            'complete_zero7_error': error,
            'identity_nonunit_endpoint': F(49, 100)+F(119, 360)*delta+error,
            'identity_margin_endpoint': F(13, 50)-F(239, 60)*delta-error,
            'old49_replacement_reserve_lower': reserve,
            'favorable_actual_residual_margin_coefficient': F(5)}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('j197_io', base/'certificate_io.py')
    read = lambda p: json.loads(io.read_artifact_bytes(base/p))
    prior = read('certificates/source_norms/j-source/j_source_labelwise_neighborhood.json')
    face = read('certificates/source_norms/j-source/j_face_alignment.json')
    surplus = read('certificates/source_norms/j-source/j_face_surplus_transport.json')
    pins = dict(PINS)
    for cert in (prior, face, surplus):
        for path, pin in cert['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original proof closure '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned original input '+path)
    engine = module('j197_inventory', base/'frontier/source_barrier_saturation.py').Experiment(base)
    for path, pin in engine.pins.items():
        require(path not in pins or pins[path] == pin, 'Consistent complete original inventory '+path)
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inventory input '+path)
        pins[path] = pin
    require(F(face['direction40_weight']) == engine.weights[40] > 0,
            'The same complete original old49 identity direction and its actual positive weight')
    original = module('j197_original', base/'frontier/j-source/j_source_labelwise_neighborhood.py')
    require(original.encode(original.guard_and_prices()) == prior['domain_and_prices'],
            'All original whole-J first-label, packing, projection and source guards')
    categories = {'unit': F(3, 20), 'test3': F(11, 120), 'test9': F(2, 45),
                  'pure3_deep': F(11, 20)*geometric(3, 3), 'test5': F(4, 75),
                  'pure5_deep': F(13, 30)*geometric(5, 2), 'test15': F(1, 25),
                  '3_times_deep5': geometric(5, 2)/3, '9_times5': geometric(5, 1)/9,
                  'deep35': geometric(3, 3)*geometric(5, 1), 'positive7': F(3, 20)}
    require(encode(categories) == face['complete_categories'] and sum(categories.values()) == F(16, 25)
            and sum(v for k, v in categories.items() if k not in ('unit', 'positive7')) == F(17, 50)
            and F(face['old49_replacement_reserve']) == F(79, 1944),
            'Every original complete face category and the same old49 direction40 comparison')
    require(3*F(1, 1000) < F(9, 20) and 2*F(1, 1000)/15 < F(17, 30),
            'All coefficient drifts fit their raw-minus-face gaps on the entire source domain')
    checks = []
    for delta, rho in ((F(0), F(0)), (F(1, 10**8), F(1, 10**8)),
                       (F(1, 60000), F(1, 10**6)), (F(1, 3000), F(1, 100000)),
                       (F(1, 2500), F(1, 100000)), (F(1, 10000), F(1, 5000)),
                       (F(0), F(1, 3000))):
        row = reserve_bound(delta, rho)
        old = original.complete_B1(100*(delta+rho))['value']
        require(old == original.independent_B1(100*(delta+rho)), 'Entire predecessor double series')
        require(row['complete_zero7_error'] <= old and row['old49_replacement_reserve_lower'] > 0,
                'The separate complete-family bound gives a positive reserve on each recorded rectangle')
        row.update({'predecessor_complete_error': old,
                    'predecessor_reserve_lower': F(79, 1944)-54*delta-old,
                    'reserve_gain': old-row['complete_zero7_error']})
        checks.append(row)
    wide = next(r for r in checks if r['source_radius'] == F(1, 2500))
    require(wide['complete_zero7_error'] == F(946116551, 75937500000)
            and wide['old49_replacement_reserve_lower'] == F(499570949, 75937500000),
            'Exact enlarged whole-J source/residual rectangle')
    actual = []
    for row in prior['actual_finite_sources']:
        bound = reserve_bound(F(row['delta']), F(row['rho']))
        require(bound['old49_replacement_reserve_lower'] > F(row['old49_replacement_reserve_lower']) > F(1, 25),
                'Same original finite labelled sources retain the improved reserve')
        actual.append({'height': row['height'], 'delta': F(row['delta']), 'rho': F(row['rho']),
                       'reserve_lower': bound['old49_replacement_reserve_lower']})
    return encode({'schema': 'erdos7-j-family-error-reserve-v1', 'source_sha256': pins,
                   'domain_and_prices': prior['domain_and_prices'], 'complete_face_categories': categories,
                   'face_reserve': F(79, 1944), 'direction40_weight': F(face['direction40_weight']),
                   'complete_rectangles': checks, 'actual_finite_sources': actual,
                   'scope': 'Ordinary whole-J source theorem on delta+rho<=1/1000. Four independent shallow labels, both complete pure-axis tails and all unchanged mixed raw caps retain their actual source and one capacity/union residual. The reserve replaces only the original old49 direction40 margin. Both J orientations and the full admissible beta-times-late simplex remain. No complete global consumer, Lean verification, attainment or unrestricted Erdos7 resolution is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j197_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact complete separate-family J reserve certificate')
    print('PASS: whole-J source1/2500, residual1/100000, complete reserve='
          +str(float(F(499570949, 75937500000))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
