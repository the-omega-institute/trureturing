"""Exact stop-loss heads and the existing full-height prime tail allowance.

Same-source convex comparison and analytic prime-product bounds are ordinary
proof premises from reports770--772. No original prime heights are truncated.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path

PINS = {
    'fibre_credit_depth_two_source_schedule_six.py':
        '3f940b8c1e7549380c1ed4997ae8bb2013a3dcc40974fc06670cc239ccf699e8',
    'fibre_credit_depth_two_source_schedule_six.json':
        'f92b2cadcad5edce4c3c5b1d6c8456acf8066f373f554d761b96477985ea733f',
    'fibre_credit_depth_two_stop_loss.py':
        '6bafb1b9ce5c358b80fffa55e48ee821be8ccb0e19951a68efc402f72d5823e8',
    'fibre_credit_depth_two_stop_loss.json':
        '84bb5bae511d57a536dbac5cc7c1f50731e288c3afbf54e8405051f775633e27',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def load(name, stem):
    path = Path(__file__).resolve().parent / (stem + '.py')
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    result = json.loads(json.dumps(module.calculate(), default=str))
    need(result == json.loads(path.with_suffix('.json').read_text()), 'Fresh pinned supplier matches result')
    return module, result


def tail(cutoff, ell):
    need(cutoff >= 286 and ell >= 4 and 3 ** ell <= cutoff, 'Full-coordinate tail premises')
    polynomial = F(1)
    for degree in range(1, 5):
        polynomial = 1 + F(degree, ell) * polynomial
    constant = F(2 * ell ** 2 + 1, 2 * ell ** 2 - 1)
    return constant ** 4 * F(1, cutoff) * F(cutoff, cutoff - 1) ** 2 * polynomial


def calculate():
    base = Path(__file__).resolve().parent
    for name, pin in PINS.items():
        need(sha256((base / name).read_bytes()).hexdigest() == pin, 'Pinned dependency: ' + name)
    source, new_source = load('e7_fourteen_source770', 'fibre_credit_depth_two_source_schedule_six')
    profile, old = load('e7_fourteen_profile771', 'fibre_credit_depth_two_stop_loss')
    mass = F(new_source['uniform_source_mass_lower'])
    factors = list(profile.BASE)
    factors[4] = ('cap', 17, F(8, 5))
    need(factors[4][1] == 17 and new_source['caps'][2] == '8/5', 'Changed physical source cap')
    need(mass == F(89120862071, 1350000000000), 'Fresh all32 source minimum')
    seed = profile.profile(factors, 1)
    need(seed['second_moment'] == F(new_source['product_query_Gamma_upper']),
         'Same source and complete convex comparator square')
    deltas = (F(2, 5), F(11, 25), F(23, 50), F(14, 25), F(13, 25), F(31, 50))
    new_steps, final_factors = profile.evolve(factors, mass, (31, 37, 41, 43, 47, 53), deltas)
    need(all(r['remaining_mass_lower'] > 0 for r in new_steps), 'Every actual head restriction has positive mass')
    need(new_steps[-1]['remaining_mass_lower'] > F(29, 10000), 'Positive fourteen-head reserve')
    rows = []
    choices = ((11, 5000, 7, F(1, 200)), (12, 10000, 8, F(1, 200)),
               (13, 20000, 9, F(1, 600)), (14, 50000, 9, F(1, 7000)))
    for size, cutoff, ell, simple in choices:
        head = new_steps[-1] if size == 14 else old['steps'][size - 9]
        live = F(head['remaining_mass_lower'])
        moment = F(head['joint_query_upper_after'])
        tau = tail(cutoff, ell)
        charge = F(4, 3) * moment * tau
        margin = live - charge
        need(margin > simple > 0, 'Strict full infinite-prime tail margin')
        rows.append({'head_size': size, 'cutoff': cutoff, 'ell': ell,
                     'source_schedule': '17 threshold6' if size == 14 else 'original763',
                     'head_mass_lower': live, 'head_Gamma_upper': moment,
                     'tau4': tau, 'tail_charge_upper': charge,
                     'final_distorted_mass_lower': margin, 'strict_simple_lower': simple})
    return {'scope': 'Finite pairwise-distinct odd numerical moduli>1. At least one of '
                     '3,5,7,11 absent from the entire original LCM. For each row at most '
                     'head_size prime divisors are <=cutoff; arbitrary finite larger '
                     'prime support, all phases and prime-power heights allowed.',
            'supplier_pins': PINS, 'changed_source_mass_lower': mass,
            'changed_source_caps': new_source['caps'], 'changed_comparator_factors': factors,
            'fourteen_head_deltas': deltas, 'fourteen_head_steps': new_steps,
            'fourteen_head_final_comparator': final_factors,
            'tail_delta': F(1, 4), 'tail_kernel_cap': F(4, 3),
            'rows': rows, 'mass_interpretation': 'Distorted submeasure, not a final Haar density.',
            'analytic_tail_proved_by_code': False, 'source_geometry_reexecuted': False,
            'lean_verification': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained tail certificate matches exact recomputation')
    print(json.dumps({'rows': [{k: r[k] for k in ('head_size', 'cutoff', 'strict_simple_lower')}
                              for r in result['rows']], 'lean_verification': False}, indent=2))
