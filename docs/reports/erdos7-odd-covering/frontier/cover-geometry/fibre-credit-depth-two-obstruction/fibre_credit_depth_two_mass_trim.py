"""Exact repeated upper-mass comparison for the ordinary all-height source.

Reuses the upper-quantile principle and source/capped-query interfaces from
reports04,744,770--772. The finite atoms locate exact quantiles; complete
moments carry every unbounded auxiliary tail. No Lean verification.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path

ATOM_LIMIT = 100
PINS = {
    'fibre_credit_depth_two_fourteen_head_tail.py':
        'cf502376f347e0521a844afdcbbaf0bd659dc74cd9d8690d7afa62b98189bc1f',
    'fibre_credit_depth_two_fourteen_head_tail.json':
        '3a2cf939ea201ce00dcdadf0ef80c90e57625bf1581bbd252f73d5d5c2000b35',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def load_module(path, name):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def append(state, factor):
    m, first, second, atoms = factor
    out = {}
    for value, weight in state['atoms'].items():
        for r in range(1, ATOM_LIMIT // value + 1):
            out[value * r] = out.get(value * r, F(0)) + weight * atoms[r]
    return {'mass': state['mass'] * m, 'first': state['first'] * first,
            'second': state['second'] * second, 'atoms': out}


def trim(state, target):
    need(0 < target <= state['mass'], 'Positive available upper submass')
    remaining = state['mass'] - target
    removed_first = removed_second = F(0)
    out = dict(state['atoms'])
    cutoff = None
    for value in sorted(out):
        debit = min(remaining, out[value])
        remaining -= debit
        out[value] -= debit
        removed_first += value * debit
        removed_second += value * value * debit
        if remaining == 0:
            cutoff = value
            break
    need(remaining == 0 and cutoff is not None, 'Finite atoms resolve the full quantile')
    result = {'mass': target, 'first': state['first'] - removed_first,
              'second': state['second'] - removed_second,
              'atoms': {n: w for n, w in out.items() if w}}
    need(all(w >= 0 for w in result['atoms'].values()), 'Nonnegative retained atoms')
    need(sum(result['atoms'].values(), F(0)) <= target, 'Exact finite submass')
    need(result['first'] >= target and result['second'] >= result['first'], 'Positive integer load moments')
    need(result['first'] ** 2 <= target * result['second'], 'Moment consistency')
    return result, {'cutoff': cutoff, 'removed_mass': state['mass'] - target,
                    'removed_first': removed_first, 'removed_second': removed_second}


def hinge(state, threshold):
    need(0 < threshold <= ATOM_LIMIT, 'Available complete low-atom window')
    low = sum(((threshold - n) * w for n, w in state['atoms'].items()
               if n < threshold), F(0))
    result = state['first'] - threshold * state['mass'] + low
    need(0 <= result <= state['second'] / (4 * threshold), 'Exact hinge consistency')
    return result


def run(profile, factors, mass, primes, deltas):
    state = {'mass': F(1), 'first': F(1), 'second': F(1), 'atoms': {1: F(1)}}
    for spec in factors:
        state = append(state, profile.factor(*spec, ATOM_LIMIT))
    initial, first_trim = trim(state, mass)
    state = initial
    steps = []
    need(len(primes) == len(deltas), 'One declared clipping level per step')
    for prime, delta in zip(primes, deltas):
        need(0 < delta < 1 and 1 / (1 - delta) <= prime, 'Legal constant clipping')
        threshold = delta * (prime - 1)
        value = hinge(state, threshold)
        loss = value / ((1 - delta) * (prime - 1))
        live = state['mass'] - loss
        need(live > 0, 'Positive exact source mass at every declared stage')
        extended = append(state, profile.factor('cap', prime, 1 / (1 - delta), ATOM_LIMIT))
        state, info = trim(extended, live)
        steps.append({'prime': prime, 'delta': delta, 'threshold': threshold,
                      'hinge': value, 'loss_upper': loss, 'trim': info, 'state': state})
    return {'initial_trim': first_trim, 'initial_state': initial, 'steps': steps}


def gate(state, prime):
    difference = state['first'] - (prime - 1) * state['mass']
    return {'prime': prime, 'first_minus_threshold_mass': difference,
            'mean_load': state['first'] / state['mass'],
            'some_constant_clipping_can_have_positive_ledger': difference < 0,
            'scope': 'This equal-mass comparator and one-step sufficient ledger only.'}


def calculate():
    base = Path(__file__).resolve().parent
    for name, pin in PINS.items():
        need(sha256((base / name).read_bytes()).hexdigest() == pin, 'Pinned supplier: ' + name)
    supplier = load_module(base / 'fibre_credit_depth_two_fourteen_head_tail.py', 'e7_trim_supplier772')
    inherited = supplier.calculate()
    need(json.loads(json.dumps(inherited, default=str)) ==
         json.loads((base / 'fibre_credit_depth_two_fourteen_head_tail.json').read_text()),
         'Fresh source and tail suppliers match retained772')
    profile = load_module(base / 'fibre_credit_depth_two_stop_loss.py', 'e7_trim_profile771')
    primes = (31, 37, 41, 43, 47, 53)
    old = run(profile, profile.BASE, F(10237584019, 168750000000), primes, (F(1, 2),) * 6)
    need(old['steps'][-1]['state']['mass'] > F(1, 1800), 'Old source fixed-half fourteen-head margin')
    old_gate = gate(old['steps'][-1]['state'], 59)
    eleven_gate = gate(old['initial_state'], 11)
    need(not old_gate['some_constant_clipping_can_have_positive_ledger'] and
         not eleven_gate['some_constant_clipping_can_have_positive_ledger'], 'Old source method boundaries')
    factors = inherited['changed_comparator_factors']
    mass = inherited['changed_source_mass_lower']
    deltas = (F(2, 5), F(4, 9), F(9, 20), F(4, 7), F(12, 23), F(8, 13))
    new = run(profile, factors, mass, primes, deltas)
    final = new['steps'][-1]['state']
    need(final['mass'] > F(363, 100000) and final['second'] < F(611, 20),
         'New source paired mass and second moment')
    new_gate = gate(final, 59)
    need(not new_gate['some_constant_clipping_can_have_positive_ledger'], 'New fixed-schedule next59 boundary')
    tail = supplier.tail(20000, 9)
    charge = F(4, 3) * final['second'] * tail
    margin = final['mass'] - charge
    need(margin > F(1, 7000), 'Fourteen-small-prime complete tail certificate')
    return {'scope': 'Finite pairwise-distinct odd numerical moduli>1; one of3,5,7,11 '
                     'absent from ENTIRE original LCM. At most14 support primes<=20000; '
                     'arbitrary finite larger support and every finite height/global phase.',
            'supplier_pins': PINS, 'atom_limit': ATOM_LIMIT,
            'old_source_half_schedule': old, 'old_source_strict_mass_lower': F(1, 1800),
            'old_source_append11_gate': eleven_gate, 'old_source_next59_gate': old_gate,
            'new_source_schedule': new, 'new_source_next59_gate': new_gate,
            'tail': {'head_size': 14, 'cutoff': 20000, 'ell': 9, 'tau4': tail,
                     'loss_upper': charge, 'final_distorted_mass_lower': margin,
                     'strict_simple_lower': F(1, 7000)},
            'infinite_auxiliary_moments_retained': True,
            'source_geometry_reexecuted': False, 'lean_verification': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained mass-trim certificate matches complete recomputation')
    print(json.dumps({'head_size': 14, 'cutoff': 20000,
                      'strict_final_distorted_mass_lower': result['tail']['strict_simple_lower'],
                      'lean_verification': False}, indent=2))
