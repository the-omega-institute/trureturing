"""Exact all-height stop-loss arithmetic for the fixed common-source profile.

The finite small-product distribution and the unrestricted first moment
account for the entire infinite product law. Source and convex-comparison
proofs are supplied by reports763/771; this is not a Lean verification.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from math import prod
from pathlib import Path
import sys

SOURCE_PIN = '3fbc339694e007783611b33f2a79a0b810df601e4a9f795991c50cbd3f45233a'
SOURCE_RESULT_PIN = '7d36e5003e12630787184af423db7a29972fa446195aa70c9b4765fc0d6d86eb'
BASE = (('anchor', 3, F(1, 2)), ('anchor', 5, F(3, 4)),
        ('cap', 7, F(3, 2)), ('cap', 13, F(3, 2)),
        ('cap', 17, F(4, 3)), ('cap', 19, F(9, 5)),
        ('cap', 23, F(11, 7)), ('cap', 29, F(7, 4)))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def factor(kind, prime, parameter, upper):
    need(kind in ('anchor', 'cap') and prime > 1, 'Declared factor type')
    if kind == 'anchor':
        need(F(1, prime) <= parameter <= 1, 'Anchor subprobability domain')
        mass, scale = parameter, F(1)
    else:
        need(0 <= parameter <= prime, 'Capped run nonnegative zero atom')
        mass, scale = F(1), parameter
    mean = mass + scale / (prime - 1)
    second = mass + scale * F(3 * prime - 1, (prime - 1) ** 2)
    atoms = {1: mass - scale / prime}
    atoms.update({r: scale * F(prime - 1, prime ** r) for r in range(2, upper + 1)})
    need(all(w >= 0 for w in atoms.values()), 'Positive finite factor atoms')
    return mass, mean, second, atoms


def profile(specs, threshold):
    threshold = F(threshold)
    need(threshold > 0, 'Positive stop-loss threshold')
    upper = (threshold.numerator - 1) // threshold.denominator
    distribution = {1: F(1)}
    mass = mean = second = F(1)
    for kind, prime, parameter in specs:
        m, first, square, atoms = factor(kind, prime, parameter, max(1, upper))
        mass *= m
        mean *= first
        second *= square
        nxt = {}
        for old, weight in distribution.items():
            for r in range(1, upper // old + 1):
                nxt[old * r] = nxt.get(old * r, F(0)) + weight * atoms[r]
        distribution = nxt
    deficit = sum(((threshold - m) * w for m, w in distribution.items()), F(0))
    hinge = mean - threshold * mass + deficit
    need(0 <= hinge <= second / (4 * threshold), 'Hinge dominated by quadratic relaxation')
    need(all(m < threshold for m in distribution), 'Strict small-product cutoff')
    need(sum(distribution.values(), F(0)) <= mass, 'Small-product submass')
    return {'mass': mass, 'first_moment': mean, 'second_moment': second,
            'threshold': threshold, 'small_product_atoms': distribution,
            'finite_deficit': deficit, 'stop_loss': hinge}


def evolve(specs, mass_lower, primes, deltas):
    need(len(primes) == len(deltas), 'One clipping parameter per added prime')
    specs = list(specs)
    mass = mass_lower
    rows = []
    for prime, delta in zip(primes, deltas):
        need(0 < delta < 1 and 1 / (1 - delta) <= prime, 'Legal clipping cap')
        threshold = delta * (prime - 1)
        data = profile(specs, threshold)
        loss = data['stop_loss'] / ((1 - delta) * (prime - 1))
        mass -= loss
        cap = 1 / (1 - delta)
        after_second = data['second_moment'] * (1 + cap * F(3 * prime - 1, (prime - 1) ** 2))
        rows.append({'prime': prime, 'delta': delta, 'profile': data,
                     'loss_upper': loss, 'remaining_mass_lower': mass,
                     'joint_query_upper_after': after_second})
        specs.append(('cap', prime, cap))
    return rows, specs


def source_mass(base):
    need(not sys.flags.optimize, 'Inherited source evaluator requires assertions enabled')
    sys.dont_write_bytecode = True
    path = base / 'fibre_credit_depth_two_eight_head_tail.py'
    need(sha256(path.read_bytes()).hexdigest() == SOURCE_PIN, 'Pinned source evaluator')
    need(sha256(path.with_suffix('.json').read_bytes()).hexdigest() == SOURCE_RESULT_PIN,
         'Pinned source result')
    spec = spec_from_file_location('e7_stoploss_source763', path)
    source = module_from_spec(spec)
    spec.loader.exec_module(source)
    result = source.calculate(base.parent)
    need(json.loads(json.dumps(result, default=str)) == json.loads(path.with_suffix('.json').read_text()),
         'Fresh source formulas match retained source result')
    need(result['source_mass_lower'] == F(10237584019, 168750000000)
         and result['joint_query_seed_upper'] == F(26010182627, 1040449536),
         'Exact mass and square source interface')
    return result['source_mass_lower'], result['dependencies']


def calculate():
    initial, dependencies = source_mass(Path(__file__).resolve().parent)
    base = profile(BASE, 15)
    need(base['mass'] == F(3, 8) and base['first_moment'] == F(109395, 57344)
         and base['second_moment'] == F(26010182627, 1040449536), 'Full comparator moments')
    rows, specs = evolve(BASE, initial, (31, 37, 41, 43, 47), (F(1, 2),) * 5)
    ceilings = (F(188849, 10 ** 6), F(183655, 10 ** 6), F(195381, 10 ** 6))
    need(all(rows[i]['profile']['stop_loss'] < ceiling for i, ceiling in enumerate(ceilings)),
         'Three exact hinge ceilings')
    simple_three = initial - sum((s / t for s, t in zip(ceilings, (15, 18, 20))), F(0))
    need(simple_three == F(9485479913, 337500000000) > F(281, 10000), 'Simple three-step reserve')
    need(rows[-1]['remaining_mass_lower'] > F(1, 125), 'Positive thirteen-head mass')
    failed, _ = evolve(specs, rows[-1]['remaining_mass_lower'], (53,), (F(1, 2),))
    need(failed[0]['remaining_mass_lower'] < 0, 'Unchanged half-clipped ledger fails at fourteen')
    return {'scope': 'Same ordinary eight-prime source and full increasing-convex comparator; '
                     'at least one of 3,5,7,11 missing. Exact reference continuation through47 '
                     'admits all original phases and arbitrary finite coordinate heights.',
            'source_pins': [SOURCE_PIN, SOURCE_RESULT_PIN], 'source_dependencies': dependencies,
            'source_mass_lower': initial, 'comparator_factors': BASE,
            'comparator_mass': base['mass'], 'comparator_first_moment': base['first_moment'],
            'comparator_second_moment': base['second_moment'], 'steps': rows,
            'simple_eleven_head_mass_lower': simple_three,
            'simple_thirteen_head_strict_mass_lower': F(1, 125),
            'fourteenth_half_clipped_ledger': failed[0],
            'failure_scope': 'This specific sufficient ledger is negative; not a covering witness.',
            'finite_original_heights_bounded': False, 'source_geometry_reexecuted': False,
            'convex_comparison_proved_by_code': False, 'lean_verification': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained exact profile agrees with complete recomputation')
    print(json.dumps({'source_mass': result['source_mass_lower'],
                      'head_sizes': [9 + i for i in range(len(result['steps']))],
                      'strict_thirteen_head_mass_lower': result['simple_thirteen_head_strict_mass_lower'],
                      'lean_verification': False}, indent=2))
