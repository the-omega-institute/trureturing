#!/usr/bin/env python3
"""One conditional containment repairs the actual profile counterexample family.

Retain E_7 and replace E_{5,7} by E_{5,7} minus E_7 in each actual
root fibre. The original family, survivor and source law are unchanged.
The ordinary positive-box argument, not sampled heights, proves the all-n bound.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod
from pathlib import Path
import argparse
import hashlib
import json

Q = (5, 7, 11, 13, 17, 19)
P = (3,) + Q
REGIONS = ('zero', 'base', 'extra5', 'missing5', 'missing5_extra7', 'missing7')
SIGNATURE = {(0, 0): 'zero', (1, 1): 'base', (2, 1): 'extra5',
             (0, 1): 'missing5', (0, 2): 'missing5_extra7', (1, 0): 'missing7'}
S0 = F(65869, 378675)
B5 = F(19132074022251234990036997833948759259,
       18473247078046657922374787501704265625)
TARGET = 51 * B5 / 310
SOURCE_SHA = 'd112692ef038bf43655f3f1089f90d574c3c9454b9f85eb4cfed8c046a6f9022'
CHECKS = {}


def check(name, value):
    if name in CHECKS or not value:
        raise RuntimeError(name)
    CHECKS[name] = True


def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for blocks in partitions(rest):
        yield ((first,),) + blocks
        for i, block in enumerate(blocks):
            yield blocks[:i] + ((first,) + block,) + blocks[i + 1:]


@lru_cache(None)
def families(mask):
    # The block containing the neutral marker records unused coordinates.
    return tuple(tuple(sum(1 << i for i in block) for block in part if 6 not in block)
                 for part in partitions(tuple(i for i in range(6) if mask >> i & 1) + (6,)))


def phi(mask, weights):
    return sum(((-1) ** len(fam) * prod((weights[m] for m in fam), start=F(1))
                for fam in families(mask)), F())


def profile_weights(region, t, residual=False):
    out = {}
    for mask in range(1, 64):
        old = int(mask & 3 == 0 and mask.bit_count() >= 2)
        mult = old if region == 'zero' else 1 + old
        if mask == 1 and region == 'extra5':
            mult += 1
        if mask == 1 and region in ('missing5', 'missing5_extra7'):
            mult -= 1
        if mask == 2 and region == 'missing5_extra7':
            mult += 1
        if mask == 2 and region == 'missing7':
            mult -= 1
        if residual and region == 'missing5_extra7' and mask == 3:
            mult = 0
        out[mask] = mult * prod((t[q] for i, q in enumerate(Q) if mask >> i & 1), start=F(1))
    return out


source_path = Path(__file__).with_name('actual_profile_threshold_counterexample.json')
source_bytes = source_path.read_bytes()
check('retained_actual_source_hash', hashlib.sha256(source_bytes).hexdigest() == SOURCE_SHA)
source = json.loads(source_bytes)
t = {int(q): F(v) for q, v in source['actual_Q_channel_masses'].items()}
corrected = F()
finite_profiles = {}
for row in source['root_profiles']:
    region = SIGNATURE[tuple(row['union_multiplicities'][:2])]
    root = row['representative_root_mod6561']
    active = [g for g in source['mixed_groups']
              if not g['root_depth'] or root % (3 ** g['root_depth']) == g['root_residue']]
    pairs = {tuple(g['channels']) for g in active if g['support'] == [5, 7]}
    singles = {g['channels'][0] for g in active if g['support'] == [7]}
    removed = {pair for pair in pairs if pair[1] in singles}
    check(region + '_literal_conditional_intersection',
          removed == ({(3, 3)} if region == 'missing5_extra7' else set()))
    for d5, d7 in product((0, 2, 3, 4), (0, 2, 3, 4, 5, 6)):
        check(f'{region}_same_union_{d5}_{d7}',
              (d7 in singles or (d5, d7) in pairs) ==
              (d7 in singles or (d5, d7) in pairs - removed))
    p = {int(k): F(v) for k, v in row['scope_union_probabilities'].items()}
    check(region + '_source_profile', p == profile_weights(region, t))
    residual = dict(p)
    residual[3] -= len(removed) * t[5] * t[7]
    check(region + '_residual_profile', residual == profile_weights(region, t, True))
    before = {m: phi(m, p) for m in range(64)}
    after = {m: phi(m, residual) for m in range(64)}
    check(region + '_old_polynomials', before == {int(k): F(v) for k, v in row['all64_polynomials'].items()})
    for mask in range(64):
        check(f'{region}_positive_nondecreasing_{mask}', after[mask] >= before[mask] > 0)
    check(region + '_exact_gain',
          after[63] - before[63] == len(removed) * t[5] * t[7] * before[60])
    mass = F(row['mass'])
    corrected += mass * after[63]
    finite_profiles[region] = {'mass': mass, 'original_phi': before[63],
                               'residual_phi': after[63], 'gain': after[63] - before[63]}

base = phi(63, profile_weights('base', t))
old = phi(63, profile_weights('zero', t))
zero_mass = F(source['zero_root_mass'])
check('finite_cross_term_cancelled', corrected == (1 - zero_mass) * base + zero_mass * old)
check('finite_lower_bound_above_uniform', corrected > S0)
check('finite_same_law_query', 5 + B5 / corrected < F(565, 51))

endpoints = {}
t_limit = {q: F(1, q - 2) for q in Q}
for region in REGIONS:
    values = {m: phi(m, profile_weights(region, t_limit, True)) for m in range(64)}
    for mask, value in values.items():
        check(f'endpoint_{region}_positive_{mask}', value > 0)
    endpoints[region] = values
check('uniform_baseline', endpoints['base'][63] == S0)
check('uniform_old_profile', endpoints['zero'][63] == F(2689, 2805))
check('uniform_positive_margin', S0 > TARGET)

# Formula samples accompany, and do not replace, the all-height ordinary proof.
samples = {}
for n in (3, 4, 5, 8):
    tn = {q: (1 - F(1, q ** n)) / (q - 2 + F(1, q ** n)) for q in Q}
    size = (3 ** n + 1) // 2
    moved = (3 ** (n - 2) - 1) // 2
    counts = {'zero': 1, 'base': 2 * 3 ** (n - 2), 'extra5': 3 ** (n - 2),
              'missing5': (3 ** (n - 2) + 1) // 2,
              'missing5_extra7': moved, 'missing7': moved}
    check(f'n{n}_root_partition', sum(counts.values()) == size)
    value = sum((F(counts[r], size) * phi(63, profile_weights(r, tn, True)) for r in REGIONS), F())
    expected = (F(size - 1, size) * phi(63, profile_weights('base', tn))
                + F(1, size) * phi(63, profile_weights('zero', tn)))
    check(f'n{n}_cancelled_formula', value == expected)
    check(f'n{n}_positive_box', all(profile_weights(r, tn, True)[m] <=
                                    profile_weights(r, t_limit, True)[m]
                                    for r in REGIONS for m in range(1, 64)))
    check(f'n{n}_uniform_margin', value >= S0 > TARGET)
    samples[n] = {'residual_lower_bound': value, 'query_bound': 5 + B5 / value}

# Keep the finite C_5 core, while every original outside its exponent box
# may have arbitrary support and phase, including additional pure originals.
# All charges use the core's fixed pure source, without reconditioning it.
depth = 5
den = {p: p - 2 + F(1, p ** depth) for p in P}
cap_total = prod((1 + 1 / den[p] for p in P), start=F(1))
cap_inside_box = prod(((p - 1) / den[p] for p in P), start=F(1))
outside_charge = cap_total - cap_inside_box
core_mass = samples[depth]['residual_lower_bound']
survival = core_mass - outside_charge
query = 5 + B5 / survival
pure_haar_mass = 1 / cap_inside_box
fresh_reserve = 1 - (1 + query) * F(51, 616)
core_labels = 7 * depth + depth * ((depth + 1) ** 6 - 1) + (depth + 1) ** 4 - 1 - 4 * depth
check('finite_core_original_count', core_labels == 234585)
check('outside_box_charge_positive', outside_charge > 0)
check('arbitrary_outside_box_survival', survival > TARGET)
check('arbitrary_outside_box_query', query < F(565, 51))
check('arbitrary_outside_box_exact_survival',
      survival == F(2155755259013490113345803666836671227,
                    12596688478752606034800835467400970240))
check('fresh_23_29_continuation', fresh_reserve > 0)
prefix_consumer = {'core_height': depth, 'core_original_count': core_labels,
                   'core_survival_lower_bound': core_mass,
                   'full_cap_euler_sum_including_unit': cap_total,
                   'box_cap_sum_including_unit': cap_inside_box,
                   'outside_box_charge': outside_charge,
                   'same_source_survival_lower_bound': survival,
                   'uniform_survivor_query_bound': query,
                   'source_pure_Haar_mass': pure_haar_mass,
                   'Haar_survival_lower_bound': pure_haar_mass * survival,
                   'fresh_23_29_relative_reserve': fresh_reserve,
                   'fresh_23_29_Haar_lower_bound': pure_haar_mass * survival * fresh_reserve}

result = {'scope': __doc__, 'source': source_path.name, 'source_sha256': SOURCE_SHA,
          'finite_profiles': finite_profiles, 'finite_residual_lower_bound': corrected,
          'finite_gain': corrected - F(source['G']), 'finite_query_bound': 5 + B5 / corrected,
          'endpoint_polynomials': endpoints, 'uniform_lower_bound': S0,
          'target': TARGET, 'uniform_survival_margin': S0 - TARGET,
          'uniform_query_bound': 5 + B5 / S0,
          'uniform_query_margin': F(565, 51) - (5 + B5 / S0),
          'sample_heights': samples, 'finite_prefix_consumer': prefix_consumer,
          'passed_checks': len(CHECKS), 'checks': CHECKS}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
args.output.write_text(json.dumps(result, default=encode, indent=2) + '\n')
print(json.dumps({'passed_checks': len(CHECKS), 'finite_G': float(corrected),
                  'finite_query': float(5 + B5 / corrected), 'uniform_G': float(S0),
                  'uniform_query': float(5 + B5 / S0),
                  'outside_box_survival': float(survival), 'outside_box_query': float(query)}, indent=2))
print('json_sha256=' + hashlib.sha256(args.output.read_bytes()).hexdigest())
