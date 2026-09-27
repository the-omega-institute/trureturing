#!/usr/bin/env python3
"""Exact scope-Shearer certificate for prefix-free rooted labels and later-four mixed towers."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import hashlib
import json

Q = (5, 7, 11, 13, 17, 19)
X = {q: F(1, q-2) for q in Q}
FULL = (1 << len(Q))-1
PAIR_PRIMES = (11, 13, 17, 19)
PAIRS = tuple(combinations(PAIR_PRIMES, 2))
PAIR_MASKS = {sum(1 << Q.index(q) for q in pair) for pair in PAIRS}
LATE_MASK = sum(1 << Q.index(q) for q in PAIR_PRIMES)
LATE_MIXED_MASKS = {mask for mask in range(1, FULL+1)
                   if not mask & ~LATE_MASK and mask.bit_count() >= 2}
B5 = F(19132074022251234990036997833948759259,
       18473247078046657922374787501704265625)
TARGET = F(565, 51)
checks = {}


def check(name, value):
    if name in checks:
        raise RuntimeError('duplicate check: ' + name)
    if not value:
        raise RuntimeError(name)
    checks[name] = True


def scopes(mask):
    return tuple(q for j, q in enumerate(Q) if mask & (1 << j))


CAP = {mask: prod((X[q] for q in scopes(mask)), start=F(1))
       for mask in range(1, FULL+1)}


def disjoint_scope_families(mask):
    # Enumerate set partitions of every used-coordinate subset. Coordinates
    # may be unused; block order is canonical by least member, not permuted.
    positions = tuple(j for j in range(len(Q)) if mask & (1 << j))

    def visit(k, blocks):
        if k == len(positions):
            yield blocks
            return
        bit = 1 << positions[k]
        yield from visit(k+1, blocks)
        yield from visit(k+1, blocks+(bit,))
        for i in range(len(blocks)):
            yield from visit(k+1, blocks[:i]+(blocks[i] | bit,)+blocks[i+1:])

    return visit(0, ())


def partition_polynomial(mask, weights):
    total = F(0)
    count = 0
    families = set()
    for blocks in disjoint_scope_families(mask):
        check_key = blocks
        if check_key in families:
            raise RuntimeError('duplicate scope family')
        families.add(check_key)
        total += (-1)**len(blocks)*prod((weights[s] for s in blocks), start=F(1))
        count += 1
    return total, count


def recursive_polynomials(weights):
    @lru_cache(None)
    def phi(mask):
        if mask == 0:
            return F(1)
        first = mask & -mask
        result = phi(mask ^ first)
        subset = mask
        while subset:
            if subset & first:
                result -= weights[subset]*phi(mask ^ subset)
            subset = (subset-1) & mask
        return result
    return {mask: phi(mask) for mask in range(FULL+1)}


def consumer(s0):
    omega = prod((F(p-2, p-1) for p in (3,)+Q), start=F(1))
    R = 5+B5/s0
    H = omega*s0
    fresh_relative = 1-F(51, 616)*(1+R)
    fresh_H = H*fresh_relative
    check('fresh_identity_'+str(s0), fresh_H == omega*(310*s0-51*B5)/616)
    return {'source_survivor_reserve': s0, 'mixed_loss_upper': 1-s0,
            'R_upper': R, 'R_decimal': float(R), 'target_minus_R': TARGET-R,
            'crossed': R < TARGET, 'Haar_survivor_lower': H,
            'Haar_survivor_decimal': float(H),
            'fresh23_29_relative_reserve': fresh_relative,
            'fresh23_29_Haar_lower': fresh_H,
            'fresh23_29_Haar_decimal': float(fresh_H)}


check('source_pure_mass', prod((F(p-2,p-1) for p in (3,)+Q), start=F(1)) == F(935,4096))
results = {}
for name, weights in (
    ('base_all63_scopes', CAP),
    ('six_old_pairs', {mask: cap*(2 if mask in PAIR_MASKS else 1) for mask, cap in CAP.items()}),
    ('all11_later_four_mixed_scopes',
     {mask: cap*(2 if mask in LATE_MIXED_MASKS else 1) for mask, cap in CAP.items()}),
):
    recursive = recursive_polynomials(weights)
    direct = {}
    for mask in range(FULL+1):
        phi, family_count = partition_polynomial(mask, weights)
        direct[mask] = {'primes': scopes(mask), 'phi': phi, 'disjoint_family_count': family_count}
        check(f'{name}_formula_{mask}', phi == recursive[mask])
        check(f'{name}_positive_{mask}', phi > 0)
    minima = {size: min((v['phi'], mask) for mask, v in direct.items() if mask.bit_count() == size)
              for size in range(7)}
    results[name] = {'weights': weights, 'all64_coordinate_polynomials': direct,
                     'minima_by_coordinate_count': minima,
                     'consumer': consumer(direct[FULL]['phi'])}

base = results['base_all63_scopes']
six = results['six_old_pairs']
late = results['all11_later_four_mixed_scopes']
check('63_scope_weights', len(CAP) == 63)
check('six_distinct_pairs', len(PAIR_MASKS) == 6)
check('base_full_phi', base['all64_coordinate_polynomials'][FULL]['phi'] == F(70991, 378675))
check('base_minima', tuple(base['minima_by_coordinate_count'][i][0] for i in range(7)) ==
      (F(1), F(2, 3), F(7, 15), F(49, 135), F(422, 1485), F(343, 1485), F(70991, 378675)))
check('six_pairs_full_phi', six['all64_coordinate_polynomials'][FULL]['phi'] == F(66184, 378675))
check('six_pairs_global_minimum', min(v['phi'] for v in six['all64_coordinate_polynomials'].values()) ==
      F(66184, 378675))
check('six_pairs_Haar', six['consumer']['Haar_survivor_lower'] == F(8273, 207360))
check('six_pairs_crosses', six['consumer']['crossed'])
check('six_pairs_fresh_positive', six['consumer']['fresh23_29_Haar_lower'] > 0)
check('eleven_late_mixed_scopes', len(LATE_MIXED_MASKS) == 11)
check('all_late_mixed_full_phi', late['all64_coordinate_polynomials'][FULL]['phi'] == F(65869, 378675))
check('all_late_mixed_global_minimum',
      min(v['phi'] for v in late['all64_coordinate_polynomials'].values()) == F(65869, 378675))
check('all_late_mixed_R', late['consumer']['R_upper'] ==
      F(35198810825365453128135695634830231134, 3213347360622843627619739560176294375))
check('all_late_mixed_Haar', late['consumer']['Haar_survivor_lower'] == F(65869, 1658880))
check('all_late_mixed_crosses', late['consumer']['crossed'])
check('all_late_mixed_fresh_positive', late['consumer']['fresh23_29_Haar_lower'] > 0)
check('full_inventory_877_disjoint_families', base['all64_coordinate_polynomials'][FULL]['disjoint_family_count'] == 877)

collision_margin = F(65869,378675)-F(51,310)*B5
collision_consumer = consumer(F(65869,378675)-F(1,300))
check('collision_margin_exact', collision_margin ==
      F(400037385456245883730046551436559491,112288364592048312861493806382908281250))
check('collision_allowance', F(1,300) < collision_margin)
check('collision_R_exact', collision_consumer['R_upper'] ==
      F(139563693496258701984384463372540640161,12607079481450752404847294407349120625))
check('collision_crosses', collision_consumer['crossed'])
check('collision_fresh_positive', collision_consumer['fresh23_29_Haar_lower'] > 0)


qpart_cap = prod((1+X[q] for q in Q), start=F(1))-1
root_tail = qpart_cap/3**6
six_layer_consumer = consumer(F(65869,378675)-root_tail)
check('complete_Qpart_weight', qpart_cap == F(1113,935))
check('six_layer_tail', root_tail == F(371,227205) < F(1,300))
check('six_layer_query', six_layer_consumer['R_upper'] ==
      F(35047987237285188387280497770277684259,3183182643006790679448699987265785000)
      and six_layer_consumer['crossed'])
check('six_layer_Haar', six_layer_consumer['Haar_survivor_lower'] == F(24469,622080))
check('six_layer_fresh_positive', six_layer_consumer['fresh23_29_Haar_lower'] > 0)

result = {'scope': 'Exact arithmetic only; ordinary scope-Shearer applicability is a separate proof obligation.',
          'primes': Q, 'scope_weights_x': X, 'six_old_pair_towers': PAIRS,
          'all11_later_four_scopes': [scopes(mask) for mask in sorted(LATE_MIXED_MASKS)],
          'B5': B5, 'target': TARGET, 'exact_loss_ceiling': 1-F(51,310)*B5,
          'results': results,
          'actual_collision_budget_maximum': collision_margin,
          'collision_allowance_1over300_consumer': collision_consumer,
          'complete_Qpart_weight': qpart_cap,
          'six_layer_root_tail_allowance': root_tail,
          'six_layer_consumer': six_layer_consumer,
          'checks': checks, 'passed_checks': len(checks),
          'claim_limit': 'No broader pair-inventory search. Positive coordinate-subset values plus the separate downward-closure argument are required for all induced event subgraphs.'}


def encode(v):
    if isinstance(v, F):
        return str(v)
    raise TypeError(type(v).__name__)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
args.output.write_text(json.dumps(result, indent=2, default=encode)+'\n')
print(json.dumps({'passed_checks': len(checks),
                  'base_phi': base['all64_coordinate_polynomials'][FULL]['phi'],
                  'six_pairs_phi': six['all64_coordinate_polynomials'][FULL]['phi'],
                  'all_late_mixed_phi': late['all64_coordinate_polynomials'][FULL]['phi'],
                  'all_late_mixed_minima': late['minima_by_coordinate_count'],
                  'all_late_mixed_consumer': late['consumer']}, indent=2, default=encode))
print(hashlib.sha256(args.output.read_bytes()).hexdigest())
