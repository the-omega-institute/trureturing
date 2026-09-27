#!/usr/bin/env python3
"""A complete95-label CRT example for central-cell-dependent root deletion.

Standard library only. This checks a finite example and the inherited scalar
interface; it does not rerun Report640's gate certificate or verify Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
import argparse
import json
import hashlib

Q = (7, 11, 13, 17, 19)
P = (3, 5) + Q + (23, 29, 31)
STAR_ROLES = ((1,0,1),(0,1,1),(1,1,1),(2,0,1),(0,2,1),
              (1,0,2),(0,1,2),(2,0,2),(2,1,1),(1,2,1),(2,2,1))

def crt(parts):
    value, modulus = 0, 1
    for p, exponent, residue in parts:
        power = p ** exponent
        value += modulus * (((residue - value) * pow(modulus, -1, power)) % power)
        modulus *= power
        value %= modulus
    return value, modulus

def original(kind, parts):
    parts = sorted(parts)
    value, modulus = crt(parts)
    return dict(kind=kind, modulus=modulus, residue=value,
                components=[dict(prime=p, exponent=e, residue=a) for p,e,a in parts])

def construct():
    rows = []
    for p in P:
        rows.append(original('pure', [(p, 1, 2 if p == 3 else 4 if p == 5 else 0)]))
    rows.append(original('central15', [(3,1,0),(5,1,0)]))
    for q in Q:
        for a,b,e in STAR_ROLES:
            # A mixed central star lives in row0 / column1, outside the15 mask.
            parts = ([(3,a,0)] if a else []) + ([(5,b,1 if a else 0)] if b else [])
            outside_root = 2 if q == 7 and a == 0 else 1
            rows.append(original('star', parts + [(q,e,outside_root)]))
    for q,r in combinations(Q,2):
        for eq,er in ((1,1),(2,1),(1,2)):
            rows.append(original('pair', [(q,eq,1),(r,er,1)]))
        rows.append(original('pair', [(3,2,0),(q,1,1),(r,1,1)]))
    return sorted(rows, key=lambda row: row['modulus'])

def central(l,m):
    return 3*(l % 3) + l//3, 5*(m % 5) + m//5

def roots(l,m):
    x3,x5 = central(l,m)
    t7 = 2 if x3 % 3 != 0 and x5 % 5 == 0 else 1
    return {q: t7 if q == 7 else 1 for q in Q}

def active(row,l,m):
    x3,x5 = central(l,m)
    values = {3:x3,5:x5}
    return all(values[c['prime']] % c['prime']**c['exponent'] == c['residue']
               for c in row['components'] if c['prime'] in values)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--write', action='store_true', help='write the explicit CRT fixture before verifying it')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.write:
        fixture = dict(schema='central-cell-root-example-v1',
                       scope='Literal ten-prime head; complete55-star40-pair inventory with one global phase per original',
                       outside_primes=list(Q), originals=construct(),
                       central_cells=[dict(l=l,m=m,residues=list(central(l,m)),
                                           mask=not(l<3 and m<5),
                                           deleted_roots=[roots(l,m)[q] for q in Q])
                                      for l in range(6) for m in range(20)],
                       inherited_base_gate='23282735008494655373261/638394875922057408000000',
                       inherited_alpha='2673/110656',
                       two_root_extension=dict(
                           replacement=dict(modulus=63,old_residue=36,new_residue=9,
                                            new_components=[dict(prime=3,exponent=2,residue=0),
                                                            dict(prime=7,exponent=1,residue=2)]),
                           added_originals=[original('pure',[(3,2,1)]),original('pure',[(5,2,6)])],
                           ternary_leaf_mask=[0],additional_live_root_at7=2,
                           inherited_gate='3214176579848528977121/134398921246748928000000',
                           full_network_density_denominator=4250),
                       new_lean_verification=False)
        args.certificate.write_text(json.dumps(fixture, indent=2)+'\n')
    raw = args.certificate.read_bytes()
    fixture = json.loads(raw)
    checks = Counter()
    def ck(name, predicate):
        if not predicate:
            raise ArithmeticError(name)
        checks[name] += 1
    rows = fixture['originals']
    by_modulus = {row['modulus']: row for row in rows}
    ck('106_distinct_original_moduli', len(rows) == len(by_modulus) == 106)
    ck('complete_role_inventory', Counter(row['kind'] for row in rows) ==
       Counter(pure=10,central15=1,star=55,pair=40))
    expected_labels = {p for p in P} | {15}
    expected_labels |= {3**a*5**b*q**e for q in Q for a,b,e in STAR_ROLES}
    expected_labels |= {q*r for q,r in combinations(Q,2)}
    expected_labels |= {q*q*r for q,r in combinations(Q,2)}
    expected_labels |= {q*r*r for q,r in combinations(Q,2)}
    expected_labels |= {9*q*r for q,r in combinations(Q,2)}
    ck('all_expected_numerical_labels', set(by_modulus) == expected_labels)
    for row in rows:
        ck('odd_valid_canonical_residue', row['modulus'] > 1 and row['modulus'] % 2 == 1
           and 0 <= row['residue'] < row['modulus'])
        product = 1
        primes = []
        for component in row['components']:
            p,e,a = (component[key] for key in ('prime','exponent','residue'))
            primes.append(p)
            product *= p**e
            ck('actual_CRT_component', row['residue'] % p**e == a and 0 <= a < p**e)
        ck('component_product_and_distinctness', product == row['modulus'] and len(set(primes)) == len(primes))
    anchors = [row for row in rows if row['kind'] in ('star','pair')]
    cell_activity = Counter()
    for cell in fixture['central_cells']:
        l,m = cell['l'],cell['m']
        ck('literal_central_cell', cell['residues'] == list(central(l,m)))
        ck('literal_mask', cell['mask'] == (not(l<3 and m<5)))
        ck('declared_root_table', cell['deleted_roots'] == [roots(l,m)[q] for q in Q])
        for q,t in zip(Q,cell['deleted_roots']):
            ck('exactly_one_live_deleted_root', 0 < t < q)
        if not cell['mask']:
            continue
        root_table = dict(zip(Q,cell['deleted_roots']))
        for row in anchors:
            is_active = active(row,l,m)
            if is_active:
                cell_activity[row['modulus']] += 1
            covered = any(component['prime'] in Q and
                          component['residue'] % component['prime'] == root_table[component['prime']]
                          for component in row['components'])
            ck('every_active_actual_anchor_absorbed', not is_active or covered)
    ck('all120_cells_once', {(cell['l'],cell['m']) for cell in fixture['central_cells']} ==
       {(l,m) for l in range(6) for m in range(20)} and len(fixture['central_cells']) == 120)
    ck('all95_anchors_have_unmasked_active_cells', set(cell_activity) == {row['modulus'] for row in anchors})
    ck('global_t7_conflict_explicit', by_modulus[21]['residue'] == 15 and by_modulus[35]['residue'] == 30
       and 15 % 7 != 30 % 7)
    for candidate in range(1,7):
        ck('no_global_live_t7', not(15 % 7 == candidate and 30 % 7 == candidate))
    # A simultaneous change of CRT reference preserves the same actual relations.
    # Shift15 keeps the literal first3/5 and15 conventions, changes higher digits.
    for shift in (0,15,30):
        for row in rows:
            shifted = (row['residue'] + shift) % row['modulus']
            for component in row['components']:
                p,e,a = (component[key] for key in ('prime','exponent','residue'))
                ck('joint_reference_translation_CRT', shifted % p**e == (a+shift) % p**e)
        ck('translated_global_t7_conflict', (15+shift) % 7 != (30+shift) % 7)
        ck('translation_keeps_literal_central_conventions',
           (2+shift) % 3 == 2 and (4+shift) % 5 == 4 and shift % 15 == 0)
        for l in range(6):
            for m in range(20):
                x3,x5 = central(l,m)
                ck('translated_mask_agrees',
                   (x3 % 3 == 0 and x5 % 5 == 0) ==
                   ((x3+shift) % 3 == 0 and (x5+shift) % 5 == 0))
                table = roots(l,m)
                for row in anchors:
                    if l<3 and m<5 or not active(row,l,m):
                        continue
                    ck('translated_active_anchor_absorbed', any(
                        c['prime'] in Q and (c['residue']+shift) % c['prime'] ==
                        (table[c['prime']]+shift) % c['prime'] for c in row['components']))
    alpha = F(fixture['inherited_alpha'])
    gamma = F(fixture['inherited_base_gate'])
    tail = F(19740202146111572828188083,495176015714152109959649689600)
    ck('inherited_head_bound', alpha*gamma > F(1,1200))
    ck('inherited_complete_network_bound',
       alpha*(gamma-F(1411,100000)-F(1,65536)-tail) > F(1,1900))

    # A single replacement forces two distinct7 roots in the SAME live cell.
    # Reconstruct the extension from the base table; do not duplicate a snapshot.
    extension = fixture['two_root_extension']
    replacement = extension['replacement']
    ck('two_root_replacement_contract', replacement['modulus'] == 63
       and replacement['old_residue'] == 36 and replacement['new_residue'] == 9
       and by_modulus[63]['residue'] == 36)
    rows2 = [{**row,'components':[dict(c) for c in row['components']]} for row in rows]
    by_modulus2 = {row['modulus']:row for row in rows2}
    changed = by_modulus2[63]
    changed['residue'] = replacement['new_residue']
    changed['components'] = replacement['new_components']
    ck('two_root_exactly_one_original_changed', sum(row != by_modulus[row['modulus']] for row in rows2) == 1)
    ck('two_root_added_actual_square_contract', extension['added_originals'] ==
       [original('pure',[(3,2,1)]),original('pure',[(5,2,6)])])
    rows2.extend(extension['added_originals'])
    by_modulus2 = {row['modulus']:row for row in rows2}
    ck('two_root_full_unique_inventory', len(rows2) == len(by_modulus2) == 108
       and set(by_modulus2) == expected_labels | {9,25})
    ck('actual_squares_not_in_first_pure_classes',
       by_modulus2[9]['residue'] % 3 != by_modulus2[3]['residue'] and
       by_modulus2[25]['residue'] % 5 != by_modulus2[5]['residue'])
    ck('actual_fixed_square_null_indices', central(3,6) == (by_modulus2[9]['residue'],by_modulus2[25]['residue']))
    for row in rows2:
        ck('two_root_actual_original_CRT', 0<=row['residue']<row['modulus'] and all(
            row['residue'] % c['prime']**c['exponent'] == c['residue'] for c in row['components']))
        product = 1
        for c in row['components']:
            product *= c['prime']**c['exponent']
        ck('two_root_actual_modulus_factorization', product == row['modulus'])
    ck('two_root_leaf_mask_contract', extension['ternary_leaf_mask'] == [0]
       and extension['additional_live_root_at7'] == 2)
    anchors2 = [row for row in rows2 if row['kind'] in ('star','pair')]
    activity2 = Counter()
    for l in range(6):
        for m in range(20):
            sets = {q:{t} for q,t in roots(l,m).items()}
            if l in extension['ternary_leaf_mask']:
                sets[7].add(extension['additional_live_root_at7'])
            for q in Q:
                ck('two_root_live_set_cardinality', all(0<t<q for t in sets[q])
                   and len(sets[q]) == (2 if q == 7 and l == 0 else 1))
            if l<3 and m<5:
                continue
            for row in anchors2:
                enabled = active(row,l,m)
                if enabled and l != 3 and m != 6:
                    activity2[row['modulus']] += 1
                covered = any(c['prime'] in Q and c['residue'] % c['prime'] in sets[c['prime']]
                              for c in row['components'])
                ck('two_root_every_active_anchor_absorbed', not enabled or covered)
    ck('two_root_all95_anchors_nonvacuous', len(anchors2) == len(activity2) == 95)
    witness = (0,5)
    ck('two_root_live_conflict_cell', central(*witness) == (0,1)
       and active(by_modulus2[21],*witness) and active(by_modulus2[63],*witness))
    witness_values = dict(zip((3,5),central(*witness)))
    central_pure = [row for row in rows2 if row['kind'] == 'pure' and
                    all(c['prime'] in (3,5) for c in row['components'])]
    ck('conflict_cell_avoids_all_actual_central_pure_originals', len(central_pure) == 4 and all(
        any(witness_values[c['prime']] % c['prime']**c['exponent'] != c['residue']
            for c in row['components']) for row in central_pure))
    # All fixed-null624 comparison vertices give positive mass at this cell.
    # Convex combinations therefore retain the same lower bound.
    cell_mass_lower = F(1,225)
    for weak3 in range(6):
        if weak3 == 3:
            continue
        for weak5 in range(20):
            if weak5 == 6:
                continue
            weight3 = F(1 if weak3 == witness[0] else 2,9)
            weight5 = F(3 if weak5 == witness[1] else 4,75)
            ck('fixed_actual_null_corner_conflict_mass_positive', weight3*weight5 >= cell_mass_lower > 0)
    ck('two_root_conflict_roots', by_modulus2[21]['residue'] % 7 == 1
       and by_modulus2[63]['residue'] % 7 == 2)
    for candidate in range(1,7):
        ck('no_single_root_at_conflict_cell', not(candidate == by_modulus2[21]['residue'] % 7
                                                 and candidate == by_modulus2[63]['residue'] % 7))
    gamma2 = F(extension['inherited_gate'])
    ck('two_root_inherited_gate_exact', gamma2 == F(3214176579848528977121,134398921246748928000000))
    bound2 = alpha*(gamma2-F(1411,100000)-F(1,65536)-tail)
    ck('two_root_network_bound', extension['full_network_density_denominator'] == 4250
       and bound2 > F(1,4250))
    result = dict(schema='central-cell-root-example-verification-v1',status='PASS',
                  check_count=sum(checks.values()),checks=dict(checks),
                  original_count=len(rows),anchor_count=len(anchors),
                  nonvacuous_anchor_count=len(cell_activity),central_cell_count=120,
                  two_root_extension=dict(original_count=len(rows2),anchor_count=len(anchors2),
                                          nonvacuous_anchor_count=len(activity2),
                                          single_root_conflict_cell=list(witness),
                                          fixed_actual_square_nulls=[3,6],
                                          conflict_central_mass_lower=str(cell_mass_lower),
                                          strictness_scope='Singleton root tables retaining and absorbing the positive conflict cell; other thinning is not excluded',
                                          inherited_gate=str(gamma2),projected_network_bound=str(bound2)),
                  fixture_sha256=hashlib.sha256(raw).hexdigest(),
                  inherited_gate_recomputed=False,new_lean_verification=False)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
