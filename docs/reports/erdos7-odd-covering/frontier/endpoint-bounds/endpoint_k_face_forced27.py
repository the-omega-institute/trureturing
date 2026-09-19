#!/usr/bin/env python3
"""Exact forced27 and complete pure3-tail caps over both actual K beta faces.

The ordinary proof supplies saturation and arbitrary-label geometry. This
checks every first-beta table, all complete cap sums, forced27 exclusions,
and the retained actual398 construction. No finite search implies universality.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_k_face_forced27.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/endpoint_k_face_linear.py': '4fa0effc17c4f42a419f96f76931f389b8ca0af3ff3a4f60fd227ddbe6fc8b46',
    'certificates/source_norms/endpoint-bounds/endpoint_k_face_linear.json': '71244eac4f9cce79585c17663f80fcc7e16a03fcfcfda373c9747acc5c844682',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
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
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('forced27_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/endpoint-bounds/endpoint_k_face_linear.json'))
    for path, pin in old['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent source pin')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
        used[path] = pin
    require(old['face_vertices'] == [398, 410, 422] and old['carrier'] == [1, 1], 'Same entire actual beta face')
    eta, roots = (F(1, 18),)+(F(1, 9),)*4, (0, 0, 1, 1, 1)
    raw_deep3 = F(3, 4)*F(1, 18)
    deep3_deletion = raw_deep3/5
    product_deletion_coefficient = F(1, 18)/5
    require((raw_deep3, deep3_deletion, product_deletion_coefficient) == (F(1, 24), F(1, 120), F(1, 90)), 'Complete deep3 old cap and deletion tails')
    cap27 = F(3, 4)*F(1, 27)
    late_first = F(1, 27)*F(1, 5)
    pure_after27 = F(1, 81)/(1-F(1, 3))
    third_child_eta = F(1, 27)-pure_after27
    exclusion_caps = (F(0), cap27-late_first, F(3, 4)*third_child_eta, F(1, 2)*F(1, 27))
    require(pure_after27 == third_child_eta == F(1, 54) and max(exclusion_caps) < cap27, 'All cell0 children and root1 fail the forbidden27 cap')
    forced27_mass = cap27/5
    require(forced27_mass == F(1, 180), 'Full forbidden27 seven-depth deletion in cell1')
    beta_vertices = []
    for position in range(3):
        beta = tuple(F(1, 4) if j == position else F(0) for j in range(3))
        old_cells = [F(1, 40), F(11, 180)]+[F(1, 30)-F(4, 45)*b for b in beta]
        cells = old_cells[:]
        cells[1] -= forced27_mass
        new_roots = (sum(old_cells[:2])-deep3_deletion, sum(old_cells[2:]))
        require(new_roots == (F(7, 90), F(7, 90)) and max(cells) == F(1, 18), 'Both test roots and the cell maximum improve throughout the affine beta face')
        beta_vertices.append({'beta': beta, 'cell_caps': cells, 'root_caps': new_roots})
    qslots = tuple(map(F, ('0', '1/5', '1/5', '3/20', '1/5')))
    tables = []
    for source_table in old['first_beta_slot_tables']:
        L = source_table['first_beta_cell']
        pre = [[F(v) for v in row] for row in source_table['pre_coefficients']]
        kept = [[eta[l]*pre[l][j]*(1-F(int(l >= 2)+int(l == 1)+int(j == 4)+int(l >= 2 and j == 4), 5))
                 for j in range(5)] for l in range(5)]
        before = [sum(kept[l][j] for l in range(5)) for j in range(5)]
        after = [v-product_deletion_coefficient*q for v, q in zip(before, qslots)]
        root_slots = [[sum(kept[l][j] for l in range(5) if roots[l] == r) for j in range(5)] for r in (0, 1)]
        require(after == list(map(F, ('0', '2/75', '14/225', '7/150', '7/150'))), 'Whole-face first-five caps with complete extra deletion')
        require(max(root_slots[0]) <= F(8, 225) and max(root_slots[1]) == F(8, 225), 'Every arbitrary15 test')
        require(max(map(max, kept)) == F(4, 225), 'Every arbitrary45 test')
        tables.append({'first_beta_cell': L, 'selected_cell_slot_caps': kept, 'first5_before_deep3': before,
                       'pure5_complement_in_slots': qslots, 'first5_after_deep3': after,
                       'first15_root_caps': root_slots, 'first45_cap': F(4, 225)})
    require(len(tables) == 3, 'All possible first-beta locations')
    old_deep5 = sum(eta)-(sum(eta[2:])+eta[1])/5
    new_deep5 = old_deep5-product_deletion_coefficient
    deep15 = max(sum(eta[:2])-eta[1]/5-product_deletion_coefficient, F(4, 5)*sum(eta[2:]))
    deep45 = max(eta[l]*(1-F(int(l >= 2)+int(l == 1), 5)) for l in range(5))
    require((new_deep5, deep15, deep45) == (F(2, 5), F(4, 15), F(4, 45)), 'Complete arbitrary descendant-five caps')
    categories = {'test3': F(7, 90), 'test9': F(1, 18), 'pure3_deep': F(7, 10)*F(1, 18),
                  'test5': F(14, 225), 'pure5_deep': new_deep5/20,
                  'test15': F(8, 225), '3_times_deep5': deep15/20,
                  'test45': F(4, 225), '9_times_deep5': deep45/20,
                  'deep35': F(1, 18)*F(1, 4)}
    nonunit = sum(categories.values())
    D, C, s = F(53, 360), F(37, 72), F(1, 4)
    positive7 = (s+C)/5
    numerator = D+nonunit+positive7
    margin = 6*D-numerator
    gain = margin-F(old['old_margin_upper'])
    require((nonunit, numerator, margin) == (F(611, 1800), F(1151, 1800), F(439, 1800)), 'Complete original-label numerator and signed margin')
    require(F(old['linear_upper'])-numerator == F(23, 900) and gain == F(1298, 24300), 'Strict improvement over72 and the old49 margin')
    uncoupled = D+C+positive7
    require(uncoupled == F(293, 360) and uncoupled-numerator == F(157, 900), 'Exact complete raw-cap improvement')
    constructor = module('forced27_actual398', base/'frontier/source-budgets/source_mass_compatibility.py')
    actual = constructor.check(3, 398)
    t, q = F(1, 18), F(1, 4)
    H = F(4, 9)+t+q/9-t*q
    require(H == C and s-H/5 == D, 'Existing complete actual398 construction saturates the mass cap')
    return {'schema': 'erdos7-endpoint-k-face-forced27-v1', 'source_sha256': used,
            'face_vertices': [398, 410, 422], 'carrier': [1, 1],
            'symmetric_face_vertices': [616, 628, 640], 'symmetric_carrier': [1, 0],
            'raw_deep3_cap': raw_deep3, 'complete_deep3_deletion': deep3_deletion,
            'deep3_five_complement_coefficient': product_deletion_coefficient,
            'forbidden27_cap': cap27, 'depth3_late_mass': late_first,
            'depth3_third_child_eta': third_child_eta, 'excluded_forbidden27_caps': exclusion_caps,
            'forced27_cell1_deletion': forced27_mass, 'affine_beta_checks': beta_vertices,
            'first_beta_slot_tables': tables, 'complete_descendant5_coefficients': (new_deep5, deep15, deep45),
            'complete_nonunit_zero7_categories': categories, 'nonunit_zero7_upper': nonunit,
            'surviving_mass': D, 'positive7_upper': positive7, 'linear_upper': numerator,
            'signed_barrier': 6, 'margin_lower': margin, 'improvement_over72': F(23, 900),
            'old49_margin_upper': F(old['old_margin_upper']), 'gain_over_old49': gain,
            'uncoupled_upper': uncoupled, 'gain_over_uncoupled': uncoupled-numerator,
            'actual398_height3_check': actual, 'actual398_complete_limit': {'s': s, 'H': H, 'S': D},
            'scope': ('Ordinary uniform endpoint linear theorem on both entire actual K beta faces. '
                      'Forced27 and complete deep3 deletion retain original labels. No claim that the '
                      'whole relaxed beta simplex is realizable, no new neighborhood, global K or Lean result.')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('forced27_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical exact forced27 face certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:forced27 exclusions, all three first-beta tables, complete original tails and actual398 mass saturation.')
    print('Uniform face linear1151/1800; signed margin439/1800; improvement23/900 over72.')
    print('This endpoint result does not update the finite neighborhood or global K certificate.')


if __name__ == '__main__':
    main()
