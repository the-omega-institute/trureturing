#!/usr/bin/env python3
"""Retain the compulsory pure-three deletion inside both shallow cross terms."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/pure_axis_shared_deletion_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/comparison-bounds/pure_axis_joint_square_comparison.py': '9ca0334f9b9c15c1fdceb5ef18befac104efd693a6a93fd1a8fc6fbd222e09ae', 'certificates/source_norms/comparison-bounds/pure_axis_joint_square_comparison.json': '8366ce45c9e3690838d3ed6d26b7dfdd456de3ed2536cef0fd1f8453a53a66f3', 'frontier/endpoint-bounds/endpoint_k_face_forced27.py': '8ea52815e6ae5b9b4df5733a8c8bae8f0704a12da0d531d794873406f0f29c87', 'certificates/source_norms/endpoint-bounds/endpoint_k_face_forced27.json': '59202ce65324295b32b028f6b67f90e4a7b8bbba5f62608a43f9bc4979dc8e79', 'profile-notes/065-128/75-forced27-and-complete-pure3-deletion-on-the-k-faces.md': 'bf21f845032d56fb86f86dfdecd5426e58eceac63a1c4e44d6fe0a16d7070f33', 'profile-notes/065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '79ae5ce60d7121afdc3fe0eaa3a87abecf21709d15e7627c2425dd7bdb4926cc', 'profile-notes/129-192/184-the-two-pure-prime-paths-share-their-shallow-square-state.md': 'e846ea515416fef583ba62fd5231b2471c3a99909947e8a7576e542ffa879754'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original result')
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


def candidate_rows(bridge, factorial, three, five, old_joint):
    table = factorial.FactorialHead(bridge)
    roots, qslots = bridge.ROOT, factorial.Q_SLOTS
    c3, c5 = three.DENSITY, five.DENSITY
    require(roots == (0, 0, 1, 1, 1) and qslots == (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5)),
            'The same actual first-five complement and canonical cells')
    mixed = tuple(tuple(table.w[c][s] if table.pre[c][s] > 0 else F(0) for s in range(5)) for c in range(5))
    require(all(0 <= v <= 1 for row in mixed for v in row), 'Pointwise source domination and every excluded rectangle')
    require(all(table.head_caps[c][s] == table.w[c][s]*table.raw[c][s]-F(int(c == 1), 135)*qslots[s]
                for c, s in product(range(5), repeat=2)), 'The existing head already paid the entire forced27 piece')
    rows, all_candidates, uncorrected = [], [], []
    for root, cell, first in product(range(2), range(5), range(5)):
        n = tuple(int(roots[c] == root)+int(c == cell) for c in range(5))
        shallow3 = 3*three.FIRST[root]+(3+2*int(roots[cell] == root))*three.SECOND[cell]
        old_cross = sum(table.head_caps[c][first] for c in range(5) if roots[c] == root)+table.head_caps[cell][first]
        # Only the root aggregate's deeper-than27 remainder was uncharged.
        correction = F(int(root == 0), 270)*qslots[first]
        cross = old_cross-correction
        old_H = tuple(sum(table.descendant[c][s]*table.w[c][s] for c in range(5) if roots[c] == root)
                      +table.descendant[cell][s]*table.w[cell][s] for s in range(5))
        removed = F(int(root == 0), 90)+F(int(cell == 1), 135)
        H = tuple(value-removed*int(s != 0) for s, value in enumerate(old_H))
        # The part carrying q(F), including both copies of the forced27
        # event when the shallow indicators overlap, remains nonnegative.
        root0_factor = tuple(sum(n[c]*table.descendant[c][s]*table.w[c][s] for c in (0, 1))
                             -removed*int(s != 0) for s in range(5))
        require(cross >= 0 and min(H) >= 0 and min(root0_factor) >= 0,
                'Every same-source deletion leaves a nonnegative q(F) coefficient, including slotQ')
        alpha3 = tuple(c3[c]*(3+2*n[c])+2*table.pre[c][first]*table.w[c][first] for c in range(5))
        b3 = old_joint.bellman_support(alpha3, tuple(2*v for v in c3), 3, 3)
        base3 = tuple((c3[c]*(n[c]+2)+table.pre[c][first]*table.w[c][first])/9 for c in range(5))
        require(b3['complete_candidates'] == base3, 'The pure-three path keeps its shallow counts and first-five cross')
        pairs, five_supports = [], []
        for c in range(5):
            alpha5 = tuple(c5[s]*(3+2*int(s == first))+2*H[s]+mixed[c][s]/9 for s in range(5))
            b5 = old_joint.bellman_support(alpha5, tuple(2*v for v in c5), 5, 2)
            five_supports.append(b5)
            for s in range(5):
                marginal5 = c5[s]*F(11 if s == first else 7, 40)+H[s]/10
                crossed = mixed[c][s]/180
                require(b5['complete_candidates'][s] == marginal5+crossed,
                        'The complete deep3/deep5 cross is paid exactly once')
                tail = base3[c]+marginal5+crossed
                upper = shallow3+3*five.FIRST[first]+2*cross+tail
                previous_relaxation = upper+2*correction+(old_H[s]-H[s])/10
                pairs.append({'deep_three_cell': c, 'deep_five_slot': s,
                              'three_joint_tail': base3[c], 'five_joint_tail': marginal5,
                              'deep_cross': crossed, 'complete_joint_tail': tail, 'joint_upper': upper})
                all_candidates.append((upper, root, cell, first, c, s))
                uncorrected.append(previous_relaxation)
        rows.append({'shallow_three_root': root, 'shallow_three_cell': cell, 'first_five_slot': first,
                     'shallow_three_moment': shallow3, 'first_five_moment': 3*five.FIRST[first],
                     'previous_shallow_cross': old_cross, 'additional_shallow_cross_deletion': correction,
                     'shallow_cross': cross, 'previous_shallow_three_deep_five_coefficients': old_H,
                     'full_deep_cross_deletion_coefficient': removed,
                     'shallow_three_deep_five_coefficients': H, 'remaining_root0_q_coefficients': root0_factor,
                     'three_bellman': b3, 'five_bellman_by_three_cell': five_supports,
                     'joint_deep_candidates': pairs, 'joint_upper': max(p['joint_upper'] for p in pairs)})
    best = max(r[0] for r in all_candidates)
    maxima = [r[1:] for r in all_candidates if r[0] == best]
    distinct = sorted({r['joint_upper'] for r in rows}, reverse=True)
    require(len(rows) == 50 and len(all_candidates) == 1250 and best == F(125, 108)
            and maxima == [(0, 1, 2, 1, 2)] and distinct[1] == F(599, 540),
            'Every independent shallow and deep coarse state, with one exact relaxed maximizer')
    require(max(uncorrected) == F(1567, 1350) and max(uncorrected)-best == F(1, 300),
            'Deep-slot coupling alone retains184; the same-source deletion supplies the strict gain')
    return {'allowed_deep_cross_weights': mixed, 'candidate_rows': rows,
            'candidate_count': len(all_candidates), 'joint_upper': best,
            'maximizing_choices': maxima, 'next_shallow_upper': distinct[1],
            'uncorrected_joint_slot_upper': max(uncorrected)}


def calculate(base):
    require(PINS, 'Pin the complete184 consumer and the75 source theorem')
    io = module('axis_deletion_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, forced = read('pure_axis_joint_square_comparison'), read('endpoint_k_face_forced27')
    pins = dict(PINS)
    for data in (prior, forced):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent actual source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('axis_deletion_'+name, io.named_artifact(base/'frontier', name+'.py'))
    require(F(forced['deep3_five_complement_coefficient']) == F(1, 90)
            and F(forced['forced27_cell1_deletion']) == F(3, 4)/135
            and F(1, 90)-F(1, 135) == F(1, 270), 'Exactly the complete75 source deletion and its previously uncharged remainder')
    bridge, factorial = load('k_face_common_seven_hinges'), load('whole_factorial_same_head')
    three, five, old_joint = load('pure_three_joint_moments'), load('pure_five_joint_moments'), load('pure_axis_joint_square_comparison')
    joint = candidate_rows(bridge, factorial, three, five, old_joint)
    old_block = F(prior['joint_moment']['joint_upper'])
    saving = old_block-joint['joint_upper']
    require(old_block == F(1567, 1350) and saving == F(1, 300), 'Replace184 complete pure-axis block once')
    D, L, oldQ = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, oldQ) == (F(53, 360), F(1151, 1800), F(6559, 1350))
            and prior['r'] == prior['rho'] == '0', 'Same saturated actual faces and complete184 vector')
    Q = oldQ-saving
    require(Q == F(13109, 2700), 'All other original LCM square categories retained')
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'Complete original52-cost source closure')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(len(tags) == len(old_costs) == len(weights) == 52 and prior['all_original_indices'] == list(range(52)),
            'Every184 original cost with all174 factorial and184 majorant improvements')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=t: engine.source.zero5_cost(tag, v) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, old_costs, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(square_weight > 0, 'Original positive complete-square consumer weight')
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*oldQ
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    propagated = sum(w*(a-b) for w, a, b in zip(weights, old_costs, costs))
    require(oldN == F(prior['numerator_upper']) and oldN-N == square_weight*saving+propagated
            and all(0 <= b <= a for a, b in zip(old_costs, costs)) and propagated >= 0 and N > 0,
            'One full numerator retaining every earlier factorial and majorant gain')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'All AP11 blocks, AP13 loss and the complete infinite count tail')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']), 'Strict complete-face improvement, still above403')
    table = factorial.FactorialHead(bridge)
    return encode({'schema': 'erdos7-pure-axis-shared-deletion-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
        'source_pre': table.pre, 'source_descendant': table.descendant, 'selected_density_weights': table.w,
        'rectangle_caps': table.head_caps, 'pure_five_complement_in_slots': factorial.Q_SLOTS,
        'complete_pure_three_deletion_coefficient': F(1, 90), 'forced27_deletion_coefficient': F(1, 135),
        'additional_root_deletion_coefficient': F(1, 270), 'joint_moment': joint,
        'previous_pure_axis_block': old_block, 'complete_square_saving': saving,
        'previous_complete_square_upper': oldQ, 'complete_square_upper': Q,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
        'previous_cost_bounds': old_costs, 'improved_cost_bounds': costs, 'majorants': majorants,
        'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'direct_numerator_improvement': square_weight*saving, 'majorant_propagation_improvement': propagated,
        'numerator_upper': N, 'AP11_block_results': prior['AP11_block_results'],
        'full_count_tail': prior['full_count_tail'], 'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Ordinary joint pure-axis moment and complete52-cost comparison on both actual saturated K faces. The same complete pure-three deletion is evaluated against the shallow root/cell multiplicity; no second subtraction of already retained27. Two Bellman reductions retain deep cell and slot, and the mixed cross occurs once. Every184/174 improvement, all other LCM classes and all infinite tails/full denominator remain. No actual-family sharpness, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('axis_deletion_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact shared-deletion joint-axis certificate')
    print('PASS:1250 joint choices, block<=125/108, full square<=13109/2700; complete face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
