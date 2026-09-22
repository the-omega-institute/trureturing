#!/usr/bin/env python3
"""Exact arithmetic for the uniform endpoint joint15/25/75 deletion gap.

The ordinary proof supplies original-label geometry and saturation. This
checks complete tails, all placement case margins and the full load sum.
No finite-family enumeration, neighborhood or Lean result is claimed.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_linear_joint15_25_75.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/endpoint-bounds/endpoint_linear_complete_pure3_deletion.py': 'c0bba2c21ed9c1d6236bfee13ff2510f71b40b44bf63600f09be3b2807897bd5',
    'certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json': '7e5b2c9d2244a9aad0b1f3e1850a52bb1a1a1e7ffbe49cbf7bd42b8017bc2cfc',
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
    io = module('joint15_25_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited pin')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
        used[path] = pin
    geometry = module('joint15_25_previous', base/'frontier/endpoint-bounds/endpoint_linear_complete_pure3_deletion.py')
    require(encode(geometry.calculate(base)) == previous, 'Reproduced full77 geometry arithmetic and complete load')
    linear = module('joint15_25_source_tables', base/'frontier/endpoint-bounds/endpoint_linear_numerator.py')
    eta, roots = linear.ETA, linear.ROOT
    h, h0, h1, eta2 = sum(eta), sum(eta[:2]), sum(eta[2:]), eta[2]
    require((h, h0, h1, eta2) == (F(1, 2), F(1, 6), F(1, 3), F(1, 9)), 'Actual endpoint root and beta masses')
    D, oldL = F(previous['mass']), F(previous['linear_upper'])
    c = F(previous['new_deep5_coefficient'])
    depth2_mass, high5_tail = F(1, 25), F(1, 125)/(1-F(1, 5))
    seven_tail = F(6, 35)/(1-F(1, 7))
    require((c, high5_tail, seven_tail) == (F(13, 30), F(1, 100), F(1, 5)), 'Pure5-complement coefficient and complete exponent tails')
    cap15, cap25, cap75 = F(1, 25), c*depth2_mass, h1*depth2_mass
    gain, bad_placement_gain = F(2, 375), F(1, 225)
    tables = []
    non_tight_max = F(0)
    for x in linear.LATE_INTERVAL:
        _, kept = linear.slot_matrices(x)
        root_slots = [[sum(kept[l][j] for l in range(5) if roots[l] == r)
                       for j in range(5)] for r in range(2)]
        other = max(root_slots[r][j] for r in range(2) for j in range(5) if (r, j) != (1, 4))
        require(root_slots[1][4] == cap15 and other <= F(1, 30), 'Every nontight original15 placement has a uniform gap')
        non_tight_max = max(non_tight_max, other)
        tables.append({'late_B_mass': x, 'root_slot_caps': root_slots, 'non_root1_H_max': other})
    per_label25 = {
        '25_in_H': h1*depth2_mass,
        '25_in_K': h*depth2_mass,
        '75_in_H': h1*depth2_mass,
        '75_in_K': h1*depth2_mass,
    }
    per_label75 = {key: h1*depth2_mass for key in per_label25}
    require(min(per_label25.values()) == min(per_label75.values()) == F(1, 75), 'Independent per-label intersection minimum for either good K test')
    both_families_gain = 2*min(per_label25.values())*seven_tail
    pureP_gain, alpha_gain = c*high5_tail, h1*high5_tail
    # q(F) loses the complete pureP tail; the disjoint alpha source loss
    # is subtracted separately after retaining the same q(F) coefficient.
    other_child_upper = c*(depth2_mass-high5_tail)-alpha_gain
    require(cap25-other_child_upper == pureP_gain+alpha_gain == F(23, 3000), 'Disjoint pureP and alpha source losses on the same child')
    require(3*high5_tail <= 2*depth2_mass and high5_tail > 0, 'Positive high source-tail mass and two-child capacity')
    bad25 = {
        'F_in_P_or_P2': cap25,
        'F_in_alpha_or_A2': h1*depth2_mass,
        'F_in_beta_or_B2': eta2*depth2_mass,
        'F_in_H': (h+h1)*depth2_mass*seven_tail,
        'F_is_other_residual_child': pureP_gain+alpha_gain,
    }
    bad75 = {
        'root0_any_F': cap75-h0*depth2_mass,
        'removed_root': cap75,
        'root1_F_in_P_alpha_P2_A2': cap75,
        'root1_F_in_beta_or_B2': eta2*depth2_mass,
        'root1_F_in_H': 2*cap75*seven_tail,
        'root1_F_is_other_residual_child': 2*h1*high5_tail,
    }
    require(min(bad25.values()) == min(bad75.values()) == bad_placement_gain, 'Every non-K test25 and non-root1-K test75 loses at least1/225')
    cases = {
        'T15_not_root1_H': cap15-non_tight_max,
        'no_source_free_Q_child': both_families_gain,
        'T25_is_unique_source_free_K': both_families_gain,
        'T75_is_root1_times_K': both_families_gain,
        'neither_T25_nor_T75_captures_K': min(bad25.values())+min(bad75.values()),
    }
    require(min(cases.values()) == gain, 'All three-test placement branches meet the uniform2/375 gap')
    categories = {key: F(value) for key, value in previous['complete_test_categories'].items()}
    require(categories['test15'] == cap15 and categories['pure5_deep'] == cap25+c*high5_tail, 'Replace only original15 and original25; retain complete b>=3 test tail')
    require(categories['3_times_deep5'] == cap75+h1*high5_tail, 'Separate original75 from its complete b>=3 test tail')
    del categories['test15']
    del categories['pure5_deep']
    del categories['3_times_deep5']
    joint = cap15+cap25+cap75-gain
    categories['joint_test15_test25_test75'] = joint
    categories['pure5_depth_at_least3'] = c*high5_tail
    categories['3_times5_depth_at_least3'] = h1*high5_tail
    newL, margin = sum(categories.values()), 6*D-sum(categories.values())
    require(joint == F(49, 750) and newL == oldL-gain == F(238, 375) and margin == F(199, 750), 'Complete joint cap, load and signed margin')
    return {
        'schema': 'erdos7-endpoint-linear-joint15-25-75-v1', 'source_vertex': 404, 'carrier': [0, 1],
        'source_sha256': used, 'mass': D, 'old_linear_upper': oldL,
        'pure5_complement_coefficient': c, 'depth2_five_mass': depth2_mass,
        'complete_high_source_five_tail_per_family': high5_tail,
        'complete_seven_cap_tail': seven_tail, 'first15_affine_endpoint_tables': tables,
        'baseline_test15': cap15, 'baseline_test25': cap25, 'baseline_test75': cap75,
        'per_label_intersections_if_test25_K': per_label25,
        'per_label_intersections_if_test75_root1_K': per_label75,
        'complete_two_forbidden_family_gain': both_families_gain,
        'other_child_disjoint_source_gains': {'pureP': pureP_gain, 'alpha': alpha_gain},
        'non_K_test25_placement_gains': bad25,
        'non_root1_K_test75_placement_gains': bad75,
        'individual_bad_placement_gain': bad_placement_gain,
        'placement_case_gains': cases, 'placement_case_slacks': {key: value-gain for key, value in cases.items()},
        'joint_gain': gain, 'joint_test15_test25_test75_upper': joint,
        'complete_test_categories': categories, 'linear_upper': newL,
        'signed_barrier': 6, 'signed_margin_lower': margin,
        'improvement_over77': oldL-newL, 'improvement_over59': F(1157, 1800)-newL,
        'scope': ('Ordinary uniform actual404 endpoint and approaching-sequence linear bound238/375. '
                  'The independent original15,25,75 tests share the actual source and complete25/75 forbidden tails. '
                  'No finite neighborhood, globalK, survival update or Lean claim.'),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('joint15_25_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical exact joint15/25/75 endpoint certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:two affine source tables, complete test25/test75 placement cases, independent label minima and complete tails.')
    print('Joint15/25/75 cap49/750; endpoint linear238/375; barrier6 margin199/750; gain2/375 over77.')


if __name__ == '__main__':
    main()
