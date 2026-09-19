#!/usr/bin/env python3
"""Use each complete fallback's own same-law Gamma13 in its row potential."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/branch_local_fallback_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765', 'frontier/cover-geometry/ap_schedule_core.py': '365b6c1f9a70dff5378a7d3a73a06879ee6193fbc69a4ac68ecfed1972e95617', 'frontier/comparison-bounds/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d', 'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': '3b8afa03444fe045c9dba7e1a74ac051c3d4032eddfeae106a47e360ad0d34e2', 'certificates/source_norms/source-budgets/assigned_j_global_comparison.json': '237194e9f0d879110596f1b015f554e8676a89730fb2cac3bcbcbc1373215a16', 'profile-notes/001-064/35-ap45-layout-costs-and-complete-core-tails.md': '5b7569bc8a8ac2c03287e8cba51140c390327405126ea2291d7b3073e14f1c20'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original fallback provider')
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
    require(PINS, 'Pinned original proof and arithmetic inputs')
    io = module('fallback_local_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, global_prior = read('allocated_seven_thresholds'), read('assigned_j_global_comparison')
    pins = dict(PINS)
    for doc in (prior, global_prior):
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    source = module('fallback_local_source', base/'verify_joint_frontier.py')
    allocation = module('fallback_local_allocation', base/'frontier/comparison-bounds/allocated_seven_thresholds.py')
    core = module('fallback_local_core', base/'frontier/cover-geometry/ap_schedule_core.py')
    old_targets = {k: F(prior[k]) for k in ('Gamma13', 'T13_81', 'bound')}
    old, _ = core.fallbacks(source, allocation.CAPS, F(prior['source_G357']), old_targets, F(prior['rho']))
    require(len(old) == len(prior['fallbacks']) == len(global_prior['fallbacks']) == 8, 'All original fallback branches')
    require(source.AC > 0 and source.AC == F(2371, 2880), 'Positive same-law Gamma13 coefficient')
    rows = []
    for inputs, record, previous, global_record in zip(source.FALLBACK_INPUTS, old, prior['fallbacks'], global_prior['fallbacks']):
        require(record == {k: (v if k == 'branch' else F(v)) for k, v in previous.items() if k != 'combined_bound'},
                'Recompute every original fallback value, including full product tails')
        name, pure, density = inputs
        require(name == record['branch'] == global_record['branch'], 'Independent original branch identity')
        old_combined = record['bound']+record['T13_81']
        require(old_combined == F(previous['combined_bound']) == F(global_record['complete_bound']),
                'Original221 complete fallback bound recovered')
        gamma = record['Gamma13']
        improvement = source.AC*(old_targets['Gamma13']-gamma)
        require(improvement >= 0, 'Each actual branch has a no-larger certified Gamma13')
        combined = old_combined-improvement
        # Independently assemble the whole row potential with its branch Gamma.
        original_caps = tuple((p, 1/u) for p, u in zip((3, 5, 7), pure))
        factor = density*prod(pure)
        hs = {h: factor*source.product_hinge(original_caps+allocation.CAPS, F(h))/record['survival_lower']
              for h in (5, 6, 7, 8)}
        direct = source.WHOLE_CONST+source.AC*(gamma-16)
        direct += sum(c*hs[h] for h, c in source.WEIGHT17)
        direct += source.P17*sum(c*hs[h] for h, c in source.WEIGHT19)
        direct += source.EXTRA5*hs[5]+record['T13_81']
        require(direct == combined, 'Direct complete row-potential assembly equals the exact substitution')
        rows.append({'branch': name, 'original_pure_masses': pure, 'original_density_bound': density,
                     'survival_lower': record['survival_lower'], 'branch_Gamma13': gamma,
                     'complete_T13_81': record['T13_81'], 'complete_hinges': hs,
                     'previous_complete_bound': old_combined, 'Gamma13_saving': improvement,
                     'complete_bound': combined, 'margin_below403': F(403)-combined})
    require(all(F(row['complete_bound']) < 403 for row in rows[:-1]) and rows[-1]['complete_bound'] > 403,
            'Seven branches pass403; the last remains above it')
    return encode({'schema': 'erdos7-branch-local-fallback-comparison-v1', 'source_sha256': pins,
                   'global_Gamma13': old_targets['Gamma13'], 'Gamma13_coefficient': source.AC,
                   'fallbacks': rows, 'remaining_branch': rows[-1]['branch'],
                   'remaining_gap403': rows[-1]['complete_bound']-403,
                   'unchanged_global_bound': global_prior['candidate_K'],
                   'scope': 'Each of the eight original complete fallback row potentials uses its own existing same-law Gamma13 upper. All original branch assumptions, survival denominators and complete exponent/count tails remain. The last fallback is still above403. The global bound and effective-source comparisons are not improved by this calculation alone. No Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('fallback_local_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact branch-local fallback certificate')
    for row in result['fallbacks']:
        print(row['branch']+': '+str(float(F(row['complete_bound']))))
    print('PASS: all eight complete branch bounds reconstructed; final403 gap='+str(float(F(result['remaining_gap403']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
