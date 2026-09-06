#!/usr/bin/env python3
"""Rejection tests for the residual-sublevel extension (not formal proofs)."""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import tempfile
import check_real_x_residual_barrier as verifier


def run(certificate: Path, replay: Path, report_path: Path) -> dict:
    results = []
    with tempfile.TemporaryDirectory(prefix='mub-barrier-negative-') as temp:
        root = Path(temp)
        centers = replay / 'centers.txt'
        binary = replay / 'residual_barrier_core'
        bounds = replay / 'ambient_matrix_bounds.txt'
        verifier.require(binary.exists(), 'run the main verifier first')

        def reject(name: str, center_file: Path, mask: int, cap: int, bounds_file=None):
            out = root / (name + '.json')
            args = [str(binary), str(center_file), str(mask), str(cap), '18', '12', str(out)]
            if bounds_file is not None:
                args.append(str(bounds_file))
            result = subprocess.run(args, capture_output=True, text=True)
            verifier.require(result.returncode != 0, 'corrupted case accepted: ' + name)
            if out.exists():
                value = json.loads(out.read_text())
                verifier.require(value['status'] != 'SUBLEVEL_COVERED', 'incomplete marked covered')
            results.append({'case': name, 'rejected': True, 'exit_code': result.returncode})

        reject('one_node_budget_is_incomplete', centers, 0, 1)
        reject('invalid_chart_rejected', centers, 33, 1)
        lines = centers.read_text().splitlines()
        truncated = root / 'truncated_centers.txt'
        truncated.write_text('\n'.join(lines[:-1])+'\n')
        reject('truncated_guard_catalogue', truncated, 32, 1, bounds)
        duplicate = root / 'duplicate_centers.txt'
        duplicate.write_text('\n'.join(lines[:-1] + [lines[1]])+'\n')
        reject('duplicate_guard_label', duplicate, 32, 1, bounds)
        shifted = root / 'shifted_centers.txt'
        parts = lines[1].split()
        parts[2] = str(int(parts[2]) + (1 << 39))
        shifted.write_text('\n'.join([lines[0], ' '.join(parts), *lines[2:]])+'\n')
        reject('wrong_guard_center', shifted, 32, 1, bounds)
        short_bounds = root / 'short_bounds.txt'
        short_bounds.write_text('40\n0 0 0 0\n')
        reject('truncated_ambient_matrix', centers, 32, 1, short_bounds)

    data = json.loads(certificate.read_text())
    changed = copy.deepcopy(data)
    changed['allowed_edges'].remove([0, 1])
    changed['allowed_edges'].append([0, 7])
    try:
        verifier.exclusion_graph(changed, replay / 'ambient_local.json.roots')
    except ValueError as error:
        verifier.require('nonedge 0,1 failed' in str(error), 'wrong graph rejection reason')
        results.append({'case': 'true_edge_reclassified_as_nonedge', 'rejected': True})
    else:
        raise ValueError('an exact orthogonal edge was accepted as a nonedge')

    # Exact affine sanity check for the extra C[-eta,eta] term.
    # f(x)=x-1/4, C=1, J=1. Root-only K={1/4} misses the sublevel point 3/8.
    eta, center, x = F(1, 8), F(1, 4), F(3, 8)
    verifier.require(abs(x-center) <= eta and x != center, 'bad affine witness')
    verifier.require(center-eta <= x <= center+eta, 'inflated image lost sublevel point')
    results.append({'case': 'uninflated_root_image_is_unsound_for_sublevel',
                    'exact_affine_witness_checked': True,
                    'scope': 'Analytic formula regression; not a universal implementation proof.'})
    verifier.require(30*verifier.DELTA+36*verifier.DELTA**2 < verifier.ETA,
                     'selected matrix radius exceeds the base barrier')
    too_large = F(1, 1 << 22)
    verifier.require(not (30*too_large+36*too_large**2 < verifier.ETA),
                     'transfer should reject this larger unsupported radius')
    results.append({'case': 'unsupported_transfer_radius', 'rejected': True})
    report = {'status': 'PASS', 'cases': results, 'lean_kernel_verified': False,
              'scope': 'Rejection tests and exact finite algebra checks, not kernel admission.'}
    report_path.write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('replay', type=Path)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.certificate, args.replay, args.report), indent=2))
