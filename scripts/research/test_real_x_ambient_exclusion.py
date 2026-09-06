#!/usr/bin/env python3
"""Adversarial tests of the ambient sublevel/tube replay; never an admission oracle."""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import check_real_x_ambient_exclusion as audit


def run(certificate: Path, verified_output: Path):
    data = json.loads(certificate.read_text())
    centers = verified_output / 'centers.txt'
    binary = verified_output / 'residual_cover'
    if not centers.is_file() or not binary.is_file():
        raise ValueError('replay once before running adversarial tests')
    result = []

    def rejects(name, fn):
        try:
            fn()
        except (ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as exc:
            result.append({'case': name, 'status': 'REJECTED', 'reason': str(exc)[:200]})
        else:
            raise AssertionError('corruption accepted: ' + name)

    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        def changed_centers(name, change):
            lines = centers.read_text().splitlines()
            change(lines)
            path = root / name
            path.write_text('\n'.join(lines) + '\n')
            return path

        shifted = changed_centers('shifted.txt', lambda lines: lines.__setitem__(1,
            ' '.join(lines[1].split()[:2] + ['0'] * 5)))
        duplicate = changed_centers('duplicate.txt', lambda lines: lines.__setitem__(2, lines[1]))
        truncated = changed_centers('truncated.txt', lambda lines: lines.pop())
        # A different small tube can pass geometry alone; coverage must bind
        # it to the residual system. Test the complete core preflight here.
        shifted_report = root / 'shifted_report.json'
        shifted_run = subprocess.run([str(binary), str(shifted), '0', '1', '18', '14',
                                      str(shifted_report)], text=True, capture_output=True)
        if shifted_run.returncode == 0 or shifted_report.exists():
            raise AssertionError('shifted tube passed coverage preflight')
        result.append({'case': 'shifted_tube_center', 'status': 'REJECTED',
                       'scope': 'coverage preflight, not geometry alone',
                       'reason': shifted_run.stderr.strip()})
        rejects('duplicate_label', lambda: audit.audit_tubes(data, duplicate))
        rejects('truncated_tube_list', lambda: audit.audit_tubes(data, truncated))

        extra = copy.deepcopy(data)
        k = next(i for i in range(60) if i not in data['canonical_vertices'])
        extra['allowed_edges'].append(sorted([k, data['canonical_vertices'][0]]))
        rejects('forbidden_type_allowed_edge', lambda: audit.audit_tubes(extra, centers))

        removed = copy.deepcopy(data)
        canon = sorted(data['canonical_vertices'])
        pair = [canon[0], canon[1]]
        removed['allowed_edges'] = [e for e in removed['allowed_edges'] if e != pair]
        rejects('real_orthogonality_claimed_as_nonedge', lambda: audit.audit_tubes(removed, centers))

        sigma = audit.SIGMA
        try:
            audit.SIGMA = Fraction(1, 2**19)
            rejects('excessive_ambient_radius', audit.constants)
        finally:
            audit.SIGMA = sigma

        incomplete = root / 'incomplete.json'
        p = subprocess.run([str(binary), str(centers), '0', '1', '18', '14', str(incomplete)],
                           capture_output=True, text=True)
        row = json.loads(incomplete.read_text())
        if p.returncode == 0 or row['status'] != 'INCOMPLETE' or row['pending'] == 0:
            raise AssertionError('node cap falsely accepted')
        result.append({'case': 'node_cap_one', 'status': 'REJECTED',
                       'pending': row['pending'], 'visited': row['nodes']})

        badreport = root / 'bad_chart.json'
        p = subprocess.run([str(binary), str(centers), '33', '1', '18', '14', str(badreport)],
                           capture_output=True, text=True)
        if p.returncode == 0 or badreport.exists():
            raise AssertionError('invalid chart accepted')
        result.append({'case': 'chart_outside_complete_atlas', 'status': 'REJECTED'})

        stale = root / 'stale'; stale.mkdir()
        (stale / 'verification.json').write_text('{"status":"PASS"}')
        rejects('invalid_run_removes_stale_success',
                lambda: audit.run(certificate, stale, 0, 1))
        if (stale / 'verification.json').exists():
            raise AssertionError('stale success survived rejected run')

        optimized = root/'optimized'
        r = subprocess.run([sys.executable, '-O', str(Path(audit.__file__)),
                            str(certificate), '--output', str(optimized)],
                           capture_output=True, text=True)
        if r.returncode == 0 or (optimized/'verification.json').exists():
            raise AssertionError('optimized Python assertions were accepted')
        # The reused kernel rejects optimized Python during import, before
        # this driver's own run entry and before it emits a failure report.
        if 'assertions are mandatory' not in r.stderr:
            raise AssertionError('optimized-mode rejection was not the intended kernel check')
        result.append({'case': 'python_optimization_disables_interval_assertions',
                       'status': 'REJECTED', 'scope': 'reused kernel import guard',
                       'reason': 'Run this checker without Python -O: assertions are mandatory.'})

    return {'status': 'PASS', 'tests': result,
            'count': len(result), 'lean_kernel_verified': False,
            'scope': 'adversarial tests, not a proof of verifier soundness'}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('certificate', type=Path)
    p.add_argument('verified_output', type=Path)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    r = run(a.certificate, a.verified_output)
    text = json.dumps(r, indent=2) + '\n'
    if a.output:
        a.output.write_text(text)
    print(text)
