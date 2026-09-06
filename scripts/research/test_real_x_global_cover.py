#!/usr/bin/env python3
"""Corruption tests for a completed global-cover replay; not an admission judge."""
from __future__ import annotations
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import tempfile
import check_real_x_global_cover as checker


def run(certificate: Path, work: Path) -> dict:
    data = json.loads(certificate.read_text())
    core = work / 'cover_core'
    centers = work / 'centers.txt'
    bounds = work / 'matrix_bounds.txt'
    original = centers.read_text().splitlines()
    tests = []
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        def reject_core(name: str, lines: list[str], budget: int = 100,
                        matrix: Path = bounds) -> None:
            path = tmp / 'centers.txt'
            path.write_text('\n'.join(lines) + '\n')
            r = subprocess.run([str(core), str(path), '0', str(budget),
                                str(tmp / 'report.json'), str(matrix)],
                               capture_output=True, text=True)
            if r.returncode == 0:
                raise AssertionError(f'corruption accepted: {name}')
            tests.append({'case': name, 'rejected': True, 'exit_code': r.returncode,
                          'diagnostic': r.stderr.strip() or r.stdout.strip()})
        bad = original.copy()
        row = bad[1].split(); row[2] = str(int(row[2]) + 2**38)
        bad[1] = ' '.join(row)
        reject_core('wrong_root_center', bad)
        bad = original.copy()
        row = bad[2].split(); row[0] = bad[1].split()[0]; bad[2] = ' '.join(row)
        reject_core('duplicate_label', bad)
        reject_core('truncated_catalogue', original[:-1])
        reject_core('empty_catalogue', [])
        reject_core('unfinished_partition', original, 1)
        invalid_bounds = tmp / 'bounds.txt'; invalid_bounds.write_text('0\n')
        reject_core('wrong_interval_precision', original, matrix=invalid_bounds)
        bad = copy.deepcopy(data)
        can = set(bad['canonical_vertices']); colors = bad['noncanonical_colors']
        edges = {tuple(e) for e in bad['allowed_edges']}
        lost = tuple(sorted(can)[:2]); edges.remove(lost)
        replacement = next((i, j) for i, j in itertools.combinations(range(60), 2)
                           if i not in can and j not in can and
                           colors[i] != colors[j] and (i, j) not in edges)
        edges.add(replacement); bad['allowed_edges'] = [list(e) for e in sorted(edges)]
        try:
            checker.graph_audit(bad, work / 'root_enclosures.txt', centers)
        except ValueError as e:
            tests.append({'case': 'false_nonedge_among_canonical_roots',
                          'rejected': True, 'diagnostic': str(e)})
        else:
            raise AssertionError('false nonedge accepted')
    return {'status': 'PASS', 'tests': tests,
            'scope': 'Negative tests are not a formal proof of checker soundness.',
            'core_sha256': hashlib.sha256(core.read_bytes()).hexdigest(),
            'input_sha256': checker.digest(certificate)}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    p.add_argument('replay_directory', type=Path)
    p.add_argument('--report', type=Path)
    a = p.parse_args(); result = run(a.certificate, a.replay_directory)
    text = json.dumps(result, indent=2) + '\n'
    if a.report:
        a.report.write_text(text)
    print(text)
