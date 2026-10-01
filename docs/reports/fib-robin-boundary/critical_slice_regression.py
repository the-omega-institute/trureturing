#!/usr/bin/env python3
"""Reject three corruptions of a previously generated critical-slice certificate.

The complete producer certificate is runtime input, never a retained fixture.
Keep critical_slice_check.py and price_band.py beside this file. Requires --out.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError('run without -O or PYTHONOPTIMIZE; checks require assertions')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    raw = gzip.decompress(args.certificate.read_bytes())
    original = json.loads(raw)
    checker = Path(__file__).resolve().with_name('critical_slice_check.py')
    mutations = []
    missing = copy.deepcopy(original)
    missing['layers'].pop()
    mutations.append(('missing-layer', missing, "len(c['layers'])==len(expected)"))
    false_cell = copy.deepcopy(original)
    false_cell['cells'][0]['classification'] = 'strict_self_matching'
    assert false_cell['cells'][0] != original['cells'][0]
    mutations.append(('false-cell', false_cell, "cell['classification']==cls"))
    false_max = copy.deepcopy(original)
    false_max['integer_patch'][0]['maximum_n'] += 1
    mutations.append(('false-patch-maximum', false_max, "block['maximum_n']==nmax"))
    reports = []
    for name, certificate, expected_check in mutations:
        path = args.out / (name + '.json.gz')
        path.write_bytes(gzip.compress(json.dumps(certificate, separators=(',', ':')).encode(), mtime=0))
        proc = subprocess.run(
            [sys.executable, '-B', str(checker), '--certificate', str(path.resolve()),
             '--out', str((args.out / name).resolve())],
            text=True, capture_output=True, check=False)
        assert proc.returncode == 1 and 'AssertionError' in proc.stderr, proc.stderr
        assert expected_check in proc.stderr, proc.stderr
        assert not (args.out / name / 'check-results.json').exists()
        reports.append({'mutation': name, 'checker_exit': proc.returncode, 'rejected': True})
    result = {
        'scope': 'Three concrete false-certificate regressions; not a complete checker audit.',
        'certificate_sha256': hashlib.sha256(raw).hexdigest(),
        'corruptions_rejected': len(reports),
        'checks': reports,
        'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__), checker, checker.with_name('price_band.py'))},
    }
    (args.out / 'results.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
