"""Rebuild and independently replay the original complete gap4 certificates.

All inputs are derived from the stated integers 4**n, 0 <= n < 250. The retained
producer deterministically recovers the original proof bytes; SHA-256 checks
are integrity checks, while the separate C++ replay checks mathematical steps.
No network, third-party solver, reference automaton or Lean execution is used.
Usage: python rebuild_gap4.py OUTPUT_DIRECTORY
"""
from pathlib import Path
from bisect import bisect_right
from hashlib import sha256
from math import isqrt
import json
import os
import subprocess
import sys

EXPECTED = {
    'gap4_power_rows.tsv': 'beda549ec107431204410568a33f6b4c9e13890bd51edc372f75748ac0095fa7',
    'gap4_0_16.proof': '5ff9c5a2d534c18f9108c9a3a08afc366a1f038984d296f68589a8a018e4f889',
    'gap4_16_32.proof': 'bb73e976a6390e34261202e29a24516330022fbe56a1f99f8eb733b9a565de97',
    'gap4_32_48.proof': 'a989437328dacefa7756bb774385f305f70c4cd68b1f73ef0da67934d19fc243',
}

def sample_bytes():
    fib = [0, 1, 1, 2]
    while fib[-1] <= 4**250:
        fib.append(fib[-1] + fib[-2])
    lines = []
    for n in range(250):
        q = 4**n
        remainder, indices = q, []
        while remainder:
            j = bisect_right(fib, remainder) - 1
            indices.append(j)
            remainder -= fib[j]
        tail = indices[-1] - 2
        if tail > 1:
            continue
        floor_phi = lambda x: (x + isqrt(5*x*x)) // 2
        digit = floor_phi(4*q) - 4*floor_phi(q)
        gaps = [u-v-1 for u,v in zip(indices, indices[1:])]
        lines.append(' '.join(map(str, [n, digit, tail] + gaps)))
    return ('\n'.join(lines)+'\n').encode('ascii')

def verify_file(path):
    actual = sha256(path.read_bytes()).hexdigest()
    if actual != EXPECTED[path.name]:
        raise RuntimeError(f'integrity mismatch: {path.name}: {actual}')
    return actual

def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: rebuild_gap4.py OUTPUT_DIRECTORY')
    here = Path(__file__).resolve().parent
    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    rows = out/'gap4_power_rows.tsv'
    rows.write_bytes(sample_bytes())
    hashes = {rows.name: verify_file(rows)}
    compiler = os.environ.get('CXX', 'g++')
    for source, binary in [('gap4_produce.cpp','producer'), ('check_gap4_certificate.cpp','checker')]:
        subprocess.run([compiler, '-O3', '-std=c++17', str(here/source), '-o', str(out/binary)], check=True)
    proofs = []
    for begin, end in [(0,16), (16,32), (32,48)]:
        proof = out/f'gap4_{begin}_{end}.proof'
        run = subprocess.run([str(out/'producer'),str(rows),'3600',str(proof),str(begin),str(end)], text=True, capture_output=True, check=True)
        (out/f'producer_{begin}_{end}.log').write_text(run.stderr)
        report = json.loads(run.stdout)
        if report.get('status') != 'UNSAT' or report.get('completed_output_cases') != 16:
            raise RuntimeError(f'producer incomplete: {report}')
        hashes[proof.name] = verify_file(proof)
        proofs.append(proof)
    checked = subprocess.run([str(out/'checker'),str(rows)]+list(map(str,proofs)), text=True, capture_output=True, check=True)
    report = json.loads(checked.stdout)
    if report.get('status') != 'PASS' or report.get('output_cases') != 48:
        raise RuntimeError('incomplete independent replay')
    report['byte_identical_originals'] = hashes
    (out/'replay.log').write_text(checked.stderr)
    (out/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
    negative = subprocess.run([sys.executable,str(here/'test_gap4_rejection.py'),str(out/'checker'),str(out)], text=True, capture_output=True, check=True)
    (out/'negative_tests.json').write_text(negative.stdout)
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
