"""Negative certificate tests. Requires a separately compiled checker.
Usage: python test_gap4_rejection.py CHECKER EVIDENCE_DIRECTORY
"""
from __future__ import annotations
from pathlib import Path
import json
import subprocess
import sys
from tempfile import TemporaryDirectory


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit('usage: test_gap4_rejection.py CHECKER EVIDENCE_DIRECTORY')
    checker, folder = Path(sys.argv[1]).resolve(), Path(sys.argv[2])
    rows = (folder / 'gap4_power_rows.tsv').read_text()
    proof = (folder / 'gap4_0_16.proof').read_text()
    tests = [
        ('wrong_digit', rows.replace('0 2 0\n', '0 1 0\n', 1), proof,
         'incorrect exact digit'),
        ('nonpower_word', rows.replace('1 1 0 1\n', '1 1 0 2\n', 1), proof,
         'sample does not represent 4^n'),
        ('missing_branch_value', rows, proof.replace('B 1 15\n', 'B 1 7\n', 1),
         'incomplete or wrong branch mask'),
        ('false_contradiction', rows, proof.replace('B 1 15\n', 'L\n', 1),
         'false contradiction leaf'),
        ('truncated_tree', rows, '\n'.join(proof.splitlines()[:9])+'\n',
         'truncated certificate'),
        ('omitted_cases', rows, 'gap4-proof-v1\nP 1 0\nL\n',
         'incomplete output-case coverage'),
        ('duplicate_case', rows, 'gap4-proof-v1\nP 1 0\nL\nP 1 0\nL\n',
         'duplicate output case'),
        ('trailing_garbage', rows, 'gap4-proof-v1\nP 1 0\nL\nEXTRA\n',
         'extra or invalid top-level proof data'),
    ]
    result = []
    with TemporaryDirectory() as temp:
        base = Path(temp)
        for name, row_data, proof_data, reason in tests:
            (base/'rows.tsv').write_text(row_data)
            (base/'bad.proof').write_text(proof_data)
            run = subprocess.run([str(checker), str(base/'rows.tsv'), str(base/'bad.proof')],
                                 text=True, capture_output=True, timeout=30)
            if run.returncode == 0 or ('REJECT: '+reason) not in run.stderr:
                raise RuntimeError(f'{name}: unexpected checker result {run.returncode}: {run.stderr}')
            result.append({'test':name,'rejected':True,'reason':reason})
    print(json.dumps({'status':'PASS','tests':result,'executed_tests':len(result)},indent=2))

if __name__ == '__main__':
    main()
