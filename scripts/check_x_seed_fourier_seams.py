#!/usr/bin/env python3
"""Replay a Fourier-seam exclusion using the existing exact seed intervals.

An ER row pair has proportional rows in the entrywise-squared matrix.
Every member of the Fourier two-parameter family has such a pair on one
side; transpose exchanges the sides. Row/column monomial equivalence
multiplies each squared minor by a nonzero phase, and permutes its indices.
Proving a nonzero squared minor for each of the 15 row and 15 column pairs
therefore excludes both families. No numerical tolerance is used.

This checker is an exact computational audit, not a Lean-kernel proof.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path
from check_x_seed_boxes import SCALE, exact_seed


def verify(document: dict) -> dict:
    H = exact_seed(document)
    witnesses = {}
    for side in ('row', 'column'):
        records = []
        for a, b in itertools.combinations(range(6), 2):
            candidates = []
            for k in range(1, 6):
                if side == 'row':
                    minor = (H[a][0] * H[a][0] * H[b][k] * H[b][k]
                             - H[a][k] * H[a][k] * H[b][0] * H[b][0])
                else:
                    minor = (H[0][a] * H[0][a] * H[k][b] * H[k][b]
                             - H[k][a] * H[k][a] * H[0][b] * H[0][b])
                candidates.append((minor.abs2().lo, k))
            lower, k = max(candidates)
            if lower <= 0:
                raise ValueError(f'{side} pair {(a, b)} has no certified nonzero squared minor')
            records.append({'pair': [a, b], 'other_indices': [0, k],
                            'squared_modulus_lower_bound': str(Fraction(lower, SCALE))})
        witnesses[side] = records
    return {
        'schema': 'mub6-fourier-seam-exclusion-v1',
        'parameter_box': document['seed'].get('parameter_box'),
        'row_pairs_certified': 15,
        'column_pairs_certified': 15,
        'witnesses': witnesses,
        'Fourier_and_transposed_Fourier_excluded': True,
        'mathematical_input': 'Squared-minor vanishing is invariant under row/column monomial equivalence; each standard Fourier-family matrix has an ER row or column pair.',
        'Lean_kernel_checked': False
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    report = verify(json.loads(raw))
    report['certificate_sha256'] = hashlib.sha256(raw).hexdigest()
    text = json.dumps(report, indent=2) + '\n'
    if args.report:
        args.report.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
