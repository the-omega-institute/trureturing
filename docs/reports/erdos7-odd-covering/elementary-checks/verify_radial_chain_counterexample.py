#!/usr/bin/env python3
"""Exact exhaustive refutation of the radial nested-chain maximum assertion.

Only the 27 original Z/9 layouts are enumerated. marked_head_profile.md gives
first-exit consolidation and the arbitrary-positive two-block extension.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction
import json
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def compute():
    weights = [28, 48, 28, 28, 1, 28, 28, 1, 28]
    total = sum(weights)
    need(total == 218 and all(w > 0 for w in weights), 'positive probability')
    shell_weight = {0: 28, 1: 1, 2: 48}
    for x, weight in enumerate(weights):
        depth = 2 if x == 1 else 1 if x % 3 == 1 else 0
        need(weight == shell_weight[depth], 'radial about residue 1')
    table = []
    for a in range(3):
        row = []
        for b in range(9):
            load = [1 + int(x % 3 == a) + int(x == b) for x in range(9)]
            value = sum(w * v * v for w, v in zip(weights, load))
            expanded = total + 3 * sum(weights[x] for x in range(9) if x % 3 == a)
            expanded += (3 + 2 * int(b % 3 == a)) * weights[b]
            need(value == expanded, 'direct load agrees with square expansion')
            row.append(value)
        table.append(row)
    maximum = max(value for row in table for value in row)
    nested = max(table[a][b] for a in range(3) for b in range(9) if b % 3 == a)
    maximizers = [[a, b] for a in range(3) for b in range(9) if table[a][b] == maximum]
    need(maximum == 614 and nested == 610 and maximizers == [[0, 1], [2, 1]],
         'the complete 27-layout domain has a strict nonnested optimum')
    need(all(b % 3 != a for a, b in maximizers), 'every global maximizer is nonnested')
    return {
        'schema': 'positive-radial-chain-counterexample-v1',
        'refuted_claim': 'For every positive radial weight on a finite one-prime prefix tree, the maximum weighted square of a load selecting one cylinder at each depth is attained by a nested chain.',
        'carrier': 'Z/9Z', 'prime': 3, 'height': 2, 'center': 1,
        'original_depth_labels': [0, 1, 2],
        'weights_by_residue': weights, 'total_weight': total,
        'weighted_square_numerators_by_mod3_then_mod9': table,
        'full_layout_count': 27, 'nested_layout_count': 9,
        'all_global_maximizers_mod3_mod9': maximizers,
        'global_maximum': str(Fraction(maximum, total)),
        'nested_maximum': str(Fraction(nested, total)),
        'strict_gap': str(Fraction(maximum - nested, total)),
        'scope': 'One actual strictly positive radial probability on Z/9Z refutes the universal chain restriction. The first-exit normal form retains all original labels. This is not a covering-system resolution or a Lean proof.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=HERE / 'certificates/radial_chain_counterexample_certificate.json')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = compute()
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2) + '\n')
    else:
        certificate = json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique)
        need(certificate == result, 'entire recomputed certificate match')
    print('PASS all 27 original layouts; positive radial measure; strict nonnested maximum')


if __name__ == '__main__':
    main()
