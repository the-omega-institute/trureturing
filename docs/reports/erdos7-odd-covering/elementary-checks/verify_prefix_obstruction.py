#!/usr/bin/env python3
"""Exact small counterexample to independent-depth overlap feasibility.

All six original labels have height2 at prime3. The first two diagonal
pairs agree modulo9; every other cross pair agrees modulo3 and differs
modulo9. Equality modulo9 is a lower bound on valuation, not an infinity
label or a chosen exact valuation2. No covering bound is asserted.
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
from itertools import product
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def strict_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'duplicate JSON key: ' + key)
        out[key] = value
    return out


def compatible(values, left, right, modulus, child_only=False):
    for i in left:
        for j in right:
            x, y = values['L' + str(i)], values['R' + str(j)]
            if not child_only and (x - y) % 3:
                return False
            equal = (x - y) % modulus == 0
            if equal != (i == j and i < 2):
                return False
    return True


def search(left, right):
    labels = ['L' + str(i) for i in left] + ['R' + str(j) for j in right]
    # Every cross pair agrees modulo3, so all six labels have one root.
    # Fix that root to1; the three possible next digits are exhaustive.
    count, witness = 0, None
    for digits in product(range(3), repeat=len(labels)):
        values = {label: 1 + 3 * digit for label, digit in zip(labels, digits)}
        if compatible(values, left, right, 9):
            count += 1
            if witness is None:
                witness = values
    return count, witness


def result():
    count, witness = search(range(3), range(3))
    require(count == 0 and witness is None, 'joint mod3/mod9 realization is impossible')
    # Both independent levels are feasible, including the effective
    # alphabet after removing pure root0: children1,2,4,5 are all active.
    root_values = {s + str(i): 1 for s in ('L', 'R') for i in range(3)}
    child_values = dict(L0=1, R0=1, L1=2, R1=2, L2=4, R2=5)
    require(all((x-y) % 3 == 0 for x in root_values.values() for y in root_values.values()),
            'level1 has one complete bipartite component')
    require(compatible(child_values, range(3), range(3), 9, child_only=True),
            'level2 independently has two matched pairs and two opposite isolates')
    require(all(x % 3 for x in child_values.values()), 'all independent child witnesses are active')
    deletions = []
    for side in ('L', 'R'):
        for removed in range(3):
            left = [i for i in range(3) if (side, removed) != ('L', i)]
            right = [j for j in range(3) if (side, removed) != ('R', j)]
            number, found = search(left, right)
            require(number > 0 and found is not None, 'every single-label deletion is realizable')
            deletions.append(dict(removed=side + str(removed), count=number, witness=found))
    return dict(schema='erdos7-original-prefix-obstruction-v1', prime=3, original_label_heights=2,
                root_equalities=[[1]*3 for _ in range(3)],
                child_equalities=[[1,0,0],[0,1,0],[0,0,0]],
                independent_root_witness=root_values, independent_child_witness=child_values,
                root_CR1_demand=1, active_root_alphabet_size=2,
                child_CR1_demand=4, active_depth2_alphabet_size=6,
                required_children_inside_one_root=4, available_children_inside_one_root=3,
                exhaustive_next_digit_assignments=729, joint_witness_count=count,
                single_label_deletions=deletions,
                scope='Feasibility cut for a common original-label prefix assignment. No source probability, killed expectation, covering inequality, general endpoint or Lean theorem is computed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=(Path(__file__).resolve().parents[1] / 'certificates/prefix_obstruction_certificate.json'))
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = result()
    if args.write:
        write_certificate_text(args.certificate, json.dumps(expected, indent=2) + '\n')
    else:
        actual = json.loads(read_artifact_text(args.certificate), object_pairs_hook=strict_object)
        require(actual == expected, 'whole certificate equals exact recomputation')
    print('PASS: both independent levels feasible; 729 joint digit assignments fail; all six single-label deletions feasible')
