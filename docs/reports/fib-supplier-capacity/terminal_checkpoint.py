"""Finite source arithmetic and falsifiers for TM61; Python 3.9+, stdlib.

This experiment reuses the exact Clifford arithmetic of h15_joint_cover.py.
It is neither a source supplier nor an admission judge. The all-source and
all-cap obligations are the ordinary proofs in TM58 and TM61.
"""

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path


MODULE_PATH = Path(__file__).with_name('h15_joint_cover.py')
SPEC = importlib.util.spec_from_file_location('existing_tm60_arithmetic', MODULE_PATH)
ARITH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ARITH)
require = ARITH.require


def literal_target(h, z, w):
    if w > h:
        return (0, 1, 4 * z)
    composition = (4 * (2 * z - w), 4 * (w - z))
    return ((2, (((0, 0, 0),) * 3, composition)) if z + w <= h
            else (1, composition, 1, 1))


def supplier(h, z, w):
    count = (h + 3) // 4
    if w > h:
        return 1
    if z <= 2 * count:
        return 1 + (z - 1) % count
    x, y = z - 2 * count, w - 2 * count
    return (x + 1) // 2 if x % 2 == y % 2 else (y + 1) // 2


def prefix(cap, z, w):
    """Actual composition guards, with no fictitious omitted context."""
    h, count = cap // 4, (cap // 4 + 3) // 4
    label = supplier(h, z, w)
    cutoff = 2 * count + 2 * label - 2
    a, b = 4 * (2 * z - w), 4 * (w - z)
    if cutoff < h:
        material = cap - 4 * cutoff
        accepted = a + b + material <= cap
        first = 'A' if accepted else 'R'
        if accepted:
            a += material
    else:
        material, first = 0, 'O'
    accepted = a + 2 * b <= cap
    if accepted:
        a, b = b, a + b
    return label, first + ('A' if accepted else 'R'), a + b, material


def decode(h, label, branch, entry, material):
    count = (h + 3) // 4
    cutoff = 2 * count + 2 * label - 2
    if branch in ('RR', 'OR'):
        return (0, 1, entry)
    if branch in ('AA', 'OA'):
        w = (entry - material) // 4
        z = label if w <= 2 * label - 1 else count + label
    elif branch == 'AR':
        z = (entry - material) // 4
        if label == 1 and z == 2 * count and h <= 4 * count - 2:
            return (0, 1, 4 * z)
        w = cutoff + 1 if z <= 2 * count else cutoff + 1 + z % 2
    else:
        w = entry // 4
        z = cutoff + 1 if w % 2 or w == cutoff + 2 else cutoff + 2
    return literal_target(h, z, w)


def powers(base):
    values = [ARITH.IDENTITY]
    for _ in range(3):
        values.append(ARITH.multiply(values[-1], base))
    return values


APOW, BPOW = powers(ARITH.A), powers(ARITH.B)


def source_word(z, w):
    r, s = 2 * z - w, w - z
    return 'a' * (2 * r - 1) + 'b' * (2 * s) + 'a' + 'b' * (2 * s - 1) + 'a' * (2 * r) + 'b'


def tree(word, shape):
    require(bool(word), 'empty tree forbidden')
    if len(word) == 1:
        return word
    if shape == 'balanced':
        split = len(word) // 2
        return tree(word[:split], shape), tree(word[split:], shape)
    result = word[0]
    for letter in word[1:]:
        result = result, letter
    return result


def leaves(value):
    stack, output = [value], []
    while stack:
        item = stack.pop()
        if isinstance(item, str):
            output.append(item)
        else:
            stack.extend((item[1], item[0]))
    return ''.join(output)


def replace(value):
    if isinstance(value, str):
        return 'b' if value == 'a' else ('b', 'a')
    return replace(value[0]), replace(value[1])


def execute(cap, z, w, shape):
    """Whole candidates are constructed with literal ordered brackets."""
    original = tree(source_word(z, w), shape)
    current = original
    for _ in range(3):
        require(ARITH.leaf_product(leaves(current)) == ARITH.IDENTITY,
                'actual source fails the common unit history')
        current = replace(current)
    current = original
    label, branch, expected_entry, material = prefix(cap, z, w)
    whole, accepted_replacements = 0, 0
    first = 'O'
    if material:
        candidate = current, tree('a' * material, 'left')
        whole += 1
        accepted = len(leaves(candidate)) <= cap
        first = 'A' if accepted else 'R'
        if accepted:
            current = candidate
    candidate = replace(current)
    whole += 1
    accepted = len(leaves(candidate)) <= cap
    if accepted:
        current = candidate
        accepted_replacements += 1
    actual_branch = first + ('A' if accepted else 'R')
    entry = len(leaves(current))
    require((actual_branch, entry) == (branch, expected_entry), 'actual prefix bridge fails')
    lo, hi, inserted = 0, cap, 0
    while hi - lo > 1:
        cut = (lo + hi) // 2
        length = hi - cut
        candidate = current, tree('a' * length, 'left')
        whole += 1
        if len(leaves(candidate)) <= cap:
            current = candidate
            inserted += length
            hi = cut
        else:
            lo = cut
    whole += 1
    final_word = leaves(current)
    require(len(final_word) == cap and hi == entry == cap - inserted,
            'actual Size_H saturation/entry acquisition fails')
    require(len(leaves((current, 'a'))) > cap, 'terminal single-leaf refusal fails')
    require(len(leaves(('b', current))) > cap, 'terminal left refusal fails')
    require(len(leaves(replace(current))) > cap, 'terminal rho refusal fails')
    expected = BPOW[cap % 4] if branch == 'AA' else APOW[cap % 4]
    require(ARITH.leaf_product(final_word) == expected, 'terminal literal E fails')
    require(decode(cap // 4, label, branch, entry, material)
            == literal_target(cap // 4, z, w), 'original literal target inverse fails')
    require(whole <= (cap - 1).bit_length() + 3, 'original joint call bound fails')
    require(accepted_replacements <= 1, 'replacement depth bound fails')
    return label, branch, expected


def target_loads(h):
    count = (h + 3) // 4
    total = [set() for _ in range(count)]
    aa = [set() for _ in range(count)]
    other = [set() for _ in range(count)]
    branches = Counter()
    for z in range(2, h + 1):
        for w in range(z + 1, 2 * z):
            target = literal_target(h, z, w)
            for delta in range(4):
                label, branch, entry, material = prefix(4 * h + delta, z, w)
                require(1 <= label <= count, 'authentic supplier range fails')
                require(decode(h, label, branch, entry, material) == target,
                        'complete composition inverse fails')
                if delta == 0:
                    total[label - 1].add(target)
                    (aa if branch == 'AA' else other)[label - 1].add(target)
                    branches[branch] += 1
    n, a, b = [list(map(len, groups)) for groups in (total, aa, other)]
    require(all(not x & y and x | y == t for x, y, t in zip(aa, other, total)),
            'initial target is not uniquely assigned a terminal category')
    k0, k1 = h + h // 2 - count - 1, h + h // 2 - 2 * count
    require(max(n) == n[0] == k0, 'K0 lower/upper loads fail')
    require(max(a + b) == b[0] == k1 and a[0] == count - 1,
            'K1 lower/upper loads fail')
    # The rank and inverse are checked on every distinct literal target;
    # shared ranks across authentic i or E categories are intentional.
    for groups, bound in ((total, k0), (aa + other, k1)):
        for group in groups:
            dictionary = sorted(group)
            encoding = {target: rank for rank, target in enumerate(dictionary)}
            require(len(dictionary) <= bound, 'rank alphabet exceeds bound')
            require(all(dictionary[encoding[target]] == target for target in group),
                    'literal rank inverse fails')
    return {'h': h, 'L': count, 'target_loads': n, 'AA_loads': a,
            'other_loads': b, 'K0': k0, 'K1_by_delta': [k0, k1, k1, k1],
            'terminal_image_by_delta': [1] + [1 if count == 1 else 2] * 3,
            'composition_branches': dict(sorted(branches.items()))}


def recompute():
    require(APOW[2] == ARITH.IDENTITY and BPOW[2] == tuple(-x for x in ARITH.IDENTITY),
            'source Clifford square relations fail')
    require(all(APOW[d] != BPOW[d] for d in (1, 2, 3)), 'nonzero residue distinction fails')
    rows = [target_loads(h) for h in range(2, 129)]
    h15 = rows[13]
    require(h15['h'] == 15 and h15['target_loads'] == [17, 12, 14, 13]
            and h15['AA_loads'] == [3, 5, 7, 9]
            and h15['other_loads'] == [14, 7, 7, 4]
            and h15['K1_by_delta'] == [17, 14, 14, 14],
            'H60..63 source-specific loads differ')
    branches, images = Counter(), {}
    executions = 0
    for h in range(2, 21):
        for z in range(2, h + 1):
            for w in range(z + 1, 2 * z):
                for delta in range(4):
                    cap = 4 * h + delta
                    for shape in ('left', 'balanced'):
                        label, branch, value = execute(cap, z, w, shape)
                        branches[branch] += 1
                        images.setdefault(cap, set()).add(value)
                        executions += 1
    for cap, values in images.items():
        expected = 1 if cap % 4 == 0 or (cap // 4 + 3) // 4 == 1 else 2
        require(len(values) == expected, 'actual terminal behavioral image differs')
    # Actual realizations refute free recovery from terminal behavior and
    # the claim that an omitted prefix inserts the positive cap residue.
    falsifiers = []
    for cap, points in ((61, ((9, 16), (10, 16))), (60, ((5, 6), (9, 16)))):
        observations = [execute(cap, z, w, 'left') for z, w in points]
        require(observations[0][0] == observations[1][0] == 1,
                'falsifier loses authentic common i')
        require(observations[0][2] == observations[1][2], 'falsifier E differs')
        require(literal_target(cap // 4, *points[0]) != literal_target(cap // 4, *points[1]),
                'falsifier original targets agree')
        falsifiers.append({'H': cap, 'i': 1, 'coordinates': points,
                           'original_targets': [literal_target(cap // 4, *p) for p in points],
                           'branches': [o[1] for o in observations],
                           'same_terminal_E': True})
    label, branch, value = execute(21, 2, 3, 'balanced')
    require((label, branch) == (2, 'OA') and value == ARITH.A and value != ARITH.B,
            'genuine omission falsifier fails')
    altered = tree(source_word(2, 3), 'balanced'), 'a'
    require(len(leaves(altered)) <= 21, 'altered prefix should be accepted')
    altered = replace(altered)
    require(len(leaves(altered)) <= 21, 'altered rho should be accepted')
    altered = altered, tree('a' * (21 - len(leaves(altered))), 'left')
    require(ARITH.leaf_product(leaves(altered)) == ARITH.B,
            'unperformed residue-prefix product differs from the falsifier')
    return {'schema': 'fib-tm61-terminal-checkpoint-v1',
            'load_domain': {'h_first': 2, 'h_last': 128, 'all_cap_residues': True},
            'load_rows': rows,
            'actual_source_domain': {'h_first': 2, 'h_last': 20,
                                     'all_cap_residues': True,
                                     'brackets': ['left', 'balanced']},
            'actual_tree_executions': executions,
            'actual_composition_parameters': sum(h * (h - 1) // 2 for h in range(2, 21)),
            'actual_branch_counts': dict(sorted(branches.items())),
            'falsifiers': falsifiers,
            'omission_falsifier': {'H': 21, 'i': 2, 'z': 2, 'w': 3,
                                   'branch': 'OA', 'actual_prefix_material': 0,
                                   'terminal_E': 'A', 'fictitious_prefix_E': 'B'},
            'H60_63': {'supplier_alphabet': 4, 'K0': [17, 17, 17, 17],
                       'K1': [17, 14, 14, 14], 'behavioral_image': [1, 2, 2, 2]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = recompute()
    canonical = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.write:
        args.certificate.write_text(canonical)
    else:
        require(args.certificate.read_text() == canonical, 'retained finite data differs')
    print(json.dumps({'actual_tree_executions': result['actual_tree_executions'],
                      'load_caps': [8, 515], 'H60_63': result['H60_63'],
                      'actual_branch_counts': result['actual_branch_counts']}, sort_keys=True))


if __name__ == '__main__':
    main()
