#!/usr/bin/env python3
"""Actual original-label repacking attaining the complete deep-five cap limit."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/full_family_five_cap_sharpness.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
    'profile-notes/001-064/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md': 'b4c9a60a2c4a13147177e747d24dfb16a29e42eb2278f5948f22d49c0001563e',
    'profile-notes/065-128/75-forced27-and-complete-pure3-deletion-on-the-k-faces.md': 'bf21f845032d56fb86f86dfdecd5426e58eceac63a1c4e44d6fe0a16d7070f33',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def mixed_label(a, b):
    """(seven class, three exponent/residue, five exponent/residue)."""
    if b == 0:
        if a in (1, 2):
            return (1, a, 1 if a == 1 else 3, 0, 0)
        return (4, a, 3+3**(a-1), 0, 0)
    ternary = 0 if a == 0 else 1 if a == 1 else 3 if a == 2 else 3+2*3**(a-1)
    if b == 1:
        return (3 if a == 0 else 5 if a == 2 else 4, a, ternary, 1, 4)
    ray = min(a+1, 4)
    return (2, a, ternary, b, 4+ray*5**(b-1))


def finite(source, N):
    A, B, C = 3**N, 5**N, 7**N
    all5, masks = (1 << B)-1, {}
    def mask(b, residue):
        key = b, residue
        if key not in masks:
            masks[key] = sum(1 << j for j in range(residue, B, 5**b))
        return masks[key]
    state, labels = [all5]*A, []
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = source.source_label(a, b, 398)
        for x in range(ra, A, 3**aa):
            state[x] &= all5 ^ mask(bb, rb)
        labels.append(source.crt_label(aa, ra, bb, rb, 0, 0))
    t, q = (1-F(3, 3**(N-1)))/18, (1-F(1, B))/4
    # 3^(2-N) written as 3/3^(N-1), including N=3.
    require(t == sum((F(1, 3**a) for a in range(3, N+1)), F(0)), 'Complete finite three source sum')
    h, s = F(5, 9)-t, F(5, 9)-t-q
    require(F(sum(v.bit_count() for v in state), A*B) == s, 'Actual raw source mass')
    groups, totals, equality_count = {j: [0]*A for j in range(1, 6)}, {}, 0
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        j, aa, ra, bb, rb = mixed_label(a, b)
        bm = mask(bb, rb)
        count = 0
        for x in range(ra, A, 3**aa):
            require(not (groups[j][x] & bm), 'Repacked old carriers are disjoint within each seven class')
            groups[j][x] |= bm
            count += (state[x] & bm).bit_count()
        oldj, oa, ora, ob, orb = source.mixed_label(a, b)
        old_count = sum((state[x] & mask(ob, orb)).bit_count() for x in range(ora, A, 3**oa))
        require(count == old_count, 'Repacking retains the mass of every original old cofactor')
        equality_count += 1
        totals[j] = totals.get(j, 0)+count
        for e in range(1, N+1):
            labels.append(source.crt_label(aa, ra, bb, rb, e, j*7**(e-1)))
    seven, seven_counts = [0]*C, {}
    for j in range(1, 7):
        for e in range(1, N+1):
            for v in range(j*7**(e-1), C, 7**e):
                require(seven[v] == 0, 'Disjoint actual seven cylinders')
                seven[v] = j
                seven_counts[j] = seven_counts.get(j, 0)+1
            if j == 6:
                labels.append(source.crt_label(0, 0, 0, 0, e, j*7**(e-1)))
    require(len(labels) == len({m for m, _ in labels}) == (N+1)**3-1, 'Every nonunit original exponent triple occurs exactly once')
    require(all(m > 1 and m % 2 and 0 <= r < m for m, r in labels), 'All labels have distinct odd nonunit moduli and valid residues')
    u, kap = F(C-seven_counts[6], C), F(seven_counts[1], C-seven_counts[6])
    require(u == (5+F(1, C))/6 and kap == (1-F(1, C))/(5+F(1, C)), 'Exact physical seven normalization')
    old_total = F(sum(totals.values()), A*B)
    require(old_total == F(4, 9)+t+q/9-t*q, 'The complete old cap sum is unchanged by repacking')
    survivor = s-kap*old_total
    coefficient = h-kap*(F(4, 9)+t)
    tests = []
    for b in range(2, N+1):
        bm = mask(b, 4*5**(b-1))
        raw = F(sum((v & bm).bit_count() for v in state), A*B)
        deleted = {j: F(sum((state[x] & groups[j][x] & bm).bit_count() for x in range(A)), A*B) for j in range(1, 6)}
        require(raw == h/5**b, 'Every deep-five test is source free beyond the pure-three source')
        require(deleted == {1: F(4, 9*5**b), 2: F(0), 3: F(0), 4: t/5**b, 5: F(0)}, 'Only shallow three/nine and the single complete deep-three family hit the test')
        value = raw-kap*sum(deleted.values())
        require(value == coefficient/5**b, 'Exact full-family deep-five survivor formula')
        tests.append({'b': b, 'raw': str(raw), 'survivor': str(value), 'scaled_survivor': str(value*5**b)})
    nested_tests = []
    for b in range(2, N+1):
        bm = mask(b, 20)
        raw = F(sum((v & bm).bit_count() for v in state), A*B)
        deletion = F(sum((state[x] & groups[j][x] & bm).bit_count() for j in groups for x in range(A)), A*B)
        value = raw-kap*deletion
        require(value == coefficient/5**b, 'Nested cylinders in the free ball attain the same exact density')
        for c in range(2, b+1):
            require(bm & mask(c, 20) == bm, 'Every nested pair intersection equals its deeper cylinder')
        nested_tests.append({'b': b, 'residue': 20, 'survivor': str(value)})
    first_mask = mask(1, 3)
    first = F(sum((v & first_mask).bit_count() for v in state), A*B)
    first -= kap*F(sum((state[x] & groups[j][x] & first_mask).bit_count() for j in groups for x in range(A)), A*B)
    require(first == F(1, 5)*(h-F(1, 9)-kap*(F(1, 3)+t)), 'Exact first-five test formula')
    full_test = first+coefficient*(q-F(1, 5))
    require(full_test == first+sum((F(row['survivor']) for row in tests), F(0)), 'One complete finite pure-five test uses all its independent original labels')
    if N == 3:
        period = A*B*C
        alive = bytearray(b'\1')*period
        for modulus, residue in labels:
            alive[residue::modulus] = b'\0'*len(alive[residue::modulus])
        require(F(sum(alive), period)/u == survivor, 'Independent CRT enumeration of the whole original family')
        for row in tests:
            b = row['b']
            require(F(sum(alive[4*5**(b-1)::5**b]), period)/u == F(row['survivor']), 'Independent full CRT cylinder survivor')
        require(F(sum(alive[3::5]), period)/u == first, 'Independent full CRT first-five survivor')
        for row in nested_tests:
            require(F(sum(alive[20::5**row['b']]), period)/u == F(row['survivor']), 'Independent full CRT nested-cylinder survivor')
    return {'height': N, 'labels': len(labels), 'original_label_sha256': sha256(json.dumps(sorted(labels)).encode()).hexdigest(),
            'old_cofactors_preserved': equality_count, 'source_mass': str(s), 'old_cap_sum': str(old_total),
            'survivor_mass': str(survivor), 'deep_coefficient': str(coefficient), 'tests': tests, 'nested_tests': nested_tests,
            'first_five_survivor': str(first), 'complete_finite_pure_five_test': str(full_test), 'direct_CRT_period': A*B*C if N == 3 else None}


def calculate(base):
    io = module('full_family_cap_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    source = module('full_family_cap_source', base/'frontier/source-budgets/source_mass_compatibility.py')
    checks = [finite(source, N) for N in (3, 4, 5)]
    t, q, kap = F(1, 18), F(1, 4), F(1, 5)
    h = F(5, 9)-t
    S = h-q-kap*(F(4, 9)+t+q/9-t*q)
    tail = h-kap*(F(4, 9)+t)
    first = (h-F(1, 9)-kap*(F(1, 3)+t))/5
    require((S, tail, first, first+tail/20) == (F(53, 360), F(2, 5), F(14, 225), F(37, 450)), 'Ordinary all-height limit formulas')
    return {'schema': 'erdos7-full-family-five-cap-sharpness-v1', 'source_sha256': PINS, 'checks': checks,
            'limits': {'mass': str(S), 'deep_coefficient': str(tail), 'first_five_cap': str(first), 'full_pure_five_test': str(first+tail/20)},
            'scope': 'Explicit actual finite original-label sequence approaching the saturated K face. Complete full-family deep-five coefficient2/5 and independent pure-five test bound37/450 are sharp in this limit. Ordinary infinite-limit proof required; no finite covering, improved global K, Lean theorem or unrestricted Erdos7 solution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('full_family_cap_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact full-family cap certificate')
    print('PASS: actual repacking keeps every original cofactor mass and attains the2/5 deep-five limit.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
