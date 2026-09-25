#!/usr/bin/env python3
CHECK_COUNT = 0

def require(condition, label):
    global CHECK_COUNT
    if not condition:
        raise ArithmeticError(label)
    CHECK_COUNT += 1

"""Verify an exact dual using only pinned inputs and rational arithmetic."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import json, argparse
ap = argparse.ArgumentParser(description='Verify the all280 fixed-null thirteen-orbit exact zero upper bound.')
ap.add_argument('--source-dir', type=Path, required=True)
ap.add_argument('--certificate', type=Path, default=Path(__file__).with_name('fixed_null_280_exact_dual.json'))
args = ap.parse_args()
D = args.source_dir
diag = json.loads(args.certificate.read_text())
raw = (D / 'actual_pair_activation_certificate.json').read_bytes()
s = json.loads(raw)
require(sha256(raw).hexdigest() == diag['source_sha256'] == '2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f', "sha256(raw).hexdigest() == diag['source_sha256'] == '2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'")
c = F(s['constants']['continuation_c'])
g = 1 - c
require(c == F(1084133, 201247200) and 0 < c < 1, 'c == F(1084133, 201247200) and 0 < c < 1')
qs = (7, 11, 13, 17, 19)
r = [F(1, q - 1) for q in qs]
a = [F(1, q * (q - 2)) for q in qs]
loss = list(map(F, s['complete_coefficients']['loss']))
W = list(map(F, s['complete_coefficients']['weighted_nonunit_query']))
P = [F()] * 512
add = [F()] * 512
for i in range(5):
    for j in range(i + 1, 5):
        T = (1 << i) + (1 << j)
        for mode in (0, 1, 4, 5):
            P[32 * mode + T] = r[i] * r[j] + a[i] * r[j] + r[i] * a[j]
for e in product(range(3), repeat=7):
    if sum((x > 0 for x in e)) != 4 or not (e[0] == 2 or e[1] == 2):
        continue
    T = sum((1 << i for i, x in enumerate(e[2:]) if x))
    add[32 * (4 * e[0] + e[1]) + T] += prod((r[i] if x == 1 else a[i] for i, x in enumerate(e[2:]) if x))
co = [g * (l + p + d) + c * w for l, p, d, w in zip(loss, P, add, W)]
require(len(co) == 512 and min(co) >= 0, 'len(co) == 512 and min(co) >= 0')
cats = diag['category_order']
N = len(cats)
cc = {}
rows = [[0], [1, 2], [4, 5]]
cols = [[0, 1, 2, 3, 4], [10], [11, 12, 13, 14], [6, 7, 8, 9], [15, 16, 17, 18, 19]]
require(cats == [[x, y] for x, y in product(rows, cols) if (x[0] // 3, y[0] // 5) != (0, 0)], 'cats == [[x, y] for x, y in product(rows, cols) if (x[0] // 3, y[0] // 5) != (0, 0)]')
for k, (xs, ys) in enumerate(cats):
    for l, m in product(xs, ys):
        require((l, m) not in cc and l != 3 and (m != 5) and ((l // 3, m // 5) != (0, 0)), '(l, m) not in cc and l != 3 and (m != 5) and ((l // 3, m // 5) != (0, 0))')
        cc[l, m] = k
require(len(cc) == 80 and N == 13, 'len(cc) == 80 and N == 13')
R = [[F()] * N for _ in range(32)]
for (l, m), k in cc.items():
    Z = [1 - (r[i] + a[i]) * (int(l // 3 == 0) + int(m // 5 == 2)) - r[i] * (int((l // 3, m // 5) == (0, 2)) + int(l == 0) + int(m == 10)) for i in range(5)]
    for T in range(32):
        R[T][k] = prod((Z[i] for i in range(5) if not T >> i & 1))

def menus(n, block, w, zero, deep, mode):
    if mode == 0:
        return [w]
    if mode == 1:
        return [[w[k] if k // block == j else F() for k in range(n)] for j in range(n // block)] + [[F()] * n]
    return [[(w[k] if mode == 2 else deep) if k == leaf else F() for k in range(n)] for leaf in range(n) if leaf != zero] + [[F()] * n]

def exact_selectors(src):
    z, w, zz, ww = src
    x = [F() if l == z else F(1, 9) if l == w else F(2, 9) for l in range(6)]
    y = [F() if m == zz else F(3, 75) if m == ww else F(4, 75) for m in range(20)]
    sels = []
    slices = []
    for e3, e5 in product(range(4), repeat=2):
        start = len(sels)
        for u, v in product(menus(6, 3, x, z, F(1), e3), menus(20, 5, y, zz, F(4, 5), e5)):
            row = [F()] * N
            for (l, m), k in cc.items():
                row[k] += u[l] * v[m]
            sels.append(row)
        slices.append((start, len(sels)))
    return (sels, slices)
cuts = []
for row in diag['cuts']:
    z, w, zz, ww = row['source']
    require(z == 3 and zz == 5, 'z == 3 and zz == 5')
    require(0 <= z < 6 and 0 <= w < 6 and (z != w) and (0 <= zz < 20) and (0 <= ww < 20) and (zz != ww), '0 <= z < 6 and 0 <= w < 6 and (z != w) and (0 <= zz < 20) and (0 <= ww < 20) and (zz != ww)')
    indices = row['indices']
    require(len(indices) == 16 and all((len(x) == 32 for x in indices)), 'len(indices) == 16 and all((len(x) == 32 for x in indices))')
    sel, slices = exact_selectors(row['source'])
    slope = [g * sel[0][k] * R[0][k] for k in range(N)]
    for mode, (lo, hi) in enumerate(slices):
        for T in range(32):
            idx = indices[mode][T]
            require(isinstance(idx, int) and lo <= idx < hi, 'isinstance(idx, int) and lo <= idx < hi')
            v = sel[idx]
            coeff = co[32 * mode + T]
            for k in range(N):
                slope[k] -= coeff * v[k] * R[T][k]
    require(slope == list(map(F, row['slope'])), "slope == list(map(F, row['slope']))")
    cuts.append({'source': row['source'], 'slope': slope, 'weight': F(row['weight'])})
weights = [cut['weight'] for cut in cuts]
result_slope = [sum((cut['weight'] * cut['slope'][k] for cut in cuts), F()) for k in range(N)]
require(all((w >= 0 for w in weights)) and sum(weights) == 1, 'all((w >= 0 for w in weights)) and sum(weights) == 1')
require(all((x <= 0 for x in result_slope)), 'all((x <= 0 for x in result_slope))')
require(result_slope == list(map(F, diag['weighted_slope'])), "result_slope == list(map(F, diag['weighted_slope']))")
print(json.dumps({'status': 'PASS', 'check_count': CHECK_COUNT, 'cuts': len(cuts), 'categories': N, 'live_unmasked_cells': len(cc), 'every_cut_reconstructed_exactly': True, 'nonnegative_weights_sum_one': True, 'weighted_slope_nonpositive': True, 'all_source_null_pairs': sorted({(row['source'][0], row['source'][2]) for row in cuts}), 'scope': diag['scope'], 'new_lean_verification': False}, indent=2))
