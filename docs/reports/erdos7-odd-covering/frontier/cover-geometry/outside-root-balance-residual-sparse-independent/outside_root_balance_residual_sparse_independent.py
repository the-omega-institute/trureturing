#!/usr/bin/env python3
"""Independent 11-statistic reduction of the fixed 692 residual.

Reuse 692's sparse forward tensor engine, while the 693 producer reconstructs
and transports dense tensors in reverse order. Branch membership is derived
from literal residue sets, independently of category integer labels.
No optimizer and no producer result is imported.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
import argparse, importlib.util, json
import numpy as np

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--base', type=Path, default=Path(__file__).resolve().parent.parent)
ap.add_argument('--witness', type=Path)
ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
a = ap.parse_args()
witness = a.witness or a.base / 'clustered_full5_allfield_dual.json'
engine = a.base / 'clustered_full5_allfield_verify.py'
spec = importlib.util.spec_from_file_location('fixed692_sparse_engine', engine)
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
w = json.loads(witness.read_text())
p = v.prepare(a.base, witness, w['denominator'])
Q = v.Q
shape = p['category_shape']
checks = 0

def ck(condition, label):
    global checks
    checks += 1
    if not condition:
        raise ValueError(label)

ck(shape == (7, 10, 10, 10, 10), 'complete category geometry')
ck(8 * prod(q * (q - 1) for q in Q) < 2**63, 'source tensor int64 bound')
ck(p['M0'] < 2**63, 'source total int64 bound')
# Literal-residue predicates, no reliance on root1 being indices 0 and 1.
root_masks, special_masks, other_masks = [], [], []
for axis, (q, categories) in enumerate(zip(Q, p['cats'])):
    is_root, is_special, is_other = [], [], []
    for cat in categories:
        roots = {z % q for z in cat}
        ck((1 in roots) == (roots == {1}), 'category has one root1 truth value')
        special = all(z == 1 for z in cat)
        other = roots == {1} and all(z != 1 for z in cat)
        ck(special or other or 1 not in roots, 'literal root1 partition')
        is_root.append(roots == {1})
        is_special.append(special)
        is_other.append(other)
    dims = [1] * 5
    dims[axis] = len(categories)
    root_masks.append(np.broadcast_to(np.array(is_root).reshape(dims), shape))
    special_masks.append(np.broadcast_to(np.array(is_special).reshape(dims), shape))
    other_masks.append(np.broadcast_to(np.array(is_other).reshape(dims), shape))
root_count = sum(mask.astype(np.int8) for mask in root_masks)
pair_good = root_count <= 1
branch_masks = [root_count == 0]
for special, other in zip(special_masks, other_masks):
    branch_masks.extend([special & pair_good, other & pair_good])
branch_partition = sum(mask.astype(np.int8) for mask in branch_masks)
ck(np.all(branch_partition[pair_good] == 1), '11 literal branches partition allowed coordinates')
ck(np.all(branch_partition[~pair_good] == 0), 'no branch retains a forbidden pair')

branch_num = [0] * 11
branch_positive_states = [0] * 11
source_num = 0
actual_states = 0
positive_states = 0
live_cells = 0
cell_rows = []
for ci, (l, m) in enumerate(p['cells']):
    base_num = np.full(shape, (2 - (l == 4)) * (4 - (m == 10)), dtype=np.int64)
    for axis, row in enumerate(p['counts'][ci]):
        dims = [1] * 5
        dims[axis] = len(row)
        base_num *= np.array(row, dtype=np.int64).reshape(dims)
    base_num *= pair_good
    active = base_num > 0
    count = int(np.count_nonzero(active))
    if not count:
        continue
    live_cells += 1
    sparse = np.zeros(p['token_shape'], dtype=object)
    flat = sparse.reshape(-1)
    for column, value in p['scatter'][ci].items():
        flat[column] = value
    debit = v.transform(sparse, p['matrices'])
    selected_debit = debit[active]
    for value in selected_debit:
        ck(type(value) is int and 0 <= value <= p['debit_bound'], 'exact actual-state debit')
    residual = np.maximum(v.G.numerator * p['debitDen'] - v.G.denominator * debit, 0)
    weighted = residual * base_num
    positive = (residual > 0) & active
    part = [int(weighted[mask].sum()) for mask in branch_masks]
    pc = [int(np.count_nonzero(positive & mask)) for mask in branch_masks]
    cell_total = int(weighted.sum())
    ck(sum(part) == cell_total, 'cell complete residual partition')
    ck(sum(pc) == int(np.count_nonzero(positive)), 'cell positive-state partition')
    for j in range(11):
        branch_num[j] += part[j]
        branch_positive_states[j] += pc[j]
    src = int(base_num.sum())
    source_num += src
    actual_states += count
    positive_states += sum(pc)
    cell_rows.append({'cell': [l, m], 'actual_states': count,
                     'source_numerator': src, 'positive_residual_states': sum(pc),
                     'branch_numerators': [str(n) for n in part]})
    if live_cells % 20 == 0:
        print(json.dumps({'live_cells': live_cells, 'actual_states': actual_states}), flush=True)

common_den = p['M0'] * v.G.denominator * p['debitDen']
coeff = [F(n, common_den) for n in branch_num]
old_upper = sum(coeff, F(0))
ck(live_cells == 79, 'complete live central cells')
ck(actual_states == 2125830, 'complete actual states')
ck(F(source_num, p['M0']) == F(305684996597, 646498195200), 'common source mass')
ck(old_upper == F(w['expected']['upper']), '692 exact positive residual')
# Independent optimization: enumerate all 32 corners; also calculate the five slopes.
slopes = [coeff[1 + 2*i] - coeff[2 + 2*i] / (q - 1) for i, q in enumerate(Q)]
ck(all(slope < 0 for slope in slopes), 'all five strict decreasing affine slopes')
corner_rows = []
for bits in product((0, 1), repeat=5):
    params = [F((q - 1) * bit, q - 2) for q, bit in zip(Q, bits)]
    value = coeff[0]
    for i, (q, t) in enumerate(zip(Q, params)):
        other = (q - t) / (q - 1)
        cap = F(q - 1, q - 2)
        ck(0 <= t <= cap and 0 <= other <= cap, 'one realizable root-balanced cap law')
        ck(t / q + (q - 1) * other / q == 1, 'root1 mass preserved')
        value += coeff[1 + 2*i] * t + coeff[2 + 2*i] * other
    corner_rows.append({'bits': list(bits), 'value': str(value)})
maximum = max(F(row['value']) for row in corner_rows)
zero_corner = next(F(row['value']) for row in corner_rows if row['bits'] == [0]*5)
ck(maximum == zero_corner, 'one global zero-special law attains envelope maximum')
# The measure-level averaging theorem permits arbitrary root-balanced Borel laws,
# including singular laws. Their special-child ratio lies in [0,q], not just
# [0,(q-1)/(q-2)]. Verify the enlarged envelope separately.
uncapped_corner_rows = []
for bits in product((0, 1), repeat=5):
    params = [F(q * bit) for q, bit in zip(Q, bits)]
    value = coeff[0]
    for i, (q, t) in enumerate(zip(Q, params)):
        other = (q - t) / (q - 1)
        ck(0 <= t <= q and 0 <= other <= q, 'root-balanced Borel category envelope')
        ck(t / q + (q - 1) * other / q == 1, 'uncapped root1 mass preserved')
        value += coeff[1 + 2*i] * t + coeff[2 + 2*i] * other
    uncapped_corner_rows.append({'bits': list(bits), 'value': str(value)})
uncapped_maximum = max(F(row['value']) for row in uncapped_corner_rows)
ck(uncapped_maximum == maximum, 'all 32 uncapped endpoints have the same maximum')
R = F(153832, 151875)
target = F(193, 100000)
ck(old_upper <= maximum < target, 'outside envelope below target')
ck(R * maximum < target, 'joint central lifted envelope below target')
result = {
    'status': 'PASS', 'exact': True,
    'scope': 'Independent full-state aggregation of the 692 fixed-dual positive residual: arbitrary joint retained measures dominated by one common root-balanced product outside source, including singular Borel factors, with the same actual support and query interface. Sparse forward engine, literal-residue branch masks, both 32-corner envelopes. Measure-level allheight averaging is an ordinary mathematical premise, not inferred from this finite check. No new gate optimum, general joint-source bound or Lean verification.',
    'program_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    'engine_sha256': sha256(engine.read_bytes()).hexdigest(),
    'witness_sha256': sha256(witness.read_bytes()).hexdigest(),
    'source_sha256': p['pins'], 'numpy_version': np.__version__,
    'checks': checks, 'reused_engine_checks': v.CHECKS,
    'live_cells': live_cells, 'actual_states': actual_states,
    'positive_residual_states': positive_states,
    'source_mass': str(F(source_num, p['M0'])),
    'common_denominator': str(common_den),
    'no_root1_coefficient': str(coeff[0]),
    'branch_coefficients': [str(x) for x in coeff],
    'branch_positive_states': branch_positive_states,
    'slopes': [str(x) for x in slopes],
    'old_upper': str(old_upper), 'outside_upper': str(maximum),
    'outside_upper_decimal': float(maximum),
    'joint_central_factor': str(R), 'lifted_upper': str(R * maximum),
    'lifted_upper_decimal': float(R * maximum),
    'target': str(target), 'lifted_margin': str(target - R * maximum),
    'maximizing_special_densities': ['0']*5,
    'all_corners': corner_rows, 'uncapped_all_corners': uncapped_corner_rows,
    'uncapped_outside_upper': str(uncapped_maximum), 'per_cell': cell_rows,
}
a.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: value for k, value in result.items() if k not in ('all_corners', 'uncapped_all_corners', 'per_cell', 'source_sha256')}, indent=2), flush=True)
