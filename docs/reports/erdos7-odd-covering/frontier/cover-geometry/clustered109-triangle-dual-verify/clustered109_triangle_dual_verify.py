#!/usr/bin/env python3
"""Exact optimizer-free verification of the 3/5/15 replacement dual.

The input witness fixes a rational mixture. All 2,125,830 actual source states
are evaluated with arbitrary-precision Python integers. The optional outside
extension is measured using all 11 root-one branches and all 32 endpoints;
passing the fixed-source certificate does not presume that extension passes.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import argparse, importlib.util, json, time
import numpy as np

CHECKS = 0


def ck(condition, label):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(label)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--old-witness', type=Path)
    ap.add_argument('--witness', type=Path, default=Path(__file__).with_name('clustered109_triangle_replacement_witness.json'))
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    ap.add_argument('--metrics', type=Path)
    args = ap.parse_args()
    started = time.perf_counter()
    helper = args.base / 'clustered_full5_allfield_verify.py'
    oldpath = args.old_witness or args.base / 'clustered_full5_allfield_dual.json'
    old_digest = sha256(oldpath.read_bytes()).hexdigest()
    helper_digest = sha256(helper.read_bytes()).hexdigest()
    ck(helper_digest == 'edc32a8aff0e0fb8319e448da05a882b618d74ea97412cacdb5412bf1c7aca56', 'pinned source engine')
    ck(old_digest == '907c8b8f2a7636179893a4cdf1646be1eaf35c9da68dc0472f2c0308f0ea934e', 'pinned old witness')
    w = json.loads(args.witness.read_text())
    ck(w['schema'] == 'clustered109-triangle-replacement-dual-v1', 'triangle witness schema')
    ck(w['old_witness_sha256'] == old_digest, 'same old witness')
    old = json.loads(oldpath.read_text())
    spec = importlib.util.spec_from_file_location('fixed692_source_engine', helper)
    v = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v)
    p = v.prepare(args.base, oldpath, old['denominator'])
    ck(w['source_sha256'] == p['pins'], 'same actual109 source')
    c, target = F(w['triangle_budget']), F(w['target'])
    ck(c == F(1084133, 201247200) and c + v.G == 1, 'unchanged head coefficient')
    ck(target == F(193, 100000), 'same threshold')
    removed = set(w['removed_groups'])
    ck(removed == {32, 128, 160}, 'only three shallow groups removed')
    D = w['triangle_denominator']
    rows = w['triangle_rows']
    ck(type(D) is int and D > 0, 'positive rational denominator')
    ck(w['triangle_domain'] == [3, 5, 15], 'all independent phase labels')
    seen = set()
    for a, b, r, num in rows:
        ck(all(type(x) is int for x in (a, b, r, num)), 'integer witness row')
        ck(0 <= a < 3 and 0 <= b < 5 and 0 <= r < 15 and num > 0, 'lawful independent layout')
        ck((a, b, r) not in seen, 'distinct layout rows')
        seen.add((a, b, r))
    ck(sum(row[3] for row in rows) == D, 'new mixture has total budget c')
    table = json.loads((args.base / 'remaining33_global_root_exclusion_certificate.json').read_text())
    C = list(map(F, table['combined512_coefficients']))
    ck((C[32], C[128], C[160]) == (3*c, 3*c, 9*c), 'removed fees contain no original-loss component')
    selectors = []
    for mode in range(16):
        ex, ey = divmod(mode, 4)
        xs = ((0,), (0, 1), (0, 1, 2, 4, 5), (0, 1, 2, 4, 5))[ex]
        ys = ((0,), (0, 1, 2, 3), tuple(m for m in range(20) if m != 5), tuple(m for m in range(20) if m != 5))[ey]
        selectors.extend((mode, a, b) for a, b in product(xs, ys))
    ck(len(selectors) == 559, 'old selector indexing')
    removed_debit = [F(0) for _ in p['cells']]
    removed_rows = []
    for mode, support, sid, column, num in old['rows']:
        j = 32*mode + support
        if j not in removed:
            continue
        ck(support == column == 0 and selectors[sid][0] == mode, 'removed root-only row')
        ex, ey = divmod(mode, 4)
        _, a, b = selectors[sid]
        for ci, (l, m) in enumerate(p['cells']):
            if (ex == 0 or l//3 == a) and (ey == 0 or m//5 == b):
                removed_debit[ci] += C[j]*F(num, old['denominator'])
        removed_rows.append([mode, support, sid, column, num])
    ck(len(removed_rows) == 6, 'exactly six old rows removed')
    # Literal outside residues determine all 11 branches, including forbidden
    # double-root1 states. They do not use a guessed category index convention.
    shape = p['category_shape']
    root_masks, special_masks, other_masks = [], [], []
    for axis, (q, categories) in enumerate(zip(v.Q, p['cats'])):
        root, special, other = [], [], []
        for cat in categories:
            roots = {z % q for z in cat}
            ck((1 in roots) == (roots == {1}), 'constant root1 on every category')
            sp = all(z == 1 for z in cat)
            ot = roots == {1} and all(z != 1 for z in cat)
            ck(sp or ot or 1 not in roots, 'literal child partition')
            root.append(roots == {1}); special.append(sp); other.append(ot)
        dims = [1]*5; dims[axis] = len(categories)
        root_masks.append(np.broadcast_to(np.array(root).reshape(dims), shape))
        special_masks.append(np.broadcast_to(np.array(special).reshape(dims), shape))
        other_masks.append(np.broadcast_to(np.array(other).reshape(dims), shape))
    root_count = sum(mask.astype(np.int8) for mask in root_masks)
    good = root_count <= 1
    branches = [root_count == 0]
    for sp, ot in zip(special_masks, other_masks):
        branches.extend([sp & good, ot & good])
    partition = sum(mask.astype(np.int8) for mask in branches)
    ck(np.all(partition[good] == 1) and np.all(partition[~good] == 0), '11 disjoint complete branches')
    M = v.G.denominator*p['debitDen']
    ck(8*prod(q*(q-1) for q in v.Q) < 2**63 and p['M0'] < 2**63, 'safe integer source mass arithmetic')
    strides = [prod(p['token_shape'][k+1:]) for k in range(5)]
    source_num = states = old_num = new_num = positive_states = scalar_samples = 0
    branch_num = [0]*11
    cellwise_branch_num = [F(0)]*11
    branch_positive = [0]*11
    root_report = {}
    cell_report = []
    for ci, (l, m) in enumerate(p['cells']):
        masses = np.full(shape, (2-(l == 4))*(4-(m == 10)), dtype=np.int64)
        for axis, row in enumerate(p['counts'][ci]):
            dims = [1]*5; dims[axis] = len(row)
            masses *= np.array(row, dtype=np.int64).reshape(dims)
        masses *= good
        active = masses > 0
        if not np.any(active):
            continue
        rt = (l//3, m//5)
        x15 = (10*rt[0] + 6*rt[1]) % 15
        hnum = 0
        for a, b, r, num in rows:
            n = int(rt[0] == a) + int(rt[1] == b) + int(x15 == r)
            hnum += num*(n*n + 2*n)
        new_debit = c*F(hnum, D)
        addback, replacement = M*removed_debit[ci], M*new_debit
        ck(addback.denominator == replacement.denominator == 1, 'exact integer residual correction')
        sparse = np.zeros(p['token_shape'], dtype=object)
        for column, value in p['scatter'][ci].items():
            sparse.flat[column] = value
        debit = v.transform(sparse, p['matrices'])
        selected = debit[active]
        ck(all(type(x) is int and 0 <= x <= p['debit_bound'] for x in selected), 'full exact old debit')
        ck(np.all(v.G.denominator*selected >= int(addback)), 'remaining debit is nonnegative')
        flat_ids = np.flatnonzero(active)
        pos = len(flat_ids)//2
        rem = int(flat_ids[pos]); cats = []
        for size in reversed(shape):
            cats.append(rem % size); rem //= size
        cats.reverse()
        maps = [dict(p['matrices'][k][cats[k]]) for k in range(5)]
        direct = 0
        for column, value in p['scatter'][ci].items():
            term = value
            for k in range(5):
                term *= maps[k].get((column//strides[k]) % p['token_shape'][k], 0)
                if not term:
                    break
            direct += term
        ck(selected[pos] == direct, 'literal scalar transport control')
        scalar_samples += 1
        residual = v.G.numerator*p['debitDen'] - v.G.denominator*debit
        old_num += int(np.sum(np.maximum(residual, 0)*masses))
        positive = np.maximum(residual + int(addback) - int(replacement), 0)
        weighted = positive*masses
        cell_total = int(np.sum(weighted))
        parts = [int(np.sum(weighted[mask])) for mask in branches]
        pc = [int(np.count_nonzero((positive > 0) & active & mask)) for mask in branches]
        ck(sum(parts) == cell_total, 'exact cell residual partition')
        for j in range(11):
            branch_num[j] += parts[j]; branch_positive[j] += pc[j]
            gamma3 = F(81,82) if l == 4 else F(1)
            gamma5 = F(1875,1876) if m == 10 else F(1)
            cellwise_branch_num[j] += F(parts[j])/(gamma3*gamma5)
        if rt not in root_report:
            root_report[rt] = {'removed_debit': str(removed_debit[ci]), 'replacement_debit': str(new_debit), 'numerator': 0}
        ck(root_report[rt]['removed_debit'] == str(removed_debit[ci]) and root_report[rt]['replacement_debit'] == str(new_debit), 'root-only correction')
        root_report[rt]['numerator'] += cell_total
        count = int(np.count_nonzero(active))
        source_num += int(masses.sum()); states += count
        new_num += cell_total; positive_states += sum(pc)
        cell_report.append({'cell': [l, m], 'actual_states': count, 'source_numerator': int(masses.sum()), 'positive_residual_numerator': str(cell_total)})
    total_den = M*p['M0']
    upper = F(new_num, total_den)
    old_upper = F(old_num, total_den)
    R = F(153832, 151875)
    ck(states == 2125830 and len(cell_report) == 79, 'complete full-state pass')
    ck(F(source_num, p['M0']) == F(305684996597, 646498195200), 'same exact source mass')
    ck(old_upper == F(p['expected']['upper']), 'recover old692 upper')
    ck(upper < target and R*upper < target, 'fixed-source and joint-central-lift certificates')
    coeff = [F(n, total_den) for n in branch_num]
    ck(sum(coeff, F(0)) == upper, 'complete 11-branch residual total')
    slopes = [coeff[1+2*i] - coeff[2+2*i]/(q-1) for i, q in enumerate(v.Q)]
    corners = []
    for bits in product((0, 1), repeat=5):
        value = coeff[0]
        for i, (q, bit) in enumerate(zip(v.Q, bits)):
            t = F(q*bit); other = (q-t)/(q-1)
            ck(t/q + (q-1)*other/q == 1, 'one common root-balanced endpoint law')
            value += coeff[1+2*i]*t + coeff[2+2*i]*other
        corners.append({'bits': list(bits), 'upper': str(value)})
    outside_upper = max(F(row['upper']) for row in corners)
    cellwise_coeff = [x/total_den for x in cellwise_branch_num]
    cellwise_slopes = [cellwise_coeff[1+2*i]-cellwise_coeff[2+2*i]/(q-1) for i,q in enumerate(v.Q)]
    cellwise_corners=[]
    for bits in product((0,1),repeat=5):
        value=cellwise_coeff[0]
        for i,(q,bit) in enumerate(zip(v.Q,bits)):
            t=F(q*bit)
            value+=cellwise_coeff[1+2*i]*t+cellwise_coeff[2+2*i]*(q-t)/(q-1)
        cellwise_corners.append({'bits':list(bits),'upper':str(value)})
    cellwise_upper=max(F(row['upper']) for row in cellwise_corners)
    ck(cellwise_upper <= R*outside_upper,'sharper cellwise bound no worse than uniform lift')
    ck(upper <= outside_upper, 'outside envelope includes reference source')
    result = {
        'status': 'PASS', 'exact': True, 'complete': True,
        'scope': 'The triangle-improved fixed actual109 gate, all measurable retention and heights via existing averaging and pooling. The 11-branch envelope is separately evaluated for common root-balanced product outside references; its pass flags determine the additional numerical conclusion. No optimum, positive primal field, arbitrary joint outside source or Lean claim.',
        'source_sha256': p['pins'], 'helper_sha256': helper_digest, 'old_witness_sha256': old_digest,
        'witness_sha256': sha256(args.witness.read_bytes()).hexdigest(),
        'program_sha256': sha256(Path(__file__).read_bytes()).hexdigest(), 'numpy_version': np.__version__,
        'removed_groups': sorted(removed), 'removed_rows': removed_rows,
        'retained_old_rows': len(old['rows'])-len(removed_rows), 'triangle_budget': str(c),
        'triangle_rows': rows, 'triangle_denominator': D,
        'actual_states': states, 'positive_residual_states': positive_states,
        'source_mass': str(F(source_num, p['M0'])), 'common_residual_denominator': str(total_den),
        'old_upper': str(old_upper), 'upper': str(upper), 'upper_decimal': float(upper),
        'target': str(target), 'below_target': upper < target,
        'joint_central_factor': str(R), 'lifted_upper': str(R*upper), 'lifted_upper_decimal': float(R*upper),
        'lifted_below_target': R*upper < target, 'lifted_margin': str(target-R*upper),
        'root_coefficients': [{'root': list(rt), 'removed_debit': x['removed_debit'], 'replacement_debit': x['replacement_debit'], 'upper': str(F(x['numerator'], total_den))} for rt, x in sorted(root_report.items())],
        'branch_coefficients': list(map(str, coeff)), 'branch_positive_states': branch_positive,
        'outside_slopes': list(map(str, slopes)), 'outside_upper': str(outside_upper),
        'outside_upper_decimal': float(outside_upper), 'outside_below_target': outside_upper < target,
        'outside_lifted_upper': str(R*outside_upper), 'outside_lifted_upper_decimal': float(R*outside_upper),
        'outside_lifted_below_target': R*outside_upper < target,
        'outside_maximizers': [row['bits'] for row in corners if F(row['upper']) == outside_upper],
        'cellwise_coefficients':list(map(str,cellwise_coeff)), 'cellwise_slopes':list(map(str,cellwise_slopes)), 'cellwise_corners':cellwise_corners, 'cellwise_upper':str(cellwise_upper), 'cellwise_upper_decimal':float(cellwise_upper), 'cellwise_below_target':cellwise_upper<target,
        'outside_32_corners': corners, 'literal_scalar_samples': scalar_samples,
        'reused_prepare_checks': v.CHECKS, 'new_checks': CHECKS, 'checks': v.CHECKS+CHECKS,
        'per_cell': cell_report,
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    if args.metrics:
        args.metrics.write_text(json.dumps({'program_sha256': result['program_sha256'], 'witness_sha256': result['witness_sha256'], 'total_seconds': time.perf_counter()-started, 'peak_rss_bytes': v.rss()}, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status', 'actual_states', 'upper', 'lifted_upper', 'checks', 'outside_upper', 'outside_lifted_upper', 'outside_below_target', 'outside_lifted_below_target')}, indent=2))


if __name__ == '__main__':
    main()
