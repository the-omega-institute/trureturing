"""Exact packed-cell envelope for report511, with a reusable rational kernel.

The arbitrary-vector inequality is proved by separate convexity in the report.
The finite grids below check the kernel, not the quantified theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse
import hashlib
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def packed(length, total):
    need(type(length) is int and length >= 1, 'positive integer vector length')
    need(type(total) is int or isinstance(total, F), 'exact rational budget')
    total = F(total)
    need(0 <= total <= length, 'budget within vector capacity')
    whole = total.numerator // total.denominator
    result = [F(1)] * whole
    if total != whole:
        result.append(total - whole)
    return result + [F(0)] * (length - len(result))


def packed_prefixes(p, q, total_a, total_b):
    entries = sorted((a * b for a in packed(p, total_a) for b in packed(q, total_b)), reverse=True)
    sums = [F(0)]
    for value in entries:
        sums.append(sums[-1] + value)
    return sums


def block_loss(total_a, total_b):
    top = packed_prefixes(23, 29, total_a, total_b)
    branches = [3 * c + 16 * (18 - c - top[18 - c]) for c in range(19)]
    return min(branches), branches


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    total_a, total_b = F(29, 16), F(253, 16)
    top = packed_prefixes(23, 29, total_a, total_b)
    need(all(top[n] == n - F(3, 16) * max(n - 15, 0) for n in range(19)), 'sharp sufficient packed cell bound')
    lower, branches = block_loss(total_a, total_b)
    need(lower == 9 and [c for c, value in enumerate(branches) if value == 9] == [0, 1, 2, 3], 'all selector-count branches')
    thresholds = (22 * (1 - total_a / 23), 28 * (1 - total_b / 29))
    need(thresholds == (F(3729, 184), F(1477, 116)), 'actual normalized pure-loss thresholds')

    grid_pairs, grid_inequalities = 0, 0
    for p, q in ((2, 3), (3, 3)):
        for a, b in product(product((F(0), F(1, 2), F(1)), repeat=p),
                            product((F(0), F(1, 2), F(1)), repeat=q)):
            bound = packed_prefixes(p, q, sum(a), sum(b))
            actual = F(0)
            need(bound[0] == 0, 'empty cell selection')
            for n, value in enumerate(sorted((x * y for x in a for y in b), reverse=True), 1):
                actual += value
                need(actual <= bound[n], 'exact grid concentration control')
                grid_inequalities += 1
            need(actual == bound[-1] == sum(a) * sum(b), 'full table mass')
            grid_pairs += 1

    # Reuse the already checked actual report510 family; recompute its two
    # losses and mixed deletion from the original numerical residues.
    witness_raw = (args.input_dir / 'fixed_pure_phase_block_deficit.json').read_bytes()
    need(hashlib.sha256(witness_raw).hexdigest() == 'ca229751f077675ebff8ad1d9bef2dac2bacd4d6f750f8e2189609b10aad3c53', 'fixed report510 sharp witness')
    witness = json.loads(witness_raw)
    family = witness['literal_family_at_height2']
    points = witness['old_points']
    weight = (17, 16, 13)
    need(witness['weight'] == list(weight) and len(points) == 3 and len(family) == 222, 'same sharpness interface')
    need(len({r['modulus'] for r in family}) == 222 and all(r['modulus'] > 1 and r['modulus'] % 2 for r in family), 'distinct original odd moduli')
    root_counts = {}
    for p in (23, 29):
        root_counts[p] = []
        for point in points:
            pure = [r for r in family if r.get('prime') == p and (point - r['residue']) % r['old_label'] == 0]
            counts = [0] * p
            for z in range(p * p):
                if all(z % (p ** r['height']) != r['residue'] % (p ** r['height']) for r in pure):
                    counts[z % p] += 1
            root_counts[p].append(counts)
    losses = tuple((p - 1) * (1 - F(sum(root_counts[p][1]), p * p)) for p in (23, 29))
    need(losses == (F(11088, 529), F(10920, 841)) and all(a > b for a, b in zip(losses, thresholds)), 'actual witness satisfies broader thresholds')
    mixed = [r for r in family if 'prime' not in r]
    need(len(mixed) == 18, 'same mixed block')
    deletion = F(0)
    for i, point in enumerate(points):
        cells = {(r['residue'] % 23, r['residue'] % 29) for r in mixed if (point - r['residue']) % r['old_label'] == 0}
        deletion += weight[i] * sum((F(root_counts[23][i][a] * root_counts[29][i][b], 667 ** 2) for a, b in cells), F(0))
    need(deletion == F(373, 667), 'same actual sharp mixed union')
    actual_totals = (23 * (1 - losses[0] / 22), 29 * (1 - losses[1] / 28))
    actual_lower, actual_branches = block_loss(*actual_totals)
    need(actual_lower == 9, 'general envelope evaluated at the actual witness')
    out = {'root_sum_caps': list(map(str, (total_a, total_b))), 'pure_loss_thresholds': list(map(str, thresholds)),
           'packed_top_n_0_to_18': list(map(str, top[:19])), 'selector_loss_branches': list(map(str, branches)),
           'uniform_loss_numerator': str(lower), 'uniform_deletion_upper': '373/667',
           'grid_pairs': grid_pairs, 'grid_inequalities': grid_inequalities,
           'actual_witness_pure_losses': list(map(str, losses)), 'actual_witness_root_sums': list(map(str, actual_totals)),
           'actual_witness_selector_loss_branches': list(map(str, actual_branches)), 'actual_witness_deletion': str(deletion),
           'scope': 'Arbitrary pure phases under the stated two loss thresholds on the same uniform product fibre; fixed eighteen mixed labels with shared old selectors. Ordinary concentration proof, no new global support bound or Lean verification.'}
    if args.output:
        args.output.write_text(json.dumps(out, indent=2) + '\n')
    else:
        need(out == json.loads(Path(__file__).with_suffix('.json').read_text()), 'retained result differs')
    print(json.dumps({key: out[key] for key in ('pure_loss_thresholds', 'uniform_loss_numerator', 'uniform_deletion_upper', 'grid_inequalities', 'actual_witness_deletion')}, indent=2))


if __name__ == '__main__':
    main()
