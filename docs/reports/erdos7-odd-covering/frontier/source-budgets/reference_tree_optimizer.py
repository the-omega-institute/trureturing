#!/usr/bin/env python3
"""Exact rooted-tree reference-law optimization; all scores are integers.

This searches only the automorphic C3/Dp product-law family, not all laws.
A coordinate optimum is not a certificate of the joint minimum.
"""
from fractions import Fraction
from itertools import combinations, product
from math import prod
import json
import random


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def tree_minimum(cost, p, height, kind):
    check(len(cost) == p ** height and kind in ('C', 'D'), 'tree input')
    check(p >= (2 if kind == 'C' else 3), 'branch count')

    def visit(prefix, step, h):
        if h == 0:
            mask = 1 << prefix
            return cost[prefix], mask, (0, 0) if kind == 'C' else (cost[prefix], mask)
        children = [visit(prefix + j * step, step * p, h - 1) for j in range(p)]
        total = sum(row[0] for row in children)
        whole = sum(row[1] for row in children)
        best = None
        # Maintain constant-sized extrema in one pass; tie-break by child.
        lowest = []
        highest = []
        for j in range(p):
            lowest = sorted(lowest + [(children[j][0], j)])[:2]
            highest = sorted(highest + [(-children[j][0], j)])[:3]
        ascending = [j for _, j in lowest]
        descending = [j for _, j in highest]
        for trunk in range(p):
            recursive, selected = children[trunk][2]
            if kind == 'C':
                chosen = next(j for j in ascending if j != trunk)
                score = children[chosen][0] + recursive
                mask = children[chosen][1] | selected
            else:
                excluded = [j for j in descending if j != trunk][:2]
                score = total - children[trunk][0] - sum(children[j][0] for j in excluded) + recursive
                mask = whole ^ children[trunk][1]
                for j in excluded:
                    mask ^= children[j][1]
                mask |= selected
            if best is None or (score, mask) < best:
                best = score, mask
        return total, whole, best

    score, mask = visit(0, 1, height)[2]
    expected = (p ** height - 1) // (p - 1) if kind == 'C' else ((p - 3) * p ** height + 2) // (p - 1)
    check(mask.bit_count() == expected, 'orbit size')
    check(score == sum(v for i, v in enumerate(cost) if mask >> i & 1), 'witness score')
    return score, mask


def orbit_masks(p, h, kind, prefix=0, step=1):
    """Independent exhaustive shape enumeration, only for small checks."""
    if h == 0:
        return (0,) if kind == 'C' else (1 << prefix,)
    children = [orbit_masks(p, h - 1, kind, prefix + j * step, step * p) for j in range(p)]
    whole = [sum(1 << (prefix + j * step + k * step * p) for k in range(p ** (h - 1))) for j in range(p)]
    out = set()
    for trunk in range(p):
        others = [j for j in range(p) if j != trunk]
        if kind == 'C':
            for chosen in others:
                out.update(whole[chosen] | sub for sub in children[trunk])
        else:
            for excluded in combinations(others, 2):
                fixed = sum(whole[j] for j in others if j not in excluded)
                out.update(fixed | sub for sub in children[trunk])
    return tuple(sorted(out))


def selected(mask, size):
    return [i for i in range(size) if mask >> i & 1]


def canonical_mask(p, h, kind):
    c = 0
    forbidden = 0
    for e in range(1, h + 1):
        modulus = p ** e
        first = p ** (e - 1) - 1
        second = 2 * p ** (e - 1) - 1
        for x in range(p ** h):
            if x % modulus == second:
                c |= 1 << x
            if x % modulus in (first, second):
                forbidden |= 1 << x
    return c if kind == 'C' else ((1 << p ** h) - 1) ^ forbidden


def actual_tensor(primes, heights, labels):
    sizes = [p ** h for p, h in zip(primes, heights)]
    period = prod(sizes)
    check(len({n for n, _ in labels}) == len(labels), 'original numerical distinctness')
    check(all(n > 1 and n % 2 and period % n == 0 for n, _ in labels), 'original labels')
    tensor = {}
    for coordinates in product(*(range(n) for n in sizes)):
        bad = False
        for n, residue in labels:
            remainder = n
            hit = True
            for p, x in zip(primes, coordinates):
                q = 1
                while remainder % p == 0:
                    remainder //= p
                    q *= p
                if x % q != residue % q:
                    hit = False
                    break
            if hit:
                bad = True
                break
        tensor[coordinates] = int(bad)
    # Independent CRT-integer enumeration verifies every cylinder union entry.
    check(sum(tensor.values()) == sum(any(x % n == r % n for n, r in labels) for x in range(period)), 'CRT union count')
    return tensor


def joint_count(tensor, masks, sizes):
    return sum(tensor[x] for x in product(*(selected(m, s) for m, s in zip(masks, sizes))))


def coordinate_descent(tensor, primes, heights, initial=None):
    sizes = [p ** h for p, h in zip(primes, heights)]
    kinds = ['C' if p == 3 else 'D' for p in primes]
    masks = list(initial) if initial is not None else [canonical_mask(p, h, k) for p, h, k in zip(primes, heights, kinds)]
    count = joint_count(tensor, masks, sizes)
    trace = [count]
    while True:
        changed = False
        for axis, (p, h, kind) in enumerate(zip(primes, heights, kinds)):
            ranges = [range(s) if j == axis else selected(masks[j], s) for j, s in enumerate(sizes)]
            cost = [0] * sizes[axis]
            for x in product(*ranges):
                cost[x[axis]] += tensor[x]
            optimum, witness = tree_minimum(cost, p, h, kind)
            check(optimum <= count, 'coordinate cannot worsen current admissible shape')
            if optimum < count:
                masks[axis] = witness
                count = optimum
                check(count == joint_count(tensor, masks, sizes), 'same-source update')
                trace.append(count)
                changed = True
        if not changed:
            break
    return dict(count=count, denominator=prod(m.bit_count() for m in masks), masks=masks, strict_trace=trace)


def verify():
    rng = random.Random(7305040)
    results = []
    for p, h, kind, trials in ((3, 2, 'C', 512), (3, 3, 'C', 80), (5, 1, 'D', 32), (5, 2, 'D', 80), (7, 2, 'D', 24)):
        masks = orbit_masks(p, h, kind)
        for trial in range(trials):
            cost = [int(trial >> j & 1) for j in range(p ** h)] if (p, h) in ((3, 2), (5, 1)) else [rng.randrange(-8, 13) for _ in range(p ** h)]
            value, witness = tree_minimum(cost, p, h, kind)
            truth = min(sum(cost[j] for j in selected(m, len(cost))) for m in masks)
            check(value == truth and witness in masks, 'exhaustive orbit optimum')
        results.append(dict(prime=p, height=h, kind=kind, shapes=len(masks), score_tables=trials))
    return results


def find_local_trap(limit=3000):
    rng = random.Random(504073)
    primes = (3, 5, 7)
    heights = (1, 1, 1)
    orbits = [orbit_masks(p, 1, 'C' if p == 3 else 'D') for p in primes]
    for trial in range(limit):
        labels = [(p, 0) for p in primes] + [(n, rng.randrange(n)) for n in (15, 21, 35, 105)]
        tensor = actual_tensor(primes, heights, labels)
        descent = coordinate_descent(tensor, primes, heights)
        if descent['count'] == 0:
            continue
        value, witness = min((joint_count(tensor, masks, primes), masks) for masks in product(*orbits))
        if value < descent['count']:
            return dict(trial=trial, labels=labels, descent=descent, global_count=value, global_masks=witness, all_product_shapes=prod(map(len, orbits)))
    return None


def fixed_actual_example():
    primes = (3, 5, 7)
    heights = (1, 1, 1)
    labels = [(3, 0), (5, 0), (7, 0), (15, 11), (21, 16), (35, 18), (105, 29)]
    tensor = actual_tensor(primes, heights, labels)
    orbits = [orbit_masks(p, 1, 'C' if p == 3 else 'D') for p in primes]
    local = (4, 28, 124)
    global_witness = (2, 22, 122)
    check(joint_count(tensor, local, primes) == 1, 'actual local mass')
    check(joint_count(tensor, global_witness, primes) == 0, 'actual global witness')
    coordinate_minima = []
    for i in range(3):
        values = []
        for shape in orbits[i]:
            masks = list(local)
            masks[i] = shape
            values.append(joint_count(tensor, masks, primes))
        coordinate_minima.append(min(values))
    check(coordinate_minima == [1, 1, 1], 'coordinatewise optimality')
    global_minimum = min(joint_count(tensor, masks, primes) for masks in product(*orbits))
    check(global_minimum == 0, 'exhaustive joint optimum')
    descent = coordinate_descent(tensor, primes, heights)
    check(descent['count'] == 1 and descent['masks'] == list(local), 'strict-descent terminal law')
    return dict(original_labels=labels, primes=primes, heights=heights,
                local_shape=[selected(m, p) for m, p in zip(local, primes)],
                global_shape=[selected(m, p) for m, p in zip(global_witness, primes)],
                local_mass='1/15', global_mass='0',
                coordinate_minimum_counts=coordinate_minima,
                denominator=15, full_product_shapes=prod(map(len, orbits)))


def fixed_two_coordinate_blocks():
    """Actual 105-period obstruction to every strict update of at most two axes."""
    primes = (3, 5, 7)
    labels = [(3, 0), (5, 0), (7, 0), (15, 11), (21, 16), (35, 18), (105, 29)]
    tensor = actual_tensor(primes, (1, 1, 1), labels)
    orbits = [orbit_masks(p, 1, 'C' if p == 3 else 'D') for p in primes]
    local = (4, 28, 124)
    plateau = (2, 28, 122)
    global_witness = (2, 22, 122)
    all_rows = [(masks, joint_count(tensor, masks, primes)) for masks in product(*orbits)]
    blocks = []
    for axis, p in enumerate(primes):
        rows = [(masks, count) for masks, count in all_rows if masks[axis] == local[axis]]
        minimum = min(count for _, count in rows)
        winners = [masks for masks, count in rows if count == minimum]
        blocks.append(dict(fixed_prime=p, product_shapes=len(rows), minimum_count=minimum,
                           minimizing_shapes=len(winners)))
    check([row['product_shapes'] for row in blocks] == [210, 63, 30], 'all two-axis blocks')
    check([row['minimum_count'] for row in blocks] == [1, 1, 1], 'no strict two-axis improvement')
    check([row['minimizing_shapes'] for row in blocks] == [2, 3, 1], 'all block minimizers')
    check(sum(count == 0 for _, count in all_rows) == 1, 'unique global zero product')
    check(joint_count(tensor, plateau, primes) == 1, 'tied two-axis move')
    check(joint_count(tensor, global_witness, primes) == 0, 'one-axis escape after tie')

    def bad_integers(masks):
        return [x for x in range(105)
                if all((m >> (x % p)) & 1 for m, p in zip(masks, primes))
                and any(x % n == r for n, r in labels)]

    check(bad_integers(local) == [53] and bad_integers(plateau) == [88], 'actual tied hits')
    return dict(denominator=15, unchanged_coordinate_blocks=blocks,
                all_updates_of_at_most_two_coordinates_have_count_at_least=1,
                global_zero_shapes=1, local_hit_integers=bad_integers(local),
                tied_escape_shape=[selected(m, p) for m, p in zip(plateau, primes)],
                tied_escape_hit_integers=bad_integers(plateau),
                tied_then_strict_counts=[1, 1, 0],
                tied_changed_primes=[3, 7], final_strict_changed_prime=5)



import argparse
from pathlib import Path
import hashlib
import importlib.util
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/source-budgets/reference_tree_optimizer.json'
SOURCES = ('certificate_io.py', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', '../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean')


def calculate(base):
    result = dict(scope='Exact single-coordinate minima; joint descent only yields a feasible-law upper bound, not the global optimum or an unrestricted theorem.', verification=verify(), actual_local_global_separation=fixed_actual_example())
    result['strict_two_coordinate_trap'] = fixed_two_coordinate_blocks()
    result['schema'] = 'reference-tree-optimizer-v1'
    result['source_sha256'] = {name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('reference_tree_certificate_io',args.base/'certificate_io.py')
    check(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        check(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),'exact reference optimizer replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
