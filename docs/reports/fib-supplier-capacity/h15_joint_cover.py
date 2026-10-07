"""Exact finite evidence for TM60; Python 3.9+, standard library only.

This is mathematical experiment/certificate code, not an admission judge or
an implementation of the authentic supplier. The source-history bridge is
the paper proof in TM59.3 and TM60.3.
"""

import argparse
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations_with_replacement
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


POINTS = tuple(
    (z, w) for z in range(2, 16)
    for w in range(z + 1, min(2 * z - 1, 15) + 1) if z + w > 15
) + tuple((z, 16) for z in range(9, 16))
POSITIVE = frozenset(
    [(7, w) for w in range(9, 14)]
    + [(8, w) for w in range(10, 16)]
    + [(9, w) for w in range(10, 17)]
    + [(10, w) for w in range(11, 17)]
    + [(11, w) for w in range(12, 16)] + [(12, 13), (12, 14)]
)
EXPECTED_PREFIX = [0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 6, 8, 10, 10, 10, 10]
EXPECTED_HISTOGRAM = {30: 1, 31: 2, 32: 23, 33: 133, 34: 458,
                      35: 1112, 36: 2205, 37: 3013, 38: 2785,
                      39: 1809, 40: 696, 41: 104}


def slots(l, c, kind):
    """Canonical nonempty slot masks of ALL targets in one interval."""
    groups = {}
    for index, (z, w) in enumerate(POINTS):
        if l < z <= c:
            key = ('column', w) if kind == 'R' and w <= c else ('row', z)
            groups[key] = groups.get(key, 0) | (1 << index)
    return tuple(sorted(groups.values()))


def block_capacity(l, c, kind):
    occupied = [(z, w) for z, w in POSITIVE if l < z <= c]
    if kind == 'F':
        return len({z for z, w in occupied})
    return (len({z for z, w in occupied if w > c})
            + len({w for z, w in occupied if w <= c}))


def tight_partitions():
    """Forward enumeration; equal partitions retain one lexicographic path."""
    prefix = [0]
    families = [{(): ()}]
    for c in range(1, 16):
        edges = [(l, kind, block_capacity(l, c, kind))
                 for l in range(c) for kind in ('F', 'R')]
        optimum = max(prefix[l] + weight for l, kind, weight in edges)
        prefix.append(optimum)
        family = {}
        for l, kind, weight in edges:
            if prefix[l] + weight != optimum:
                continue
            block = slots(l, c, kind)
            for partition, path in families[l].items():
                joined = tuple(sorted(partition + block))
                candidate = path + ((l, c, kind),)
                if joined not in family or candidate < family[joined]:
                    family[joined] = candidate
        families.append(family)
    require(prefix == EXPECTED_PREFIX, 'prefix recurrence differs')
    partitions = sorted(families[15])
    require(len(partitions) == 41, 'tight partition count differs')
    positive_mask = sum(1 << i for i, p in enumerate(POINTS) if p in POSITIVE)
    for partition in partitions:
        union = 0
        for slot in partition:
            require(slot > 0 and not slot & union, 'partition overlaps/has an empty slot')
            union |= slot
        require(union == (1 << 42) - 1, 'partition is not full')
        require(sum(bool(slot & positive_mask) for slot in partition) == 10,
                'tight positive slot count differs')
    return (prefix, [len(f) for f in families], partitions,
            [families[15][p] for p in partitions])


def slot_map(partition):
    return [next(j for j, mask in enumerate(partition) if mask & (1 << i))
            for i in range(42)]


def graph(partitions, maps, triple):
    offsets = [0, len(partitions[triple[0]])]
    offsets.append(offsets[1] + len(partitions[triple[1]]))
    return [[offsets[j] + maps[p][i] for j, p in enumerate(triple)]
            for i in range(42)], sum(len(partitions[p]) for p in triple)


def maximum_matching(edges, slot_count):
    """Breadth-first alternating paths, independent of the prior DFS code."""
    row_slot = [-1] * 42
    slot_row = [-1] * slot_count
    for root in range(42):
        queue = deque([root])
        parent = {}
        rows = {root}
        free = None
        while queue and free is None:
            row = queue.popleft()
            for slot in edges[row]:
                if slot in parent:
                    continue
                parent[slot] = row
                owner = slot_row[slot]
                if owner == -1:
                    free = slot
                    break
                if owner not in rows:
                    rows.add(owner)
                    queue.append(owner)
        while free is not None and free != -1:
            row = parent[free]
            previous = row_slot[row]
            row_slot[row] = free
            slot_row[free] = row
            free = previous
    unmatched = {i for i, slot in enumerate(row_slot) if slot == -1}
    reached = set(unmatched)
    queue = deque(unmatched)
    neighbors = set()
    while queue:
        for slot in edges[queue.popleft()]:
            neighbors.add(slot)
            owner = slot_row[slot]
            require(owner != -1, 'augmenting path remains')
            if owner not in reached:
                reached.add(owner)
                queue.append(owner)
    cardinality = sum(slot != -1 for slot in row_slot)
    require(len(reached) - len(neighbors) == 42 - cardinality,
            'Hall deficiency does not match cardinality')
    require(len(set(slot for slot in row_slot if slot != -1)) == cardinality,
            'matching repeats a slot')
    require(all(slot == -1 or slot in edges[row] for row, slot in enumerate(row_slot)),
            'matching assigns a nonincident slot')
    return cardinality, sum(1 << i for i in reached), len(neighbors), row_slot


def check_hall(edges, mask, expected_neighbors=None):
    require(type(mask) is int and 0 < mask < (1 << 42), 'invalid Hall mask')
    neighbors = {slot for i in range(42) if mask & (1 << i) for slot in edges[i]}
    require(bin(mask).count('1') > len(neighbors), 'Hall inequality fails')
    if expected_neighbors is not None:
        require(len(neighbors) == expected_neighbors, 'Hall neighbor count differs')


def check_prior(path, prefix, partitions):
    prior = json.loads(path.read_text())
    require(prior['points'] == [list(p) for p in POINTS], 'prior target order differs')
    require(prior['positive_points'] == [list(p) for p in sorted(POSITIVE)],
            'prior positive targets differ')
    require(prior['prefix_capacity'] == prefix, 'prior prefix differs')
    old_partitions = [tuple(sorted(sum(1 << i for i in group) for group in p))
                      for p in prior['partitions']]
    require(len(old_partitions) == 41 and set(old_partitions) == set(partitions),
            'prior tight partitions differ from forward recomputation')
    for partition, plan in zip(old_partitions, prior['plans']):
        combined = []
        previous = 0
        for l, c, kind in plan:
            require(l >= previous and kind in ('F', 'R'), 'prior path invalid')
            require(not slots(previous, l, 'F'), 'prior omitted occupied interval')
            require(prefix[l] + block_capacity(l, c, kind) == prefix[c],
                    'prior path is not tight')
            combined.extend(slots(l, c, kind))
            previous = c
        require(previous == 15 and tuple(sorted(combined)) == partition,
                'prior path does not induce its partition')
    maps = [slot_map(p) for p in old_partitions]
    triples = list(combinations_with_replacement(range(41), 3))
    keys = {','.join(map(str, t)) for t in triples}
    require(set(prior['hall_witnesses']) == keys, 'prior Hall cases incomplete')
    for triple in triples:
        edges, _ = graph(old_partitions, maps, triple)
        indices = prior['hall_witnesses'][','.join(map(str, triple))]
        require(len(indices) == len(set(indices)) and all(0 <= i < 42 for i in indices),
                'prior Hall target indices invalid')
        check_hall(edges, sum(1 << i for i in indices))


def multiply(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)


IDENTITY = (Fraction(1), Fraction(0), Fraction(0), Fraction(1))
A = (Fraction(1), Fraction(0), Fraction(0), Fraction(-1))
B = (Fraction(1, 2), Fraction(1), Fraction(-5, 4), Fraction(-1, 2))


def leaf_product(word):
    value = IDENTITY
    for letter in word:
        value = multiply(value, A if letter == 'a' else B)
    return value


def rho(word):
    return ''.join('b' if letter == 'a' else 'ba' for letter in word)


def target(z, w):
    if w > 15:
        return (0, 1, 4 * z)
    composition = (4 * (2 * z - w), 4 * (w - z))
    if z + w <= 15:
        return (2, (((0, 0, 0),) * 3, composition))
    return (1, composition, 1, 1)


def upper_evidence():
    require(multiply(A, A) == IDENTITY, 'A relation fails')
    require(multiply(B, B) == tuple(-x for x in IDENTITY), 'B relation fails')
    require(tuple(x + y for x, y in zip(multiply(A, B), multiply(B, A)))
            == IDENTITY, 'Clifford anticommutator fails')
    # Independence of 1,A,B,AB makes this four-dimensional representation
    # faithful, so a matrix identity is an identity in the source algebra.
    basis = [list(column) for column in zip(IDENTITY, A, B, multiply(A, B))]
    for i in range(4):
        pivot = next((j for j in range(i, 4) if basis[j][i]), None)
        require(pivot is not None, 'Clifford representation is not faithful')
        basis[i], basis[pivot] = basis[pivot], basis[i]
        divisor = basis[i][i]
        basis[i] = [x / divisor for x in basis[i]]
        for j in range(i + 1, 4):
            factor = basis[j][i]
            basis[j] = [x - factor * y for x, y in zip(basis[j], basis[i])]
    branches = Counter()
    calls = Counter()
    targets = set()
    for r in range(1, 15):
        for s in range(1, 16 - r):
            z, w = r + s, r + 2 * s
            word = 'a' * (2 * r - 1) + 'b' * (2 * s) + 'a'
            word += 'b' * (2 * s - 1) + 'a' * (2 * r) + 'b'
            require((word.count('a'), word.count('b')) == (4 * r, 4 * s),
                    'actual word composition fails')
            current = word
            for _ in range(3):
                require(leaf_product(current) == IDENTITY, 'actual unit word fails')
                current = rho(current)
            initial = target(z, w)
            targets.add(initial)
            if w > 15:
                label = 1
            elif z <= 8:
                label = 1 + ((z - 1) % 4)
            else:
                x, y = z - 8, w - 8
                label = (x + 1) // 2 if x % 2 == y % 2 else (y + 1) // 2
            require(1 <= label <= 4, 'upper label out of range')
            cutoff = 6 + 2 * label
            for delta in range(4):
                cap = 60 + delta
                material = cap - 4 * cutoff
                current = word
                accepted_context = len(current) + material <= cap
                if accepted_context:
                    current += 'a' * material
                candidate = rho(current)
                accepted_rho = len(candidate) <= cap
                if accepted_rho:
                    current = candidate
                entry = len(current)
                branch = ('A' if accepted_context else 'R')
                branch += 'A' if accepted_rho else 'R'
                if branch == 'AA':
                    ww = (entry - material) // 4
                    zz = label if ww <= 2 * label - 1 else 4 + label
                    output = target(zz, ww)
                elif branch == 'AR':
                    zz = (entry - material) // 4
                    ww = cutoff + 1 if zz <= 8 else cutoff + 1 + zz % 2
                    output = target(zz, ww)
                elif branch == 'RA':
                    ww = entry // 4
                    zz = cutoff + 1 if ww % 2 or ww == cutoff + 2 else cutoff + 2
                    output = target(zz, ww)
                else:
                    output = (0, 1, entry)
                require(output == initial, 'TM58 literal initial output fails')
                l, u, accepted_material, whole = 0, cap, 0, 2
                while u - l > 1:
                    k = (l + u) // 2
                    context = 'a' * (u - k)
                    whole += 1
                    if len(current) + len(context) <= cap:
                        current += context
                        accepted_material += len(context)
                        u = k
                    else:
                        l = k
                whole += 1
                require(len(current) == cap and len(current + 'a') > cap,
                        'terminal saturation/refusal fails')
                require(cap - accepted_material == entry == u,
                        'Size_H did not acquire actual entry')
                require(whole <= 9, 'simultaneous call bound fails')
                branches[branch] += 1
                calls[whole] += 1
    require(len(targets) == 56 and sum(branches.values()) == 420,
            'complete upper composition/target count differs')
    return {'compositions': 105, 'cap_residues': 4, 'executions': 420,
            'initial_targets': 56, 'unit_matrix_products': 315,
            'branches': dict(sorted(branches.items())),
            'whole_call_histogram': dict(sorted(calls.items())),
            'read_calls': 0, 'accepted_rho_bound': 1, 'whole_call_bound': 9}


def recompute():
    require(len(POINTS) == 42 and len(POSITIVE) == 30 and POSITIVE <= set(POINTS),
            'target/weight support differs')
    prefix, counts, partitions, paths = tight_partitions()
    maps = [slot_map(p) for p in partitions]
    histogram = Counter()
    witnesses = []
    largest = None
    for triple in combinations_with_replacement(range(41), 3):
        edges, slot_count = graph(partitions, maps, triple)
        m, mask, neighbors, matching = maximum_matching(edges, slot_count)
        require(m < 42, 'three tight paths cover every target')
        check_hall(edges, mask, neighbors)
        witnesses.append([m, mask, neighbors])
        histogram[m] += 1
        if largest is None or m > largest['cardinality']:
            largest = {'triple': triple, 'cardinality': m, 'row_to_slot': matching}
    require(dict(histogram) == EXPECTED_HISTOGRAM, 'matching histogram differs')
    require(len(witnesses) == 12341, 'triple count differs')
    result = {'schema': 'fib-h15-joint-cover-v1', 'points': POINTS,
              'positive_points': sorted(POSITIVE), 'prefix_capacity': prefix,
              'prefix_partition_counts': counts, 'partitions': partitions,
              'paths': paths, 'triple_order': 'lexicographic combinations with repetition',
              'hall_rows': witnesses, 'coverage_histogram': dict(sorted(histogram.items())),
              'maximum_matching': largest, 'upper': upper_evidence()}
    return result, prefix, partitions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=Path(__file__).with_name('h15_joint_cover.json'))
    parser.add_argument('--write', action='store_true', help='write regenerated finite data')
    parser.add_argument('--prior', type=Path, help='also check discovery certificate')
    args = parser.parse_args()
    result, prefix, partitions = recompute()
    if args.prior:
        check_prior(args.prior, prefix, partitions)
    canonical = json.dumps(result, separators=(',', ':'), sort_keys=True) + '\n'
    if args.write:
        args.certificate.write_text(canonical)
    else:
        require(args.certificate.read_text() == canonical, 'retained certificate differs')
    print(json.dumps({'tight_partitions': len(partitions), 'triples': len(result['hall_rows']),
                      'maximum_covered': result['maximum_matching']['cardinality'],
                      'prefix_partition_counts': result['prefix_partition_counts'],
                      'upper': result['upper'], 'prior_checked': bool(args.prior)}, sort_keys=True))


if __name__ == '__main__':
    main()
