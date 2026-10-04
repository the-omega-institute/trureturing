"""Check report 388 Section 38: two complete sources of an actual noncover.

The printed finite certificate does not assert a whole cover or test the
symbolic fresh-prime extension. Run with Python 3 using only its standard library.
"""

import itertools
import json
import math

p, B = 7, 3
period, source_period = 9 * 125 * p, 27 * p


def crt(conditions):
    conditions = [(a % n, n) for a, n in conditions if n > 1]
    total = math.prod(n for _, n in conditions)
    return sum(a * (total // n) * pow(total // n, -1, n) for a, n in conditions) % total


def theta(z, depth):
    value = 0
    for b in range(depth):
        value += ((z // 3**b) % 3) * 5**b
    return value


original = {3: 1, 9: 0}
metadata = {}
for b in range(1, B + 1):
    original[5**b] = theta(3**(b - 1), b)
    original[3 * 5**b] = crt([(0, 3), (theta(2 * 3**(b - 1), b), 5**b)])
    original[9 * 5**b] = crt([(2, 9), (5 - b, 5**b)])

lower_p_phases = [[0, 2, 3, 4], [1, 3, 4, 5]]
for a, b in itertools.product(range(3), range(B + 1)):
    if a < 2:
        phase_p, old_three = lower_p_phases[a][b], 0
    else:
        phase_p = [2, 3, 6, 6][b]
        old_three = [5, 5, 3, 6][b]
    d = 3**a * 5**b * p
    original[d] = crt([(old_three, 3**a), (0, 5**b), (phase_p, p)])
    metadata[d] = (a, b)

labels = sorted(original)
assert len(labels) == 23
assert labels == [d for d in range(2, period + 1) if period % d == 0]
for d, e in itertools.combinations(labels, 2):
    if e % d == 0:
        assert original[d] != original[e] % d, (d, e)

points = {u: [crt([(u, 9), (theta(z, B), 125), (z, p)]) for z in range(source_period)] for u in (3, 6)}
pullback = {u: {d: {z for z, x in enumerate(points[u]) if x % d == alpha}
               for d, alpha in original.items()} for u in (3, 6)}
lower = [d for d in labels if d % 9]
lower_union = set().union(*(pullback[3][d] for d in lower))
assert lower_union == set().union(*(pullback[6][d] for d in lower))
liability = set(range(source_period)) - lower_union
assert len(liability) == 1
assert liability == {z for z in range(source_period) if z % 27 == 0 and z % 7 == 6}
for u in (3, 6):
    assert set().union(*pullback[u].values()) == set(range(source_period))

all_sources = {d: pullback[3][d] | pullback[6][d] for d in original}
private_sources = {d: all_sources[d] - set().union(*(all_sources[e] for e in labels if e != d))
                   for d in labels}
assert private_sources[7] == {0}
assert private_sources[21] == {162}

surviving_lower = [d for d in lower if all_sources[d]]
slots = {}
for d in surviving_lower:
    a, k = 0, d
    while k % 3 == 0:
        k //= 3
        a += 1
    b, h = 0, k
    while h % 5 == 0:
        h //= 5
        b += 1
    slots.setdefault(3**b * h, []).append(d)
assert len(slots) == 7 and all(len(v) == 2 for v in slots.values())

required_low_menu = 0
required_flat = 0
cases = 0
top_sources = [d for d in labels if d % 9 == 0 and all_sources[d]]
for reps in itertools.product(*(slots[n] for n in sorted(slots) if n != 3)):
    occupied_slots = set(slots) - {3}
    assert all((3**metadata[d][1] * p) in occupied_slots for d in top_sources)
    for root in range(3):
        retained_union = set().union(*(all_sources[d] for d in reps))
        retained_union |= {z for z in range(source_period) if z % 3 == root}
        hole = set(range(source_period)) - retained_union
        assert hole <= set().union(*(all_sources[d] for d in labels if d not in reps))
        witnesses = [(d, min(private_sources[d] & hole)) for d in (5, 15) if private_sources[d] & hole]
        assert witnesses
        required_low_menu += 1
        flat_witnesses = [(d, min(private_sources[d] & hole)) for d in (7, 21) if d not in reps and private_sources[d] & hole]
        if root in (1, 2):
            assert flat_witnesses
            required_flat += 1
        else:
            assert not flat_witnesses
        cases += 1

uncovered = [x for x in range(period) if not any(x % d == alpha for d, alpha in original.items())]
original_private_residues = {d: [x for x in range(original[d], period, d)
                                if all(x % e != original[e] for e in labels if e != d)] for d in labels}
original_private_counts = {d: len(values) for d, values in original_private_residues.items()}
assert all(original_private_counts.values())
outside_witness = crt([(8, 9), (0, 125), (6, 7)])
assert outside_witness in uncovered
result = {
    "scope": "Actual divisor-closed comparable-disjoint NONCOVER, with both fixed safe sources completely covered and nonempty shared top liability",
    "A": 2, "B": 3, "p": p,
    "period": period, "original_count": len(labels),
    "original_classes": original,
    "original_uncovered_count": len(uncovered),
    "outside_selected_ternary_root_witness": outside_witness,
    "outside_witness_mod_9": outside_witness % 9,
    "original_private_counts": original_private_counts,
    "original_private_witnesses": {d: min(values) for d, values in original_private_residues.items()},
    "source_period": source_period,
    "source_covered_counts": {u: len(set().union(*pullback[u].values())) for u in (3, 6)},
    "shared_top_liability": sorted(liability),
    "actual_tops": {u: {d: sorted(pullback[u][d]) for d in top_sources if pullback[u][d]} for u in (3, 6)},
    "flat_lower_private_traces": {d: sorted(private_sources[d]) for d in (7, 21)},
    "all_lower_rep_root_cases": cases,
    "cases_with_unavoidable_singleton_menu_3_source": required_low_menu,
    "cases_with_unavoidable_flat_prime_lower_trace": required_flat,
    "N3": sum(d % 3 == 0 for d in labels), "n0": sum(d % 3 != 0 for d in labels), "z": 0,
}
print(json.dumps(result, indent=2))
