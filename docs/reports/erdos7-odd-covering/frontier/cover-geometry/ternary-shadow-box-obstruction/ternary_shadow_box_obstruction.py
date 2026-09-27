#!/usr/bin/env python3
"""Refute noncoverage from ternary shadow constraints alone (report 377).

The 11-box cover has distinct downward-closed supports, disjoint comparable
boxes and private witnesses. Reusing the literal residues at distinct odd
primes leaves a nonempty actual residual with one strong common marginal law.
Exact finite controls use no solver, imports from the repository, or asserts.
This is not an odd distinct covering system or a Lean verification.
"""
from itertools import combinations, product
from collections import Counter
from fractions import Fraction
import json
from math import prod


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


names = 'abcde'
# A Boolean variable is false at 1, true at 2. Each pair gives a clause's unique falsification.
pairs = [('ab', (2, 1)), ('bc', (2, 1)), ('ac', (2, 2)),
         ('ad', (1, 1)), ('de', (2, 1)), ('ae', (1, 2))]
boxes = [(c, {c: 0}) for c in names]
boxes += [(label, dict(zip(label, values))) for label, values in pairs]
points = list(product(range(3), repeat=5))

def hit(point, box):
    return all(point[names.index(c)] == value for c, value in box.items())

members = {label: {p for p in points if hit(p, box)} for label, box in boxes}
scopes = {label: frozenset(box) for label, box in boxes}
require(len(set(scopes.values())) == len(boxes) == 11, 'distinct nonempty scopes')
incidence = {p: [label for label, box in boxes if hit(p, box)] for p in points}
require(all(incidence.values()), 'whole ternary cover')
comparable_pairs = [(a, b) for a, b in combinations(scopes, 2)
                    if scopes[a] <= scopes[b] or scopes[b] <= scopes[a]]
require(all(not members[a].intersection(members[b]) for a, b in comparable_pairs), 'comparable disjointness')
private = {label: [p for p in members[label] if incidence[p] == [label]] for label, box in boxes}
require(all(private.values()), 'all boxes have private points')
# This is the relevant divisor-closure condition: every nonempty subscope of each ACTUAL label exists.
require(all(frozenset(sub) in scopes.values() for scope in scopes.values()
            for size in range(1, len(scope)+1) for sub in combinations(scope, size)),
        'nonempty divisor/downward closure')

# A schedule has only one singleton and at most one edge compatible with its initial prefixes.
schedule_rows = []
from itertools import permutations
for schedule in permutations(names):
    prefix_scopes = {frozenset(schedule[:k]) for k in range(1, 6)}
    on_labels = [label for label in scopes if scopes[label] in prefix_scopes]
    covered = set().union(*(members[label] for label in on_labels))
    require(len(covered) in (81, 108), 'on-schedule mass')
    require(len(covered) < len(points), 'every schedule misses')
    schedule_rows.append(len(covered))

# Boolean clause minimal unsatisfiability: deleting one of six yields at least one satisfying assignment.
boolean = list(product((1, 2), repeat=5))
clause_deletion_survivors = {label: sum(all(not hit(p, box) for other, box in boxes[5:] if other != label) for p in boolean)
                           for label, box in boxes[5:]}
require(all(clause_deletion_survivors.values()), 'clause-wise minimal unsatisfiability')

# The same literal boxes on distinct prime coordinates are genuine odd APs.
# Enumerate their full integer period independently of the ternary cube.
primes = (5, 7, 11, 13, 17)
prime_for = dict(zip(names, primes))

def crt_box(box):
    modulus = prod(prime_for[c] for c in box)
    value = 0
    for c, residue in box.items():
        p = prime_for[c]
        other = modulus // p
        value += residue * other * pow(other, -1, p)
    return value % modulus, modulus

aps = [(label, *crt_box(box)) for label, box in boxes]
Q = prod(primes)
require(len({modulus for _, _, modulus in aps}) == 11, 'original moduli distinct')
require(all(modulus > 1 and modulus % 2 for _, _, modulus in aps), 'odd nonunit moduli')
for label, residue, modulus in aps:
    actual_divisors = {d for d in range(2, modulus+1) if modulus % d == 0}
    require(actual_divisors <= {d for _, _, d in aps}, 'actual divisor closure')
residual = []
actual_private = {label: [] for label, _, _ in aps}
shadow_images = set()
for n in range(Q):
    coordinates = tuple(n % p for p in primes)
    hits = [label for label, residue, modulus in aps if n % modulus == residue]
    require(hits == [label for label, box in boxes if hit(coordinates, box)], 'CRT event vector')
    if not hits:
        residual.append(n)
    elif len(hits) == 1:
        actual_private[hits[0]].append(n)
    if all(x < 3 for x in coordinates):
        require(bool(hits), 'ternary selected product is not covered')
        shadow_images.add(coordinates)
require(shadow_images == set(points), 'full selected ternary product')
require(len(residual) == 40618 and 3 in residual, 'actual residual')
require(all(actual_private.values()), 'actual private witnesses')
maximum_counts = []
for p in primes:
    counts = Counter(n % p for n in residual)
    maximum_counts.append(max(counts.values()))
    require(max(counts.values())*(p-2) <= len(residual), 'common strong marginal cap')
require(maximum_counts == [11269, 7179, 4231, 3477, 2593], 'actual maximum counts')
actual = dict(primes=primes, original_aps=aps, full_period=Q,
              uncovered_count=len(residual), explicit_uncovered_integer=3,
              private_counts={label: len(pts) for label, pts in actual_private.items()},
              one_private_integer={label: pts[0] for label, pts in actual_private.items()},
              maximum_coordinate_counts=maximum_counts,
              uniform_residual_caps=[str(Fraction(c, len(residual))) for c in maximum_counts],
              target_caps=[str(Fraction(1, p-2)) for p in primes],
              covered_selected_product_size=len(shadow_images),
              scope='Actual distinct odd irredundant divisor-closed AP family, but not a whole cover')

result = {
    'coordinates': names, 'height_vector': [1]*5, 'carrier_size': len(points), 'box_count': len(boxes),
    'boxes': [{'scope': label, 'values': box} for label, box in boxes],
    'whole_cover': True, 'distinct_scopes': True,
    'comparable_pair_count': len(comparable_pairs), 'comparable_disjoint': True,
    'private_point_counts': {label: len(pts) for label, pts in private.items()},
    'one_private_witness_each': {label: sorted(pts)[0] for label, pts in private.items()},
    'nonempty_scope_downward_closed': True,
    'multiplicity_histogram': dict(sorted(Counter(map(len, incidence.values())).items())),
    'total_box_mass': str(sum(Fraction(len(pts), len(points)) for pts in members.values())),
    'schedule_count': len(schedule_rows),
    'schedule_covered_points_histogram': dict(sorted(Counter(schedule_rows).items())),
    'clause_deletion_survivor_counts': clause_deletion_survivors,
    'actual_prime_family': actual,
    'scope': 'Exact ternary shadow relation; not a cover by distinct original odd prime moduli, not an Erdos 7 counterexample.'
}
print(json.dumps(result, indent=2))
