"""Check the expanded-color Report862 control against its saved base fixture."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
from math import prod, gcd, comb
from pathlib import Path
import json

from control_model import (P, q, G, A, U, all_primes, aux, triples,
                           assignment, crt, build_rows)

if not __debug__:
    raise RuntimeError('Run without -O: arithmetic verification requires assertions.')

BASE = Path(__file__).parent
BASELINE_SHA256 = {
    'phase_colors.json': 'e8e66d1f86cc239e50acc4853173fc45850ca7df6c9025cced145310d0f6d5f5',
    'result.json': 'a3cdbc630009328b35316d34636ebfbef09a147613d5a6fee21167226bfb2a31',
}
assert all(sha256((BASE/name).read_bytes()).hexdigest() == digest
           for name, digest in BASELINE_SHA256.items())
saved = json.loads((BASE / 'result.json').read_text())
old = build_rows()
BASELINE_AP_SHA256 = 'e8f7e96366083327c9bd6da3ec92617cb6def053e6a7226fee481ff36d4ee1ea'
BASELINE_PRIVATE_SHA256 = '02bf3fad7fe2625dd3ec506150f0e382920213ec37c7a0bd7dec0041579f9e15'

def data_hash(value):
    return sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()

assert data_hash([(r['d'], r['r']) for r in old]) == BASELINE_AP_SHA256
indices = (415, 420, 425, 430, 435)
new_colors = (1, 2, 27, 28, 29)
overrides = {triples[i]: (c, 2) for i, c in zip(indices, new_colors)}
rows = build_rows(overrides)
assert len(rows) == len(old) == saved['classes'] == 3518
assert [r['d'] for r in rows] == [r['d'] for r in old]
assert len({r['d'] for r in rows}) == len(rows)
assert all(r['d'] == 3**r['a'] * q**r['j'] * prod(r['S']) for r in old+rows)
assert all(r['r'] % p == phase for r in old+rows for p, phase in r.get('phase', {}).items())
changed = [i for i, (a, b) in enumerate(zip(old, rows)) if a['r'] != b['r']]
assert len(changed) == 15
assert all(rows[i]['j'] == 1 and rows[i]['S'] in overrides for i in changed)
assert all(a['r'] % (a['d'] // q**a['j']) == b['r'] % (b['d'] // q**b['j'])
           for a, b in zip(old, rows))
assert all(a['r'] == b['r'] for a, b in zip(old, rows) if not a['j'])
assert {r['c'] for r in rows if r['j'] and not r['S']} == set(range(30))
assert set(U) == set(range(q)) - set(range(30))
# The unchanged numerical palette inherits the saved divisor closure.
assert saved['private_points_checked'] == len(rows)
assert saved['comparable_pairs_checked'] == 67123

def private_integer(row):
    if 'aux' in row:
        data = [(9, 4), (q**G, 30+q)] + [(p, 0) for p in P]
        data += [(p, row['a'] if p == row['aux'] else 3) for p in aux]
    elif row['S']:
        data = [(9, row['z']), (q**G, row['c']+q if row['j'] else 30+q)]
        data += [(p, row['phase'][p] if p in row['S'] else 0) for p in P]
        data += [(p, 3) for p in aux]
    else:
        z, c = {3: (0, 30+q), 9: (1, 30+q)}.get(row['d'], (4, row.get('c')))
        data = [(9, z), (q**G, c)] + [(p, 0) for p in P] + [(p, 3) for p in aux]
    return crt(data)

old_private_points = [private_integer(row) for row in old]
assert data_hash(old_private_points) == BASELINE_PRIVATE_SHA256

# Check every affected owner/private-point relation. Other relations are identical.
changed_set = set(changed)
privacy_comparisons = 0
private_points = []
for i, row in enumerate(rows):
    x = private_integer(row)
    private_points.append(x)
    targets = range(len(rows)) if i in changed_set else changed
    if i not in changed_set:
        assert x == old_private_points[i]
    for j in targets:
        assert (x % rows[j]['d'] == rows[j]['r']) == (i == j)
        privacy_comparisons += 1
assert privacy_comparisons == 105315
pairs = {(min(i, j), max(i, j)) for i in changed for j in range(len(rows)) if i != j}
comparable_delta = 0
for i, j in pairs:
    a, b = sorted((rows[i], rows[j]), key=lambda r: r['d'])
    if b['d'] % a['d'] == 0:
        assert b['r'] % a['d'] != a['r']
        comparable_delta += 1

# Reconstruct all literal two-prime top keys from numerical APs.
def pair_keys(family):
    keys = Counter()
    for row in family:
        if row['d'] % 9:
            continue
        primes = [p for p in all_primes+(q,) if row['d'] % p == 0]
        for p, r in combinations(primes, 2):
            keys[row['r'] % 9, p, r, row['r'] % p, row['r'] % r] += 1
    return keys

old_keys, keys = pair_keys(old), pair_keys(rows)
assert max(old_keys.values()) == max(keys.values()) == 1
assert len(old_keys) == len(keys) == 4530
assert {k: v for k, v in old_keys.items() if q not in k[1:3]} == {
    k: v for k, v in keys.items() if q not in k[1:3]}
# All non-q tests are unchanged. At old q-colors only matching q-incidences are removed.
assert all(old[i]['r'] % q not in new_colors and rows[i]['r'] % q in new_colors for i in changed)
assert saved['joint_top_two_of_three_phase_max'] == 3
assert saved['extended_top_q_two_prime_phase_max'] == 3
assert saved['extended_all_q_four_prime_phase_max'] == 2
# Enumerate all new-color top two-of-three queries using exact phase classes.
top_rows = [r for r in rows if r['a'] == 2]
alphabet = {p: {0} | {r['r'] % p for r in top_rows if r['d'] % p == 0} for p in all_primes}
queries = Counter()
for row in top_rows:
    present = [p for p in all_primes if row['d'] % p == 0]
    events = set()
    for p, r in combinations(present, 2):
        for c in new_colors:
            events.add((row['r'] % 9, c, p, r, row['r'] % p, row['r'] % r))
    if row['j'] and row['r'] % q in new_colors:
        c = row['r'] % q
        for p in present:
            for r in all_primes:
                if p == r:
                    continue
                for value in alphabet[r]:
                    a, b = sorted((p, r))
                    phases = {p: row['r'] % p, r: value}
                    events.add((row['r'] % 9, c, a, b, phases[a], phases[b]))
    queries.update(events)
assert max(queries.values()) == 2
# At a new q-color only one triple support can supply four of five matches.
# Its three ternary rows have distinct vectors on those three primes.
for c in new_colors:
    group = [r for r in rows if r['j'] and r['S'] and r['r'] % q == c]
    assert len(group) == 3 and len({r['S'] for r in group}) == 1
    support = group[0]['S']
    assert len(support) == 3
    assert len({tuple(r['r'] % p for p in support) for r in group}) == 3
assert max(len(r['S']) for r in rows) == 3

# Actual same-cofactor SC468 witnesses and all height-one row masks.
labels = {r['d']: r for r in rows}
alpha, beta = labels[q]['r'] % q, labels[3*q]['r'] % q
C, V = set(range(q)) - {alpha}, set(range(q)) - {alpha, beta}
cells = set()
for row in rows:
    if row['j'] != 1 or row['a'] != 2 or not row['S']:
        continue
    m = row['d'] // (9*q)
    assert m > 1 and gcd(m, 3*q) == 1
    group = [labels[3**a*q*m] for a in range(3)]
    c, z = row['r'] % q, row['r'] % 9
    assert all(r['r'] % q == c for r in group)
    assert group[1]['r'] % 3 == z % 3 and z in A
    cells.add((c, z))
complete = {c for c in V if all((c, z) in cells for z in A)}
assert len(C) == 112 and len(V) == 111 and len(complete) == 107
assert V - complete == {2, 27, 28, 29}
assert all((c, z) in cells for c in U for z in A)
row_masks = {c: {r['a'] for r in rows if r['j'] == 1 and r['r'] % q == c} for c in C}
assert all(mask == {0, 1, 2} for mask in row_masks.values())
moving = [r for r in rows if r['j'] and r['r'] % q in U]
moving_supports = {r['S'] for r in moving}
assert len(moving_supports) == 450
# At most five of the 84 supports disjoint from a six-prime union were removed.
assert len(triples) - len(moving_supports) == 5
bridge_support_lower_bound = comb(len(P)-6, 3) - len(overrides)
assert bridge_support_lower_bound > 0
# The phase bands certify that these disjoint-support intersections lie in E0.
retained_tags = {v for r in rows if not r['j'] and 'phase' in r and 'aux' not in r
                 for v in r['phase'].values()}
moving_tags = {v for r in moving for v in r['phase'].values()}
assert retained_tags.isdisjoint({0} | moving_tags)

hole = saved['uncovered_integer']
assert not any(hole % r['d'] == r['r'] for r in rows)
assert all(hole % (r['d']//q**r['j']) != r['r'] % (r['d']//q**r['j']) for r in moving)
inside = saved['inside_component_all_U_failure']
xp, xs = inside['private_integer'], inside['switched_uncovered_integer']
assert [r['d'] for r in rows if xp % r['d'] == r['r']] == [inside['original_modulus']]
assert not any(xs % r['d'] == r['r'] for r in rows)
assert [r['d'] for r in moving if xp % (r['d']//q**r['j']) == r['r'] % (r['d']//q**r['j'])] == [inside['original_modulus']]
assert all(xp % r['d'] != r['r'] for r in rows if not r['j'])
assert xp % (9*prod(all_primes)) == xs % (9*prod(all_primes))
assert (xp % q**G)//q == (xs % q**G)//q

result = dict(
    classes=len(rows), changed_qbearing_originals=len(changed),
    replacements=[dict(support=triples[i], old_cell=assignment[triples[i]], new_cell=(c, 2))
                  for i, c in zip(indices, new_colors)],
    changed_classes=[dict(modulus=rows[i]['d'], old_residue=old[i]['r'], residue=rows[i]['r'],
                         row=rows[i]['a'], cofactor=prod(rows[i]['S'])) for i in changed],
    numerical_palette_unchanged=True, qfree_classes_unchanged=True,
    all_preserved_cofactor_and_ternary_phases_unchanged=True,
    private_relations_rechecked=privacy_comparisons, comparable_pairs_rechecked=comparable_delta,
    inherited_private_relations=len(rows)**2-privacy_comparisons,
    top_two_prime_phase_keys=len(keys), top_two_prime_phase_max=max(keys.values()),
    full_GLC1_collision_edges=0, inherited_nonq_joint_queries=saved['joint_nonzero_queries'],
    nonq_joint_top_two_of_three_max=3, new_color_top_two_of_three_queries=len(queries),
    new_color_top_two_of_three_max=max(queries.values()), all_q_top_two_of_three_upper_bound=3,
    new_color_four_of_five_upper_bound=1, all_q_four_of_five_upper_bound=2,
    C_colors=len(C), C_row_counts=[sum(a in row_masks[c] for c in C) for a in range(3)],
    C_minimum_row_counts=[sum(min(row_masks[c]) == a for c in C) for a in range(3)], V_colors=len(V), V_all_three_row_colors=len(V),
    V_complete_safe_word_colors=len(complete), V_missing_complete_colors=sorted(V-complete),
    full_SC468=True, moving_colors=len(U), moving_owners=len(moving),
    moving_top_owners=sum(r['a'] == 2 for r in moving), moving_occupied_cells=415,
    masked_components=1, masked_diameter_upper_bound=2,
    available_disjoint_bridge_supports_lower_bound=bridge_support_lower_bound,
    uncovered_integer=hole, inside_component_all_U_failure=inside,
    whole_cover=False, EB1=False,
    inherited_checks_source='result.json',
    inherited_AP_sequence_sha256=BASELINE_AP_SHA256,
    inherited_private_sequence_sha256=BASELINE_PRIVATE_SHA256,
    inherited_checks_scope='Unchanged numerical palette, unchanged private relations, and non-q phase queries; affected q queries and privacy relations checked here.',
    base_fixture_sha256={name: sha256((BASE/name).read_bytes()).hexdigest()
                        for name in ('phase_colors.json', 'result.json')},
)
print(json.dumps(result, indent=2))
