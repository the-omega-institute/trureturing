#!/usr/bin/env python3
"""Bounded AP control for SecondDigitInsertion.Condition.

This family is not a cover and has no EB1 or divisor-closure certificate.
The control separates top-free fixed tags across three old ternary words
from independent per-word tags and from low payers overlapping top classes.
All arithmetic uses exact integers. A supplied 113-entry tag vector is
converted into a concrete failing target; no tag-space or W-space search
is used.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("This verifier requires assertions; do not run Python with -O.")

import argparse
from dataclasses import dataclass
from itertools import combinations
import json
from math import gcd, isqrt, prod
from pathlib import Path

Q = 113
VERTEX_PRIMES = (17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79)
SUPPORT = (5, 7) + VERTEX_PRIMES
EDGES = tuple(combinations(range(16), 2))[:Q]
DEGREES = tuple(sum(v in edge for edge in EDGES) for v in range(16))
INCIDENCE = {
    (v, root): k
    for v in range(16)
    for k, root in enumerate((r for r, edge in enumerate(EDGES) if v in edge), 1)
}
MIDDLE_PAIRS = tuple((a, b) for a in range(11) for b in range(11) if a or b)[:Q]
W = prod(p**10 for p in SUPPORT)


def crt(equations):
    value, modulus = 0, 1
    for m, a in equations:
        assert m > 0 and gcd(modulus, m) == 1
        value += modulus * (((a - value) * pow(modulus, -1, m)) % m)
        modulus *= m
        value %= modulus
    return value


@dataclass(frozen=True)
class AP:
    kind: str
    row: int
    height: int
    cofactor: int
    modulus: int
    residue: int
    root: int = -1
    vertex: int = -1
    word: int = -1
    phase: int = -1
    exponent: int = 0

    def contains(self, x):
        return (x - self.residue) % self.modulus == 0

    def active(self, x, root):
        return (
            (x - self.residue) % (3**self.row) == 0
            and (x - self.residue) % self.cofactor == 0
            and x % Q == self.residue % Q
            and root == (self.residue // Q) % Q
        )


def make_family():
    family = [AP('pure3', 1, 0, 1, 3, 1), AP('pure9', 2, 0, 1, 9, 2)]
    for root, (a, b) in enumerate(MIDDLE_PAIRS):
        m = 5**a * 7**b
        modulus = 3 * Q**2 * m
        family.append(AP('middle', 1, 2, m, modulus,
                         crt(((3, 0), (Q**2, Q*root), (m, 0))), root=root))
    for word in (0, 3, 6):
        for root, edge in enumerate(EDGES):
            for vertex in edge:
                p, k = VERTEX_PRIMES[vertex], INCIDENCE[vertex, root]
                n = (word // 3) * DEGREES[vertex] + k
                exponent, height = 1 + (n-1) % 10, 2 + (n-1) // 10
                m = p**exponent
                modulus = 9 * Q**height * m
                residue = crt(((9, word), (Q**height, Q*root), (m, k)))
                family.append(AP('top', 2, height, m, modulus, residue,
                                 root, vertex, word, k, exponent))
    return tuple(family)


FAMILY = make_family()
MIDDLE = tuple(a for a in FAMILY if a.kind == 'middle')
TOP = tuple(a for a in FAMILY if a.kind == 'top')
TOP_INDEX = {(a.word, a.root, a.vertex): a for a in TOP}


def private_point(owner):
    if owner.kind == 'pure3':
        return 1
    if owner.kind == 'pure9':
        return 2
    word = owner.word if owner.kind == 'top' else 0
    phases = {p: 0 for p in SUPPORT}
    if owner.kind == 'top':
        phases[5] = phases[7] = 1
        phases[VERTEX_PRIMES[owner.vertex]] = owner.phase
    return crt(((9, word), (Q**6, Q*owner.root),
                *((p**10, phases[p]) for p in SUPPORT)))


def endpoint_matching(roots):
    """Construct a matching for at most four edges of a simple graph."""
    roots = tuple(roots)
    assert len(roots) <= 4
    # Every subfamily has enough incident vertices: a simple graph on
    # <=3 vertices cannot have more edges than vertices with <=4 edges.
    for size in range(len(roots)+1):
        for subset in combinations(roots, size):
            assert len({v for r in subset for v in EDGES[r]}) >= size

    def extend(pos, used, pairs):
        if pos == len(roots):
            return pairs
        root = roots[pos]
        for vertex in EDGES[root]:
            if vertex not in used:
                result = extend(pos+1, used | {vertex}, pairs + ((root, vertex),))
                if result is not None:
                    return result
        return None

    result = extend(0, set(), ())
    assert result is not None
    return dict(result)


def source_for(x, root):
    inserted = x % Q + Q*root + Q**2*(x//Q)
    return crt(((Q**6, inserted), (9*W, x)))


def tag_failure(tags):
    assert len(tags) == Q and all(isinstance(t, int) and t >= 0 for t in tags)
    slots = tuple(range(0, 81, 3))
    bins = {slot: tuple(r for r, t in enumerate(tags) if t % 81 == slot) for slot in slots}
    slot = min(slots, key=lambda s: (len(bins[s]), s))
    roots = bins[slot]
    assert len(roots) <= 4  # 113 < 27 * 5, even with incompatible tags.
    matching = endpoint_matching(roots)
    phases = {p: 0 for p in SUPPORT}
    for root, vertex in matching.items():
        phases[VERTEX_PRIMES[vertex]] = INCIDENCE[vertex, root]
    # Zero target q-tail makes every selected top's entire q-prefix match.
    x = crt(((81, slot), (Q**5, 0), *((p**10, phases[p]) for p in SUPPORT)))
    assert not any(a.height <= 1 and a.contains(x) for a in FAMILY)
    blockers = []
    overlapping_low = []
    for root in range(Q):
        source = source_for(x, root)
        assert MIDDLE[root].active(x, root) and MIDDLE[root].contains(source)
        if root in matching:
            top = TOP_INDEX[slot % 9, root, matching[root]]
            assert top.active(x, root) and top.contains(source)
            assert (x-tags[root]) % 81 == 0
            blockers.append({'root': root, 'prime': VERTEX_PRIMES[top.vertex],
                             'exponent': top.exponent, 'q_height': top.height})
            overlapping_low.append(root)
        else:
            assert (x-tags[root]) % 81 != 0
        # Direct finite decision of C's existential d at this actual x.
        top_free = not any(a.active(x, root) for a in TOP)
        lower_tags_ok = all((x-tags[a.root]) % 81 == 0
                            for a in MIDDLE if a.active(x, root))
        assert not (top_free and lower_tags_ok)
    return {
        'target': str(x), 'slot_mod_81': slot, 'old_word_mod_9': slot % 9,
        'small_bin_roots': list(roots), 'matching_blockers': blockers,
        'all_113_choices_fail_condition': True,
        'matching_bin_has_simultaneous_low_payers': overlapping_low,
        'target_q_tail_zero_through_power': 5,
    }


def per_word_pool_certificate():
    lookup = {edge: root for root, edge in enumerate(EDGES)}
    used, pools = set(), []
    for vertices in combinations(range(16), 4):
        local_edges = tuple(combinations(vertices, 2))
        for omitted in local_edges:
            roots = tuple(lookup[e] for e in local_edges if e != omitted and e in lookup)
            if len(roots) == 5 and not used.intersection(roots):
                assert len({v for r in roots for v in EDGES[r]}) == 4
                pools.append(roots)
                used.update(roots)
                break
        if len(pools) == 9:
            break
    assert len(pools) == 9 and len(used) == 45
    # Each pool has five roots but only four vertex primes. GLC phase
    # uniqueness lets one vertex block at most one root, at every W-point.
    groups = [0] * Q
    for group, roots in enumerate(pools):
        for root in roots:
            groups[root] = group
    tags_by_word = {str(u): [u + 9*g for g in groups] for u in (0, 3, 6)}
    for u, tags in tags_by_word.items():
        for group, roots in enumerate(pools):
            assert all(tags[r] == int(u) + 9*group for r in roots)
    return {'root_pools': [list(pool) for pool in pools],
            'pool_root_counts': [5] * 9, 'pool_vertex_counts': [4] * 9,
            'independent_tags_by_word': tags_by_word}


def structural_checks():
    assert all(p > 1 and all(p % d for d in range(2, isqrt(p)+1))
               for p in (3, Q) + SUPPORT)
    assert len(set(SUPPORT)) == len(SUPPORT)
    assert len(FAMILY) == 793 and len(TOP) == 678 and len(MIDDLE) == Q
    assert len({a.modulus for a in FAMILY}) == len(FAMILY)
    assert all(a.modulus > 1 and a.modulus % 2 == 1 for a in FAMILY)
    assert all(a.modulus == 3**a.row * Q**a.height * a.cofactor for a in FAMILY)
    assert all(0 <= a.residue < a.modulus and W % a.cofactor == 0 for a in FAMILY)
    assert gcd(W, 3*Q) == 1 and len(SUPPORT) == 18
    assert max(a.row for a in FAMILY) == 2 and max(a.height for a in FAMILY) == 6
    assert max(a.exponent for a in TOP) == 10
    assert max(max(pair) for pair in MIDDLE_PAIRS) == 10
    for u in (0, 3, 6):
        for root in range(Q):
            assert sum(a.word == u and a.root == root for a in TOP) == 2
        for vertex, p in enumerate(VERTEX_PRIMES):
            phases = [a.residue % p for a in TOP if a.word == u and a.vertex == vertex]
            assert len(phases) == len(set(phases)) == DEGREES[vertex]
            assert all(0 < k < p for k in phases)
    for owner in FAMILY:
        x = private_point(owner)
        assert [a for a in FAMILY if a.contains(x)] == [owner]
    assert not any(a.contains(5) for a in FAMILY)
    numerical_labels = {a.modulus for a in FAMILY}
    assert 5 not in numerical_labels
    divisible_original = next(a.modulus for a in FAMILY if a.modulus % 5 == 0)
    assert divisible_original in numerical_labels and divisible_original % 5 == 0
    return {
        'family_size': 793, 'top_count': 678, 'middle_count': 113,
        'distinct_odd_nonunit_labels': 793, 'exact_private_points_verified': 793,
        'cofactor_support': list(SUPPORT), 'cofactor_prime_count': 18,
        'max_cofactor_prime_height': 10, 'max_q_height': 6,
        'max_ternary_height': 2, 'top_inventory_per_word_color_root': 2,
        'vertex_degrees': list(DEGREES), 'literal_collision_edges_per_word': 0,
        'projected_blocked_root_upper_bound_per_word': 16,
        'projected_good_root_lower_bound_per_word': 97,
        'explicit_uncovered_integer': 5,
        'cover_family': False, 'EB1': False, 'divisor_closure': False,
        'non_divisor_closure_witness': {'missing_divisor': 5,
                                        'present_original_modulus': divisible_original},
        'diagnostic_low_service_requires': 'x mod 3 = 0, x mod 113 = 0, x mod 5^10 = x mod 7^10 = 0',
    }



def overlap_payer_witnesses(tags):
    """One exact top/low overlap and replacement payment at every slot."""
    witnesses = []
    for slot in range(0, 81, 3):
        root = next(r for r, tag in enumerate(tags) if tag % 81 == slot)
        vertex = EDGES[root][0]
        p, k = VERTEX_PRIMES[vertex], INCIDENCE[vertex, root]
        phases = {prime: 0 for prime in SUPPORT}
        phases[p] = k
        x = crt(((81, slot), (Q**5, 0),
                 *((prime**10, phases[prime]) for prime in SUPPORT)))
        source = source_for(x, root)
        middle = MIDDLE[root]
        top = TOP_INDEX[slot % 9, root, vertex]
        assert middle.contains(source) and top.contains(source)
        assert middle.active(x, root) and top.active(x, root)
        assert (x-tags[root]) % 81 == 0
        new_modulus = 81 * Q * middle.cofactor
        new_residue = crt(((81, tags[root]), (Q, middle.residue % Q),
                           (middle.cofactor, middle.residue % middle.cofactor)))
        assert (x-new_residue) % new_modulus == 0
        assert new_modulus < middle.modulus
        witnesses.append({'slot_mod_81': slot, 'root': root,
                          'target': str(x), 'overlapping_top_prime': p,
                          'overlapping_top_q_height': top.height,
                          'replacement_modulus': new_modulus,
                          'replacement_residue': new_residue})
    assert len(witnesses) == 27
    return witnesses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tags', type=Path, help='JSON list of 113 nonnegative integers')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    tags = json.loads(args.tags.read_text()) if args.tags else [3*(r % 27) for r in range(Q)]
    result = {'structural_checks': structural_checks(),
              'independent_per_word_certificate': per_word_pool_certificate(),
              'supplied_tags': tags, 'condition_failure': tag_failure(tags)}
    # A 27-slot surjection pays every diagnostic slot when top/low overlap
    # is permitted. This is a surviving route, not a whole-cover claim.
    balanced_tags = [3*(r % 27) for r in range(Q)]
    assert {t % 81 for t in balanced_tags} == set(range(0, 81, 3))
    result['surviving_overlap_route'] = {
        'balanced_tags_cover_all_27_diagnostic_slots': True,
        'low_payers_remain_available_when_top_classes_overlap': True,
        'concrete_overlap_and_replacement_payment_count': 27,
        'concrete_witnesses': overlap_payer_witnesses(balanced_tags),
        'scope': 'diagnostic fiber only; no whole residual or actual cover claim',
    }
    # Boundary examples exercise empty bins and tags incompatible mod 3.
    result['boundary_witnesses'] = {
        'all_tags_zero': tag_failure([0]*Q),
        'all_tags_incompatible': tag_failure([1]*Q),
    }
    payload = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
