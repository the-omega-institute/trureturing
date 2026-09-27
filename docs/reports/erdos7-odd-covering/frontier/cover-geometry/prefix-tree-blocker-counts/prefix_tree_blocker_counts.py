#!/usr/bin/env python3
"""Independent exact controls for complete q-ary subtrees in p-ary trees.

These are finite combinatorial controls, not covering-system examples.
The p=3,q=2 case enumerates masks and independently enumerates witnesses.
The p=5,q=3 case uses exact binomial weights on child bad-leaf counts.
"""

from collections import Counter
from itertools import combinations, product
import json
from math import comb, prod


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def recursively_good(bad_mask, p, q, depth, first_leaf=0):
    if depth == 0:
        return not (bad_mask & (1 << first_leaf))
    stride = p ** (depth - 1)
    return sum(
        recursively_good(bad_mask, p, q, depth - 1, first_leaf + i * stride)
        for i in range(p)
    ) >= q


def embedded_subtree_leaf_masks(p, q, depth, first_leaf=0):
    if depth == 0:
        return [1 << first_leaf]
    stride = p ** (depth - 1)
    child_witnesses = [
        embedded_subtree_leaf_masks(p, q, depth - 1, first_leaf + i * stride)
        for i in range(p)
    ]
    result = []
    for chosen in combinations(range(p), q):
        for masks in product(*(child_witnesses[i] for i in chosen)):
            # Chosen child intervals are disjoint, so sum is also bitwise OR.
            result.append(sum(masks))
    check(len(result) == len(set(result)), "duplicate embedded tree witnesses")
    return result


def summarize(p, q, depth, good_histogram, blocked_histogram):
    leaf_count = p ** depth
    good_total = sum(good_histogram.values())
    blocked_total = sum(blocked_histogram.values())
    check(good_total + blocked_total == 2 ** leaf_count, "wrong total mask count")
    for b in range(leaf_count + 1):
        check(good_histogram[b] + blocked_histogram[b] == comb(leaf_count, b),
              "wrong mask count at a given number of bad leaves")
    minimum = min(b for b, n in blocked_histogram.items() if n)
    r = p - q + 1
    check(minimum == r ** depth, "sharp blocker threshold failed")
    minimal_blocker_count_formula = comb(p, r) ** sum(r ** j for j in range(depth))
    check(blocked_histogram[minimum] == minimal_blocker_count_formula,
          "number of minimum blockers failed the extremal-tree count")
    return {
        "p": p,
        "q": q,
        "depth": depth,
        "leaf_count": leaf_count,
        "mask_count": good_total + blocked_total,
        "root_good_count": good_total,
        "root_blocked_count": blocked_total,
        "minimum_bad_leaves_for_blocked_root": minimum,
        "minimum_attaining_mask_count": blocked_histogram[minimum],
        "minimum_attaining_count_formula": minimal_blocker_count_formula,
        "histogram_by_bad_leaf_count": [
            {"bad_leaves": b, "root_good": good_histogram[b],
             "root_blocked": blocked_histogram[b]}
            for b in range(leaf_count + 1)
        ],
    }


def enumerate_small_control():
    p, q, depth = 3, 2, 2
    witnesses = embedded_subtree_leaf_masks(p, q, depth)
    good, blocked = Counter(), Counter()
    first_blocker = {}
    for bad_mask in range(1 << (p ** depth)):
        recursive = recursively_good(bad_mask, p, q, depth)
        has_good_subtree = any((bad_mask & witness) == 0 for witness in witnesses)
        check(recursive == has_good_subtree, "recursive predicate differs from tree existence")
        b = bad_mask.bit_count()
        (good if recursive else blocked)[b] += 1
        if not recursive:
            first_blocker.setdefault(b, bad_mask)
    result = summarize(p, q, depth, good, blocked)
    minimum = result["minimum_bad_leaves_for_blocked_root"]
    example = first_blocker[minimum]
    result.update({
        "method": "all 512 bad-leaf masks; explicit embedded-subtree witnesses",
        "enumerated_mask_count": 512,
        "embedded_complete_q_ary_subtree_count": len(witnesses),
        "subtree_equivalence_checks": 512,
        "one_minimum_bad_mask_integer": example,
        "one_minimum_bad_leaf_indices": [i for i in range(9) if example & (1 << i)],
        "scope": "q=2 is solely a combinatorial control, not an odd-cover example",
    })
    return result


def weighted_large_control():
    p, q, depth = 5, 3, 2
    good, blocked = Counter(), Counter()
    combinations_checked = 0
    first_blocker = {}
    for child_bad_counts in product(range(p + 1), repeat=p):
        combinations_checked += 1
        multiplicity = prod(comb(p, b) for b in child_bad_counts)
        good_children = sum(p - b >= q for b in child_bad_counts)
        b = sum(child_bad_counts)
        (good if good_children >= q else blocked)[b] += multiplicity
        if good_children < q:
            first_blocker.setdefault(b, child_bad_counts)
    result = summarize(p, q, depth, good, blocked)
    child_good = sum(comb(p, b) for b in range(p + 1) if p - b >= q)
    child_blocked = 2 ** p - child_good
    independent_blocked_count = sum(
        comb(p, j) * child_good ** j * child_blocked ** (p - j)
        for j in range(q)
    )
    check(result["root_blocked_count"] == independent_blocked_count,
          "weighted count disagrees with independent root-state count")
    minimum = result["minimum_bad_leaves_for_blocked_root"]
    result.update({
        "method": "exact product of binomial(p, child_bad_count) over child count tuples",
        "child_count_tuples_enumerated": combinations_checked,
        "full_masks_enumerated": 0,
        "child_good_mask_count": child_good,
        "child_blocked_mask_count": child_blocked,
        "independent_root_state_blocked_count": independent_blocked_count,
        "one_minimum_child_bad_count_tuple": first_blocker[minimum],
        "scope": "finite combinatorial control, not an odd-cover example",
    })
    return result


def main():
    results = [enumerate_small_control(), weighted_large_control()]
    payload = {
        "success": True,
        "scope": "Independent finite controls for the tree lemma; no Lean claim",
        "controls": results,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))



if __name__ == "__main__":
    main()
