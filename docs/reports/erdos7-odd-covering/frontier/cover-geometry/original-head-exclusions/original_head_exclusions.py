#!/usr/bin/env python3
"""Check simultaneous head exclusions in a partial odd AP family.

Uses exact residue membership and Boolean subtree existence. The family is not
an odd cover, and its avoid-set is not claimed as a minimum-cover residual.
"""
from itertools import combinations, product
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def contains_tree(leaves, radix, depth, branching):
    """Existence of a complete subtree in the lowest-digit-first prefix tree."""
    level = set(leaves)
    for b in range(depth-1, -1, -1):
        level = {v for v in range(radix**b)
                 if sum(v+d*radix**b in level for d in range(radix)) >= branching}
    return 0 in level


def verify():
    period = 1225
    originals = {5:0, 7:0, 25:21, 35:34, 49:48, 175:173, 245:242, 1225:241}
    require(set(originals) == {d for d in range(2, period+1) if period % d == 0},
            "complete divisor-closed nonunit head inventory")
    comparable_checks = 0
    for e,d in combinations(sorted(originals), 2):
        if d % e == 0:
            require((originals[d]-originals[e]) % e != 0,
                    "every comparable original pair is disjoint")
            comparable_checks += 1
    private = {}
    for d,a in originals.items():
        witnesses = [x for x in range(period) if x % d == a
                     and all(x % e != b for e,b in originals.items() if e != d)]
        require(witnesses, "each AP has a private residue relative to this partial family")
        private[d] = witnesses[0]

    source = [x for x in range(period) if all(x % d != a for d,a in originals.items())]
    require(source, "this partial family is not a covering system")
    triples = [(x % 5, (x//5) % 5, x % 49) for x in source]
    roots = sorted({r for r,c,y in triples})
    children = {r:sorted({c for rr,c,y in triples if rr == r}) for r in roots}
    incidence = {r:[len({c for rr,c,y in triples if rr == r and y % 7 == g})
                    for g in range(7)] for r in roots}
    require(roots == [1,2,3,4] and [len(children[r]) for r in roots] == [4,5,5,5],
            "exact occupied five-prefix profile")
    require([max(incidence[r]) for r in roots] == [4,5,5,5],
            "no occupied root has incidence bound one or two")
    standalone_five = contains_tree({x % 25 for x in source}, 5, 2, 3)
    standalone_seven = contains_tree({x % 49 for x in source}, 7, 2, 5)
    require(standalone_five and standalone_seven, "both standalone complete-tree conditions")
    choices = tuple(combinations(range(5), 3))
    projections = {(r,T):{y for rr,c,y in triples if rr == r and c in T}
                   for r in roots for T in choices}
    checks = 0
    for r,s in combinations(roots, 2):
        for left,right in product(choices, repeat=2):
            require(contains_tree(projections[(r,left)] | projections[(s,right)], 7, 2, 3),
                    "literal full product-tree blocking")
            checks += 1
    for d,a in originals.items():
        require(not any(x % d == a for x in source), "every fixed original cylinder is excluded")
    return {
        "period":period,
        "original_residues":originals,
        "original_private_witnesses":private,
        "nonunit_divisor_inventory_checks":len(originals),
        "comparable_original_disjointness_checks":comparable_checks,
        "local_irredundancy_witness_checks":len(private),
        "source_points":len(source),
        "source":source,
        "occupied_children":children,
        "child_incidence_counts_by_first7root":incidence,
        "root_incidence_maxima":[max(incidence[r]) for r in roots],
        "full_product_tree_checks":checks,
        "standalone_ternary5tree":standalone_five,
        "standalone_fiveary7tree":standalone_seven,
        "partial_family_is_cover":not source,
        "scope":"Exact avoid-set of an irredundant divisor-closed partial odd AP family; no whole cover, global minimality, or actual odd-cover residual is asserted."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(), indent=2) + "\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
