---
bibkey: costa2026smallabelian
authors: Simone Costa; Stefano Della Fiore; Mattia Fontana; Lluís Vena
year: 2026
title: "Graham conjecture on small sets in abelian groups"
doi: 10.48550/arXiv.2603.20961
url: https://arxiv.org/html/2603.20961v1
claim: Theorem 2.4 gives the restricted-pair-sum subgroup characterization after the two-element boundary is corrected from k>=2 to k>=3.
strata_touched:
  - D5/S3/Combinatorics/RestrictedPairSumClassification
license: citation-only
triage: anchor
---

# Graham conjecture on small sets in abelian groups

Theorem 2.4 of arXiv:2603.20961v1 is used as the source for the corrected
finite restricted-pair-sum classification. The printed `k >= 2` boundary is
false: in `Z/5Z`, `A = {1,4}` has its only distinct-pair sum equal to zero,
but `{0,1,4}` is not a subgroup because `1+1=2`.

The formal proof uses finite translation bijectivity. A non-involution forces a
distinct inverse pair by translating `A.erase c`; the resulting inverse pair
gives diagonal closure away from two exceptions, and the translation
stabilizer recovers the exceptions. Thus, for finite nonzero `A` with
`3 <= A.card`, the proved implication sends restricted sums in `insert 0 A`
to an additive subgroup carrier. The elementary converse is not formalized in
this module.

In the original quotient `Q`, the contrapositive supplies a same-`Q`
mergeable pair: replace `x_a,x_b` by `x_a+x_b`, preserving distinctness,
nonzeroness and the total. The literal lattice pullback through the basis map
is available, but a covering interval can split the adjacent `(a,b)` block at
its internal cut. The split-block expansion and the original coefficient-one
ordering target therefore remain open. This note records no novelty claim.

## Verified locator

- Version: https://arxiv.org/html/2603.20961v1
- Theorem: 2.4
