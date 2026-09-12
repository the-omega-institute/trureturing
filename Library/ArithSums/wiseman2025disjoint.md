---
bibkey: wiseman2025disjoint
authors: Gus Wiseman
year: 2025
title: OEIS A384350 and A384318 — disjoint strict partition families
doi: null
url: https://oeis.org/A384350
claim: The entries conjecture that an outside subset sum characterizes nonuniqueness of disjoint strict partition families.
strata_touched:
  - D5/S3/ArithSums/DisjointStrictRefinement
license: citation-only
triage: anchor
---

# Disjoint strict partition families

## Verified locator

doi: null
url: https://oeis.org/A384350

The COMMENTS in https://oeis.org/A384350/internal and
https://oeis.org/A384318/internal label the characterization by more than one
disjoint strict partition family a conjecture. A384350 counts subsets of an
initial interval; A384318 counts strict partitions of a prescribed total.

The NAME in https://oeis.org/A384322/internal and the FORMULA in
https://oeis.org/A384317/internal state the correspondence without a proof.
These sources establish the question and its terminology.

## Mathematical scope

For a finite positive set S, a family chooses one positive strict integer
partition for each member, with that member as the sum of its block. All
blocks are pairwise disjoint. The singleton family is always available;
nonuniqueness means that at least one block can be changed.

The repository proof uses the least changed member. Every part in its block
is smaller than that member. Any such part in S would retain its own singleton
block, contradicting disjointness. Conversely, an outside subset sum permits
replacement of one singleton block. This is a pointwise statement for every S;
no sequence coefficients or independent product of block counts are asserted.

## Proof scope

Proposition 1 on p.3 of arXiv:2601.10227 and p.2 of arXiv:2206.04261 discuss
reducing an already refinable part to two missing parts; they do not prove
the disjoint-family implication used here.

No exhaustive literature absence or global novelty is claimed. Unopened
paper content remains ASSUMED-UNVERIFIED.
