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

Read all fields from https://oeis.org/A384350/internal and
https://oeis.org/A384318/internal on 2026-09-10. Their COMMENTS explicitly say
“Conjecture” for the characterization by more than one disjoint strict
partition family. A384350 counts subsets of an initial interval; A384318
counts strict partitions of a prescribed total. Their displayed revisions
were 2025-10-20 and 2025-06-11 respectively.

Also read https://oeis.org/A384322/internal (NAME, revision 2025-07-27) and
https://oeis.org/A384317/internal (FORMULA and cross-references, revision
2025-05-28). They state the correspondence without providing a proof.
These locators attest the question and its terminology, not a published proof.

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

## Search boundary

The implementation report `docs/reports/a384350-0910/report.md` records the
repository, pinned Mathlib, Loogle, GitHub and arXiv searches. The triage seat
reported searches in five full PDFs, without a page-by-page review. This worker
additionally searched extracted text of arXiv:2601.10227 (15 pages) and
2206.04261 (28 pages), reading matching contexts. The former p.3 Proposition 1
and the latter p.2 discuss reducing an already refinable part to two missing
parts; they do not prove the disjoint-family implication used here.

No exhaustive literature absence or global novelty is claimed. Unopened
paper content remains ASSUMED-UNVERIFIED.
