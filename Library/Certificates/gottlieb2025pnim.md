---
bibkey: gottlieb2025pnim
authors: Eric Gottlieb; Matjaž Krnc; Peter Muršič
year: 2025
title: Nim on Integer Partitions and Hyperrectangles
doi: 10.48550/arXiv.2506.04991
url: https://arxiv.org/abs/2506.04991
claim: Section 1.2 defines PNim row and column subset deletion; section 2 defines Young's order; section 3 and Proposition 2 define heaviness; printed Conjecture 2 predicts a heavy interval below any heavy rectangle.
strata_touched:
  - D5/S0/Certificates/Games/PnimHeavyIntervalRefutation
license: citation-only
triage: anchor
---

# PNim and the heavy-interval conjecture

In single-partition PNim, a move deletes a nonempty subset of diagram
rows or columns, merging the remaining rows or columns. Partitions have
positive nonincreasing parts. Young's order compares lengths and aligned
parts. The Sprague-Grundy value is the least excluded follower value.

Proposition 2 gives the longest-play length of a nonempty partition as
its first part plus its number of parts minus one. A partition is heavy
when its Sprague-Grundy value equals this length. Proposition 1 states
the corresponding upper bound, not the longest-play identity.

Printed Conjecture 2, page 14, asserts that if [(a+1)^(b+1)] is heavy,
then every partition between [a+1,a,...,a-b+1] and that rectangle in
Young's order is heavy. Both endpoints are partitions exactly when the
integer parameters satisfy a >= b >= 0. This note attests the printed
definitions and assertion, not the assertion's truth. The formal
refutation uses a=8, b=7 and [9,9,8,8,8,5,5,5], whose Grundy value is
3 rather than its longest-play length 16; the upper rectangle is heavy.
No priority or corrected conjecture is asserted.

The arXiv API queries on 2026-09-17 returned one PNim paper (this v1),
one matching title, and six papers matching Gottlieb and Krnc. These
bounded searches do not establish absence of a settlement in journal
versions, non-arXiv manuscripts, or later sources.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2506.04991
- URL: https://arxiv.org/abs/2506.04991
- Version: https://arxiv.org/pdf/2506.04991v1 (2025-06-05).
- Scope: section 1.2 (PNim moves and Theorem 1), section 2 (Young's
  order), section 3 (Proposition 2 and heaviness), and printed page 14
  (Conjecture 2).
