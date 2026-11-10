---
bibkey: okischwarcz2025multipleexchange
authors: Taihei Oki and Tamás Schwarcz
year: 2025
title: Generalizing the Multiple Exchange Property for Matroid Bases
doi: null
url: https://arxiv.org/abs/2511.16021v3
claim: Two prescribed subsets of opposite base differences extend to a simultaneous exchange whose common cardinality is at most their union rank.
strata_touched:
  - D5/S3/Combinatorics/Matroids/PrescribedExchange
license: citation-only
triage: anchor
---

# Rank-bounded simultaneous prescribed exchange

## Verified locator

Source: https://arxiv.org/abs/2511.16021v3

The title page identifies Taihei Oki and Tamás Schwarcz and the version
arXiv:2511.16021v3, 28 July 2026. The finite-ground matroid convention is
stated in the introduction and Section 2.2. Theorem 1.6(i), restated on
printed page 12, says that for bases A and B and subsets X of A minus B
and Y of B minus A, there are subsets U of A minus B and V of B minus A
containing X and Y respectively, with equal cardinality at most the rank
of X union Y, such that both exchanged sets are bases.

Section 3.1, printed pages 12–15, proves the bound through integral
weight splitting for the same common base of the contraction/deletion
minors of the matroid and its dual. Theorem 2.2 supplies splitting;
Theorem 2.1 supplies greedy rank profiles. Equations (9)–(19) combine
those profiles with rank submodularity.

The expansion preceding equation (17) has constant
$+|Y|-|X|$, whereas its next line displays $-|X\cup Y|$.
The former agrees with the expansion and with the cancellation against
(19). The native proof uses a direct telescoping inequality for paired
integer threshold ranks, without assuming the inconsistent display.

The Lean statement quantifies over every finite ambient type in any
universe and uses native matroid grounds, extended rank converted by
toNat, and finite set cardinality. It includes proper and empty grounds,
intersecting or equal bases, loops, coloops, rank zero and matroids
without a field representation. It asserts the existence part only;
Theorem 1.6(ii)'s oracle-query assertion is outside its scope.

The paper attests the mathematical result and is cited without
redistributing its PDF. The direct threshold telescoping is an
application of the paper's paired submodular rank argument.
