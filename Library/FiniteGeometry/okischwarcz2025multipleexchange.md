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
  - D5/S3/Combinatorics/Matroids/LocalSearchRobustness
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

## Local-search robustness

Theorem 1.7 and Lemma 4.1 in Section 4, printed pages 19–20, concern
arbitrary single-exchange paths of bases with real weights. The local
error is the actual radius-one neighborhood maximum minus the next
base's weight. Every such error is nonnegative, and their sum bounds
the final base's deficit against every radius-k comparator around the
initial base. No improvement or optimal-start assumption occurs.

Lemma 4.1 is used in the natural-radius form
$H_r(B_1)+H_1(B_0)\ge H_{r+1}(B_0)+W(B_1)$ for $r\ge0$.
Its proof selects a maximizer in the neighborhood of $B_0$; the printed
initial argmax uses an unspecified $B$, interpreted as $B_0$ by equation
(21). The size-one prescribed-exchange branch selects a minimum-weight
element of $A\setminus B_0$. The native proof first handles $A=B_0$ and
uses the antichain property of bases to establish nonemptiness in the
remaining branch. The direct simultaneous exchange supplier is
Theorem 1.6(i), with singleton prescriptions. Cardinality and weight
identities use the same pair of exchanged bases. The natural-radius
indexing includes zero radius without truncated-subtraction ambiguity.
