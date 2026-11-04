---
slug: barrese-prescribed-ordered-level-enumeration
bibkey: barrese2023levels
doi: 10.48550/arXiv.2312.10855
url: https://arxiv.org/abs/2312.10855v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.source2023_count
  - D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator_count
---

# Ferrers Boards with Prescribed Ordered Level Numbers

## Problem

Kenneth Barrese, *Weighted File Placements on Singleton Boards*,
[arXiv:2312.10855v1](https://arxiv.org/pdf/2312.10855v1), Section 2.2, asks:

> This suggests the open question, given an ordered set of level numbers:
> (l_1, l_2, . . . , l_n), how many unique Ferrers boards have those specific level numbers.

Section 5 repeats this question. For every positive m and n, count every weakly increasing
n-tuple of column heights between zero and mn in the fixed n-column, mn-row rectangle,
with a prescribed top-down vector l of n nonnegative level totals. A level has m rows;
its total counts actual occupied cells. Leading zero columns and empty top levels are retained.
The input board need not be singleton, and no permutation of l is allowed.

The same prescribed-level counting problem has an earlier all-width formulation in Kenneth
Barrese, Nicholas Loehr, Jeffrey Remmel and Bruce E. Sagan, *Bijections on m-level Rook Placements*,
[arXiv:1508.05944v1](https://arxiv.org/pdf/1508.05944v1), Section 6.2:

> If C is a singleton board, then perhaps counting the number of Ferrers boards B
> with l(B) = C would be a good start to this problem, but this too remains open.

For every positive m and every nonempty positive singleton target C, count all normalized
Ferrers boards B of arbitrary width with l(B)=C. Definition 4 reverses the nonempty
bottom-up level totals. Here normalization uses positive weakly increasing column-height lists:
Section 4.1 aligns lower-right cells and treats leading zero padding as another notation
for the same board. Arbitrary horizontal translations as distinct unbounded absolute-grid
subsets are a different carrier. The bibliographic header identifies the later 2023 question;
the original 2015 formulation and its governing conventions are identified explicitly here.

## Motivation

Pre-registration [#23382](https://github.com/the-omega-institute/trureturing/issues/23382)
fixes the complete prescribed-level problem in both source conventions. The joint conclusion
uses `BarreseOrderedLevels.source2023_count` for the fixed rectangle and
`BarreseSourceNormalization.lOperator_count` for the actual native all-width operator fiber.
These are two scopes of one registered counting answer, not separate problem credits.
The larger question of counting an entire m-level rook equivalence class is outside this answer.

## Gap

The bounded literature and all-state registration qualification recorded in #23382 found no
complete earlier answer or other-owner equivalent registration within its searched scope.
The existing singleton representative and rook-equivalence results do not enumerate these fibers.
The square-family supplier in [PR #14863](https://github.com/the-omega-institute/trureturing/pull/14863) concerns a proper subfamily; the rectangular Gaussian
polynomial is an ingredient, not a complete prescribed-level solution. These findings do not
establish worldwide absence, originality or priority.

## Route

Put r=m-1 and write a for bottom-up totals. Let G(N,k) be the finite Gaussian polynomial,
defined by G(N,0)=1, G(0,k+1)=0 and
G(N+1,k+1)=G(N,k+1)+q^(N-k)G(N,k). Set
T_a(u,v)=0 unless v<=u and mv<=a; otherwise set
T_a(u,v)=[q^(a-mv)]G(u-v+r,r).
For states u,v in {0,...,U}, evaluate F([],u)=1 and
F(a::as,u)=sum_(v=0)^U T_a(u,v)F(as,v).

Padded row-column conjugation with horizontal reflection preserves each literal level total.
Subtracting a level's final row v from its first m-1 rows gives a rectangle of weight a-mv.
The proof directly uses `D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle.gauss_rectangle`.
Compatible level gluing then identifies the finite scalar recurrence with the native board count.
The fixed-ambient answer is F(reverse(l),n).

For the all-width problem, positive source columns are bijective to finite Young diagrams.
The bottom level total derives width<=last(c), and vanishing above length(c) derives
height<=m*length(c). Unique padding therefore gives F(reverse(c),last(c)) without a width
premise. The actual trimmed operator equality fiber is bijective to this level-total fiber.
If any entry of c is zero, the extended formula is zero. The separate extension l(empty)=[]
has one preimage, with U=0; Definition 4 itself requires a largest nonempty level.

## Falsifier

A mismatch between a native board fiber and its recurrence value for any positive m and
any original ordered data would refute the claimed correspondence. This includes m=1,
empty or infeasible data, the all-zero fixed-ambient vector, leading zero slots, top padding,
and the all-width bound derived from data. Changing to unordered levels, singleton inputs,
a prescribed input width or unbounded absolute translations changes the question.

## Evidence

The seven D5 sources establish the row coordinates, rectangle correspondence, Gaussian transfer,
compatible gluing, native fixed-ambient count, derived all-width padding and exact native
l-operator fiber count. `gauss_rectangle` and Mathlib's `YoungDiagram.rowLen_ofRowLens`
are reused directly. The scalar recurrence is over U+1 row-bound states, not over original boards.

All thirteen authored public theorem registrations compile. Four have validated source-binding
certificates: `BarreseAllWidths.all_width_count`, `BarreseAllWidths.width_bound`,
`FerrersLevelCounting.paths_card` and `FerrersLevelGluing.flat_card`.
Nine audits remain unfinished under [#23540](https://github.com/the-omega-institute/trureturing/issues/23540):
`BarreseOrderedLevels.native_count` (`source.params`);
`BarreseOrderedLevels.source2023_count`, `BarreseSourceNormalization.lOperator_count` and
`BarreseSourceNormalization.source2015_count` (`source.dictionary_or_proof_coordinate`);
`FerrersLevelTransfer.level_card` (`source.unsafe_or_external`, site `Nat.decLe`);
`FerrersRowCoordinates.board_row_count`, `conjugate_involutive` and `diagram_rowLen`
(`source.telescope_reconstruction`); and `FerrersRowCoordinates.diagram_mem` (`source.state_binder`).
These are unfinished source-binding audits, not validated certificates or undecidability results.

## Triage

`theorem`; this is the externally printed prescribed ordered level-number counting question.
The two terminal declarations cover the complete fixed-ambient and normalized all-width source
scopes jointly. Auxiliary modules and consumed coordinate helpers are not additional problems.

## ASSUMED-UNVERIFIED

Literature and ownership absence are bounded by the completed qualification in #23382.
The finite 2015 answer uses the paper's normalization, lower-right alignment and left-zero-padding
working convention; it does not count arbitrary absolute horizontal translations separately.
The empty native operator is an explicitly declared extension. Nine source-binding audits remain
unfinished as listed above. Compilation and mathematical correspondence do not establish
worldwide novelty, required CI, merge, first dev push or solved-problem credit.
