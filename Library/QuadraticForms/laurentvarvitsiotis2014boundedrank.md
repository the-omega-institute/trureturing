---
bibkey: laurentvarvitsiotis2014boundedrank
authors: Monique Laurent and Antonios Varvitsiotis
year: 2014
title: A new graph parameter related to bounded rank positive semidefinite matrix completions
doi: 10.1007/s10107-013-0648-x
url: https://arxiv.org/abs/1204.0734
claim: On a chordal graph, clique-positive partial real symmetric matrices admit PSD completions whose rank is the largest specified clique-block rank; equal overlap Gram data can be aligned by an orthogonal transformation.
strata_touched: []
license: citation-only
triage: anchor
---

# Rank-preserving chordal completion

Mathematical Programming 145, pages 291–325. The introduction states that
for a chordal graph PSD completion exists exactly when every fully specified
principal submatrix is PSD, and that the minimum completion rank equals the
largest rank of those principal submatrices. The proof of Lemma 2 gives the
rank-preserving gluing mechanism: two PSD matrices with equal principal overlap
blocks have a common PSD completion, obtained by orthogonally aligning their
Gram families on the overlap. Dependence of overlap vectors is allowed.

The real chordal theorem with an arbitrary natural upper bound on every
clique-block rank is the corresponding upper-bound form. Unspecified input
nonedges are discarded; their entries need not be symmetric. The empty carrier
and zero-dimensional Gram family are included in the formal statement.
This is established mathematics, without a novelty or open-problem claim.

## Verified locator

- DOI: https://doi.org/10.1007/s10107-013-0648-x
- Preprint: https://arxiv.org/abs/1204.0734
- Full-text rendering: https://arxiv.org/html/1204.0734

## Lean local suppliers

The rank-controlled Gram factorization and equal-Gram ambient isometry use
TauCetiProject/TauCeti at immutable revision
`0ae45cec5df3d83669e6a8403d229ddbf562d89c`, specifically:

- `TauCeti/LinearAlgebra/Matrix/Rank.lean`:
  `Matrix.exists_eq_mul_fin_rank` and `Matrix.exists_eq_mul_of_rank_le`.
- `TauCeti/Analysis/Matrix/GramFactorization.lean`:
  `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` and
  `Matrix.PosSemidef.exists_eq_conjTranspose_mul_self_of_rank_le`.
- `TauCeti/Analysis/InnerProductSpace/LinearCombination.lean`:
  `Finsupp.inner_linearCombination_eq_of_inner_eq`.
- `TauCeti/Analysis/InnerProductSpace/Gram/Rigidity.lean`:
  `TauCeti.ker_eq_of_inner_self_eq`, `rangeEquivOfInnerEq`,
  `rangeEquivOfInnerEq_apply`, `spanEquivOfInnerEq`,
  `spanEquivOfInnerEq_apply`, and
  `exists_linearIsometryEquiv_of_inner_eq`.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Rank source authors: The Tau Ceti contributors, Jon Crall, Claude Fable 5.
Other supplier source authors: The Tau Ceti contributors.
The full Apache-2.0 license is retained at
`docs/reports/licenses/TauCeti-LICENSE.txt`. The upstream tree has no NOTICE file.
The source repository is https://github.com/TauCetiProject/TauCeti .
Only these consumed declarations are adapted, with local names, imports and
pinned-Mathlib API adjustments. They are reused content, not new mathematics.

The upstream toolchain is Lean 4.36.0-rc2, while the host uses Lean 4.35.0;
the Mathlib revisions also differ. Each transplant is retired when an equivalent
full declaration exists in this repository's own pinned Mathlib and the current
consumers compile by direct application, including empty and zero-dimensional
cases. Upstream acceptance alone is not the retirement condition.
