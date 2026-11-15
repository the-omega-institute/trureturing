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

## Earlier paper: rank-constrained completion, arXiv:1203.6602v2

M. E.-Nagy, M. Laurent and A. Varvitsiotis, *Complexity of the positive
semidefinite matrix completion problem with a rank constraint*,
https://arxiv.org/abs/1203.6602v2 (full text:
https://arxiv.org/pdf/1203.6602v2). Definition 1.1, page 2, defines a Gram
representation using unit real vectors and prescribed edge inner products.
The subsequent rank-constrained elliptope notation uses rank **at most** k.
Lemma 2.1, page 6, characterizes planar realizability on a cycle by a signing
of the componentwise principal arccosines whose signed sum belongs to 2πℤ.
Its domain is the full closed cube of edge values [-1,1], not just its interior
or data supplied with an initial realization. It cites the earlier Gram-dimension
paper for this criterion.

For a cycle of any length n≥3, the correspondence is x(i)=a(i) and
θ(i)=arccos(a(i))∈[0,π]. Membership in E₂(Cₙ) means that the diagonal-one
partial matrix has a PSD completion of rank at most 2, equivalently a unit-vector
Gram realization in the real plane. The single signing ε∈{-1,1}ⁿ must satisfy
the common closure equation ∑ᵢ ε(i)θ(i)=2πk for an integer k. Rank-one and
nonspanning realizations, repeated vectors and edge values ±1 remain included.
This is a separate classical criterion: chordless cycles of length at least 4
are nonchordal, so it is not an application of the chordal theorem.

## Earlier paper: Gram dimension, arXiv:1112.5960v1

Monique Laurent and Antonios Varvitsiotis, *The Gram dimension of a graph*,
https://arxiv.org/abs/1112.5960v1 (full text:
https://arxiv.org/pdf/1112.5960v1), Section 3.1, Lemma 7 and proof, page 10.
The introductory sentence and proof identify the target as a Gram realization
in ℝ²; the displayed lemma abbreviates the target as a Gram representation.
Its angle parameters lie in [0,π], and it gives the signed-angle closure
criterion. The proof builds successive planar angles and checks the closing
edge. The version-specific locator is essential: arXiv:1112.5960v2
(https://arxiv.org/pdf/1112.5960v2) omits this lemma.

Both earlier-paper discussions are citation-only contextual attribution, with
no copied source text or code. They do not change this note's own 2014
bibliographic metadata or attribute the cycle result to its chordal theorem.
The complete cycle derivation and applicability boundaries are in the existing
RankBoundedChordalPsdCompletion Blueprint narrative.

## Mathlib suppliers for the separate cycle derivation

At Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- `Mathlib/Analysis/InnerProductSpace/PiL2.lean`:
  `Complex.orthonormalBasisOneI` and its coordinate representation identify
  ℂ isometrically with `EuclideanSpace ℝ (Fin 2)`.
- `Mathlib/Analysis/Complex/Circle.lean`: `Circle.coe_inv_eq_conj`
  turns a unit-circle quotient into multiplication by the conjugate.
- `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`:
  `Complex.arg_of_im_nonneg_of_ne_zero` and `Complex.arg_of_im_neg`
  give the two signed principal-arccosine branches, including the real axis
  in the nonnegative branch.
- `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`:
  `Circle.exp_arg`, `Circle.exp_eq_one` and `Circle.exp_two_pi_mul_int`
  recover a unit complex number from its argument and characterize the
  integer-period closure equation. `Circle.expHom`, defined in
  `Mathlib/Analysis/Complex/Circle.lean`, carries finite sums to products.
- `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`:
  `Equiv.prod_comp` reindexes the cyclic numerator product.
  `Mathlib/Algebra/Order/BigOperators/Group/LocallyFinite.lean`:
  `Finset.prod_Iio_mul_eq_prod_Iic` supplies the prefix-product step.
  `Mathlib/Logic/Equiv/Fin/Rotate.lean`: `finRotate_apply` expresses cyclic
  successor, including wrap to zero.
- `Mathlib/Analysis/Complex/Trigonometric.lean`:
  `Complex.exp_ofReal_mul_I_re`; and
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean`:
  `Real.cos_arccos`, valid on the closed interval [-1,1].

These are reused suppliers for an application exposition, not new mathematical
content, a new retained theorem or a claim of literature novelty.

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
