/- GID: D5/S3/Weil/Pick/DiagonalSignNegativeIndex
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/DiagonalSignNegativeIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A real diagonal Hermitian matrix has positive and negative indices equal to the counts of positive and negative diagonal weights. -/

import D5.S3.SpectralTopology.PointGapExactInertia
import Mathlib.Tactic

/-!
# Diagonal signs and Hermitian inertia

The repository already owns the positive and negative Hermitian indices, the
rank partition `posIndex + negIndex = rank`, pullback monotonicity of positive
index, and the fact that matrix negation exchanges the two indices. This node
uses diagonal coordinate projectors to identify the exact inertia of a real
diagonal matrix from the signs of its entries.

This is finite-dimensional linear algebra. No Cauchy full-rank theorem,
Stieltjes representation, Weil realization, or statement about RH is assumed.
-/

/- Library-search audit trail (2026-09-03):
   * `RHLinalg.posIndex` and `RHLinalg.negIndex` are reused from
     `D5/S3/Weil/ZetaLinear/PosIndex`.
   * `RHLinalg.posIndex_eq_rank_of_posSemidef` and
     `RHLinalg.posIndex_conj_le` supply the positive-index calculus.
   * `FiniteSpectralLocalizer.posIndex_neg_eq_negIndex` supplies index exchange
     under matrix negation.
   * `PointGapExactInertia.posIndex_add_negIndex_eq_rank` supplies the exact
     nonzero-spectrum partition.
   * Pinned Mathlib supplies positive-semidefinite diagonal matrices and
     `Matrix.rank_diagonal`.
   * Repository searches for `DiagonalSignNegativeIndex`, diagonal sign-count
     inertia, and exact diagonal negative-index counting found no public owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace D5.S3.Weil.Pick.DiagonalSignNegativeIndex

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open D5.S3.SpectralTopology.PointGapExactInertia

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A complex Hermitian diagonal matrix whose entries are supplied as reals. -/
def realDiagonal (weight : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (weight i : ℂ))

/-- The number of strictly positive diagonal weights. -/
def positiveWeightCount (weight : ι → ℝ) : ℕ :=
  #{i | 0 < weight i}

/-- The number of strictly negative diagonal weights. -/
def negativeWeightCount (weight : ι → ℝ) : ℕ :=
  #{i | weight i < 0}

/-- The number of nonzero diagonal weights. -/
def nonzeroWeightCount (weight : ι → ℝ) : ℕ :=
  #{i | weight i ≠ 0}

/-- The diagonal projector onto coordinates with positive weight. -/
def positiveCoordinateProjector (weight : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if 0 < weight i then 1 else 0)

/-- The diagonal projector onto coordinates with negative weight. -/
def negativeCoordinateProjector (weight : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if weight i < 0 then 1 else 0)

/-- The positive weight retained on a positive coordinate and zero elsewhere. -/
def positiveSelectedWeight (weight : ι → ℝ) (i : ι) : ℝ :=
  if 0 < weight i then weight i else 0

/-- The positive magnitude of a negative coordinate and zero elsewhere. -/
def negativeMagnitudeWeight (weight : ι → ℝ) (i : ι) : ℝ :=
  if weight i < 0 then -weight i else 0

/-- A real diagonal matrix is Hermitian. -/
theorem real_diagonal_isHermitian (weight : ι → ℝ) :
    (realDiagonal weight).IsHermitian := by
  unfold realDiagonal
  exact Matrix.isHermitian_diagonal_of_self_adjoint _
    (funext fun i => by simp [RCLike.star_def])

private theorem positive_coordinate_projector_isHermitian
    (weight : ι → ℝ) :
    (positiveCoordinateProjector weight).IsHermitian := by
  unfold positiveCoordinateProjector
  exact Matrix.isHermitian_diagonal_of_self_adjoint _
    (funext fun i => by simp [RCLike.star_def])

private theorem negative_coordinate_projector_isHermitian
    (weight : ι → ℝ) :
    (negativeCoordinateProjector weight).IsHermitian := by
  unfold negativeCoordinateProjector
  exact Matrix.isHermitian_diagonal_of_self_adjoint _
    (funext fun i => by simp [RCLike.star_def])

private theorem positive_selected_weight_nonneg
    (weight : ι → ℝ) (i : ι) :
    0 ≤ positiveSelectedWeight weight i := by
  unfold positiveSelectedWeight
  split_ifs with h
  · exact h.le
  · exact le_rfl

private theorem negative_magnitude_weight_nonneg
    (weight : ι → ℝ) (i : ι) :
    0 ≤ negativeMagnitudeWeight weight i := by
  unfold negativeMagnitudeWeight
  split_ifs with h
  · exact neg_nonneg.mpr h.le
  · exact le_rfl

private theorem positive_selected_diagonal_posSemidef
    (weight : ι → ℝ) :
    (realDiagonal (positiveSelectedWeight weight)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr
    (positive_selected_weight_nonneg weight i)

private theorem negative_magnitude_diagonal_posSemidef
    (weight : ι → ℝ) :
    (realDiagonal (negativeMagnitudeWeight weight)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr
    (negative_magnitude_weight_nonneg weight i)

/-- Positive-coordinate pullback deletes all nonpositive diagonal weights. -/
theorem positive_coordinate_pullback
    (weight : ι → ℝ) :
    (positiveCoordinateProjector weight)ᴴ * realDiagonal weight *
        positiveCoordinateProjector weight =
      realDiagonal (positiveSelectedWeight weight) := by
  rw [(positive_coordinate_projector_isHermitian weight).eq]
  unfold positiveCoordinateProjector realDiagonal positiveSelectedWeight
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : 0 < weight i <;> simp [h]

/-- Negative-coordinate pullback of the negated form records positive
magnitudes exactly on negative coordinates. -/
theorem negative_coordinate_pullback
    (weight : ι → ℝ) :
    (negativeCoordinateProjector weight)ᴴ * (-(realDiagonal weight)) *
        negativeCoordinateProjector weight =
      realDiagonal (negativeMagnitudeWeight weight) := by
  have hNeg :
      -(realDiagonal weight) = realDiagonal (fun i => -weight i) := by
    ext i j
    simp [realDiagonal]
  rw [hNeg, (negative_coordinate_projector_isHermitian weight).eq]
  unfold negativeCoordinateProjector realDiagonal negativeMagnitudeWeight
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : weight i < 0 <;> simp [h]

private theorem positive_selected_diagonal_rank
    (weight : ι → ℝ) :
    (realDiagonal (positiveSelectedWeight weight)).rank =
      positiveWeightCount weight := by
  classical
  simp [realDiagonal, positiveSelectedWeight, positiveWeightCount,
    Matrix.rank_diagonal]

private theorem negative_magnitude_diagonal_rank
    (weight : ι → ℝ) :
    (realDiagonal (negativeMagnitudeWeight weight)).rank =
      negativeWeightCount weight := by
  classical
  simp [realDiagonal, negativeMagnitudeWeight, negativeWeightCount,
    Matrix.rank_diagonal]

/-- The rank of a real diagonal matrix is the number of its nonzero weights. -/
theorem real_diagonal_rank_eq_nonzero_count
    (weight : ι → ℝ) :
    (realDiagonal weight).rank = nonzeroWeightCount weight := by
  classical
  simp [realDiagonal, nonzeroWeightCount, Matrix.rank_diagonal]

/-- Positive and negative coordinates partition the nonzero coordinates. -/
theorem positive_add_negative_count_eq_nonzero
    (weight : ι → ℝ) :
    positiveWeightCount weight + negativeWeightCount weight =
      nonzeroWeightCount weight := by
  unfold positiveWeightCount negativeWeightCount nonzeroWeightCount
  have hDisjoint :
      Disjoint
        (Finset.univ.filter fun i => 0 < weight i)
        (Finset.univ.filter fun i => weight i < 0) := by
    rw [Finset.disjoint_left]
    intro i hPositive hNegative
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      at hPositive hNegative
    exact (not_lt_of_ge hPositive.le) hNegative
  rw [← Finset.card_union_of_disjoint hDisjoint]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hPositive | hNegative)
    · exact hPositive.ne'
    · exact hNegative.ne
  · intro hNonzero
    rcases lt_trichotomy (weight i) 0 with hNegative | hZero | hPositive
    · exact Or.inr hNegative
    · exact False.elim (hNonzero hZero)
    · exact Or.inl hPositive

/-- The positive sign count is bounded by the positive index of the full
real diagonal form. -/
theorem positive_weight_count_le_posIndex
    (weight : ι → ℝ) :
    positiveWeightCount weight ≤
      posIndex (real_diagonal_isHermitian weight) := by
  have hPull :=
    RHLinalg.posIndex_conj_le
      (real_diagonal_isHermitian weight)
      (positiveCoordinateProjector weight)
  have hPullIndex :
      posIndex
          (isHermitian_conjTranspose_mul_mul
            (positiveCoordinateProjector weight)
            (real_diagonal_isHermitian weight)) =
        positiveWeightCount weight := by
    rw [positive_coordinate_pullback]
    calc
      posIndex (positive_selected_diagonal_posSemidef weight).isHermitian =
          (realDiagonal (positiveSelectedWeight weight)).rank :=
        RHLinalg.posIndex_eq_rank_of_posSemidef
          (positive_selected_diagonal_posSemidef weight)
      _ = positiveWeightCount weight :=
        positive_selected_diagonal_rank weight
  exact hPullIndex ▸ hPull

/-- The negative sign count is bounded by the negative index of the full
real diagonal form. -/
theorem negative_weight_count_le_negIndex
    (weight : ι → ℝ) :
    negativeWeightCount weight ≤
      negIndex (real_diagonal_isHermitian weight) := by
  have hPull :=
    RHLinalg.posIndex_conj_le
      (real_diagonal_isHermitian weight).neg
      (negativeCoordinateProjector weight)
  have hPullIndex :
      posIndex
          (isHermitian_conjTranspose_mul_mul
            (negativeCoordinateProjector weight)
            (real_diagonal_isHermitian weight).neg) =
        negativeWeightCount weight := by
    rw [negative_coordinate_pullback]
    calc
      posIndex (negative_magnitude_diagonal_posSemidef weight).isHermitian =
          (realDiagonal (negativeMagnitudeWeight weight)).rank :=
        RHLinalg.posIndex_eq_rank_of_posSemidef
          (negative_magnitude_diagonal_posSemidef weight)
      _ = negativeWeightCount weight :=
        negative_magnitude_diagonal_rank weight
  calc
    negativeWeightCount weight =
        posIndex
          (isHermitian_conjTranspose_mul_mul
            (negativeCoordinateProjector weight)
            (real_diagonal_isHermitian weight).neg) := hPullIndex.symm
    _ ≤ posIndex (real_diagonal_isHermitian weight).neg := hPull
    _ = negIndex (real_diagonal_isHermitian weight) :=
      posIndex_neg_eq_negIndex (real_diagonal_isHermitian weight)

/-- A real diagonal Hermitian matrix has exact positive and negative inertia
counts given by the signs of its diagonal weights. -/
theorem real_diagonal_inertia_eq_sign_counts
    (weight : ι → ℝ) :
    posIndex (real_diagonal_isHermitian weight) =
        positiveWeightCount weight ∧
      negIndex (real_diagonal_isHermitian weight) =
        negativeWeightCount weight := by
  have hPositive := positive_weight_count_le_posIndex weight
  have hNegative := negative_weight_count_le_negIndex weight
  have hIndices :
      posIndex (real_diagonal_isHermitian weight) +
          negIndex (real_diagonal_isHermitian weight) =
        nonzeroWeightCount weight := by
    calc
      posIndex (real_diagonal_isHermitian weight) +
          negIndex (real_diagonal_isHermitian weight) =
        (realDiagonal weight).rank :=
          posIndex_add_negIndex_eq_rank (real_diagonal_isHermitian weight)
      _ = nonzeroWeightCount weight :=
        real_diagonal_rank_eq_nonzero_count weight
  have hCounts := positive_add_negative_count_eq_nonzero weight
  omega

/-- In particular, the negative index of a real diagonal matrix is exactly the
number of negative entries. -/
theorem real_diagonal_negIndex_eq_negative_count
    (weight : ι → ℝ) :
    negIndex (real_diagonal_isHermitian weight) =
      negativeWeightCount weight :=
  (real_diagonal_inertia_eq_sign_counts weight).2

#print axioms real_diagonal_rank_eq_nonzero_count
#print axioms positive_add_negative_count_eq_nonzero
#print axioms positive_weight_count_le_posIndex
#print axioms negative_weight_count_le_negIndex
#print axioms real_diagonal_inertia_eq_sign_counts
#print axioms real_diagonal_negIndex_eq_negative_count

end D5.S3.Weil.Pick.DiagonalSignNegativeIndex
