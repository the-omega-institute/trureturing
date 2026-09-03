/- GID: D5/S3/SpectralTopology/PointGapFiniteScaleStability
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/PointGapFiniteScaleStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A point-gap localizer stays invertible under a small relative position perturbation. -/

import D5.S3.SpectralTopology.PointGapExactInertia
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite-scale stability of a point-gap localizer

The zero-scale finite spectral localizer is invertible exactly when the
spectral shift has a point gap. This node turns on the position scale and
separates the change into a Hermitian block-diagonal direction.

For the zero-scale localizer `L₀`, the position direction `Dₓ`, and scale
`κ`, the full localizer satisfies

`Lκ = L₀ + κ Dₓ = L₀ (1 + L₀⁻¹ κ Dₓ)`.

Consequently, under a point gap, invertibility of the full localizer is
exactly invertibility of the relative factor. With the L2 operator norm, the
Neumann-series criterion gives the explicit sufficient condition

`‖L₀⁻¹‖ * ‖κ‖ * ‖Dₓ‖ < 1`.

This is a finite-dimensional stability theorem. It does not yet prove that
the Hermitian signature is constant along the scale path, identify a
normalized topological index, establish a bulk-boundary correspondence, take
an infinite-volume limit, or imply RH.
-/

/- Library-search audit trail (2026-09-02):
   * `FiniteSpectralLocalizer` owns the localizer, point-gap predicate,
     zero-scale invertibility equivalence, and Hermitianity of the full block
     matrix.
   * `PointGapExactInertia` owns the exact positive and negative zero-scale
     inertia under a point gap.
   * Pinned Mathlib supplies the nonsingular matrix inverse identities, the L2
     operator norm on finite matrices, submultiplicativity of that norm, and
     `isUnit_one_sub_of_norm_lt_one`.
   * Repository search found no existing owner for the relative localizer
     factor or this finite-scale Neumann criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator

namespace D5.S3.SpectralTopology.PointGapFiniteScaleStability

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open D5.S3.SpectralTopology.PointGapExactInertia

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The Hermitian block-diagonal direction contributed by the shifted
position observable. -/
def positionDirection
    (X : Matrix n n ℂ) (x : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks
    (positionShift X x) 0 0 (-(positionShift X x))

/-- The position perturbation measured in zero-scale localizer coordinates. -/
def relativePositionPerturbation
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (finiteSpectralLocalizer X H 0 x z)⁻¹ *
    ((kappa : ℂ) • positionDirection X x)

/-- The relative factor whose invertibility controls the finite-scale
localizer. -/
def relativePositionFactor
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  1 + relativePositionPerturbation X H kappa x z

/-- A Hermitian position observable gives a Hermitian position direction. -/
theorem position_direction_isHermitian
    (X : Matrix n n ℂ) (x : ℝ) (hX : X.IsHermitian) :
    (positionDirection X x).IsHermitian := by
  have hPosition : (positionShift X x).IsHermitian :=
    position_shift_isHermitian X x hX
  exact hPosition.fromBlocks (by simp) hPosition.neg

/-- The finite-scale localizer is the zero-scale localizer plus the scaled
position direction. -/
theorem finite_spectral_localizer_scale_decomposition
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    finiteSpectralLocalizer X H kappa x z =
      finiteSpectralLocalizer X H 0 x z +
        (kappa : ℂ) • positionDirection X x := by
  ext row column
  rcases row with row | row <;>
    rcases column with column | column <;>
      simp [finiteSpectralLocalizer, positionDirection]

/-- Under a point gap, the finite-scale localizer factors through its
zero-scale value and the relative position factor. -/
theorem finite_spectral_localizer_relative_factorization
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z) :
    finiteSpectralLocalizer X H kappa x z =
      finiteSpectralLocalizer X H 0 x z *
        relativePositionFactor X H kappa x z := by
  have hZero : IsUnit (finiteSpectralLocalizer X H 0 x z) :=
    (has_point_gap_iff_zero_scale_localizer_isUnit X H x z).1 hGap
  have hDet : IsUnit (finiteSpectralLocalizer X H 0 x z).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hZero
  calc
    finiteSpectralLocalizer X H kappa x z =
        finiteSpectralLocalizer X H 0 x z +
          (kappa : ℂ) • positionDirection X x :=
      finite_spectral_localizer_scale_decomposition X H kappa x z
    _ = finiteSpectralLocalizer X H 0 x z *
        (1 + (finiteSpectralLocalizer X H 0 x z)⁻¹ *
          ((kappa : ℂ) • positionDirection X x)) := by
      symm
      rw [mul_add, mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv
          (finiteSpectralLocalizer X H 0 x z) hDet,
        one_mul]
    _ = finiteSpectralLocalizer X H 0 x z *
        relativePositionFactor X H kappa x z := by
      rfl

/-- Under a point gap, finite-scale localizer invertibility is exactly
invertibility of the relative position factor. -/
theorem finite_scale_localizer_isUnit_iff_relative_factor_isUnit
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z) :
    IsUnit (finiteSpectralLocalizer X H kappa x z) ↔
      IsUnit (relativePositionFactor X H kappa x z) := by
  have hZero : IsUnit (finiteSpectralLocalizer X H 0 x z) :=
    (has_point_gap_iff_zero_scale_localizer_isUnit X H x z).1 hGap
  have hDet : IsUnit (finiteSpectralLocalizer X H 0 x z).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hZero
  calc
    IsUnit (finiteSpectralLocalizer X H kappa x z) ↔
        IsUnit
          (finiteSpectralLocalizer X H 0 x z *
            relativePositionFactor X H kappa x z) := by
      rw [finite_spectral_localizer_relative_factorization
        X H kappa x z hGap]
    _ ↔ IsUnit
        ((finiteSpectralLocalizer X H 0 x z *
          relativePositionFactor X H kappa x z).det) :=
      Matrix.isUnit_iff_isUnit_det _
    _ ↔ IsUnit
        ((finiteSpectralLocalizer X H 0 x z).det *
          (relativePositionFactor X H kappa x z).det) := by
      rw [Matrix.det_mul]
    _ ↔ IsUnit (finiteSpectralLocalizer X H 0 x z).det ∧
        IsUnit (relativePositionFactor X H kappa x z).det :=
      IsUnit.mul_iff
    _ ↔ IsUnit (relativePositionFactor X H kappa x z).det :=
      and_iff_right hDet
    _ ↔ IsUnit (relativePositionFactor X H kappa x z) :=
      (Matrix.isUnit_iff_isUnit_det _).symm

/-- The relative position perturbation is bounded by the inverse zero-scale
norm, the scale norm, and the position-direction norm. -/
theorem relative_position_perturbation_norm_le
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    ‖relativePositionPerturbation X H kappa x z‖ ≤
      ‖(finiteSpectralLocalizer X H 0 x z)⁻¹‖ *
        (‖(kappa : ℂ)‖ * ‖positionDirection X x‖) := by
  unfold relativePositionPerturbation
  simpa only [norm_smul] using
    (Matrix.l2_opNorm_mul
      (finiteSpectralLocalizer X H 0 x z)⁻¹
      ((kappa : ℂ) • positionDirection X x))

/-- A relative position perturbation of operator norm below one gives an
invertible relative factor. -/
theorem relative_position_factor_isUnit_of_norm_lt_one
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hSmall : ‖relativePositionPerturbation X H kappa x z‖ < 1) :
    IsUnit (relativePositionFactor X H kappa x z) := by
  have hNeg :
      ‖-relativePositionPerturbation X H kappa x z‖ < 1 := by
    simpa only [norm_neg] using hSmall
  simpa [relativePositionFactor] using
    (isUnit_one_sub_of_norm_lt_one
      (x := -relativePositionPerturbation X H kappa x z) hNeg)

/-- Under a point gap, a relative perturbation of norm below one preserves
finite-scale localizer invertibility. -/
theorem finite_scale_localizer_isUnit_of_relative_norm_lt_one
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z)
    (hSmall : ‖relativePositionPerturbation X H kappa x z‖ < 1) :
    IsUnit (finiteSpectralLocalizer X H kappa x z) :=
  (finite_scale_localizer_isUnit_iff_relative_factor_isUnit
    X H kappa x z hGap).2
      (relative_position_factor_isUnit_of_norm_lt_one
        X H kappa x z hSmall)

/-- The product bound `‖L₀⁻¹‖ ‖κ‖ ‖Dₓ‖ < 1` is a directly checkable
sufficient condition for finite-scale localizer invertibility. -/
theorem finite_scale_localizer_isUnit_of_scale_bound
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z)
    (hSmall :
      ‖(finiteSpectralLocalizer X H 0 x z)⁻¹‖ *
          (‖(kappa : ℂ)‖ * ‖positionDirection X x‖) < 1) :
    IsUnit (finiteSpectralLocalizer X H kappa x z) := by
  apply finite_scale_localizer_isUnit_of_relative_norm_lt_one
    X H kappa x z hGap
  exact
    (relative_position_perturbation_norm_le X H kappa x z).trans_lt
      hSmall

/-- A point gap supplies exact zero-scale chiral inertia and finite-scale
invertibility throughout the explicit Neumann stability budget. -/
theorem point_gap_exact_inertia_and_finite_scale_stability
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z)
    (hSmall :
      ‖(finiteSpectralLocalizer X H 0 x z)⁻¹‖ *
          (‖(kappa : ℂ)‖ * ‖positionDirection X x‖) < 1) :
    (posIndex
        (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
        Fintype.card n ∧
      negIndex
        (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
        Fintype.card n) ∧
      IsUnit (finiteSpectralLocalizer X H kappa x z) := by
  exact ⟨zero_scale_localizer_inertia_of_point_gap X H x z hGap,
    finite_scale_localizer_isUnit_of_scale_bound
      X H kappa x z hGap hSmall⟩

#print axioms position_direction_isHermitian
#print axioms finite_spectral_localizer_scale_decomposition
#print axioms finite_spectral_localizer_relative_factorization
#print axioms finite_scale_localizer_isUnit_iff_relative_factor_isUnit
#print axioms relative_position_perturbation_norm_le
#print axioms relative_position_factor_isUnit_of_norm_lt_one
#print axioms finite_scale_localizer_isUnit_of_relative_norm_lt_one
#print axioms finite_scale_localizer_isUnit_of_scale_bound
#print axioms point_gap_exact_inertia_and_finite_scale_stability

end

end D5.S3.SpectralTopology.PointGapFiniteScaleStability