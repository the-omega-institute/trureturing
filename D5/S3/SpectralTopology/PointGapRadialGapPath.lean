/- GID: D5/S3/SpectralTopology/PointGapRadialGapPath
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/PointGapRadialGapPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A point-gap norm budget keeps the whole radial localizer path invertible. -/

import D5.S3.SpectralTopology.PointGapFiniteScaleStability

/-!
# Radial gap paths for finite spectral localizers

The finite-scale stability theorem controls one endpoint `Lκ` through the
Neumann budget

`‖L₀⁻¹‖ * ‖κ‖ * ‖Dₓ‖ < 1`.

This node promotes that endpoint estimate to the entire radial path

`L(t) = L(tκ)`,  `0 ≤ t ≤ 1`.

The key observation is that the budget is monotone under radial contraction:

`budget(tκ) ≤ budget(κ)`.

Consequently the admissible scale region is star-shaped about zero, every
radial segment inside the explicit budget stays in the invertible Hermitian
locus, and any gap closure on such a segment forces the endpoint budget to be
at least one. Combining the path certificate with the existing point-gap
counting theorem records exact zero-scale inertia at the initial endpoint.

The node does not yet identify the positive and negative inertia at every
nonzero scale. That requires a separate inertia-continuation theorem on the
finite Hermitian invertible locus.
-/

/- Library-search audit trail (2026-09-03):
   * `PointGapFiniteScaleStability` owns the finite-scale Neumann criterion
     and the position direction.
   * `PointGapExactInertia` owns exact zero-scale chiral inertia under a point
     gap.
   * Repository search found no owner for the radial localizer path, the
     star-shaped admissible scale set, or the necessary budget condition for a
     radial gap closure.
   * Pinned Mathlib supplies norm identities for real scalars embedded in
     `ℂ`, interval membership, and ordered multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace D5.S3.SpectralTopology.PointGapRadialGapPath

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer
open D5.S3.SpectralTopology.PointGapExactInertia
open D5.S3.SpectralTopology.PointGapFiniteScaleStability

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The explicit Neumann budget attached to one real localizer scale. -/
def scaleGapBudget
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) : ℝ :=
  ‖(finiteSpectralLocalizer X H 0 x z)⁻¹‖ *
    (‖(kappa : ℂ)‖ * ‖positionDirection X x‖)

/-- A scale is admissible when the spectral shift has a point gap and its
explicit Neumann budget is strictly below one. -/
def IsAdmissibleScale
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) : Prop :=
  HasPointGap H z ∧ scaleGapBudget X H kappa x z < 1

/-- The radial path from the zero-scale localizer to the scale-`kappa`
localizer. -/
def radialLocalizer
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) (t : ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  finiteSpectralLocalizer X H (t * kappa) x z

/-- The zero scale consumes no Neumann budget. -/
theorem scale_gap_budget_zero
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ) :
    scaleGapBudget X H 0 x z = 0 := by
  simp [scaleGapBudget]

private theorem norm_real_scale_le
    (t kappa : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t * kappa : ℝ) : ℂ)‖ ≤ ‖(kappa : ℂ)‖ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ht0, one_mul] using
      mul_le_mul_of_nonneg_right ht1 (abs_nonneg kappa)

/-- Contracting a real scale along the unit interval cannot increase its gap
budget. -/
theorem radial_scale_gap_budget_le
    (X H : Matrix n n ℂ) (kappa x t : ℝ) (z : ℂ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    scaleGapBudget X H (t * kappa) x z ≤
      scaleGapBudget X H kappa x z := by
  unfold scaleGapBudget
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (norm_real_scale_le t kappa ht0 ht1)
    (norm_nonneg (positionDirection X x))

/-- Under a point gap the zero scale is always admissible. -/
theorem admissible_scale_zero
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z) :
    IsAdmissibleScale X H 0 x z := by
  exact ⟨hGap, by simp [scaleGapBudget]⟩

/-- The admissible scale set is star-shaped about zero. -/
theorem admissible_scale_radial
    (X H : Matrix n n ℂ) (kappa x t : ℝ) (z : ℂ)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsAdmissibleScale X H (t * kappa) x z := by
  exact ⟨hAdmissible.1,
    (radial_scale_gap_budget_le X H kappa x t z ht0 ht1).trans_lt
      hAdmissible.2⟩

/-- The radial localizer is the affine zero-scale localizer plus the scaled
position direction. -/
theorem radial_localizer_affine
    (X H : Matrix n n ℂ) (kappa x t : ℝ) (z : ℂ) :
    radialLocalizer X H kappa x z t =
      finiteSpectralLocalizer X H 0 x z +
        ((t * kappa : ℝ) : ℂ) • positionDirection X x := by
  simpa only [radialLocalizer] using
    finite_spectral_localizer_scale_decomposition
      X H (t * kappa) x z

/-- The radial path starts at the zero-scale localizer. -/
@[simp]
theorem radial_localizer_zero
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    radialLocalizer X H kappa x z 0 =
      finiteSpectralLocalizer X H 0 x z := by
  simp [radialLocalizer]

/-- The radial path ends at the requested finite scale. -/
@[simp]
theorem radial_localizer_one
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ) :
    radialLocalizer X H kappa x z 1 =
      finiteSpectralLocalizer X H kappa x z := by
  simp [radialLocalizer]

/-- A Hermitian position observable makes every radial-path matrix
Hermitian. -/
theorem radial_localizer_isHermitian
    (X H : Matrix n n ℂ) (kappa x t : ℝ) (z : ℂ)
    (hX : X.IsHermitian) :
    (radialLocalizer X H kappa x z t).IsHermitian := by
  simpa only [radialLocalizer] using
    finite_spectral_localizer_isHermitian X H (t * kappa) x z hX

/-- Every point on an admissible radial segment is invertible. -/
theorem radial_localizer_isUnit
    (X H : Matrix n n ℂ) (kappa x t : ℝ) (z : ℂ)
    (hAdmissible : IsAdmissibleScale X H kappa x z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (radialLocalizer X H kappa x z t) := by
  unfold radialLocalizer
  apply finite_scale_localizer_isUnit_of_scale_bound
    X H (t * kappa) x z hAdmissible.1
  simpa only [scaleGapBudget] using
    (radial_scale_gap_budget_le X H kappa x t z ht.1 ht.2).trans_lt
      hAdmissible.2

/-- An admissible scale supplies a Hermitian invertible path on the whole unit
interval. -/
theorem radial_hermitian_gap_path
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (radialLocalizer X H kappa x z t).IsHermitian ∧
        IsUnit (radialLocalizer X H kappa x z t) := by
  intro t ht
  exact ⟨radial_localizer_isHermitian X H kappa x t z hX,
    radial_localizer_isUnit X H kappa x t z hAdmissible ht⟩

/-- If a finite-scale localizer closes its gap despite a point gap at zero
scale, its explicit Neumann budget must be at least one. -/
theorem one_le_scale_gap_budget_of_gap_closure
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z)
    (hClosed : ¬ IsUnit (finiteSpectralLocalizer X H kappa x z)) :
    1 ≤ scaleGapBudget X H kappa x z := by
  by_contra hBudget
  have hSmall : scaleGapBudget X H kappa x z < 1 :=
    lt_of_not_ge hBudget
  apply hClosed
  apply finite_scale_localizer_isUnit_of_scale_bound X H kappa x z hGap
  simpa only [scaleGapBudget] using hSmall

/-- A gap closure anywhere on a radial unit segment forces the endpoint budget
to be at least one. -/
theorem one_le_endpoint_budget_of_radial_gap_closure
    (X H : Matrix n n ℂ) (kappa x t : ℝ) (z : ℂ)
    (hGap : HasPointGap H z)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hClosed : ¬ IsUnit (radialLocalizer X H kappa x z t)) :
    1 ≤ scaleGapBudget X H kappa x z := by
  have hScaled : 1 ≤ scaleGapBudget X H (t * kappa) x z := by
    apply one_le_scale_gap_budget_of_gap_closure X H (t * kappa) x z hGap
    simpa only [radialLocalizer] using hClosed
  exact hScaled.trans
    (radial_scale_gap_budget_le X H kappa x t z ht.1 ht.2)

/-- A point gap gives exact initial chiral inertia together with a Hermitian
invertible path to every admissible finite scale. -/
theorem point_gap_exact_inertia_and_radial_gap_path
    (X H : Matrix n n ℂ) (kappa x : ℝ) (z : ℂ)
    (hX : X.IsHermitian)
    (hAdmissible : IsAdmissibleScale X H kappa x z) :
    (posIndex
        (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
        Fintype.card n ∧
      negIndex
        (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
        Fintype.card n) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (radialLocalizer X H kappa x z t).IsHermitian ∧
          IsUnit (radialLocalizer X H kappa x z t) := by
  exact ⟨zero_scale_localizer_inertia_of_point_gap
      X H x z hAdmissible.1,
    radial_hermitian_gap_path X H kappa x z hX hAdmissible⟩

#print axioms scale_gap_budget_zero
#print axioms radial_scale_gap_budget_le
#print axioms admissible_scale_zero
#print axioms admissible_scale_radial
#print axioms radial_localizer_affine
#print axioms radial_localizer_zero
#print axioms radial_localizer_one
#print axioms radial_localizer_isHermitian
#print axioms radial_localizer_isUnit
#print axioms radial_hermitian_gap_path
#print axioms one_le_scale_gap_budget_of_gap_closure
#print axioms one_le_endpoint_budget_of_radial_gap_closure
#print axioms point_gap_exact_inertia_and_radial_gap_path

end

end D5.S3.SpectralTopology.PointGapRadialGapPath