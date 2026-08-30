/- GID: D5/S3/Analytic/Zeta/GoldenSpectrum/ReflectionPairTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/GoldenSpectrum/ReflectionPairTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reciprocal transfer has determinant one; positive isometry occurs
     exactly at pointwise-neutral radial charge. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for a reciprocal two-channel transfer whose
     determinant-one balance is separated from pointwise isometry found no
     exact D5 owner.
   * Existing Lorentz and reflection modules use different state equations.
   * Pinned Mathlib supplies two-by-two determinant formulas and real algebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Matrix

namespace D5.S3.Analytic.Zeta.GoldenSpectrum.ReflectionPairTransfer

/-- A reflection pair with reciprocal radial charges. -/
def reflectionPairTransfer (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q, 0; 0, q⁻¹]

/-- Euclidean norm-square preservation for the corresponding two-channel
transfer. -/
def IsReflectionPairIsometry (q : ℝ) : Prop :=
  ∀ x y : ℝ,
    (q * x) ^ 2 + (q⁻¹ * y) ^ 2 = x ^ 2 + y ^ 2

/-- Reciprocal paired transfer has determinant one whenever the charge is
nonzero. -/
theorem reflection_pair_determinant_one {q : ℝ} (hq : q ≠ 0) :
    Matrix.det (reflectionPairTransfer q) = 1 := by
  simp [reflectionPairTransfer, Matrix.det_fin_two, hq]

/-- Isometry forces the growing channel itself to have unit squared charge. -/
theorem isometry_forces_charge_sq_one {q : ℝ}
    (hIso : IsReflectionPairIsometry q) :
    q ^ 2 = 1 := by
  have hBasis := hIso 1 0
  simpa using hBasis

/-- For a positive charge, paired transfer is an isometry exactly at the
pointwise-neutral value one. -/
theorem reflection_pair_isometry_iff {q : ℝ} (hq : 0 < q) :
    IsReflectionPairIsometry q ↔ q = 1 := by
  constructor
  · intro hIso
    have hSq := isometry_forces_charge_sq_one hIso
    nlinarith
  · intro hOne
    subst q
    intro x y
    simp

/-- Determinant balance alone does not imply pointwise neutrality or isometry. -/
theorem determinant_balance_not_isometry :
    Matrix.det (reflectionPairTransfer 2) = 1 ∧
      ¬ IsReflectionPairIsometry 2 := by
  constructor
  · exact reflection_pair_determinant_one (by norm_num)
  · intro hIso
    have hSq := isometry_forces_charge_sq_one hIso
    norm_num at hSq

/-- The two reciprocal channels have logarithmic charges summing to zero. -/
theorem reciprocal_pair_log_balance (q : ℝ) :
    Real.log q + Real.log q⁻¹ = 0 := by
  rw [Real.log_inv]
  ring

/-- Positive charge greater than one expands one basis channel and contracts
its reflected partner. -/
theorem hyperbolic_pair_of_one_lt {q : ℝ} (hq : 1 < q) :
    1 < q ∧ q⁻¹ < 1 := by
  exact ⟨hq, inv_lt_one_of_one_lt₀ hq⟩

/-- The neutral pair is both determinant-balanced and isometric. -/
example :
    Matrix.det (reflectionPairTransfer 1) = 1 ∧
      IsReflectionPairIsometry 1 := by
  constructor
  · exact reflection_pair_determinant_one one_ne_zero
  · exact (reflection_pair_isometry_iff zero_lt_one).2 rfl

#print axioms reflection_pair_determinant_one
#print axioms isometry_forces_charge_sq_one
#print axioms reflection_pair_isometry_iff
#print axioms determinant_balance_not_isometry
#print axioms reciprocal_pair_log_balance
#print axioms hyperbolic_pair_of_one_lt

end D5.S3.Analytic.Zeta.GoldenSpectrum.ReflectionPairTransfer
