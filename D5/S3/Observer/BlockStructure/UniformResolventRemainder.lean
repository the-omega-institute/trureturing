/- GID: D5/S3/Observer/BlockStructure/UniformResolventRemainder
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/UniformResolventRemainder
   mirror-E: none(waiver:general-matrix-family)
   anchors: []
   utility: none
   digest: Spectral lower bounds give dimension-independent quadratic resolvent errors. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Tactic

namespace D5.S3.Observer.BlockStructure.UniformResolventRemainder

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive spectral floor bounds the actual inverse in the Euclidean operator norm. -/
theorem inverse_control_of_lower_bound (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {c : ℝ} (hc : 0 < c) (hfloor : c • (1 : Matrix ι ι ℝ) ≤ A) :
    IsUnit A ∧ ‖A⁻¹‖ ≤ c⁻¹ := by
  have hs : ∀ x ∈ spectrum ℝ A, c ≤ x := by
    apply (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) hA).mp
    simpa only [Algebra.algebraMap_eq_smul_one] using hfloor
  have hu : IsUnit A := (spectrum.zero_notMem_iff ℝ).mp fun hz =>
    (not_le_of_gt hc) (hs 0 hz)
  refine ⟨hu, ?_⟩
  rw [Matrix.nonsing_inv_eq_ringInverse, ← cfc_ringInverse_id (R := ℝ) A hu hA]
  apply norm_cfc_le (inv_nonneg.mpr hc.le)
  intro x hx
  have hcx := hs x hx
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (hc.le.trans hcx))]
  simpa only [one_div] using one_div_le_one_div_of_le hc hcx

/-- A symmetric perturbation of spectral norm at most one leaves a spectral floor of one. -/
theorem perturbed_lower_bound (A E : Matrix ι ι ℝ)
    (hfloor : (2 : ℝ) • (1 : Matrix ι ι ℝ) ≤ A)
    (hE : E.IsHermitian) (hsmall : ‖E‖ ≤ 1) :
    (1 : Matrix ι ι ℝ) ≤ A + E := by
  have he : (-1 : ℝ) • (1 : Matrix ι ι ℝ) ≤ E := by
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) hE).mpr
    intro x hx
    have hn : ‖x‖ ≤ 1 :=
      (IsometricContinuousFunctionalCalculus.norm_spectrum_le E hx hE).trans hsmall
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hn)).1
  simpa only [← add_smul, show (2 : ℝ) + -1 = 1 by norm_num, one_smul] using
    add_le_add hfloor he

/-- The two inverse bounds use constants independent of the finite index type. -/
theorem inverse_bounds (A E : Matrix ι ι ℝ) (hA : A.IsHermitian) (hE : E.IsHermitian)
    (hfloor : (2 : ℝ) • (1 : Matrix ι ι ℝ) ≤ A) (hsmall : ‖E‖ ≤ 1) :
    ‖A⁻¹‖ ≤ 1 / 2 ∧ ‖(A + E)⁻¹‖ ≤ 1 := by
  constructor
  · simpa only [one_div] using
      (inverse_control_of_lower_bound A hA (by norm_num : (0 : ℝ) < 2) hfloor).2
  · have hf : (1 : ℝ) • (1 : Matrix ι ι ℝ) ≤ A + E := by
      simpa only [one_smul] using perturbed_lower_bound A E hfloor hE hsmall
    simpa only [inv_one] using
      (inverse_control_of_lower_bound (A + E) (hA.add hE) zero_lt_one hf).2

/-- The five-factor exact resolvent remainder has uniform quadratic constant one quarter. -/
theorem remainder_bound (A E : Matrix ι ι ℝ) (hA : A.IsHermitian) (hE : E.IsHermitian)
    (hfloor : (2 : ℝ) • (1 : Matrix ι ι ℝ) ≤ A) (hsmall : ‖E‖ ≤ 1) :
    ‖A⁻¹ * E * A⁻¹ * E * (A + E)⁻¹‖ ≤ ‖E‖ ^ 2 / 4 := by
  obtain ⟨ha, hae⟩ := inverse_bounds A E hA hE hfloor hsmall
  calc
    _ ≤ ‖A⁻¹‖ * ‖E‖ * ‖A⁻¹‖ * ‖E‖ * ‖(A + E)⁻¹‖ := by
      apply (Matrix.l2_opNorm_mul _ _).trans
      gcongr
      apply (Matrix.l2_opNorm_mul _ _).trans
      gcongr
      apply (Matrix.l2_opNorm_mul _ _).trans
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 / 2 : ℝ) * ‖E‖ * (1 / 2) * ‖E‖ * 1 := by gcongr
    _ = _ := by ring

#print axioms inverse_control_of_lower_bound
#print axioms perturbed_lower_bound
#print axioms inverse_bounds
#print axioms remainder_bound

end

end D5.S3.Observer.BlockStructure.UniformResolventRemainder
