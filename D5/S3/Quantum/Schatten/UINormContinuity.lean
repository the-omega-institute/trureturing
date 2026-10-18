/- GID: D5/S3/Quantum/Schatten/UINormContinuity
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/UINormContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of unitarily invariant norms and balanced scalar optimization. -/

import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Matrix.Normed

/-! Continuity and scalar balancing for finite matrix norms. -/

noncomputable section

namespace D5.S3.Quantum.Schatten.UINorm

open Matrix

set_option maxHeartbeats 1000000 in
-- Finite-dimensional convex continuity elaborates the matrix space through two Pi layers.
/-- Every unitarily invariant norm is continuous for the usual finite matrix topology. -/
theorem continuous_N {n : ℕ} (ν : UINorm n) : Continuous ν.N := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  have hconv : ConvexOn ℝ Set.univ ν.N := by
    refine ⟨convex_univ, ?_⟩
    intro X _ Y _ a b ha hb _
    have hreal (c : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (hc : 0 ≤ c) :
        ν.N (c • X) = c * ν.N X := by
      have heq : c • X = (c : ℂ) • X := by
        ext i j
        simp [Complex.real_smul]
      rw [heq, ν.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      ν.N (a • X + b • Y) ≤ ν.N (a • X) + ν.N (b • Y) := ν.add_le _ _
      _ = a * ν.N X + b * ν.N Y := by rw [hreal a X ha, hreal b Y hb]
  exact continuousOn_univ.mp
    (ConvexOn.continuousOn (E := Matrix (Fin n) (Fin n) ℂ) isOpen_univ hconv)

/-- Optimization of all balanced positive scalar tests, including vanishing factors. -/
theorem sq_le_mul_of_balanced_bounds (m f g : ℝ) (hm : 0 ≤ m) (hf : 0 ≤ f)
    (hg : 0 ≤ g) (h : ∀ t : ℝ, 0 < t → 2 * m ≤ t * f + t⁻¹ * g) :
    m ^ 2 ≤ f * g := by
  by_cases hm0 : m = 0
  · subst m
    simpa using mul_nonneg hf hg
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  by_cases hf0 : f = 0
  · subst f
    have ht : 0 < (g + 1) / m := div_pos (by linarith) hmpos
    have hh := h ((g + 1) / m) ht
    rw [mul_zero, zero_add, inv_div] at hh
    have hh' := (le_div_iff₀ (show 0 < g + 1 by linarith)).mp
      (show 2 * m ≤ m * g / (g + 1) by simpa [div_mul_eq_mul_div] using hh)
    nlinarith
  · have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hf0)
    have hh := h (m / f) (div_pos hmpos hfpos)
    rw [div_mul_cancel₀ _ hf0, inv_div] at hh
    have hh' := (le_div_iff₀ hmpos).mp
      (show m ≤ f * g / m by
        have : 2 * m ≤ m + f * g / m := by simpa [div_mul_eq_mul_div] using hh
        linarith)
    nlinarith

end D5.S3.Quantum.Schatten.UINorm
