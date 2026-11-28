/- GID: D5/S3/Geometry/UnitQuaternionCircle
   generality: G
   mirror-B: none(waiver:covered-by-circle-coefficient-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Public circle coordinates inside the whole round unit-quaternion group. -/

import D5.S3.Geometry.UnitQuaternionMetric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-! Omega original.

Public circle coordinates inside the whole round unit-quaternion group. -/

open scoped Quaternion InnerProductSpace
noncomputable section

namespace SimpleGraph.CirclePowerPath

open Real Omega.Geometry.UnitQuaternion

abbrev U := unitary ℍ[ℝ]

/-- The standard great circle in the unit round three-sphere. -/
def phase (t : ℝ) : U :=
  ofUnit ⟨cos t, sin t, 0, 0⟩ (by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
    simpa [Quaternion.normSq_def, pow_two, add_comm] using sin_sq_add_cos_sq t)

@[simp] theorem phase_re (t : ℝ) : (phase t : ℍ[ℝ]).re = cos t := rfl
@[simp] theorem phase_imI (t : ℝ) : (phase t : ℍ[ℝ]).imI = sin t := rfl
@[simp] theorem phase_imJ (t : ℝ) : (phase t : ℍ[ℝ]).imJ = 0 := rfl
@[simp] theorem phase_imK (t : ℝ) : (phase t : ℍ[ℝ]).imK = 0 := rfl

@[simp] theorem phase_zero : phase 0 = 1 := by
  apply Subtype.ext
  ext <;> simp [phase, ofUnit]

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  apply Subtype.ext
  ext <;> simp [phase, ofUnit, cos_add, sin_add] <;> ring

@[simp] theorem phase_neg (t : ℝ) : phase (-t) = (phase t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← phase_add, neg_add_cancel, phase_zero]

theorem phase_sub (s t : ℝ) : phase (s - t) = phase s * (phase t)⁻¹ := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

theorem phase_comm (s t : ℝ) : phase s * phase t = phase t * phase s := by
  rw [← phase_add, ← phase_add, add_comm]

theorem phase_injective_near_zero {t : ℝ} (ht : |t| < 2 * π)
    (h : phase t = 1) : t = 0 := by
  have hc : cos t = 1 := congrArg (fun x : U => (x : ℍ[ℝ]).re) h
  exact (cos_eq_one_iff_of_lt_of_lt (by linarith [(abs_lt.mp ht).1])
    (abs_lt.mp ht).2).mp hc

theorem phase_inner (s t : ℝ) :
    ⟪(phase s : ℍ[ℝ]), (phase t : ℍ[ℝ])⟫_ℝ = cos (s - t) := by
  simp [Quaternion.inner_def, phase, ofUnit, cos_sub]

theorem phase_dist (s t : ℝ) : roundDist (phase s) (phase t) = arccos (cos (s - t)) := by
  rw [roundDist, phase_inner]

theorem phase_dist_exact {s t : ℝ} (h : |s - t| ≤ π) :
    roundDist (phase s) (phase t) = |s - t| := by
  rw [phase_dist, ← cos_abs, arccos_cos (abs_nonneg _) h]

theorem phase_dist_le (s t : ℝ) : roundDist (phase s) (phase t) ≤ |s - t| := by
  by_cases h : |s - t| ≤ π
  · exact (phase_dist_exact h).le
  · exact (round_le_pi _ _).trans (le_of_not_ge h)

/-- A principal real representative, including the endpoint at minus one. -/
theorem exists_principal (t : ℝ) : ∃ h : ℝ, |h| ≤ π ∧ phase h = phase t ∧
    roundDist (phase t) 1 = |h| := by
  let z : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have hn : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  have hz : z ≠ 0 := by simp [z]
  have hc : cos z.arg = cos t := by
    rw [Complex.cos_arg hz, hn, div_one]
    simp [z, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hs : sin z.arg = sin t := by
    rw [Complex.sin_arg, hn, div_one]
    simp [z, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hp : phase z.arg = phase t := by
    apply Subtype.ext
    ext <;> simp [hc, hs]
  have hb : |z.arg| ≤ π := abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  refine ⟨z.arg, hb, hp, ?_⟩
  rw [← hp, ← phase_zero, phase_dist_exact (by simpa using hb)]
  simp

end SimpleGraph.CirclePowerPath
