/- GID: D5/S3/Quantum/AURICOmega/UnitQuaternionPolar
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/UnitQuaternionPolar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every unit quaternion is cos t + sin t n with n a unit imaginary, and de Moivre holds. -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Complex.Module

/-! Polar form of unit quaternions.

A unit quaternion `q` is `cos θ + sin θ • n` with `θ = arccos (re q)` and `n` a unit imaginary
quaternion: the real part of `q` is `cos θ` and the imaginary part has norm `√(1 - re q ^ 2)`,
which is `sin θ`. A unit imaginary quaternion `n` squares to `-1`, so `z ↦ re z + im z • n` is a
real algebra map from the complex numbers sending `exp (t * I)` to `cos t + sin t • n`; de Moivre's
formula is the image of `exp (k * x) = exp x ^ k`. -/

open scoped Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.UnitQuaternionPolar

/-- Polar form: a unit quaternion is `cos θ + sin θ • n` with `θ = arccos (re q)` and `n` a unit
imaginary quaternion. -/
theorem exists_eq_cos_arccos_add_sin_smul (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    ∃ n : ℍ[ℝ], n.re = 0 ∧ ‖n‖ = 1 ∧
      q = ((Real.cos (Real.arccos q.re) : ℝ) : ℍ[ℝ]) + Real.sin (Real.arccos q.re) • n := by
  have hsplit : ‖q.im‖ ^ 2 = 1 - q.re ^ 2 := by
    have h1 : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hq, one_mul]
    rw [Quaternion.normSq_def'] at h1
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    change 0 ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 - q.re ^ 2
    change q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 at h1
    linear_combination h1
  have hre : q.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖q.im‖]
  have hcos : Real.cos (Real.arccos q.re) = q.re :=
    Real.cos_arccos (by nlinarith [sq_nonneg (q.re + 1)]) (by nlinarith [sq_nonneg (q.re - 1)])
  have hsin : Real.sin (Real.arccos q.re) = ‖q.im‖ := by
    rw [Real.sin_arccos, ← hsplit, Real.sqrt_sq (norm_nonneg _)]
  rw [hcos, hsin]
  by_cases h0 : q.im = 0
  · refine ⟨⟨0, 1, 0, 0⟩, rfl, ?_, ?_⟩
    · have h : ‖(⟨0, 1, 0, 0⟩ : ℍ[ℝ])‖ * ‖(⟨0, 1, 0, 0⟩ : ℍ[ℝ])‖ = 1 := by
        rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
        norm_num
      nlinarith [norm_nonneg (⟨0, 1, 0, 0⟩ : ℍ[ℝ])]
    · rw [h0, norm_zero, zero_smul, add_zero]
      conv_lhs => rw [← Quaternion.re_add_im q, h0, add_zero]
  · have hn0 : ‖q.im‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    refine ⟨‖q.im‖⁻¹ • q.im, ?_, ?_, ?_⟩
    · rw [Quaternion.re_smul, Quaternion.re_im, smul_zero]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn0]
    · rw [smul_smul, mul_inv_cancel₀ hn0, one_smul, Quaternion.re_add_im]

/-- De Moivre's formula for a unit imaginary quaternion `n`: the real algebra map from the complex
numbers sending `I` to `n` carries `exp (t * I)` to `cos t + sin t • n`, and
`exp (k * (t * I)) = exp (t * I) ^ k`. -/
theorem cos_add_sin_smul_pow (n : ℍ[ℝ]) (hre : n.re = 0) (hn : ‖n‖ = 1) (θ : ℝ) (k : ℕ) :
    (((Real.cos θ : ℝ) : ℍ[ℝ]) + Real.sin θ • n) ^ k =
      ((Real.cos (k * θ) : ℝ) : ℍ[ℝ]) + Real.sin (k * θ) • n := by
  have hsq : n * n = -1 := by
    rw [← sq, Quaternion.sq_eq_neg_normSq.mpr hre, Quaternion.normSq_eq_norm_mul_self, hn,
      mul_one, Quaternion.coe_one]
  have e : ∀ t : ℝ, ((Real.cos t : ℝ) : ℍ[ℝ]) + Real.sin t • n =
      Complex.liftAux n hsq (Complex.exp (t * Complex.I)) := fun t => by
    rw [Complex.liftAux_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]; rfl
  rw [e, e, ← map_pow, ← Complex.exp_nat_mul, Complex.ofReal_mul, Complex.ofReal_natCast,
    mul_assoc]

end D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
