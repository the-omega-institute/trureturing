/- GID: D5/S3/Quantum/Subentropy/UniformIntegrals
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/UniformIntegrals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact improper integrals for the uniform two- and four-level subentropy kernels. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Improper scalar integrals for the maximally mixed subentropy kernels. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Subentropy.UniformIntegrals

open MeasureTheory Set Filter
open scoped Topology

private theorem log_difference_limit (a b : ℝ) :
    Tendsto (fun t : ℝ => Real.log (t + a) - Real.log (t + b)) atTop (𝓝 0) := by
  convert (Real.tendsto_log_comp_add_sub_log a).sub
    (Real.tendsto_log_comp_add_sub_log b) using 1 <;> simp only [sub_sub_sub_cancel_right, sub_self]

/-- Integrability and evaluation of a convergent reciprocal difference. -/
theorem reciprocal_difference (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => 1 / (t + a) - 1 / (t + b)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), 1 / (t + a) - 1 / (t + b)) = Real.log b - Real.log a := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt
      (fun t : ℝ => Real.log (t + a) - Real.log (t + b))
      (1 / (t + a) - 1 / (t + b)) t := by
    intro t ht
    have hta : 0 < t + a := by linarith [ht.out]
    have htb : 0 < t + b := by linarith
    convert (((hasDerivAt_id t).add_const a).log hta.ne').sub
      (((hasDerivAt_id t).add_const b).log htb.ne') using 1 <;> rfl
  have hp : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (t + a) - 1 / (t + b) := by
    intro t ht
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by linarith [ht.out]) (by linarith)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp (log_difference_limit a b), ?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hd hp (log_difference_limit a b)

/-- Integrability and evaluation of every shifted inverse power of order at least two. -/
theorem inverse_power (a : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun t : ℝ => 1 / (t + a) ^ (n + 2)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), 1 / (t + a) ^ (n + 2)) =
        1 / (((n : ℝ) + 1) * a ^ (n + 1)) := by
  have hexp : -((n + 2 : ℕ) : ℝ) < -1 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have heq : (fun t : ℝ => (t + a) ^ (-((n + 2 : ℕ) : ℝ))) =
      (fun t : ℝ => 1 / (t + a) ^ (n + 2)) := by
    funext t
    rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div]
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact integrableOn_add_rpow_Ioi_of_lt hexp (by linarith)
  · have hshift := (measurePreserving_add_right volume a).setIntegral_preimage_emb
      (MeasurableEquiv.addRight a).measurableEmbedding
      (fun t : ℝ => t ^ (-((n + 2 : ℕ) : ℝ))) (Ioi a)
    have hpre : (fun t : ℝ => t + a) ⁻¹' Ioi a = Ioi 0 := by
      ext t
      simp
    rw [hpre, heq, integral_Ioi_rpow_of_lt hexp ha] at hshift
    rw [hshift]
    have hpower : -((n + 2 : ℕ) : ℝ) + 1 = -((n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hpower, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
    push_cast
    field_simp

/-- The exact integral of the two-level uniform subentropy kernel. -/
theorem integral_uniformTwo_kernel :
    (∫ t in Ioi (0 : ℝ),
      1 / (t + 1 / 2) - 1 / (t + 1) - 1 / (4 * (t + 1 / 2) ^ 2)) =
      Real.log 2 - 1 / 2 := by
  obtain ⟨hd, hv⟩ := reciprocal_difference (1 / 2) 1 (by norm_num) (by norm_num)
  obtain ⟨hp, hw⟩ := inverse_power (1 / 2) (by norm_num) 0
  have heq : (fun t : ℝ =>
      1 / (t + 1 / 2) - 1 / (t + 1) - 1 / (4 * (t + 1 / 2) ^ 2)) =
      (fun t : ℝ => (1 / (t + 1 / 2) - 1 / (t + 1)) -
        (1 / 4) * (1 / (t + 1 / 2) ^ (0 + 2))) := by
    funext t
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, integral_sub hd (hp.const_mul (1 / 4)), integral_const_mul, hv, hw]
  norm_num [Real.log_div]

/-- The exact integral of the four-level uniform subentropy kernel. -/
theorem integral_uniformFour_kernel :
    (∫ t in Ioi (0 : ℝ),
      1 / (t + 1 / 4) - 1 / (t + 1) - 3 / (8 * (t + 1 / 4) ^ 2) +
        1 / (16 * (t + 1 / 4) ^ 3) - 1 / (256 * (t + 1 / 4) ^ 4)) =
      Real.log 4 - 13 / 12 := by
  obtain ⟨hd, hv⟩ := reciprocal_difference (1 / 4) 1 (by norm_num) (by norm_num)
  obtain ⟨h₂, v₂⟩ := inverse_power (1 / 4) (by norm_num) 0
  obtain ⟨h₃, v₃⟩ := inverse_power (1 / 4) (by norm_num) 1
  obtain ⟨h₄, v₄⟩ := inverse_power (1 / 4) (by norm_num) 2
  have heq : (fun t : ℝ =>
      1 / (t + 1 / 4) - 1 / (t + 1) - 3 / (8 * (t + 1 / 4) ^ 2) +
        1 / (16 * (t + 1 / 4) ^ 3) - 1 / (256 * (t + 1 / 4) ^ 4)) =
      (fun t : ℝ => ((1 / (t + 1 / 4) - 1 / (t + 1)) -
        (3 / 8) * (1 / (t + 1 / 4) ^ (0 + 2))) +
        (1 / 16) * (1 / (t + 1 / 4) ^ (1 + 2)) -
        (1 / 256) * (1 / (t + 1 / 4) ^ (2 + 2))) := by
    funext t
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hi := integral_sub
    ((hd.sub (h₂.const_mul (3 / 8))).add (h₃.const_mul (1 / 16)))
    (h₄.const_mul (1 / 256))
  have hj := integral_add (hd.sub (h₂.const_mul (3 / 8))) (h₃.const_mul (1 / 16))
  have hk := integral_sub hd (h₂.const_mul (3 / 8))
  simp only [Pi.add_apply, Pi.sub_apply] at hi hj hk
  rw [heq, hi, hj, hk, integral_const_mul, integral_const_mul, integral_const_mul,
    hv, v₂, v₃, v₄]
  norm_num [Real.log_div]
  ring

end D5.S3.Quantum.Subentropy.UniformIntegrals
