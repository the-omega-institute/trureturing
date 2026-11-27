/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedPrimePowers
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedPrimePowers
   mirror-E: none(waiver:analytic-prime-power-estimate)
   anchors: []
   utility: none
   digest: The weighted prime-power bound includes the critical weight index one. -/

import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel

/-! The Chebyshev root bounds transport directly to the native Robin weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
open D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel
  (B B_real P centered_prime_power_weight weight_nonneg)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedPrimePowers

private lemma weight_measurable (j : ℝ) : Measurable (weight j) := by
  unfold weight H
  fun_prop

private lemma power_integrable {j p x : ℝ} (hj : 0 ≤ j) (hp : p < j) (hx : 1 < x) :
    IntegrableOn (fun t => t ^ p * weight j t) (Ioi x) := by
  simpa only [Real.exp_log (zero_lt_one.trans hx)] using
    (B_real hj hp (Real.log_pos hx)).1

private lemma root_integrable {j p x : ℝ} (hj : 0 ≤ j) (hp : p < j) (hx : 1 < x) :
    IntegrableOn (fun t => Chebyshev.psi (t ^ p) * weight j t) (Ioi x) := by
  have hx0 := zero_lt_one.trans hx
  have hm : Measurable (fun t : ℝ => t ^ p) := by fun_prop
  apply ((power_integrable hj hp hx).const_mul (Real.log 4 + 4)).mono'
  · exact ((Chebyshev.psi_mono.measurable.comp hm).mul
      (weight_measurable j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw := weight_nonneg hj (hx.trans ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.psi_nonneg _) hw)]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right
        (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (hx0.trans ht).le p)) hw

private lemma root_eq {j r x : ℝ}
    (hj : 0 ≤ j) (hr : 0 < r) (hp : r⁻¹ < j) (hx : 1 < x) :
    (∫ t in Ioi x, Chebyshev.psi (t ^ r⁻¹) * weight j t) =
      B j r⁻¹ (Real.log x) + r⁻¹ * J (r * j) (x ^ r⁻¹) := by
  have heq : ∀ t : ℝ, Chebyshev.psi (t ^ r⁻¹) * weight j t -
      t ^ r⁻¹ * weight j t = (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) * weight j t :=
    fun t => (sub_mul _ _ _).symm
  have he := integral_sub (root_integrable hj hp hx) (power_integrable hj hp hx)
  simp only [heq] at he
  have hmain := (B_real hj hp (Real.log_pos hx)).2
  rw [Real.exp_log (zero_lt_one.trans hx)] at hmain
  rw [centered_prime_power_weight hr hx, ← hmain, one_div] at he
  linarith

/-- The weighted correction is bounded by the actual square, cube and
fifth-root responses. All integrals extend to infinity. The pointwise
inequality is due to Costa Pereira, as reproduced in Broadbent et al.,
arXiv:2002.11068v2, equation (3.16). -/
theorem powerCorrection_le_roots {j x : ℝ} (hj : 1 ≤ j) (hx : 1 < x) :
    P j x ≤
      (B j (2 : ℝ)⁻¹ (Real.log x) + (2 : ℝ)⁻¹ * J (2 * j) (x ^ (2 : ℝ)⁻¹)) +
      (B j (3 : ℝ)⁻¹ (Real.log x) + (3 : ℝ)⁻¹ * J (3 * j) (x ^ (3 : ℝ)⁻¹)) +
      (B j (5 : ℝ)⁻¹ (Real.log x) + (5 : ℝ)⁻¹ * J (5 * j) (x ^ (5 : ℝ)⁻¹)) := by
  let f (r t : ℝ) := Chebyshev.psi (t ^ r⁻¹) * weight j t
  have hj0 : 0 ≤ j := by linarith
  have h2 : (2 : ℝ)⁻¹ < j := (by norm_num : (2 : ℝ)⁻¹ < 1).trans_le hj
  have h3 : (3 : ℝ)⁻¹ < j := (by norm_num : (3 : ℝ)⁻¹ < 1).trans_le hj
  have h5 : (5 : ℝ)⁻¹ < j := (by norm_num : (5 : ℝ)⁻¹ < 1).trans_le hj
  have hi2 : IntegrableOn (f 2) (Ioi x) := root_integrable hj0 h2 hx
  have hi3 : IntegrableOn (f 3) (Ioi x) := root_integrable hj0 h3 hx
  have hi5 : IntegrableOn (f 5) (Ioi x) := root_integrable hj0 h5 hx
  have hSum : IntegrableOn (fun t => f 2 t + f 3 t + f 5 t) (Ioi x) :=
    (hi2.add hi3).add hi5
  have hPoint (t : ℝ) (ht : x < t) :
      0 ≤ (Chebyshev.psi t - Chebyshev.theta t) * weight j t ∧
      (Chebyshev.psi t - Chebyshev.theta t) * weight j t ≤
        f 2 t + f 3 t + f 5 t := by
    have hw := weight_nonneg hj0 (hx.trans ht)
    refine ⟨mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) hw, ?_⟩
    simpa only [f, add_mul] using mul_le_mul_of_nonneg_right
      (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t) hw
  have hCorrection : IntegrableOn
      (fun t => (Chebyshev.psi t - Chebyshev.theta t) * weight j t) (Ioi x) := by
    apply hSum.mono'
    · exact ((Chebyshev.psi_mono.measurable.sub
        Chebyshev.theta_mono.measurable).mul (weight_measurable j)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hPoint t ht).1]
      exact (hPoint t ht).2
  have hbound := setIntegral_mono_on hCorrection hSum measurableSet_Ioi
    (fun t ht => (hPoint t ht).2)
  change P j x ≤ (∫ t in Ioi x, ((f 2 + f 3) t + f 5 t)) at hbound
  rw [integral_add (hi2.add hi3) hi5] at hbound
  change P j x ≤
    (∫ t in Ioi x, f 2 t + f 3 t) + (∫ t in Ioi x, f 5 t) at hbound
  rw [integral_add hi2 hi3] at hbound
  dsimp only [f] at hbound
  rw [root_eq hj0 (by norm_num) h2 hx, root_eq hj0 (by norm_num) h3 hx,
    root_eq hj0 (by norm_num) h5 hx] at hbound
  exact hbound

#print axioms powerCorrection_le_roots

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedPrimePowers
