/- GID: D5/S3/Weil/Mertens/CenteredTail
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CenteredTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Centering the original weighted prime limit cancels its logarithmic tail. -/

import D5.S3.Weil.Mertens.Third
import D5.S3.Weil.Mertens.WeightedPrimeLimit

namespace D5.S3.Weil.Mertens.CenteredTail

open Real Set MeasureTheory Filter Asymptotics
open scoped Topology
open _root_.Mertens

noncomputable section

/-- The finite weighted-prime limit cancels exactly from the original Mertens tail. -/
theorem E2p_isLittleO_inv_log :
    E₂p =o[atTop] (fun x : ℝ => 1 / log x) := by
  obtain ⟨ell, hell⟩ := WeightedPrimeLimit.exists_E1p_limit
  refine isLittleO_iff.mpr ?_
  intro c hc
  have hevent : ∀ᶠ t : ℝ in atTop, |E₁p t - ell| < c / 2 := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hell (c / 2) (half_pos hc))
  obtain ⟨B, hB⟩ := eventually_atTop.mp hevent
  filter_upwards [eventually_ge_atTop (max B 2)] with x hx
  have hx2 : 2 ≤ x := (le_max_right B 2).trans hx
  have hxB : B ≤ x := (le_max_left B 2).trans hx
  have hlog : 0 < log x := log_pos (by linarith)
  have hint : IntegrableOn
      (fun t : ℝ => (E₁p t - ell) / (t * log t ^ 2)) (Ioi x) := by
    simpa only [sub_div] using
      (integrable_E₁p_div_mul_log_sq hx2).sub
        (integrable_const_div_mul_log_sq ell hx2)
  have hcenter : E₂p x = (E₁p x - ell) / log x -
      ∫ t in Ioi x, (E₁p t - ell) / (t * log t ^ 2) := by
    simp_rw [sub_div]
    rw [integral_sub (integrable_E₁p_div_mul_log_sq hx2)
      (integrable_const_div_mul_log_sq ell hx2), integ_div_mul_log_sq ell hx2,
      E₂p.eq hx2]
    ring
  have htail : |∫ t in Ioi x, (E₁p t - ell) / (t * log t ^ 2)| ≤
      (c / 2) / log x := by
    apply abs_le.mpr
    constructor
    · have hlow := setIntegral_mono_on
        (integrable_const_div_mul_log_sq (-(c / 2)) hx2) hint measurableSet_Ioi
        (fun t ht => div_le_div_of_nonneg_right
          (abs_le.mp (hB t (hxB.trans ht.le)).le).1
          (mul_nonneg (by linarith [ht]) (sq_nonneg _)))
      rw [integ_div_mul_log_sq (-(c / 2)) hx2, neg_div] at hlow
      exact hlow
    · have hupp := setIntegral_mono_on hint
        (integrable_const_div_mul_log_sq (c / 2) hx2) measurableSet_Ioi
        (fun t ht => div_le_div_of_nonneg_right
          (abs_le.mp (hB t (hxB.trans ht.le)).le).2
          (mul_nonneg (by linarith [ht]) (sq_nonneg _)))
      rw [integ_div_mul_log_sq (c / 2) hx2] at hupp
      exact hupp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlog), hcenter]
  calc
    _ ≤ |(E₁p x - ell) / log x| +
        |∫ t in Ioi x, (E₁p t - ell) / (t * log t ^ 2)| := abs_sub _ _
    _ ≤ (c / 2) / log x + (c / 2) / log x := by
      apply add_le_add _ htail
      rw [abs_div, abs_of_pos hlog]
      exact div_le_div_of_nonneg_right (hB x hxB).le hlog.le
    _ = c * (1 / log x) := by ring

#print axioms E2p_isLittleO_inv_log

end
end D5.S3.Weil.Mertens.CenteredTail
