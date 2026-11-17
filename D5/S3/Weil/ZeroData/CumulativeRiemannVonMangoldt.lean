/- GID: D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cumulative positive zeta zero count has its classical leading constant. -/

import D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness

/-! Cumulative counting asymptotics for the canonical zeta zero configuration. -/

set_option autoImplicit false

namespace D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt

open Filter
open scoped Topology
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness

/-- The multiplicity-weighted positive zeta zero count has leading term
`T * log T / (2 * pi)`, unconditionally. -/
theorem cumulative_count_asymptotic :
    Filter.Tendsto
      (fun T : ℝ => (Zeta23.zetaZeroConfig.N 0 T : ℝ) / (T * Real.log T))
      Filter.atTop (nhds (1 / (2 * Real.pi))) := by
  obtain ⟨U, D, hU, hD, hcount⟩ := zeta_cumulative_count_coarse
  have hzero : Tendsto (fun T : ℝ => D / Real.log T) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul D
  have herr : Tendsto
      (fun T : ℝ => (Zeta23.zetaZeroConfig.N 0 T : ℝ) / (T * Real.log T) -
        1 / (2 * Real.pi)) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop U] with T hT
    have hT0 : 0 < T := (zero_lt_one.trans hU).trans_le hT
    have hlog : 0 < Real.log T := Real.log_pos (hU.trans_le hT)
    have hquot : (Zeta23.zetaZeroConfig.N 0 T : ℝ) / (T * Real.log T) -
        1 / (2 * Real.pi) =
        ((Zeta23.zetaZeroConfig.N 0 T : ℝ) -
          (1 / (2 * Real.pi)) * T * Real.log T) / (T * Real.log T) := by
      field_simp
    rw [Real.norm_eq_abs, hquot, abs_div, abs_of_pos (mul_pos hT0 hlog)]
    calc
      _ ≤ D * T / (T * Real.log T) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hT0 hlog).le
        simpa only [Zeta23.zetaZeroConfig_N] using hcount T hT
      _ = D / Real.log T := by field_simp
  simpa only [zero_add, sub_add_cancel] using
    herr.add_const (1 / (2 * Real.pi))

end D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt
