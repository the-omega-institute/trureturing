/- GID: D5/S0/Asymptotics/NamingRate/LogarithmicMargin
   generality: G
   mirror-B: D5/B/S0/Asymptotics/NamingRate/LogarithmicMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A logarithmic error eventually leaves a strict quarter-scale linear margin. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter
open scoped Topology

namespace D5.S0.Asymptotics.NamingRate.LogarithmicMargin

/-- An `O(log n)` error is eventually strictly smaller than the gap between
`n / 2` and `n / 4`. -/
theorem logarithmic_error_eventually_leaves_quarter_margin
    (error : ℕ → ℝ)
    (herror : error =O[atTop] fun n : ℕ => Real.log n) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 - error n > (n : ℝ) / 4 := by
  have hlog :
      (fun n : ℕ => Real.log n) =o[atTop] fun n : ℕ => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hsmall := herror.trans_isLittleO hlog
  filter_upwards
    [hsmall.bound (show (0 : ℝ) < 1 / 8 by norm_num), eventually_gt_atTop 0]
      with n hn hn_pos
  have hn_pos_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have herror_le : error n ≤ (1 / 8 : ℝ) * n := by
    calc
      error n ≤ ‖error n‖ := Real.le_norm_self _
      _ ≤ (1 / 8 : ℝ) * ‖(n : ℝ)‖ := hn
      _ = (1 / 8 : ℝ) * n := by rw [Real.norm_of_nonneg hn_pos_real.le]
  linarith

#print axioms logarithmic_error_eventually_leaves_quarter_margin

end D5.S0.Asymptotics.NamingRate.LogarithmicMargin
