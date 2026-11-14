/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCrossing
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerCollisionCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict crossings from endpoint asymptotics and logarithmic lattice density. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Endpoint asymptotics suffice to force crossings at arbitrarily late indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology

namespace D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing

private lemma eventual_log_scaled_bounds {f : ℕ → ℝ} {P c ε : ℝ}
    (hP : 0 < P) (hc : 0 < c) (hε : 0 < ε)
    (hf : Tendsto (fun n => f n * P ^ n) atTop (𝓝 c)) :
    ∀ᶠ n in atTop, 0 < f n ∧
      Real.log c - ε < Real.log (f n) + (n : ℝ) * Real.log P ∧
      Real.log (f n) + (n : ℝ) * Real.log P < Real.log c + ε := by
  have hl := (Real.continuousAt_log hc.ne').tendsto.comp hf
  have hlo := hl.eventually (eventually_gt_nhds (by linarith : Real.log c - ε < Real.log c))
  have hhi := hl.eventually (eventually_lt_nhds (by linarith : Real.log c < Real.log c + ε))
  have hp := hf.eventually (eventually_gt_nhds hc)
  filter_upwards [hp, hlo, hhi] with n hn hlo hhi
  have hfn : 0 < f n := (mul_pos_iff_of_pos_right (pow_pos hP n)).mp hn
  dsimp only [Function.comp_apply] at hlo hhi
  rw [Real.log_mul hfn.ne' (pow_pos hP n).ne', Real.log_pow] at hlo hhi
  exact ⟨hfn, hlo, hhi⟩

/-- Dense logarithmic differences turn distinct endpoint limits into strict crossings. -/
theorem collision_of_scaled_limits
    {f g : ℝ → ℕ → ℝ} {P Q α β cα cβ dα dβ : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hαβ : α < β)
    (hcα : 0 < cα) (hcβ : 0 < cβ) (hdα : 0 < dα) (hdβ : 0 < dβ)
    (hfα : Tendsto (fun n => f α n * P ^ n) atTop (𝓝 cα))
    (hfβ : Tendsto (fun n => f β n * P ^ n) atTop (𝓝 cβ))
    (hgα : Tendsto (fun n => g α n * Q ^ n) atTop (𝓝 dα))
    (hgβ : Tendsto (fun n => g β n * Q ^ n) atTop (𝓝 dβ))
    (hlog : Real.log (cα / dα) < Real.log (cβ / dβ))
    (hlattice : ∀ u v : ℝ, u < v → ∀ N : ℕ, ∃ i j : ℕ,
      N ≤ i ∧ N ≤ j ∧ u < (i : ℝ) * Real.log P - (j : ℝ) * Real.log Q ∧
      (i : ℝ) * Real.log P - (j : ℝ) * Real.log Q < v)
    (hcont : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      ContinuousOn (fun κ => f κ i - g κ j) (Icc α β))
    (M : ℕ) :
    ∃ κ ∈ Ioo α β, ∃ i j : ℕ, M ≤ i ∧ M ≤ j ∧ 1 ≤ i ∧ 1 ≤ j ∧
      f κ i = g κ j := by
  let A := Real.log cα - Real.log dα
  let B := Real.log cβ - Real.log dβ
  have hAB : A < B := by
    simpa only [A, B, Real.log_div hcα.ne' hdα.ne',
      Real.log_div hcβ.ne' hdβ.ne'] using hlog
  let ε := (B - A) / 12
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hfa := eventual_log_scaled_bounds hP hcα hε hfα
  have hfb := eventual_log_scaled_bounds hP hcβ hε hfβ
  have hga := eventual_log_scaled_bounds hQ hdα hε hgα
  have hgb := eventual_log_scaled_bounds hQ hdβ hε hgβ
  have hevent : ∀ᶠ n in atTop,
      (0 < f α n ∧ Real.log cα - ε < Real.log (f α n) + (n : ℝ) * Real.log P ∧
        Real.log (f α n) + (n : ℝ) * Real.log P < Real.log cα + ε) ∧
      (0 < f β n ∧ Real.log cβ - ε < Real.log (f β n) + (n : ℝ) * Real.log P ∧
        Real.log (f β n) + (n : ℝ) * Real.log P < Real.log cβ + ε) ∧
      (0 < g α n ∧ Real.log dα - ε < Real.log (g α n) + (n : ℝ) * Real.log Q ∧
        Real.log (g α n) + (n : ℝ) * Real.log Q < Real.log dα + ε) ∧
      (0 < g β n ∧ Real.log dβ - ε < Real.log (g β n) + (n : ℝ) * Real.log Q ∧
        Real.log (g β n) + (n : ℝ) * Real.log Q < Real.log dβ + ε) := by
    filter_upwards [hfa, hfb, hga, hgb] with n ha hb hc hd
    exact ⟨ha, hb, hc, hd⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have huv : A + 3 * ε < B - 3 * ε := by dsimp [ε]; linarith
  obtain ⟨i, j, hi, hj, hijlo, hijhi⟩ :=
    hlattice (A + 3 * ε) (B - 3 * ε) huv (max N (max M 1))
  have hiN : N ≤ i := le_trans (le_max_left _ _) hi
  have hjN : N ≤ j := le_trans (le_max_left _ _) hj
  have hiM : M ≤ i := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hi
  have hjM : M ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
  have hi1 : 1 ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hi
  have hj1 : 1 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
  rcases hN i hiN with ⟨hai, hbi, _, _⟩
  rcases hN j hjN with ⟨_, _, haj, hbj⟩
  have hsmall : f α i < g α j := by
    apply (Real.log_lt_log_iff hai.1 haj.1).mp
    dsimp [A] at hijlo
    linarith [hai.2.2, haj.2.1]
  have hlarge : g β j < f β i := by
    apply (Real.log_lt_log_iff hbj.1 hbi.1).mp
    dsimp [B] at hijhi
    linarith [hbi.2.1, hbj.2.2]
  obtain ⟨κ, hκ, hzero⟩ := intermediate_value_Ioo hαβ.le (hcont i j hi1 hj1)
    (show (0 : ℝ) ∈ Ioo (f α i - g α j) (f β i - g β j) from
      ⟨sub_neg.mpr hsmall, sub_pos.mpr hlarge⟩)
  exact ⟨κ, hκ, i, j, hiM, hjM, hi1, hj1, sub_eq_zero.mp hzero⟩

end D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing
