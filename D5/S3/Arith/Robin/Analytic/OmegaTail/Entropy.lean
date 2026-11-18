/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Entropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy asymptotics of binomial coefficients with moving interior proportions. -/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy

private lemma log_choose_identity {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    log (n.choose k : ℝ) = (n : ℝ) * binEntropy ((k : ℝ) / n) +
      (log (Stirling.stirlingSeq n) - log (Stirling.stirlingSeq k) -
        log (Stirling.stirlingSeq (n - k))) +
      (1 / 2 : ℝ) * (log (2 * (n : ℝ)) - log (2 * (k : ℝ)) -
        log (2 * ((n - k : ℕ) : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hjR : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hkn
  have hj : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub hkn.le
  have hq : 1 - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n := by
    rw [hj]; field_simp
  rw [Nat.cast_choose ℝ hkn.le,
    log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  simp only [binEntropy, log_inv, hq, log_div hkR.ne' hnR.ne',
    log_div hjR.ne' hnR.ne', Stirling.log_stirlingSeq_formula,
    log_div hnR.ne' (exp_pos 1).ne', log_div hkR.ne' (exp_pos 1).ne',
    log_div hjR.ne' (exp_pos 1).ne', log_exp]
  rw [hj]
  field_simp
  <;> ring

/-- The logarithm of a binomial coefficient per trial converges to binary entropy
when its selected proportion converges to an interior point. -/
private theorem log_choose_limit {α : Type*} {l : Filter α} (n k : α → ℕ) {q : ℝ}
    (hn : Tendsto n l atTop) (hq0 : 0 < q) (hq1 : q < 1)
    (hq : Tendsto (fun x => (k x : ℝ) / n x) l (𝓝 q)) :
    Tendsto (fun x => log ((n x).choose (k x) : ℝ) / n x) l (𝓝 (binEntropy q)) := by
  have hnR : Tendsto (fun x => (n x : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have hnp := hn.eventually (eventually_gt_atTop 0)
  have hki : ∀ᶠ x in l, 0 < k x ∧ k x < n x := by
    filter_upwards [hnp, hq.eventually (lt_mem_nhds hq0),
      hq.eventually (gt_mem_nhds hq1)] with x hn0 hk0 hk1
    have hn0R : (0 : ℝ) < n x := by exact_mod_cast hn0
    exact ⟨by exact_mod_cast (div_pos_iff_of_pos_right hn0R).mp hk0,
      by exact_mod_cast (div_lt_one hn0R).mp hk1⟩
  have hkR : Tendsto (fun x => (k x : ℝ)) l atTop := by
    apply (hnR.atTop_mul_pos hq0 hq).congr'
    filter_upwards [hnp] with x hx
    exact mul_div_cancel₀ _ (by exact_mod_cast hx.ne' : (n x : ℝ) ≠ 0)
  have hk : Tendsto k l atTop := tendsto_natCast_atTop_iff.mp hkR
  have hjq : Tendsto (fun x => ((n x - k x : ℕ) : ℝ) / n x) l (𝓝 (1 - q)) := by
    apply (tendsto_const_nhds.sub hq).congr'
    filter_upwards [hnp, hki] with x hn0 hk0
    rw [Nat.cast_sub hk0.2.le]
    field_simp
  have hjR : Tendsto (fun x => ((n x - k x : ℕ) : ℝ)) l atTop := by
    apply (hnR.atTop_mul_pos (sub_pos.mpr hq1) hjq).congr'
    filter_upwards [hnp] with x hx
    exact mul_div_cancel₀ _ (by exact_mod_cast hx.ne' : (n x : ℝ) ≠ 0)
  have hj : Tendsto (fun x => n x - k x) l atTop := tendsto_natCast_atTop_iff.mp hjR
  have hst (j : α → ℕ) (hj : Tendsto j l atTop) :
      Tendsto (fun x => log (Stirling.stirlingSeq (j x)) / n x) l (𝓝 0) :=
    ((Stirling.tendsto_stirlingSeq_sqrt_pi.comp hj).log (by positivity)).div_atTop hnR
  have hlog (j : α → ℕ) (hj : Tendsto j l atTop) (c : ℝ)
      (hc : Tendsto (fun x => (j x : ℝ) / n x) l (𝓝 c)) :
      Tendsto (fun x => log (2 * (j x : ℝ)) / n x) l (𝓝 0) := by
    have hjR' : Tendsto (fun x => (j x : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hj
    have he := (hnR.const_div_atTop (log 2)).add
      (((isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hjR').mul hc)
    simp only [zero_mul, zero_add] at he
    apply he.congr'
    filter_upwards [hj.eventually (eventually_gt_atTop 0)] with x hx
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hx.ne'), add_div]
    congr 1
    dsimp only [Function.comp_def, id_eq]
    field_simp [show (j x : ℝ) ≠ 0 by exact_mod_cast hx.ne']
  have hnn : Tendsto (fun x => (n x : ℝ) / n x) l (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hnp] with x hx
    exact (div_self (by exact_mod_cast hx.ne' : (n x : ℝ) ≠ 0)).symm
  have herr := (((hst n hn).sub (hst k hk)).sub (hst _ hj)).add
    ((((hlog n hn 1 hnn).sub (hlog k hk q hq)).sub (hlog _ hj (1-q) hjq)).const_mul
      (1 / 2 : ℝ))
  have hh := (binEntropy_continuous.continuousAt.tendsto.comp hq).add herr
  simp only [sub_zero, zero_sub, mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [hnp, hki] with x hn0 hk0
  rw [log_choose_identity hk0.1 hk0.2]
  dsimp only [Function.comp_def]
  field_simp [show (n x : ℝ) ≠ 0 by exact_mod_cast hn0.ne']
  <;> ring

/-- The entropy exponent on any growing common scale, with both bin sizes and
selected sizes varying and the selected proportion strictly interior. -/
theorem log_choose_scaled {α : Type*} {l : Filter α} (y : α → ℝ) (n k : α → ℕ)
    {d r : ℝ} (hy : Tendsto y l atTop) (hd : 0 < d) (hr : 0 < r) (hrd : r < d)
    (hn : Tendsto (fun x => (n x : ℝ) / y x) l (𝓝 d))
    (hk : Tendsto (fun x => (k x : ℝ) / y x) l (𝓝 r)) :
    Tendsto (fun x => log ((n x).choose (k x) : ℝ) / y x) l
      (𝓝 (d * binEntropy (r / d))) := by
  have hnR : Tendsto (fun x => (n x : ℝ)) l atTop := by
    apply (hy.atTop_mul_pos hd hn).congr'
    filter_upwards [hy.eventually_gt_atTop 0] with x hx
    exact mul_div_cancel₀ _ hx.ne'
  have hnn : Tendsto n l atTop := tendsto_natCast_atTop_iff.mp hnR
  have hq : Tendsto (fun x => (k x : ℝ) / n x) l (𝓝 (r / d)) := by
    apply (hk.div hn hd.ne').congr'
    filter_upwards [hy.eventually_gt_atTop 0] with x hx
    exact div_div_div_cancel_right₀ hx.ne' _ _
  have h := (log_choose_limit n k hnn (div_pos hr hd) ((div_lt_one hd).mpr hrd) hq).mul hn
  rw [mul_comm (binEntropy (r / d)) d] at h
  apply h.congr'
  filter_upwards [hnR.eventually_gt_atTop 0] with x hx
  exact div_mul_div_cancel₀ hx.ne'

end D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
