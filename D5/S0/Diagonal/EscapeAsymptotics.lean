/- GID: D5/S0/Diagonal/EscapeAsymptotics
   generality: G
   mirror-B: D5/B/S0/Diagonal/EscapeAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite diagonal escape ratio tends to one as the listing size grows. -/

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecificLimits.Normed

namespace D5.S0.Diagonal.EscapeAsymptotics

/-- For a fixed finite value count and fixed-point count, the escape ratio tends to one. -/
theorem escape_ratio_tendsto_one (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n) :
    Filter.Tendsto (fun N : ℕ => (1 - (k : ℝ) / (n : ℝ) ^ N) ^ N)
      Filter.atTop (nhds 1) := by
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hn_one : (1 : ℝ) < n := by linarith
  have h_inv_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
  have h_inv_lt_one : (n : ℝ)⁻¹ < 1 := (inv_lt_one₀ hn_pos).mpr hn_one
  have h_decay_base :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) * (n : ℝ)⁻¹ ^ N * (k : ℝ))
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_self_mul_const_pow_of_lt_one h_inv_nonneg h_inv_lt_one).mul_const (k : ℝ)
  have h_decay :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) * ((k : ℝ) / (n : ℝ) ^ N))
        Filter.atTop (nhds 0) := by
    apply h_decay_base.congr'
    filter_upwards with N
    rw [div_eq_mul_inv, inv_pow]
    ring
  have h_bounds :
      ∀ᶠ N in Filter.atTop,
        0 ≤ (k : ℝ) / (n : ℝ) ^ N ∧ (k : ℝ) / (n : ℝ) ^ N ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hk_real : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    have hn_pow : (n : ℝ) ≤ (n : ℝ) ^ N :=
      le_self_pow₀ hn_one.le (Nat.one_le_iff_ne_zero.mp hN)
    constructor
    · positivity
    · exact (div_le_one (pow_pos hn_pos N)).mpr (hk_real.trans hn_pow)
  have h_lower :
      Filter.Tendsto
        (fun N : ℕ => 1 - (N : ℝ) * ((k : ℝ) / (n : ℝ) ^ N))
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub h_decay)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    h_lower tendsto_const_nhds ?_ ?_
  · filter_upwards [h_bounds] with N hN
    have h_neg : (-2 : ℝ) ≤ -((k : ℝ) / (n : ℝ) ^ N) := by linarith [hN.2]
    simpa [sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -((k : ℝ) / (n : ℝ) ^ N)) h_neg N)
  · filter_upwards [h_bounds] with N hN
    exact pow_le_one₀ (sub_nonneg.mpr hN.2) (sub_le_self 1 hN.1)

end D5.S0.Diagonal.EscapeAsymptotics
