/- GID: D5/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne
   generality: I
   mirror-B: D5/B/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden displacement series tends to one as its first parameter tends to infinity. -/

/- Library-search audit trail (2026-08-27):
* Searches of `D5/**/*.lean` and `Blueprint/**/*.scribe.cs` found no existing theorem named
  `golden_displacement_series_tendsto_one` and no golden displacement series limit theorem.
* The frozen strict-antitone module exports `dTerm_le_of_parameters_le`; it supplies the eventual
  dominator at a summable baseline and is used directly below. The same import chain reaches
  `dTerm_summable`, which supplies such a baseline for every fixed second parameter.
* Pinned Mathlib provides `tendsto_tsum_of_dominated_convergence` and
  `tendsto_rpow_atTop_of_base_lt_one`; both are used directly below.
* The public `dTerm_zero`, `dTerm_one`, and `le_nS` identify the termwise limit without introducing
  a general local lemma.
-/

import D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesStrictAntitone

open Filter
open Topology
open GoldenDesubstitutionLength
open GoldenDisplacementEulerProduct
open D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesStrictAntitone

namespace D5.S3.Analytic.Asymptotics.GoldenDisplacementSeriesTendstoOne

noncomputable section

private lemma tendsto_one_of_summable_baseline (s0 w : ℝ)
    (hsum0 : Summable (dTerm s0 w)) :
    Tendsto (fun s : ℝ => ∑' n : ℕ, dTerm s w n) atTop (𝓝 1) := by
  let limitTerm : ℕ → ℝ := fun n => if n = 1 then 1 else 0
  have hpointwise : ∀ n : ℕ, Tendsto (fun s : ℝ => dTerm s w n) atTop
      (𝓝 (limitTerm n)) := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [limitTerm, dTerm_zero]
    by_cases hn1 : n = 1
    · subst n
      simp [limitTerm, dTerm_one]
    have hnTwo : 2 ≤ n := by omega
    have hbaseNat : 2 ≤ nS n := hnTwo.trans (le_nS hn0)
    have hbase : (1 : ℝ) < nS n := by
      exact_mod_cast lt_of_lt_of_le (by omega : 1 < 2) hbaseNat
    have hinvPos : 0 < (nS n : ℝ)⁻¹ := inv_pos.mpr (zero_lt_one.trans hbase)
    have hinvLower : (-1 : ℝ) < (nS n : ℝ)⁻¹ := by linarith
    have hpow : Tendsto (fun s : ℝ => (nS n : ℝ) ^ (-s)) atTop (𝓝 0) := by
      simpa only [Real.rpow_neg_eq_inv_rpow] using
        tendsto_rpow_atTop_of_base_lt_one ((nS n : ℝ)⁻¹)
          hinvLower (inv_lt_one_of_one_lt₀ hbase)
    simpa [limitTerm, dTerm, hn0, hn1] using hpow.mul_const ((n : ℝ) ^ (-w))
  have hbound : ∀ᶠ s in atTop, ∀ n : ℕ, ‖dTerm s w n‖ ≤ dTerm s0 w n := by
    filter_upwards [eventually_ge_atTop s0] with s hs n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (dTerm_nonneg s w n)] using
      dTerm_le_of_parameters_le hs le_rfl n
  have hlimit := tendsto_tsum_of_dominated_convergence hsum0 hpointwise hbound
  simpa [limitTerm] using hlimit

/-- For every fixed `w`, the golden displacement series tends to its parameter-independent
index-one term as `s` tends to positive infinity. -/
theorem golden_displacement_series_tendsto_one (w : ℝ) :
    Tendsto (fun s : ℝ => ∑' n : ℕ, dTerm s w n) atTop (𝓝 1) := by
  let s0 : ℝ := max 0 (1 - w) + 1
  have hs0 : 0 ≤ s0 := by
    dsimp [s0]
    linarith [le_max_left (0 : ℝ) (1 - w)]
  have hsw : 1 < s0 + w := by
    dsimp [s0]
    linarith [le_max_right (0 : ℝ) (1 - w)]
  have hsumNorm : Summable (fun n : ℕ => ‖dTerm s0 w n‖) :=
    dTerm_summable hs0 hsw
  have hsum0 : Summable (dTerm s0 w) := by
    have hterms : (fun n : ℕ => ‖dTerm s0 w n‖) = dTerm s0 w := by
      funext n
      exact Real.norm_of_nonneg (dTerm_nonneg s0 w n)
    rwa [hterms] at hsumNorm
  exact tendsto_one_of_summable_baseline s0 w hsum0

end

end D5.S3.Analytic.Asymptotics.GoldenDisplacementSeriesTendstoOne
