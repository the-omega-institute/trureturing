/- GID: D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesValueSet
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/GoldenDisplacementSeriesValueSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Attained golden displacement values equal the open ray above one. -/

/- Library-search audit trail (2026-08-28):
* Searches of `D5/**/*.lean` and `Blueprint/**/*.scribe.cs` for the proposed module and
  declaration names, the full value-set equality, and unboundedness found no prior result.
  The repository search found the exact zero-slice summability criterion, strict lower bound,
  and no-gap theorem, all available through the single connectivity import below.
* Searches of pinned `Mathlib/**/*.lean` found
  `tendsto_sum_range_one_div_nat_succ_atTop`, `tendsto_finsetSum`,
  `continuousAt_const_rpow`, and `Summable.sum_le_tsum`. The proof takes a finite harmonic
  sum above the target, approaches exponent one from above so the matching finite p-series
  sum stays above the target, bounds the full convergent p-series below by that finite sum
  using termwise nonnegativity, and applies the imported no-gap theorem.
-/

import D5.S3.Analytic.Connectivity.GoldenDisplacementSeriesValueConnectedness

open Filter
open GoldenDisplacementEulerProduct
open D5.S1.Deficit.Displacement.DisplacementSeriesDivergence
open D5.S3.Analytic.Connectivity.GoldenDisplacementSeriesValueConnectedness
open D5.S3.Analytic.SeriesInequalities.GoldenDisplacementSeriesStrictLowerBound

namespace D5.S3.Analytic.Characterizations.GoldenDisplacementSeriesValueSet

/-- The values attained by convergent golden displacement series equal the open ray above one. -/
theorem golden_displacement_series_values_eq_Ioi_one :
    {x : ℝ | ∃ s w : ℝ, Summable (dTerm s w) ∧ ∑' n : ℕ, dTerm s w n = x} =
      Set.Ioi 1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨s, w, hsum, rfl⟩
    exact one_lt_golden_displacement_series hsum
  · intro x hx
    obtain ⟨N, hN⟩ :=
      (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop x).exists
    have hinv :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hexponent :
        Tendsto (fun k : ℕ => -(1 + 1 / ((k : ℝ) + 1))) atTop (nhds (-1 : ℝ)) := by
      simpa using ((tendsto_const_nhds.add hinv).neg :
        Tendsto (fun k : ℕ => -(1 + 1 / ((k : ℝ) + 1))) atTop (nhds (-(1 + 0))))
    have hfinite :
        Tendsto
          (fun k : ℕ => ∑ i ∈ Finset.range N,
            ((i + 1 : ℕ) : ℝ) ^ (-(1 + 1 / ((k : ℝ) + 1))))
          atTop
          (nhds (∑ i ∈ Finset.range N, (1 / (i + 1) : ℝ))) := by
      apply tendsto_finsetSum
      intro i hi
      simpa [Function.comp_def, one_div, Real.rpow_neg_one] using
        (Real.continuousAt_const_rpow
          (by positivity : ((i + 1 : ℕ) : ℝ) ≠ 0)).tendsto.comp hexponent
    obtain ⟨k, hk⟩ := (hfinite.eventually (lt_mem_nhds hN)).exists
    let w : ℝ := 1 + 1 / ((k : ℝ) + 1)
    have hw : 1 < w := by
      dsimp [w]
      exact lt_add_of_pos_right 1 (one_div_pos.mpr (by positivity))
    have hsum : Summable (dTerm 0 w) := summable_dTerm_zero_iff.mpr hw
    have hpartial : x < ∑ n ∈ Finset.range N, dTerm 0 w (n + 1) := by
      simpa [w, dTerm] using hk
    have hle :
        ∑ n ∈ Finset.range N, dTerm 0 w (n + 1) ≤ ∑' n : ℕ, dTerm 0 w n := by
      have hinj : Set.InjOn (fun n : ℕ => n + 1) (Finset.range N) :=
        fun a _ b _ hab => Nat.add_right_cancel hab
      rw [← Finset.sum_image hinj]
      exact hsum.sum_le_tsum _ (fun n _ => dTerm_nonneg 0 w n)
    have hvalue :
        ∑' n : ℕ, dTerm 0 w n ∈
          {y : ℝ | ∃ s w : ℝ, Summable (dTerm s w) ∧ ∑' n : ℕ, dTerm s w n = y} :=
      ⟨0, w, hsum, rfl⟩
    exact Ioo_one_subset_golden_displacement_series_values _ hvalue
      ⟨hx, hpartial.trans_le hle⟩

end D5.S3.Analytic.Characterizations.GoldenDisplacementSeriesValueSet
