/- GID: D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classifies every fixed-parameter golden displacement slice bijectively. -/

/- Library-search audit trail (2026-08-28):
* Repository searches found the exact two-constraint summability region, fixed-second-parameter
  limit at one, strict antitonicity, continuity on the convergence region, and strict lower
  bound. They found no reverse-solved slice criterion or fixed-parameter value classification.
* Pinned Mathlib provides `not_summable_iff_tendsto_nat_atTop_of_nonneg`,
  `Metric.mem_nhds_iff`, and `intermediate_value_Icc'`; all are used directly below.
* At the reverse-solved boundary the series is not summable. Its nonnegative partial sums
  therefore tend to positive infinity. Continuity of a sufficiently large finite partial sum
  supplies a convergent point above any prescribed target, while the fixed-parameter limit
  supplies a farther point below it. The intermediate value theorem fills the target exactly.
-/

import D5.S3.Analytic.Asymptotics.GoldenDisplacementSeriesTendstoOne
import D5.S3.Analytic.Boundary.GoldenDisplacementSeriesContinuity
import D5.S3.Analytic.SeriesInequalities.GoldenDisplacementSeriesStrictLowerBound

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion
open D5.S3.Analytic.Asymptotics.GoldenDisplacementSeriesTendstoOne
open D5.S3.Analytic.Boundary.GoldenDisplacementSeriesContinuity
open D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesStrictAntitone
open D5.S3.Analytic.SeriesInequalities.GoldenDisplacementSeriesStrictLowerBound

namespace D5.S3.Analytic.Characterizations.GoldenDisplacementSeriesSliceBijection

noncomputable section

/-- For fixed `w`, the series is summable exactly when `s` is strictly greater than both
reverse-solved affine boundary values. -/
theorem golden_displacement_slice_summable_iff (s w : ℝ) :
    Summable (dTerm s w) ↔
      max ((1 - w) / 2) ((1 - 2 * w) / 3) < s := by
  rw [dTerm_summable_iff_two_constraints]
  rw [max_lt_iff]
  constructor <;> rintro ⟨hfirst, hsecond⟩ <;> constructor <;> linarith

/-- For fixed `w`, the series-value map sends its exact summability domain bijectively onto
the real values strictly greater than one. -/
theorem golden_displacement_series_slice_bijOn (w : ℝ) :
    Set.BijOn (fun s : ℝ => ∑' n : ℕ, dTerm s w n)
      {s : ℝ | Summable (dTerm s w)} (Set.Ioi 1) := by
  let a : ℝ := max ((1 - w) / 2) ((1 - 2 * w) / 3)
  let f : ℝ → ℝ := fun s => ∑' n : ℕ, dTerm s w n
  have hsum_iff (s : ℝ) : Summable (dTerm s w) ↔ a < s := by
    simpa [a] using golden_displacement_slice_summable_iff s w
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact one_lt_golden_displacement_series hs
  · intro s₁ hs₁ s₂ hs₂ heq
    rcases lt_trichotomy s₁ s₂ with hlt | hequal | hgt
    · have hstrict :=
        golden_displacement_series_strict_antitone
          (s1 := s₁) (w1 := w) (s2 := s₂) (w2 := w)
          hlt.le le_rfl (Or.inl hlt) hs₁
      exact (hstrict.ne heq.symm).elim
    · exact hequal
    · have hstrict :=
        golden_displacement_series_strict_antitone
          (s1 := s₂) (w1 := w) (s2 := s₁) (w2 := w)
          hgt.le le_rfl (Or.inl hgt) hs₂
      exact (hstrict.ne heq).elim
  · intro x hx
    have hlimit := golden_displacement_series_tendsto_one w
    have hbelow : ∀ᶠ s in Filter.atTop, f s < x := by
      simpa [f] using hlimit.eventually (Iio_mem_nhds hx)
    obtain ⟨b, hbx, hab⟩ :=
      (hbelow.and (Filter.eventually_gt_atTop a)).exists
    have hnonsum : ¬Summable (dTerm a w) := by
      rw [hsum_iff a]
      exact lt_irrefl a
    have hpartialLimit :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg (dTerm_nonneg a w)).mp hnonsum
    obtain ⟨N, hNx⟩ :
        ∃ N : ℕ, x < ∑ i ∈ Finset.range N, dTerm a w i :=
      (hpartialLimit.eventually (Filter.eventually_gt_atTop x)).exists
    have hfiniteContinuous :
        Continuous (fun s : ℝ => ∑ i ∈ Finset.range N, dTerm s w i) := by
      apply continuous_finsetSum
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simpa only [dTerm_zero] using continuous_const
      · have hiCast : (i : ℝ) ≠ 0 := by exact_mod_cast hi0
        have hnSCast : (GoldenDesubstitutionLength.nS i : ℝ) ≠ 0 := by
          exact_mod_cast GoldenSubstitutionOrbit.nS_ne_zero i
        simp only [dTerm, if_neg hi0]
        exact
          ((Real.continuous_const_rpow hnSCast).comp continuous_neg).mul
            continuous_const
    have hnear :
        {s : ℝ | x < ∑ i ∈ Finset.range N, dTerm s w i} ∈ nhds a :=
      hfiniteContinuous.continuousAt.eventually (Ioi_mem_nhds hNx)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let δ : ℝ := min (ε / 2) ((b - a) / 2)
    let c : ℝ := a + δ
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) (by linarith)
    have hac : a < c := by
      dsimp [c]
      linarith
    have hcb : c < b := by
      have hδle : δ ≤ (b - a) / 2 := min_le_right _ _
      dsimp [c]
      linarith
    have hcball : c ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hδle : δ ≤ ε / 2 := min_le_left _ _
      rw [abs_of_nonneg (by linarith : 0 ≤ c - a)]
      dsimp [c]
      linarith
    have hcxPartial : x < ∑ i ∈ Finset.range N, dTerm c w i :=
      hball hcball
    have hsumc : Summable (dTerm c w) := (hsum_iff c).2 hac
    have hpartialLe :
        ∑ i ∈ Finset.range N, dTerm c w i ≤ f c := by
      dsimp [f]
      exact hsumc.sum_le_tsum (Finset.range N) (fun i _ => dTerm_nonneg c w i)
    have hcAbove : x < f c := hcxPartial.trans_le hpartialLe
    have hcontinuous : ContinuousOn f (Set.Icc c b) := by
      have hpairContinuous : Continuous (fun s : ℝ => (s, w)) :=
        continuous_id.prodMk continuous_const
      have hmaps : Set.MapsTo (fun s : ℝ => (s, w)) (Set.Icc c b)
          {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
        intro s hs
        exact (hsum_iff s).2 (hac.trans_le hs.1)
      simpa [f, Function.comp_def] using
        golden_displacement_series_continuousOn.comp
          hpairContinuous.continuousOn hmaps
    obtain ⟨s, hsInterval, hsValue⟩ :=
      intermediate_value_Icc' hcb.le hcontinuous ⟨hbx.le, hcAbove.le⟩
    refine ⟨s, (hsum_iff s).2 (hac.trans_le hsInterval.1), ?_⟩
    exact hsValue

end

end D5.S3.Analytic.Characterizations.GoldenDisplacementSeriesSliceBijection
