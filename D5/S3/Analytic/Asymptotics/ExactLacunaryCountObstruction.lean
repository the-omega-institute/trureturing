/- GID: D5/S3/Analytic/Asymptotics/ExactLacunaryCountObstruction
   generality: I
   mirror-B: D5/B/S3/Analytic/Asymptotics/ExactLacunaryCountObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact lacunary series cannot equal a weighted monotone-count primitive on a tail. -/

import D5.S3.Analytic.Asymptotics.CommonPhaseSpectralCurvature
import D5.S3.Analytic.Asymptotics.ExactLacunaryCoefficients
import D5.S3.Analytic.Asymptotics.OneSidedTailCurvature
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology

namespace ExactLacunaryCountObstruction

open ExactLacunaryCoefficients
open OneSidedTailCurvature (q r)

/-- The model with frequencies `3^(n+1)` and exact coefficients `1/(ρ_n (1-ρ_n))`. -/
noncomputable def modelSeries (β : ℕ → ℝ) (t : ℝ) : ℝ :=
  -2 * (∑' n, Real.exp ((β n - 1) * t) *
    ((coefficient (β n) (frequency n)).re * Real.cos (frequency n * t) -
      (coefficient (β n) (frequency n)).im * Real.sin (frequency n * t)))

private theorem modelSeries_add_common_phase (β : ℕ → ℝ) (m : ℤ) (h : ℝ) :
    modelSeries β (2 * Real.pi * (m : ℝ) + h) =
      CommonPhaseSpectralCurvature.spectralSeries (realWeight β (2 * Real.pi * (m : ℝ)))
        (imagWeight β (2 * Real.pi * (m : ℝ))) (fun n => β n - 1) frequency h := by
  unfold modelSeries CommonPhaseSpectralCurvature.spectralSeries
  apply congrArg (fun s : ℝ => -2 * s)
  refine tsum_congr fun n => ?_
  obtain ⟨j, hj⟩ := phase_eq_int_turn n m
  have hphase : frequency n * (2 * Real.pi * (m : ℝ) + h) =
      frequency n * h + (j : ℝ) * (2 * Real.pi) := by
    rw [mul_add, hj, add_comm]
  simp only [CommonPhaseSpectralCurvature.spectralTerm, realWeight, imagWeight, hphase,
    Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, mul_add, Real.exp_add]
  ring

/-- A monotone count and its weighted tail primitive cannot realize the exact model on a tail.
Here `T` is the logarithmic threshold for the count and its primitive. -/
theorem no_monotone_tail_realization {β : ℕ → ℝ}
    (hβlo : ∀ n, 1 / 2 ≤ β n) (hβhi : ∀ n, β n ≤ 1) :
    ¬ ∃ (V k : ℝ → ℝ) (T : ℝ),
      MonotoneOn V (Ici (Real.exp T)) ∧
      (∀ ⦃a b : ℝ⦄, 0 < a → T ≤ a → a ≤ b →
        IntervalIntegrable (fun v => q v * r V v) volume a b ∧
        k b - k a = ∫ v in a..b, q v * r V v) ∧
      ∀ᶠ t in atTop, t * k t = modelSeries β t := by
  rintro ⟨V, k, T, hV, htail, hmodel⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hmodel
  let threshold := max (max T M) 0
  have hperiod : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨m, hm⟩ := exists_int_gt ((threshold + 1) / (2 * Real.pi))
  let t₀ : ℝ := 2 * Real.pi * (m : ℝ)
  have hcenter : threshold + 1 < t₀ := by
    simpa only [t₀, mul_comm (m : ℝ)] using (div_lt_iff₀ hperiod).1 hm
  have hleft : threshold < t₀ - 1 := by linarith only [hcenter]
  have hleft_pos : 0 < t₀ - 1 := (le_max_right (max T M) 0).trans_lt hleft
  have hT : T ≤ t₀ - 1 :=
    ((le_max_left T M).trans (le_max_left (max T M) 0)).trans hleft.le
  have hM' : M ≤ t₀ - 1 :=
    ((le_max_right T M).trans (le_max_left (max T M) 0)).trans hleft.le
  have ht₀ : 0 ≤ t₀ := by linarith only [hleft_pos]
  have hab : t₀ - 1 ≤ t₀ + 1 := by linarith

  have hV' : MonotoneOn V (Icc (Real.exp (t₀ - 1)) (Real.exp (t₀ + 1))) :=
    hV.mono fun _ hx => (Real.exp_le_exp.mpr hT).trans hx.1
  have hprimitive ⦃x y : ℝ⦄ (hx : x ∈ Icc (t₀ - 1) (t₀ + 1))
      (_hy : y ∈ Icc (t₀ - 1) (t₀ + 1)) (hxy : x ≤ y) :
      k y - k x = ∫ v in x..y, q v * r V v :=
    (htail (hleft_pos.trans_le hx.1) (hT.trans hx.1) hxy).2
  obtain ⟨C, _, hcurvature⟩ := OneSidedTailCurvature.weighted_tail_curvature
    hleft_pos hab hV' (htail hleft_pos hT hab).1 hprimitive

  obtain ⟨hA_nonneg, hA, hB, hBfreq, hmoment⟩ := weighted_summability ht₀ hβlo hβhi
  have hdamping (n : ℕ) : |β n - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hβhi n))]
    linarith only [hβlo n]
  let S := CommonPhaseSpectralCurvature.spectralSeries (realWeight β t₀) (imagWeight β t₀)
    (fun n => β n - 1) frequency
  have hdiv : Tendsto (fun h => (S h + S (-h) - 2 * S 0) / h ^ 2) (𝓝[≠] 0) atTop :=
    CommonPhaseSpectralCurvature.tendsto_symmetric_second_difference_div_sq_atTop
      (realWeight β t₀) (imagWeight β t₀) (fun n => β n - 1) frequency
      hA_nonneg hA hB hBfreq hdamping hmoment
  have hright_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 fun x hx => by simpa using (ne_of_gt hx : x ≠ 0)
  have hlarge := tendsto_atTop.1 (hdiv.mono_left hright_nhds) (C + 1)
  obtain ⟨h, hlarge, hh⟩ := (hlarge.and (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))).exists

  have hpoint (u : ℝ) (hu : -1 ≤ u) : (t₀ + u) * k (t₀ + u) = S u := by
    have htime : M ≤ t₀ + u := hM'.trans (by linarith only [hu])
    exact (hM (t₀ + u) htime).trans (modelSeries_add_common_phase β m u)
  have hpos := hpoint h (by linarith only [hh.1])
  have hneg : (t₀ - h) * k (t₀ - h) = S (-h) := by
    simpa only [← sub_eq_add_neg] using hpoint (-h) (by linarith only [hh.2])
  have hzero : t₀ * k t₀ = S 0 := by
    simpa only [add_zero] using hpoint 0 (by norm_num)
  have hupper := hcurvature (t := t₀) (h := h) hh.1.le
    (by linarith only [hh.2]) (by linarith only [hh.2])
  rw [mul_assoc, hpos, hneg, hzero] at hupper
  have hbounded : (S h + S (-h) - 2 * S 0) / h ^ 2 ≤ C :=
    (div_le_iff₀ (pow_pos hh.1 2)).2 hupper
  exact (not_le_of_gt (lt_add_of_pos_right C zero_lt_one)) (hlarge.trans hbounded)

end ExactLacunaryCountObstruction
