/- GID: D5/S3/Weil/ZeroData/ActualHighZeroFilter
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ActualHighZeroFilter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A compact positive filter isolates a protected actual zeta mode. -/

import D5.S3.Analytic.Asymptotics.ThreeAtomZeroFilter
import D5.S3.Weil.ZeroData.ActualOccurrenceRightStripHeight

/-! The cutoff ranges over the actual occurrence indices in the explicit formula. -/

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Weil.ZeroData.ActualHighZeroFilter

open ActualReciprocalSquareBounds ActualOccurrenceRightStripHeight
open PositiveSpectralKernel

noncomputable section

private def mode (j : ℕ) : ℂ := actualZero j - 1

private theorem mode_decomp (j : ℕ) :
    (((actualZero j).re - 1 : ℝ) : ℂ) + ((actualZero j).im : ℂ) * Complex.I = mode j := by
  apply Complex.ext <;> simp [mode, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]

/-- A single compact probability annihilates every upper-half-plane zero and its conjugate
above the two cutoffs, while keeping the protected mode. Repeated occurrences consume the
same multiplicity-weighted support budget provided by the fixed-strip estimate. -/
theorem exists_actual_high_zero_filter {σ H : ℝ} (hσ : 1 / 2 < σ) (hH : 0 ≤ H)
    (p : ℕ) (hp : 0 < (actualZero p).im) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Icc 0 (∑' j : ℕ, if σ < (actualZero j).re ∧ H < (actualZero j).im ∧
        actualZero j ≠ actualZero p then 2 * Real.pi / (actualZero j).im else 0)) = 1 ∧
      (∀ j : ℕ, σ < (actualZero j).re → H < (actualZero j).im →
        actualZero j ≠ actualZero p →
        expMoment ν (actualZero j - 1) = 0 ∧
        expMoment ν (star (actualZero j - 1)) = 0) ∧
      expMoment ν (actualZero p - 1) ≠ 0 := by
  classical
  let selected : ℕ → Prop := fun j =>
    σ < (actualZero j).re ∧ H < (actualZero j).im ∧ actualZero j ≠ actualZero p
  have hγ (j : ℕ) (hj : selected j) : 0 < (actualZero j).im := hH.trans_lt hj.2.1
  have hsparse : Summable (fun j => if selected j then (actualZero j).im⁻¹ else 0) := by
    apply Summable.of_nonneg_of_le _ _ (actual_positive_rightStrip_inverse_height_summable hσ)
    · intro j
      by_cases hj : selected j
      · rw [ite_eq_left hj]
        exact inv_nonneg.mpr (hγ j hj).le
      · rw [ite_eq_right hj]
    · intro j
      by_cases hj : selected j
      · rw [ite_eq_left hj, ite_eq_left ⟨hj.1, hγ j hj⟩]
      · rw [ite_eq_right hj]
        split
        · rename_i hjpos
          exact inv_nonneg.mpr hjpos.2.le
        · exact le_rfl
  have havoid (j : ℕ) (hj : selected j) :
      mode p ≠ mode j ∧ mode p ≠ star (mode j) := by
    constructor
    · intro h
      apply hj.2.2
      simpa [mode] using congrArg (fun z : ℂ => z + 1) h.symm
    · intro h
      have him := congrArg Complex.im h
      have hjpos := hγ j hj
      simp [mode, Complex.sub_im] at him
      linarith
  obtain ⟨ν, hν, hmass, hcut, hkeep⟩ :=
    exists_selective_spectral_filter
      (r := fun j => (actualZero j).re - 1) (γ := fun j => (actualZero j).im)
      (w := mode p) selected hγ hsparse
      (fun j hj => by simpa only [mode_decomp] using havoid j hj)
  refine ⟨ν, hν, ?_, ?_, hkeep⟩
  · change ν (Icc 0 (∑' j, if selected j then 2 * Real.pi / (actualZero j).im else 0)) = 1
    exact hmass
  · intro j hRe hIm hne
    simpa only [mode_decomp, mode] using hcut j ⟨hRe, hIm, hne⟩

/-- Above a common height cutoff, the compact support can be made arbitrarily short.
The cutoff is independent of the protected positive-ordinate occurrence. -/
theorem exists_small_actual_high_zero_filter {σ h : ℝ} (hσ : 1 / 2 < σ) (hh : 0 < h) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ p : ℕ, 0 < (actualZero p).im →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 h) = 1 ∧
        (∀ j : ℕ, σ < (actualZero j).re → H < (actualZero j).im →
          actualZero j ≠ actualZero p →
          expMoment ν (actualZero j - 1) = 0 ∧
          expMoment ν (star (actualZero j - 1)) = 0) ∧
        expMoment ν (actualZero p - 1) ≠ 0 := by
  classical
  let f (j : ℕ) : ℝ :=
    (2 * Real.pi) * (if σ < (actualZero j).re ∧ 0 < (actualZero j).im
      then (actualZero j).im⁻¹ else 0)
  have hf : Summable f := (actual_positive_rightStrip_inverse_height_summable hσ).mul_left _
  have hpos (j : ℕ) : 0 ≤ f j := by
    apply mul_nonneg (by positivity)
    split
    · rename_i hj
      exact inv_nonneg.mpr hj.2.le
    · exact le_rfl
  have hlim : Tendsto (fun n : ℕ => (∑' j, f j) - ∑ j ∈ Finset.range n, f j)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => ∑' j, f j) atTop (𝓝 (∑' j, f j)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hc.sub hf.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hh))
  have htail : (∑' j : ℕ, f (j + N)) < h := by
    have hN' := hN N le_rfl
    have he := hf.sum_add_tsum_nat_add N
    linarith
  let H : ℝ := ∑ j ∈ Finset.range N, |(actualZero j).im|
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlow (j : ℕ) (hj : j < N) : (actualZero j).im ≤ H :=
    (le_abs_self _).trans (Finset.single_le_sum
      (f := fun n : ℕ => |(actualZero n).im|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr hj))
  refine ⟨H, hH, fun p hp => ?_⟩
  let width (j : ℕ) : ℝ :=
    if σ < (actualZero j).re ∧ H < (actualZero j).im ∧ actualZero j ≠ actualZero p
      then 2 * Real.pi / (actualZero j).im else 0
  have hdom (j : ℕ) : 0 ≤ width j ∧ width j ≤ f j := by
    dsimp only [width]
    split
    · rename_i hj
      have hi := hH.trans_lt hj.2.1
      have hpv : σ < (actualZero j).re ∧ 0 < (actualZero j).im := ⟨hj.1, hi⟩
      exact ⟨(div_pos (by positivity) hi).le,
        by simp only [f, ite_eq_left hpv, div_eq_mul_inv, le_refl]⟩
    · exact ⟨le_rfl, hpos j⟩
  have hw : Summable width := Summable.of_nonneg_of_le
    (fun j => (hdom j).1) (fun j => (hdom j).2) hf
  have hfirst : (∑ j ∈ Finset.range N, width j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have he := hlow j (Finset.mem_range.mp hj)
    simp [width, not_lt_of_ge he]
  have hwidth : (∑' j, width j) ≤ h := by
    have he := hw.sum_add_tsum_nat_add N
    rw [hfirst, zero_add] at he
    rw [← he]
    exact (((summable_nat_add_iff N).2 hw).tsum_le_tsum (fun j => (hdom (j + N)).2)
      ((summable_nat_add_iff N).2 hf)).trans htail.le
  obtain ⟨ν, hν, hmass, hcut, hkeep⟩ := exists_actual_high_zero_filter hσ hH p hp
  have hmass' : ν (Icc 0 (∑' j, width j)) = 1 := hmass
  haveI : IsProbabilityMeasure ν := hν
  have hu : ν (Icc 0 h) ≤ 1 := (measure_mono (subset_univ _)).trans_eq measure_univ
  exact ⟨ν, hν, le_antisymm hu
    (hmass' ▸ measure_mono (Icc_subset_Icc_right hwidth)), hcut, hkeep⟩

end

end D5.S3.Weil.ZeroData.ActualHighZeroFilter
