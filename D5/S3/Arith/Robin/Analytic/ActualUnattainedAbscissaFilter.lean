/- GID: D5/S3/Arith/Robin/Analytic/ActualUnattainedAbscissaFilter
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ActualUnattainedAbscissaFilter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A short positive filter isolates a dominant actual conjugate pair. -/

import D5.S3.Arith.Robin.ForwardKernel.KappaGap
import D5.S3.Weil.ZeroData.ActualHighZeroFilter
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

/-! The unattained abscissa lets the protected mode exceed every surviving low zero. -/

open Complex MeasureTheory Set
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualHighZeroFilter
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula (zeroEquiv)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap
open PositiveSpectralKernel

namespace D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter

private theorem actual_conjugate_occurrence (j : ℕ) :
    ∃ k : ℕ, actualZero k = star (actualZero j) := by
  let n := actualData.conjugation (actualOccurrenceEquiv j).1
  let i : Fin (actualData.multiplicity n) := ⟨0, actualData.multiplicity_pos n⟩
  refine ⟨actualOccurrenceEquiv.symm ⟨n, i⟩, ?_⟩
  simp only [actualZero, Equiv.apply_symm_apply, n]
  exact actualData.zero_conjugation _

private theorem actual_occurrence_of_zero {z : ℂ}
    (hz : D5.S3.Weil.ZeroSum.IsNontrivialZero z) :
    ∃ j : ℕ, actualZero j = z := by
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hz
  let i : Fin (actualData.multiplicity n) := ⟨0, actualData.multiplicity_pos n⟩
  exact ⟨actualOccurrenceEquiv.symm ⟨n, i⟩, by
    simpa only [actualZero, Equiv.apply_symm_apply] using hn⟩

/-- When the actual abscissa is unattained, one can retain a conjugate pair at a
prescribed minimum frequency and with real part exceeding every surviving mode outside
that pair by a strict gap. The cutoff and filter have arbitrary positive width. -/
theorem exists_dominant_actual_zero_filter {σ h F : ℝ} (hσ : 1 / 2 < σ)
    (hσΘ : σ < zeroAbscissa) (hh : 0 < h)
    (hun : ∀ z : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ p : ℕ, ∃ b : ℝ, ∃ ν : Measure ℝ,
      0 < (actualZero p).im ∧ F < (actualZero p).im ∧
      σ ≤ b ∧ b < (actualZero p).re ∧ IsProbabilityMeasure ν ∧ ν (Icc 0 h) = 1 ∧
      (∀ j : ℕ, b < (actualZero j).re → actualZero j ≠ actualZero p →
        actualZero j ≠ star (actualZero p) → expMoment ν (actualZero j - 1) = 0) ∧
      expMoment ν (actualZero p - 1) ≠ 0 := by
  classical
  obtain ⟨H, hH, hfilter⟩ := exists_small_actual_high_zero_filter hσ hh
  let L := max H F
  have hL : 0 ≤ L := hH.trans (le_max_left _ _)
  let hf := Zeta23.zerosIn_finite (-(L + 1)) L
  let low := hf.toFinset
  have hlowFinite : ∀ z ∈ low, z.re < zeroAbscissa := by
    intro z hz
    have hz' := hf.mem_toFinset.mp hz
    exact hun z hz'.1
  obtain ⟨b, hσb, hbΘ, hlow⟩ :
      ∃ b : ℝ, σ ≤ b ∧ b < zeroAbscissa ∧ ∀ z ∈ low, z.re ≤ b := by
    by_cases hne : low.Nonempty
    · obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image low Complex.re hne
      exact ⟨max σ z.re, le_max_left _ _, max_lt hσΘ (hlowFinite z hz),
        fun y hy => (hmax y hy).trans (le_max_right _ _)⟩
    · exact ⟨σ, le_rfl, hσΘ, fun z hz => (hne ⟨z, hz⟩).elim⟩
  have hheight (j : ℕ) (hj : b < (actualZero j).re) : L < |(actualZero j).im| := by
    by_contra! hj'
    have hz : actualZero j ∈ low := hf.mem_toFinset.mpr
      ⟨(zeroEquiv actualData (actualOccurrenceEquiv j).1).property,
        by linarith [(abs_le.mp hj').1], (abs_le.mp hj').2⟩
    exact (not_lt_of_ge (hlow _ hz)) hj
  obtain ⟨_, ⟨z, hz, rfl⟩, hzRe⟩ :=
    exists_lt_of_lt_csSup zero_real_parts_nonempty hbΘ
  obtain ⟨j, hj⟩ := actual_occurrence_of_zero hz
  have hjRe : b < (actualZero j).re := by rwa [hj]
  obtain ⟨p, hpRe, hpHeight⟩ : ∃ p : ℕ, b < (actualZero p).re ∧ L < (actualZero p).im := by
    have habs := hheight j hjRe
    rcases le_or_gt 0 (actualZero j).im with hjp | hjn
    · exact ⟨j, hjRe, by simpa only [abs_of_nonneg hjp] using habs⟩
    · obtain ⟨k, hk⟩ := actual_conjugate_occurrence j
      refine ⟨k, ?_, ?_⟩
      · simpa [hk] using hjRe
      · simpa [hk, abs_of_neg hjn] using habs
  have hp := hL.trans_lt hpHeight
  obtain ⟨ν, hν, hνmass, hkill, hkeep⟩ := hfilter p hp
  refine ⟨p, b, ν, hp, (le_max_right _ _).trans_lt hpHeight, hσb, hpRe,
    hν, hνmass, ?_, hkeep⟩
  intro j hj hnp hnc
  have habs := hheight j hj
  rcases le_or_gt 0 (actualZero j).im with hjp | hjn
  · have hjL : L < (actualZero j).im := by simpa only [abs_of_nonneg hjp] using habs
    exact (hkill j (hσb.trans_lt hj) ((le_max_left _ _).trans_lt hjL) hnp).1
  · obtain ⟨k, hk⟩ := actual_conjugate_occurrence j
    have hkRe : σ < (actualZero k).re := by simpa [hk] using hσb.trans_lt hj
    have hkL : L < (actualZero k).im := by simpa [hk, abs_of_neg hjn] using habs
    have hkne : actualZero k ≠ actualZero p := by
      intro he
      apply hnc
      simpa [hk] using congrArg (fun x : ℂ => star x) he
    simpa [hk] using (hkill k hkRe ((le_max_left _ _).trans_lt hkL) hkne).2

end D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter
