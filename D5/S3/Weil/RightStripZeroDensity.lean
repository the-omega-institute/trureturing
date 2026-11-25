/- GID: D5/S3/Weil/RightStripZeroDensity
   generality: I
   mirror-B: D5/B/S3/Weil/RightStripZeroDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power-saving zero counts and reciprocal-height summability to the right of a fixed line. -/

import D5.S3.Weil.MollifiedDyadicMeanSquare
import D5.S3.Weil.RightStripInverseHeight

/-! The actual zeta mean square yields a power saving in every fixed right strip. -/

namespace Zeta23

open Complex MeasureTheory Set
open D5.S3.Weil

private theorem mollifier_eq (X : ℕ) (s : ℂ) :
    ZetaPntBounds.MollifiedZetaPolynomial.mollifier X s = moebiusMollifier X s := by
  unfold ZetaPntBounds.MollifiedZetaPolynomial.mollifier
    ZetaPntBounds.MollifiedZetaPolynomial.dirichletPolynomial moebiusMollifier
  simp only [Complex.cpow_neg, div_eq_mul_inv]

private theorem paddedDyadicHeights_eq {T : ℝ} (hT : 2 ≤ T) :
    paddedDyadicHeights T = ZetaTruncationMeanSquare.paddedBand T := by
  ext t
  change ((T - 1 ≤ t ∧ t ≤ 2 * T + 1) ∨ (-(2 * T + 1) ≤ t ∧ t ≤ -(T - 1))) ↔
    (T - 1 ≤ |t| ∧ |t| ≤ 2 * T + 1)
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact ⟨fun h => h.elim id (fun hneg => by linarith [hneg.2]), Or.inl⟩
  · rw [abs_of_neg ht]
    constructor
    · rintro (h | h)
      · linarith [h.1]
      · exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h
      exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩

/-- For any fixed cutoff strictly to the right of the critical line, the actual
multiplicity-weighted dyadic strip count grows sublinearly by a power. -/
theorem rightStripDyadicCount_power_saving {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ η D : ℝ, 0 < η ∧ 0 ≤ D ∧ ∀ T : ℝ, 2 ≤ T →
      (rightStripDyadicCount σ T : ℝ) ≤ D * T ^ (1 - η) := by
  rcases le_or_gt 1 σ with hσ' | hσ'
  · exact ⟨1 / 2, 0, by norm_num, le_rfl, fun T _ => by
      simp [rightStripDyadicCount_eq_zero hσ' T]⟩
  let a : ℝ := (σ + 1 / 2) / 2
  let r : ℝ := min ((σ - a) / 2) (1 / 4)
  let d : ℝ := a - 1 / 2
  let δ : ℝ := d / 4
  have ha : 1 / 2 < a := by dsimp [a]; linarith
  have ha' : a < 1 := by dsimp [a]; linarith
  have had : a < σ := by dsimp [a]; linarith
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hquarter : r ≤ 1 / 4 := min_le_right _ _
  have hrsmall : r ≤ 1 / 2 := hquarter.trans (by norm_num)
  have haσ : a + r ≤ σ := by
    have := min_le_left ((σ - a) / 2) (1 / 4 : ℝ)
    linarith
  have hd : 0 < d := sub_pos.mpr ha
  have hη : 0 < δ * d := by dsimp [δ]; positivity
  obtain ⟨C, hC, hmoment⟩ :=
    MollifiedDyadicMeanSquare.dyadic_mollified_zeta_mean_square (b := 1 + r) ha ha'
  obtain ⟨D, hD, hbound⟩ := rightStripDyadicCount_le_of_moebius_second_moment
    hr hrsmall haσ hσ' hη hC.le (fun T => ⌊T ^ δ⌋₊) (fun T hT u hu => by
      rw [paddedDyadicHeights_eq hT]
      have h := (hmoment u T hu.1 hu.2 hT).2
      simpa only [ZetaTruncationMeanSquare.vertical, mollifier_eq, d, δ] using h)
  exact ⟨δ * d / 2, D, by positivity, hD, hbound⟩

/-- The reciprocal heights of actual zeta zeros strictly to the right of any
fixed line `σ > 1/2` are summable, counted with multiplicity. -/
theorem summable_rightStrip_inverse_height {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ σ < ρ.re} =>
      (zeroMult ρ : ℝ) / |(ρ : ℂ).im|) := by
  obtain ⟨η, D, hη, hD, hcount⟩ := rightStripDyadicCount_power_saving hσ
  exact summable_rightStrip_inverse_height_of_dyadic_count hD hη hcount

end Zeta23
