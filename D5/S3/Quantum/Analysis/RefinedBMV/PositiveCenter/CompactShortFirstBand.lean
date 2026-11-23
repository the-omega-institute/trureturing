/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortFirstBand
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first compact short-gap Taylor models in fixed normalized coordinates. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorMoments
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorResiduals
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.HalfGapSlope

/-! The first compact strip, with lower coordinate between one half and one. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open DimThree.Certificate (Sparse)

private def U₁ : Model := Model.affineCoordinate 0 (3 / 4) (1 / 4)
private def D₁ : Model := Model.affineCoordinate 1 (1 / 2) (1 / 2)
private def H₁ : Model := Model.affineCoordinate 2 (3 / 22) (3 / 22)
private def V₁ : Model := U₁.add D₁
private def A₁ : Model := U₁.mul (Model.ofRat (1 / 2))
private def T₁ : Model := V₁.sub A₁
private def neg (p : Model) : Model := Model.zero.sub p

private def m0 (r : ℚ) (X : Model) : Model := marginalMoment 0 19 r X H₁
private def m1 (r : ℚ) (X : Model) : Model := marginalMoment 1 18 r X H₁
private def m2 (r : ℚ) (X : Model) : Model := marginalMoment 2 17 r X H₁
private def Zmu := m0 1 (neg U₁)
private def Zmv := m0 2 (neg V₁)
private def Zv := m0 2 V₁
private def Zd := m0 1 D₁
private def Jt (j : ℕ) : Model := tiltedMoment (2 * j) (21 - 2 * j) (3 / 2) T₁ H₁
private def F₁ : Model := sinhcGeometricModel (3 / 22) (H₁.mul A₁)
private def Gap₁ : Model := neg (positiveRateGapModel H₁ (neg U₁))
private def DecayInput₁ : Model := neg ((H₁.add (Model.ofRat 1)).mul U₁)

private theorem coordinates {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hu₂ : u ≤ 1) (huv : u < v) (hd₂ : v - u ≤ 1) :
    let s := 4 * u - 3
    let t := 2 * (v - u) - 1
    let z := 22 / (p : ℝ) - 1
    InBox s t z ∧ U₁.Encloses s t z u ∧
      D₁.Encloses s t z (v - u) ∧ H₁.Encloses s t z (3 / (p : ℝ)) := by
  dsimp only
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith
  have hp₂ : 22 / (p : ℝ) ≤ 2 := (div_le_iff₀ hp₀).2 (by linarith)
  have hb : InBox (4 * u - 3) (2 * (v - u) - 1) (22 / (p : ℝ) - 1) := by
    unfold InBox
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨?_, by linarith⟩⟩
    linarith [div_pos (by norm_num : (0 : ℝ) < 22) hp₀]
  refine ⟨hb, ?_, ?_, ?_⟩
  · have h := Model.affineCoordinate_sound hb 0 (3 / 4) (1 / 4)
    convert h using 1 <;> first | rfl | (norm_num <;> ring)
  · have h := Model.affineCoordinate_sound hb 1 (1 / 2) (1 / 2)
    convert h using 1 <;> first | rfl | (norm_num <;> ring)
  · have h := Model.affineCoordinate_sound hb 2 (3 / 22) (3 / 22)
    convert h using 1 <;> first | rfl | (norm_num <;> ring)

private theorem neg_sound {p : Model} {s t z f : ℝ} (hf : p.Encloses s t z f) :
    (neg p).Encloses s t z (-f) := by
  simpa only [neg, zero_sub] using Model.sub_sound (Model.zero_sound s t z) hf

private def slope (r : ℚ) (X inverse : Model) : Model := (m1 r X).mul inverse

private theorem slope_sound {p : ℕ} (hp : 0 < p) {s t z x : ℝ} {X I : Model} {r : ℚ}
    (hb : InBox s t z) (hh : H₁.Encloses s t z (3 / (p : ℝ))) (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / 19 < 1)
    (hi : I.Encloses s t z (1 / compactZ p x)) :
    (slope r X I).Encloses s t z (compactZSlope p x) := by
  rw [compactZSlope_eq hp, ← iteratedDeriv_compactZ_eq_integral hp]
  have h := marginalMoment_sound (k := 1) (terms := 18) hp (by decide) hb hh hx hr
    (by simpa using hsmall)
  simpa only [slope, m1, div_eq_mul_inv, one_mul] using Model.mul_sound hb h hi

end RefinedBMV.PositiveCenter.CompactTaylorModel
