/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactSlopeCheckpoints
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two fixed coordinates suffice for the uniform lower reflected marginal slope. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactHalfLogBounds
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

/-! The two scalar bounds used in the middle-gap comparison. -/

namespace RefinedBMV.PositiveCenter.CompactGap

open Filter
open scoped Topology

noncomputable section

open private rate c W R from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities

open private W_eq_reflected from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel

open private hasDerivAt_exp_decay from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailAverage

private def marginalScale (h x : ℝ) : ℝ := c h * upperTailGap h x ^ 2 * Real.exp (-x)

private theorem marginalScale_pos {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    0 < marginalScale h x := by
  have hg := tail_gap_pos hh hx
  unfold marginalScale c
  positivity

private theorem marginal_eq_ratio {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    compositionMoment p 0 (-x) = R (rate p) x / marginalScale (rate p) x - 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < rate p := by unfold rate; positivity
  have he := W_eq_reflected hp x
  change R (rate p) x - marginalScale (rate p) x =
    marginalScale (rate p) x * compositionMoment p 0 (-x) at he
  have hpos := marginalScale_pos hh hx
  rw [eq_sub_iff_add_eq, eq_div_iff hpos.ne']
  linarith only [he, mul_add (marginalScale (rate p) x) (compositionMoment p 0 (-x)) 1,
    mul_comm (compositionMoment p 0 (-x) + 1) (marginalScale (rate p) x)]

private theorem marginalScale_deriv {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    HasDerivAt (marginalScale h)
      (marginalScale h x * (2 * Real.exp (-(h * x)) / upperTailGap h x - 1)) x := by
  have hF := hasDerivAt_upperTailGap (t := x) hh
  have hE := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id' x).neg
  have hd := (((hF.pow 2).const_mul (c h)).mul hE)
  change HasDerivAt (marginalScale h) _ x at hd
  refine hd.congr_deriv ?_
  unfold marginalScale
  simp only [Function.comp_apply, Pi.pow_apply]
  field_simp [(tail_gap_pos hh hx).ne']
  <;> ring

private theorem R_deriv {h x : ℝ} (hh : 0 < h) :
    HasDerivAt (R h)
      ((3 + 2 * h) * (Real.exp (-(h * x)) - Real.exp (-((3 + 2 * h) * x)))) x := by
  refine (((hasDerivAt_exp_decay (3 + 2 * h) x).sub_const 1).add
    ((hasDerivAt_upperTailGap hh).const_mul (3 + 2 * h))).congr_deriv ?_
  ring

private def slopeNumerator (h t q : ℝ) : ℝ :=
  let f := upperTailGap h t
  let k := 3 + 2 * h
  f * (k * (Real.exp (-(h * t)) - Real.exp (-(k * t)))) +
    ((1 - q) * f - 2 * Real.exp (-(h * t))) * R h t + q * f * marginalScale h t

private theorem halfSlope_of_numerator {p : ℕ} (hp : 0 < p) {t q : ℝ} (ht : 0 < t)
    (hs : 0 ≤ slopeNumerator (rate p) t q) :
    q / 2 ≤ reflectedHalfLogSlope (compositionMoment p 0) t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let h := rate p
  have hh : 0 < h := by dsimp [h, rate]; positivity
  have hB := marginalScale_pos hh ht
  have hf := tail_gap_pos hh ht
  have hC := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  have hloc : (fun t ↦ R h t / marginalScale h t - 1) =ᶠ[𝓝 t]
      (fun t ↦ compositionMoment p 0 (-t)) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact (marginal_eq_ratio hp hx).symm
  have hd := ((R_deriv (x := t) hh).div (marginalScale_deriv hh ht) hB.ne').sub_const 1
  have hd := hd.congr_of_eventuallyEq hloc.symm
  unfold reflectedHalfLogSlope
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply (le_div_iff₀ hC).2
  apply (mul_le_mul_iff_left₀ (mul_pos hf hB)).1
  apply sub_nonneg.mp
  rw [hd.deriv, marginal_eq_ratio hp ht]
  convert hs using 1
  unfold slopeNumerator
  dsimp only [h] at hB hf ⊢
  field_simp [hB.ne', hf.ne']
  <;> ring

open CompactTaylorModel

private def spacingModel : Model := Model.affineCoordinate 0 (3 / 22) (3 / 22)
private def rateModel : Model := (Model.ofRat 3).add ((Model.ofRat 2).mul spacingModel)
private def scaleModel : Model :=
  (((Model.ofRat 3).add spacingModel).mul rateModel).mul (Model.ofRat (1 / 2))
private def negModel (p : Model) : Model := Model.zero.sub p
private def negTime (t : ℚ) : Model := Model.ofRat (-t)
private def spacingTime (t : ℚ) : Model := spacingModel.mul (negTime t)
private def rateTime (t : ℚ) : Model := rateModel.mul (negTime t)
private def gapModel (t : ℚ) : Model := negModel (positiveRateGapModel spacingModel (negTime t))

private def score (t q : ℚ) : Model :=
  let F := gapModel t
  let Eh := (spacingTime t).centeredExp
  let Ek := (rateTime t).centeredExp
  let R := (Ek.sub (Model.ofRat 1)).add (rateModel.mul F)
  let R' := rateModel.mul (Eh.sub Ek)
  let B := (scaleModel.mul (F.pow 2)).mul (negTime t).centeredExp
  ((F.mul R').add ((((Model.ofRat (1 - q)).mul F).sub ((Model.ofRat 2).mul Eh)).mul R))
    |>.add (((Model.ofRat q).mul F).mul B)

private def modelChecks (t q : ℚ) : Prop :=
  (spacingTime t).argumentRadius ≤ 2 ∧ (spacingTime t).expChecks ∧
    (rateTime t).expChecks ∧ (negTime t).expChecks ∧ 0 < (score t q).lower

private theorem halfSlope_of_checks {p : ℕ} (hp : 11 ≤ p) {t q : ℚ} (ht : 0 < (t : ℝ))
    (hc : modelChecks t q) :
    (q : ℝ) / 2 ≤ reflectedHalfLogSlope (compositionMoment p 0) (t : ℝ) := by
  have hp₀ : 0 < p := by omega
  have hp₁₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hpR : (0 : ℝ) < p := by linarith
  let s := 22 / (p : ℝ) - 1
  let h := rate p
  have hh : 0 < h := by dsimp [h, rate]; positivity
  have hb : InBox s 0 0 := by
    have hup : 22 / (p : ℝ) ≤ 2 := (div_le_iff₀ hpR).2 (by linarith)
    have hlo : 0 < 22 / (p : ℝ) := by positivity
    exact ⟨abs_le.mpr ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩, by norm_num,
      by norm_num⟩
  have hH : spacingModel.Encloses s 0 0 h := by
    have hm := Model.affineCoordinate_sound hb 0 (3 / 22) (3 / 22)
    convert hm using 1 <;> first | rfl | (norm_num [h, rate, s] <;> ring)
  have hK : rateModel.Encloses s 0 0 (3 + 2 * h) := by
    simpa only [rateModel, Rat.cast_ofNat] using Model.add_sound (Model.ofRat_sound 3 s 0 0)
      (Model.mul_sound hb (Model.ofRat_sound 2 s 0 0) hH)
  have hC : scaleModel.Encloses s 0 0 (c h) := by
    simpa only [scaleModel, c, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, mul_one_div] using
      Model.mul_sound hb (Model.mul_sound hb (Model.add_sound (Model.ofRat_sound 3 s 0 0) hH) hK)
        (Model.ofRat_sound (1/2) s 0 0)
  have hT : (negTime t).Encloses s 0 0 (-(t : ℝ)) := by
    simpa only [negTime, Rat.cast_neg] using Model.ofRat_sound (-t) s 0 0
  have hHt : (spacingTime t).Encloses s 0 0 (-(h * (t : ℝ))) := by
    simpa only [spacingTime, mul_neg] using Model.mul_sound hb hH hT
  have hKt : (rateTime t).Encloses s 0 0 (-((3 + 2 * h) * (t : ℝ))) := by
    simpa only [rateTime, mul_neg] using Model.mul_sound hb hK hT
  obtain ⟨hGap, hEh, hEk, hEt, hScore⟩ := hc
  have hF : (gapModel t).Encloses s 0 0 (upperTailGap h (t : ℝ)) := by
    have hx := positiveRateGapModel_sound hb hH hT hh.ne' (neg_ne_zero.mpr ht.ne') hGap
    have hm := Model.sub_sound (Model.zero_sound s 0 0) hx
    convert hm using 1 <;> simp only [gapModel, negModel, upperTailGap, mul_neg, zero_sub, neg_div]
    ring
  have heh := Model.expChecks_sound hb hHt hEh
  have hek := Model.expChecks_sound hb hKt hEk
  have het := Model.expChecks_sound hb hT hEt
  have hR := Model.add_sound (Model.sub_sound hek (Model.ofRat_sound 1 s 0 0))
    (Model.mul_sound hb hK hF)
  have hR' := Model.mul_sound hb hK (Model.sub_sound heh hek)
  have hB := Model.mul_sound hb (Model.mul_sound hb hC (Model.pow_sound hb hF 2)) het
  have hVal : (score t q).Encloses s 0 0 (slopeNumerator h (t : ℝ) (q : ℝ)) := by
    simpa only [score, R, marginalScale, slopeNumerator, Rat.cast_sub, Rat.cast_one,
      Rat.cast_ofNat] using Model.add_sound
      (Model.add_sound (Model.mul_sound hb hF hR') (Model.mul_sound hb
        (Model.sub_sound (Model.mul_sound hb (Model.ofRat_sound (1-q) s 0 0) hF)
          (Model.mul_sound hb (Model.ofRat_sound 2 s 0 0) heh)) hR))
      (Model.mul_sound hb (Model.mul_sound hb (Model.ofRat_sound q s 0 0) hF) hB)
  have hn : 0 ≤ slopeNumerator h (t : ℝ) (q : ℝ) :=
    (div_nonneg (by exact_mod_cast hScore.le) scale_real_pos.le).trans (Model.lower_sound hb hVal)
  exact halfSlope_of_numerator hp₀ ht hn

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
/-- Uniform lower endpoint of the reflected marginal slope in the middle band. -/
theorem reflectedHalfLogSlope_ge_five_twelfths {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 0 < t) :
    5 / 12 ≤ reflectedHalfLogSlope (compositionMoment p 0) t := by
  apply reflectedHalfLogSlope_ge_five_twelfths_of_checkpoints hp _ _ ht
  · have h := halfSlope_of_checks (t := 2) (q := 23 / 20) hp (by norm_num) (by
      unfold modelChecks Model.expChecks
      decide +kernel)
    norm_num at h
    exact h
  · have h := halfSlope_of_checks (t := 29 / 10) (q := 1159 / 1218) hp (by norm_num)
      (by
        unfold modelChecks Model.expChecks
        decide +kernel)
    norm_num at h
    exact h

end

end RefinedBMV.PositiveCenter.CompactGap
