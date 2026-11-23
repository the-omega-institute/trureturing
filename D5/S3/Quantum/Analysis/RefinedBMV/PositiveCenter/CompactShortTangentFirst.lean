/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentFirst
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-order mixed-kernel certificate on the first short-gap box. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure

/-! The short-gap midpoint tangent on the first compact interval. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open scoped BigOperators

open private Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

open private shortRootMultiplierReal from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison

private def box := CompactMiddleBox.ofIntervals (1 / 2) (5 / 8) 0 (1 / 8)
private def U := box.U
private def D := box.D
private def H := box.H
private def V := U.add D
private def neg (M : Model) := Model.zero.sub M
private def half := Model.ofRat (1 / 2)
private def halfGap := D.mul half
private def offset := (U.add halfGap).sub (Model.ofRat (19 / 32))
private def marginal (k : ℕ) (X : Model) := marginalMoment k 19 1 X H

private def inverse (X : Model) : Model :=
  let c := Model.center X
  let displacement := (X.sub (Model.ofRat c)).mul (Model.ofRat c⁻¹)
  let candidate := Model.series 9 (fun n ↦ Model.ofRat ((-1 : ℚ) ^ n / c)) displacement
  reciprocalFrom X candidate.polynomial X.lower.toNat

private def slope (X : Model) := (marginal 1 X).mul (inverse (marginal 0 X))
private def ZV := marginal 0 V
private def ZD := marginal 0 D
private def SV := slope V
private def SD := slope D
private def SUneg := slope (neg U)
private def SVneg := slope (neg V)
private def curvature := ((marginal 2 D).mul (inverse ZD)).sub (SD.pow 2)
private def multiplier := shortRootMultiplier D SUneg SVneg SV SD curvature (inverse U)
private def A := (inverse U).sub (SUneg.mul half)
private def B := (inverse V).sub (SVneg.mul half)
private def skew := (B.sub A).mul half
private def skewRadius : ℚ := ((skew.absUpper : ℚ) / scale) / 2
private def maxSkew := (Model.ofRat skewRadius).widen skewRadius
private def moment (j : Fin 4) (k : Fin 3) :=
  shiftedShortMidpointMomentModel j k 21 6 (19 / 32) (3 / 32) 9 offset H
private def joint := shortMidpointJointModel A B halfGap maxSkew (3 / 16) moment
private def kappa := ((Model.ofRat 1).add H).mul (Model.ofRat (1 / 4))
private def tangent := ((ZV.mul ZD).add (Model.ofRat 1)).mul half
private def negScore := neg ((joint.sub (A.mul B)).add
  (((kappa.mul V).mul tangent).mul multiplier))

private theorem inverse_sound {X : Model} {s t z x : ℝ} (hb : InBox s t z)
    (hx : X.Encloses s t z x) (h : 0 < X.lower) :
    (inverse X).Encloses s t z (1 / x) :=
  reciprocalFrom_lower_sound hb hx _ h

private theorem marginal_sound {p : ℕ} (hp : 0 < p) (k : ℕ) {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ)))
    (hx : X.Encloses s t z x) (hr : |x| ≤ 1) :
    (marginal k X).Encloses s t z (iteratedDeriv k (compactZ p) x) := by
  simpa [marginal] using marginalMoment_sound (k := k) (terms := 19) (r := 1)
    hp (by decide) hb hh hx (by simpa using hr) (by norm_num)

private theorem marginal_zero_sound {p : ℕ} (hp : 0 < p) {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ)))
    (hx : X.Encloses s t z x) (hr : |x| ≤ 1) :
    (marginal 0 X).Encloses s t z (compactZ p x) := by
  simpa using marginal_sound hp 0 hb hh hx hr

private theorem slope_sound {p : ℕ} (hp : 0 < p) {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ)))
    (hx : X.Encloses s t z x) (hr : |x| ≤ 1) (hpos : 0 < (marginal 0 X).lower) :
    (slope X).Encloses s t z (compactZSlope p x) := by
  have h := Model.mul_sound hb (marginal_sound hp 1 hb hh hx hr)
    (inverse_sound hb (marginal_zero_sound hp hb hh hx hr) hpos)
  simpa [slope, compactZSlope, marginalLogSlope, div_eq_mul_inv] using h

private theorem first_tangent_of_checks {p : ℕ} {u v : ℝ} (hp : 11 ≤ p)
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 5 / 8) (huv : u < v) (hd₁ : v - u ≤ 1 / 8)
    (hiu : 0 < U.lower) (hiv : 0 < V.lower) (hzv : 0 < ZV.lower) (hzd : 0 < ZD.lower)
    (hzu : 0 < (marginal 0 (neg U)).lower) (hzvneg : 0 < (marginal 0 (neg V)).lower)
    (hmultiplier : 0 ≤ multiplier.lower) (hscore : 0 < negScore.lower) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hu : 0 < u := by linarith
  have hv := hu.trans huv
  have hd : 0 < v - u := sub_pos.mpr huv
  obtain ⟨s,t,z,hb,hU,hD,hH⟩ := CompactMiddleBox.boxCoordinates hp
    (u₀ := 1 / 2) (u₁ := 5 / 8) (d₀ := 0) (d₁ := 1 / 8)
    (by norm_num) (by norm_num) (by simpa using hu₀) (by simpa using hu₁)
    (by simpa using hd.le) (by simpa using hd₁)
  have hU : U.Encloses s t z u := hU
  have hD : D.Encloses s t z (v - u) := hD
  have hH : H.Encloses s t z (3 / (p : ℝ)) := hH
  have hV : V.Encloses s t z v := by
    simpa only [V, add_sub_cancel] using Model.add_sound hU hD
  have hneg {X : Model} {x : ℝ} (hx : X.Encloses s t z x) :
      (neg X).Encloses s t z (-x) := by
    simpa only [neg, zero_sub] using Model.sub_sound (Model.zero_sound s t z) hx
  have bU : |u| ≤ 1 := by rw [abs_of_pos hu]; linarith
  have bV : |v| ≤ 1 := by rw [abs_of_pos hv]; linarith
  have bD : |v-u| ≤ 1 := by rw [abs_of_pos hd]; linarith
  have hZV := marginal_zero_sound hp₀ hb hH hV bV
  have hZD := marginal_zero_sound hp₀ hb hH hD bD
  have hSV := slope_sound hp₀ hb hH hV bV hzv
  have hSD := slope_sound hp₀ hb hH hD bD hzd
  have hSUneg := slope_sound hp₀ hb hH (hneg hU) (by simpa using bU) hzu
  have hSVneg := slope_sound hp₀ hb hH (hneg hV) (by simpa using bV) hzvneg
  have hInvU := inverse_sound hb hU hiu
  have hInvV := inverse_sound hb hV hiv
  have hcurvature : curvature.Encloses s t z (deriv (compactZSlope p) (v - u)) := by
    rw [deriv_compactZSlope hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀]
    simpa only [curvature, ZD, SD, div_eq_mul_inv] using Model.sub_sound
      (Model.mul_sound hb (marginal_sound hp₀ 2 hb hH hD bD) (inverse_sound hb hZD hzd))
      (Model.pow_sound hb hSD 2)
  have hMul := shortRootMultiplier_sound hb hD hSUneg hSVneg hSV hSD hcurvature hInvU
  have hHalf : half.Encloses s t z (1 / 2 : ℝ) := by
    simpa [half] using Model.ofRat_sound (1 / 2) s t z
  have hOne : (Model.ofRat 1).Encloses s t z 1 := by simpa using Model.ofRat_sound 1 s t z
  have hA : A.Encloses s t z (reflectedHalfLogSlope (compositionMoment p 0) u) := by
    rw [reflectedHalfLogSlope_eq_compactZSlope hp₀ hu.ne']
    simpa only [A, SUneg, div_eq_mul_inv] using
      Model.sub_sound hInvU (Model.mul_sound hb hSUneg hHalf)
  have hB : B.Encloses s t z (reflectedHalfLogSlope (compositionMoment p 0) v) := by
    rw [reflectedHalfLogSlope_eq_compactZSlope hp₀ hv.ne']
    simpa only [B, SVneg, div_eq_mul_inv] using
      Model.sub_sound hInvV (Model.mul_sound hb hSVneg hHalf)
  have hHalfGap : halfGap.Encloses s t z ((v - u) / 2) := by
    simpa [halfGap, div_eq_mul_inv] using Model.mul_sound hb hD hHalf
  have hOffset : offset.Encloses s t z ((u + v) / 2 - 19 / 32) := by
    have hconst : (Model.ofRat (19 / 32)).Encloses s t z (19 / 32 : ℝ) := by
      simpa using Model.ofRat_sound (19 / 32) s t z
    have he : u + (v - u) / 2 = (u + v) / 2 := by ring
    simpa only [offset, he] using Model.sub_sound (Model.add_sound hU hHalfGap) hconst
  have hMoment (j : Fin 4) (k : Fin 3) :
      (moment j k).Encloses s t z (shortMidpointMoment p j k ((u + v) / 2)) := by
    have hbound : Real.exp (2 * |(19 / 32 : ℝ)|) ≤ 9 := by
      have hupper := compactExp_sub_truncation_geometric_le (z := (19 / 16 : ℝ))
        (R := (19 / 16 : ℝ)) (m := 8) (by decide) (by norm_num) (by norm_num)
      have hupper' := (le_abs_self _).trans hupper
      norm_num [Finset.sum_range_succ, Nat.factorial] at hupper' ⊢
      linarith
    have hroff : |(u + v) / 2 - 19 / 32| ≤ (3 / 32 : ℝ) := abs_le.mpr
      ⟨by linarith, by linarith⟩
    have hh := shiftedShortMidpointMomentModel_sound (k := (k : ℕ)) (centerTerms := 21)
      (offsetTerms := 6) hp (by decide) (by decide) j hb hH hOffset
      (r := 3 / 32) (center := 19 / 32) (bound := 9)
      (by simpa using hroff) (by norm_num) (by norm_num) (by simpa using hbound)
    have he : (19 / 32 : ℝ) + ((u + v) / 2 - 19 / 32) = (u + v) / 2 := by ring
    simpa only [moment, Rat.cast_div, Rat.cast_ofNat, he] using hh
  let a := reflectedHalfLogSlope (compositionMoment p 0) u
  let b := reflectedHalfLogSlope (compositionMoment p 0) v
  have hSkew : skew.Encloses s t z ((b-a) / 2) := by
    simpa [skew, a, b, div_eq_mul_inv] using Model.mul_sound hb (Model.sub_sound hB hA) hHalf
  have hMax : maxSkew.Encloses s t z (max 0 ((b-a)/2)) := by
    apply Model.widen_sound (g := (skewRadius : ℝ)) (Model.ofRat_sound skewRadius s t z)
    have hc := Model.absUpper_sound hb hSkew
    have he : (skewRadius : ℝ) = (skew.absUpper : ℝ) / scale / 2 := by
      unfold skewRadius
      push_cast
      all_goals rfl
    rw [he, abs_le]
    have hcap : 0 ≤ (skew.absUpper : ℝ) / scale := by positivity
    have hmax_le : max 0 ((b-a)/2) ≤ (skew.absUpper : ℝ) / scale :=
      max_le hcap ((le_abs_self _).trans hc)
    have hmax_ge : 0 ≤ max 0 ((b-a)/2) := le_max_left _ _
    exact ⟨by linarith, by linarith⟩
  have hJoint := shortMidpointJointModel_sound (radius := 3 / 16) hb hA hB hHalfGap hMax hMoment
  have hκ : kappa.Encloses s t z (compactKappa p) := by
    have hquarter : (Model.ofRat (1 / 4)).Encloses s t z (1 / 4 : ℝ) := by
      simpa using Model.ofRat_sound (1 / 4) s t z
    simpa [kappa, compactKappa, div_eq_mul_inv] using
      Model.mul_sound hb (Model.add_sound hOne hH) hquarter
  have hTangent := Model.mul_sound hb (Model.add_sound (Model.mul_sound hb hZV hZD) hOne) hHalf
  have hbound := hneg (Model.add_sound (Model.sub_sound hJoint (Model.mul_sound hb hA hB))
    (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hκ hV) hTangent) hMul))
  rw [shortJointMajorant_eq_moments] at hbound
  have hNet : negScore.Encloses s t z (-shortMidpointTangentScore p u v (3 / 16) 1) := by
    simp only [Rat.cast_div, Rat.cast_ofNat] at hbound
    simp only [shortMidpointTangentScore, div_one]
    convert hbound using 1 <;> first | rfl | ring
  have hPositive := (div_pos (by exact_mod_cast hscore) scale_real_pos).trans_le
    (Model.lower_sound hb hNet)
  have hMPositive := (div_nonneg (by exact_mod_cast hmultiplier) scale_real_pos.le).trans
    (Model.lower_sound hb hMul)
  exact logKernel_mixed_neg_of_shortMidpointTangent hp₀ hu huv (by norm_num)
    (by linarith) (by norm_num) hMPositive (neg_pos.mp hPositive)

end RefinedBMV.PositiveCenter.CompactTaylorModel
