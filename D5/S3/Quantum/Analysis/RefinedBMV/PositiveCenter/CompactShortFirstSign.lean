/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortFirstSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point sign replay on the first compact short-gap box. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortFirstBand
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortFirstWitnesses

/-! The kernel sign on the first compact short-gap box. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open DimThree.Certificate (Sparse)
open private U₁ D₁ H₁ V₁ A₁ T₁ neg neg_sound m0 m1 m2 Zmu Zmv Zv Zd Jt F₁ Gap₁ DecayInput₁
  coordinates slope slope_sound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortFirstBand

private def inverse (p : Model) (q : Sparse) : Model := reciprocalFrom p q p.lower.toNat

private def rootRatio : ℚ := 22 / 25
private def rootModel : Model :=
  ((Zv.mul (Model.ofRat rootRatio)).add (Zd.mul (Model.ofRat rootRatio⁻¹))).mul (Model.ofRat (1 / 2))

private theorem sqrt_le_affine_root {x y q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 < q) :
    Real.sqrt (x * y) ≤ (x * q + y * q⁻¹) * (1 / 2) := by
  have hxq : 0 ≤ x * q := mul_nonneg hx hq.le
  have hyq : 0 ≤ y * q⁻¹ := mul_nonneg hy (inv_nonneg.mpr hq.le)
  have hxy : x * q * (y * q⁻¹) = x * y := by
    field_simp [hq.ne']
  rw [← hxy, Real.sqrt_mul hxq]
  nlinarith only [sq_nonneg (Real.sqrt (x * q) - Real.sqrt (y * q⁻¹)),
    Real.sq_sqrt hxq, Real.sq_sqrt hyq]

private def Su := slope 1 (neg U₁) (inverse Zmu CompactShortFirstWitnesses.negLower)
private def Sv := slope 2 (neg V₁) (inverse Zmv CompactShortFirstWitnesses.negUpper)
private def Tv := slope 2 V₁ (inverse Zv CompactShortFirstWitnesses.upper)
private def Td := slope 1 D₁ (inverse Zd CompactShortFirstWitnesses.gap)
private def Wd := ((m2 1 D₁).mul (inverse Zd CompactShortFirstWitnesses.gap)).sub (Td.pow 2)
private def Iu := inverse U₁ CompactShortFirstWitnesses.lowerCoordinate
private def Iv := inverse V₁ CompactShortFirstWitnesses.upperCoordinate
private def K := inverse Gap₁ CompactShortFirstWitnesses.cutoff
private def J := jointEvenTaylor 3 A₁ (inverse F₁ CompactShortFirstWitnesses.sinhc) Jt
private def score :=
  shortScore U₁ D₁ H₁ Zv Zd Su Sv Tv Td Wd Iu Iv K U₁.centeredExp DecayInput₁.centeredExp J rootModel

private theorem m0_sound {p : ℕ} (hp : 0 < p) {s t z x : ℝ} {X : Model} {r : ℚ}
    (hb : InBox s t z) (hh : H₁.Encloses s t z (3 / (p : ℝ))) (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / 20 < 1) :
    (m0 r X).Encloses s t z (compactZ p x) := by
  simpa only [m0, iteratedDeriv_zero] using
    marginalMoment_sound (k := 0) (terms := 19) hp (by decide) hb hh hx hr (by simpa using hsmall)

private theorem firstSign_of_checks {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hu₂ : u ≤ 1) (huv : u < v) (hd₂ : v - u ≤ 1)
    (hZmu : 0 < Zmu.lower) (hZmv : 0 < Zmv.lower)
    (hZv : 0 < Zv.lower) (hZd : 0 < Zd.lower) (hIu : 0 < U₁.lower) (hIv : 0 < V₁.lower)
    (hJ : 0 < F₁.lower) (hK : 0 < Gap₁.lower)
    (hMultiplier : 0 ≤ (shortRootMultiplier D₁ Su Sv Tv Td Wd Iu).lower)
    (hGap : (H₁.mul (neg U₁)).argumentRadius ≤ 2)
    (hExp : U₁.expChecks) (hDecay : DecayInput₁.expChecks) (hScore : 0 < score.lower) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let s := 4 * u - 3
  let t := 2 * (v - u) - 1
  let z := 22 / (p : ℝ) - 1
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hu : 0 < u := by linarith
  have hd : 0 < v - u := sub_pos.mpr huv
  have hv := hu.trans huv
  have bU : |u| ≤ 1 := by simpa only [abs_of_pos hu] using hu₂
  have bV : |v| ≤ 2 := by rw [abs_of_pos hv]; linarith
  have bD : |v - u| ≤ 1 := by simpa only [abs_of_pos hd] using hd₂
  obtain ⟨hb, huₘ, hdₘ, hhₘ⟩ :
      InBox s t z ∧ U₁.Encloses s t z u ∧ D₁.Encloses s t z (v - u) ∧
        H₁.Encloses s t z (3 / (p : ℝ)) := coordinates hp hu₁ hu₂ huv hd₂
  have hvₘ : V₁.Encloses s t z v := by
    simpa only [add_sub_cancel] using Model.add_sound huₘ hdₘ
  have ha : A₁.Encloses s t z (u / 2) := by
    simpa [A₁, div_eq_mul_inv] using Model.mul_sound hb huₘ (Model.ofRat_sound (1/2) s t z)
  have ht : T₁.Encloses s t z (v - u / 2) := Model.sub_sound hvₘ ha
  have htBound : |v - u / 2| ≤ (3 / 2 : ℝ) := by
    rw [abs_of_pos (show 0 < v - u / 2 by linarith)]
    linarith
  have hzmU := m0_sound (r := 1) hp₀ hb hhₘ (neg_sound huₘ) (by simpa using bU) (by norm_num)
  have hzmV := m0_sound (r := 2) hp₀ hb hhₘ (neg_sound hvₘ) (by simpa using bV) (by norm_num)
  have hzV := m0_sound (r := 2) hp₀ hb hhₘ hvₘ (by exact_mod_cast bV) (by norm_num)
  have hzD := m0_sound (r := 1) hp₀ hb hhₘ hdₘ (by exact_mod_cast bD) (by norm_num)
  have hiMu := reciprocalFrom_lower_sound hb hzmU CompactShortFirstWitnesses.negLower hZmu
  have hiMv := reciprocalFrom_lower_sound hb hzmV CompactShortFirstWitnesses.negUpper hZmv
  have hiV := reciprocalFrom_lower_sound hb hzV CompactShortFirstWitnesses.upper hZv
  have hiD := reciprocalFrom_lower_sound hb hzD CompactShortFirstWitnesses.gap hZd
  have hsU := slope_sound (r := 1) hp₀ hb hhₘ (neg_sound huₘ) (by simpa using bU) (by norm_num) hiMu
  have hsV := slope_sound (r := 2) hp₀ hb hhₘ (neg_sound hvₘ) (by simpa using bV) (by norm_num) hiMv
  have htV := slope_sound (r := 2) hp₀ hb hhₘ hvₘ (by exact_mod_cast bV) (by norm_num) hiV
  have htD := slope_sound (r := 1) hp₀ hb hhₘ hdₘ (by exact_mod_cast bD) (by norm_num) hiD
  have hwD : Wd.Encloses s t z (deriv (compactZSlope p) (v - u)) := by
    rw [deriv_compactZSlope hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀]
    have h₂ := marginalMoment_sound (k := 2) (terms := 17) (r := 1) hp₀ (by decide) hb hhₘ hdₘ
      (by exact_mod_cast bD) (by norm_num)
    simpa only [div_eq_mul_inv, one_mul] using
      Model.sub_sound (Model.mul_sound hb h₂ hiD) (Model.pow_sound hb htD 2)
  have hiu := reciprocalFrom_lower_sound hb huₘ CompactShortFirstWitnesses.lowerCoordinate hIu
  have hiv := reciprocalFrom_lower_sound hb hvₘ CompactShortFirstWitnesses.upperCoordinate hIv
  have hrate : 0 < 3 / (p : ℝ) := by positivity
  have hGapSound : Gap₁.Encloses s t z (upperTailGap (3 / (p : ℝ)) u) := by
    have hm := neg_sound (positiveRateGapModel_sound hb hhₘ (neg_sound huₘ)
      hrate.ne' (neg_ne_zero.mpr hu.ne') hGap)
    simpa only [Gap₁, upperTailGap, mul_neg, neg_div, neg_sub] using hm
  have hcut := reciprocalFrom_lower_sound hb hGapSound CompactShortFirstWitnesses.cutoff hK
  have hHA := Model.mul_sound hb hhₘ ha
  have hExpArg : |(3 / (p : ℝ)) * (u / 2)| ≤ (3 / 22 : ℝ) := by
    have hp₁₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
    have hrateBound : 3 / (p : ℝ) ≤ (3 / 11 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp₁₁
    rw [abs_of_pos (mul_pos hrate (half_pos hu))]
    calc
      _ ≤ (3 / 11 : ℝ) * (1 / 2) :=
        mul_le_mul hrateBound (by linarith) (by positivity) (by norm_num)
      _ = _ := by norm_num
  have hsinh : F₁.Encloses s t z
      (Real.sinh ((3 / (p : ℝ)) * (u / 2)) / ((3 / (p : ℝ)) * (u / 2))) :=
    sinhcGeometricModel_sound (radius := 3 / 22) hb hHA
      (mul_ne_zero hrate.ne' (half_pos hu).ne') (by exact_mod_cast hExpArg) (by norm_num)
  have hiJ := reciprocalFrom_lower_sound hb hsinh CompactShortFirstWitnesses.sinhc hJ
  have hjoint : J.Encloses s t z (compositionMomentEvenTaylor p 3 u v) :=
    jointEvenTaylor_sound hb ha hiJ (fun j hj ↦ by
      change (tiltedMoment (2 * j) (21 - 2 * j) (3/2) T₁ H₁).Encloses s t z _
      refine tiltedMoment_sound hp (by omega) hb hhₘ ht (by exact_mod_cast htBound) ?_
      rw [div_lt_iff₀ (by positivity)]
      norm_num
      exact_mod_cast (show 3 < (21 - 2 * j).succ by omega))
  have hDecayInput : DecayInput₁.Encloses s t z (-(1 + 3 / (p : ℝ)) * u) := by
    simpa only [DecayInput₁, neg_mul, add_comm, Rat.cast_one] using
      neg_sound (Model.mul_sound hb (Model.add_sound hhₘ (Model.ofRat_sound 1 s t z)) huₘ)
  have hroot := Model.mul_sound hb
    (Model.add_sound (Model.mul_sound hb hzV (Model.ofRat_sound rootRatio s t z))
      (Model.mul_sound hb hzD (Model.ofRat_sound rootRatio⁻¹ s t z)))
    (Model.ofRat_sound (1 / 2) s t z)
  have hroot' : rootModel.Encloses s t z
      ((compactZ p v * (rootRatio : ℝ) + compactZ p (v - u) * (rootRatio : ℝ)⁻¹) * (1 / 2)) := by
    simpa [rootModel] using hroot
  have hbound := sqrt_le_affine_root (compactZ_pos hp₀ v).le (compactZ_pos hp₀ (v - u)).le
    (show 0 < (rootRatio : ℝ) by norm_num [rootRatio])
  have hcompare := shortScore_lower_of_upper_root hp₀ hb hu huv huₘ hdₘ hhₘ hzV hzD hsU hsV htV htD hwD
    hiu hiv hcut (Model.expChecks_sound hb huₘ hExp)
      (Model.expChecks_sound hb hDecayInput hDecay) hjoint hroot' hbound hMultiplier
  exact logKernel_mixed_neg_of_joint_lower hp₀ hu huv
    (compactMixedT_strictAnti_of_slope hp₀ hu
      (reflectedHalfLogSlope_lt_two_add_spacing hp (hu₁.trans huv.le))).antitone
    (compositionMomentEvenTaylor_le hp₀ 3 hu v)
    ((div_pos (by exact_mod_cast hScore) scale_real_pos).trans_le hcompare)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- The mixed derivative is negative on the first compact short-gap box. -/
theorem logKernel_mixed_neg_short_first {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hu₂ : u ≤ 1) (huv : u < v) (hd₂ : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  apply firstSign_of_checks hp hu₁ hu₂ huv hd₂ <;> decide +kernel

end RefinedBMV.PositiveCenter.CompactTaylorModel
