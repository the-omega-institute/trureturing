/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailJointScore
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint scalar score for the leading square and linear correction. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailPair
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapMoments

/-! The leading and linear mixed derivatives with a shared positive normalization. -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private tail_add_gap from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailFormula
open private CompactGap.W_eq_reflected from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel
open private CompactGap.W CompactGap.R CompactGap.c CompactGap.rate from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities
open private hasDerivAt_shortGapWeight from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapMoments
open private compositionMoment_marginal_smooth from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization

private noncomputable def geometricValue (h u : ℝ) : ℝ :=
  let n := 3 + h
  let k := 3 + 2 * h
  n * (1 + Real.exp (-(k * u))) / 2 + h -
    (1 - Real.exp (-(k * u))) / upperTailGap h u

private noncomputable def geometricDerivative (h u : ℝ) : ℝ :=
  let n := 3 + h
  let k := 3 + 2 * h
  let e := Real.exp (-(k * u))
  (upperTailSlope h u * (1 - e) - k * e) / upperTailGap h u - k * n * e / 2

private noncomputable def lossValue (h u : ℝ) : ℝ :=
  (1 - Real.exp (-((3 + h) * u)) * (1 + (3 + h) * upperTailGap h u)) / 2

private noncomputable def lossDerivative (h u : ℝ) : ℝ :=
  (3 + h) * (3 + 2 * h) / 2 * upperTailGap h u * Real.exp (-((3 + h) * u))

private theorem hasDerivAt_geometricValue {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    HasDerivAt (geometricValue h) (geometricDerivative h u) u := by
  let n : ℝ := 3 + h
  let k : ℝ := 3 + 2 * h
  let e := Real.exp (-(k * u))
  let f := upperTailGap h u
  let j := upperTailSlope h u
  have hE := hasDerivAt_upperTailLinearDecay k u
  have hF := hasDerivAt_upperTailGap (t := u) hh
  have hf : 0 < f := tail_gap_pos hh hu
  have hf' : Real.exp (-(h * u)) = j * f := by
    rw [← hF.deriv]
    exact (div_eq_iff hf.ne').mp (upperTailGap_logDeriv hh hu)
  have hconstant := ((hE.const_add 1).const_mul (n / 2)).add_const h
  have hquotient := (hE.const_sub 1).div (hF.congr_deriv hf') hf.ne'
  convert hconstant.sub hquotient using 1
  · funext t
    unfold geometricValue
    dsimp only [n, k, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
    ring
  · change (j * (1 - e) - k * e) / f - k * n * e / 2 =
      n / 2 * (-k * e) - (-(-k * e) * f - (1 - e) * (j * f)) / f ^ 2
    field_simp [hf.ne'] <;> ring

private theorem middleTail_coefficients_closed {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    let h : ℝ := 3 / (p : ℝ)
    h * middleTailLinearGeom (p + 1) h u = geometricValue h u ∧
    h * deriv (middleTailLinearGeom (p + 1) h) u = geometricDerivative h u ∧
    middleTailLinearLoss (p + 1) h u = lossValue h u ∧
    deriv (middleTailLinearLoss (p + 1) h) u = lossDerivative h u := by
  intro h
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have hform {t : ℝ} (ht : 0 < t) :
      h * middleTailLinearGeom (p + 1) h t = geometricValue h t := by
    have H := (middleTailLinear_coefficients hp ht).1
    change upperTailLinearA1 h t = _ at H
    unfold upperTailLinearA1 at H
    unfold geometricValue
    linarith only [H]
  have hnear : (fun t ↦ h * middleTailLinearGeom (p + 1) h t) =ᶠ[𝓝 u]
      geometricValue h := by
    filter_upwards [eventually_gt_nhds hu] with t ht
    exact hform ht
  have hdiff :=
    ((hasDerivAt_middleTailLinearGeom (p + 1) h u).differentiableAt.hasDerivAt).const_mul h
  have hgDeriv : h * deriv (middleTailLinearGeom (p + 1) h) u = geometricDerivative h u := by
    rw [← hdiff.deriv, hnear.deriv_eq, (hasDerivAt_geometricValue hh hu).deriv]
  have hL := (middleTailLinear_coefficients hp hu).2
  change 1 - upperTailLinearA h u = _ at hL
  have hlval : middleTailLinearLoss (p + 1) h u = lossValue h u := by
    unfold upperTailLinearA at hL
    unfold lossValue
    linarith only [hL, mul_comm (Real.exp (-((3 + h) * u))) (1 + (3 + h) * upperTailGap h u)]
  have hrate : h * ((p + 1 : ℕ) : ℝ) = 3 + h := by
    dsimp only [h]
    push_cast
    field_simp [hpR.ne'] <;> ring
  have hrate' : h * (((p + 1 : ℕ) : ℝ) + 1) = 3 + 2 * h := by
    linarith only [hrate]
  have hgap : 1 - Real.exp (-(h * u)) = h * upperTailGap h u := by
    unfold upperTailGap
    field_simp [hh.ne'] <;> ring
  have hld : deriv (middleTailLinearLoss (p + 1) h) u = lossDerivative h u := by
    rw [(hasDerivAt_middleTailLinearLoss (p + 1) h u).deriv, hrate, hgap]
    unfold lossDerivative
    linear_combination
      (Real.exp (-((3 + h) * u)) * upperTailGap h u / 2) *
        (h * (((p + 1 : ℕ) : ℝ) + 1) * hrate + (3 + h) * hrate')
  exact ⟨hform hu, hgDeriv, hlval, hld⟩

/-- The physical linear profile under the same positive scaling as the leading score. -/
theorem middleTailLinear_clearedMixed_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let B := middleTailRatio h u v
    let a := reflectedHalfLogSlope (compositionMoment p 0)
    let j := upperTailSlope h
    let η := j d * (h + j d)
    let f := upperTailGap h d
    let c := (3 + h) * (3 + 2 * h) / 2
    let y := 1 + h + j v + a v
    let z := 2 + h - a u
    let L := lossValue h u
    (2 / B * (Real.sqrt (C u) * Real.sqrt (C v))) *
      deriv (fun t ↦ deriv (fun x ↦ middleTailLinearContribution p x t) u) v =
        2 * Real.exp (-((1 + h) * d)) / (c * f) *
          (-y * (z * geometricValue h u + geometricDerivative h u) +
            ((y + j d) * (z * L + lossDerivative h u + L * j d) + L * η) / f) := by
  intro h d C B a j η f c y z L
  let β : ℝ → ℝ := fun t ↦ 1 - Real.exp (-(h * t))
  let D := middleTailLinearGeom (p + 1) h
  let E := middleTailLinearLoss (p + 1) h
  have hExact := middleTailLinear_mixed_eq hp hu huv
  change deriv (fun t ↦ deriv (fun x ↦ middleTailLinearContribution p x t) u) v =
    (h ^ 2 / c * (Real.exp ((2 + h) * u) * (Real.sqrt (C u))⁻¹) *
      (Real.exp (-((1 + h) * v)) * (Real.sqrt (C v))⁻¹ * (β v)⁻¹)) *
      (-y * (z * D u + deriv D u) +
        ((y + j d) * (z * E u + deriv E u + E u * j d) + E u * η) / β d) at hExact
  have hh : 0 < h := by dsimp only [h]; positivity
  have hv := hu.trans huv
  have hd : 0 < d := sub_pos.mpr huv
  have hf : 0 < f := tail_gap_pos hh hd
  have hfv : 0 < upperTailGap h v := tail_gap_pos hh hv
  have hc : 0 < c := by dsimp only [c]; positivity
  have hCu : 0 < Real.sqrt (C u) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hCv : 0 < Real.sqrt (C v) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne'))
  have hβ (t : ℝ) : β t = h * upperTailGap h t := by
    unfold upperTailGap
    change β t = h * (β t / h)
    field_simp [hh.ne'] <;> ring
  have he : Real.exp ((2 + h) * u) * Real.exp (-((1 + h) * v)) =
      Real.exp u * Real.exp (-((1 + h) * d)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  obtain ⟨hD, hD', hL, hL'⟩ := middleTail_coefficients_closed hp hu
  change h * D u = geometricValue h u at hD
  change h * deriv D u = geometricDerivative h u at hD'
  change E u = L at hL
  change deriv E u = lossDerivative h u at hL'
  have hD₀ : D u = geometricValue h u / h := (eq_div_iff hh.ne').mpr (by simpa [mul_comm] using hD)
  have hD₁ : deriv D u = geometricDerivative h u / h :=
    (eq_div_iff hh.ne').mpr (by simpa [mul_comm] using hD')
  have hB : B = Real.exp u * f / upperTailGap h v := rfl
  have hfactor : (2 / B * (Real.sqrt (C u) * Real.sqrt (C v))) *
      (h ^ 2 / c * (Real.exp ((2 + h) * u) * (Real.sqrt (C u))⁻¹) *
        (Real.exp (-((1 + h) * v)) * (Real.sqrt (C v))⁻¹ * (β v)⁻¹)) =
      2 * h * Real.exp (-((1 + h) * d)) / (c * f) := by
    rw [hB, hβ v]
    calc
      _ = (2 * h / (c * f * Real.exp u)) *
          (Real.exp ((2 + h) * u) * Real.exp (-((1 + h) * v))) := by
        field_simp [hh.ne', hf.ne', hfv.ne', hc.ne', hCu.ne', hCv.ne', (Real.exp_pos u).ne']
        <;> ring
      _ = _ := by
        rw [he]
        field_simp [(Real.exp_pos u).ne', hc.ne', hf.ne'] <;> ring
  have hβd : β d = h * f := hβ d
  rw [hExact, ← mul_assoc, hfactor, hD₀, hD₁, hL, hL', hβd]
  field_simp [hh.ne', hc.ne', hf.ne'] <;> ring

/-- The leading mixed contribution after clearing its positive ratio and marginal weights. -/
noncomputable def middleTailLeadingScore (h u d a b : ℝ) : ℝ :=
  let v := d + u
  let f := upperTailGap h
  let j := upperTailSlope h d
  let q := f v * Real.exp (-u) / f d
  let δ := Real.exp (-(h * d)) * f u / (f d * f v)
  let η := j * (h + j)
  let ell := 1 - j
  (1 - q ^ 2) * (η + δ * (ell - a) - b * ell) + b * a * (1 - q) ^ 2 + 2 * δ * ell * q ^ 2

/-- The linear correction under the same normalization. -/
noncomputable def middleTailLinearScore (h u d a b : ℝ) : ℝ :=
  let j := upperTailSlope h d
  let η := j * (h + j)
  let f := upperTailGap h d
  let c := (3 + h) * (3 + 2 * h) / 2
  let y := 1 + h + upperTailSlope h (d + u) + b
  let z := 2 + h - a
  let L := lossValue h u
  2 * Real.exp (-((1 + h) * d)) / (c * f) *
    (-y * (z * geometricValue h u + geometricDerivative h u) +
      ((y + j) * (z * L + lossDerivative h u + L * j) + L * η) / f)

private theorem middleTail_gapSlope_sub {h u d : ℝ} (hh : 0 < h) (hu : 0 < u) (hd : 0 < d) :
    let f := upperTailGap h
    upperTailSlope h d - upperTailSlope h (d + u) =
      Real.exp (-(h * d)) * f u / (f d * f (d + u)) := by
  intro f
  have hd' : 0 < f d := tail_gap_pos hh hd
  have hv : 0 < d + u := add_pos hd hu
  have hv' : 0 < f (d + u) := tail_gap_pos hh hv
  have hE : Real.exp (-(h * (d + u))) = Real.exp (-(h * d)) * Real.exp (-(h * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← upperTailGap_logDeriv hh hd, ← upperTailGap_logDeriv hh hv,
    (hasDerivAt_upperTailGap hh).deriv, (hasDerivAt_upperTailGap hh).deriv, hE]
  change Real.exp (-(h * d)) / f d -
    (Real.exp (-(h * d)) * Real.exp (-(h * u))) / f (d + u) = _
  field_simp [hd'.ne', hv'.ne']
  have hsum : f (d + u) = f u + Real.exp (-(h * u)) * f d := tail_add_gap hh u d
  rw [hsum]
  ring

/-- The exact paired score suffices on the central strip where the radical
mixed contribution is already known to be strictly negative. -/
theorem logKernel_mixed_neg_of_middleTail_scores {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4) (hd₀ : 13 / 4 ≤ v - u)
    (hscore :
      let h : ℝ := 3 / (p : ℝ)
      let a := reflectedHalfLogSlope (compositionMoment p 0)
      middleTailLeadingScore h u (v - u) (a u) (a v) +
        middleTailLinearScore h u (v - u) (a u) (a v) < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
  let B := middleTailRatio h u v
  let a := reflectedHalfLogSlope (compositionMoment p 0)
  let scale := 2 / B * (Real.sqrt (C u) * Real.sqrt (C v))
  have hp₀ : 0 < p := by omega
  have hh : 0 < h := by dsimp only [h]; positivity
  have hu : 0 < u := by linarith only [hu₀]
  have hd : 0 < d := by dsimp only [d]; linarith only [hd₀]
  have huv : u < v := sub_pos.mp hd
  have hv := hu.trans huv
  have hv₁ : 1 ≤ v := by linarith only [hu₀, hd₀]
  have hfd : 0 < upperTailGap h d := tail_gap_pos hh hd
  have hfv : 0 < upperTailGap h v := tail_gap_pos hh hv
  have hB : 0 < B := div_pos (mul_pos (Real.exp_pos u) hfd) hfv
  have hCu : 0 < Real.sqrt (C u) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr hu.ne'))
  have hCv : 0 < Real.sqrt (C v) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr hv.ne'))
  have hscale : 0 < scale := mul_pos (div_pos (by norm_num) hB) (mul_pos hCu hCv)
  have hq : B⁻¹ = upperTailGap h v * Real.exp (-u) / upperTailGap h d := by
    change (Real.exp u * upperTailGap h d / upperTailGap h v)⁻¹ = _
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos u).ne', hfd.ne', hfv.ne'] <;> ring
  have hδ := middleTail_gapSlope_sub hh hu hd
  change upperTailSlope h d - upperTailSlope h (d + u) =
    Real.exp (-(h * d)) * upperTailGap h u / (upperTailGap h d * upperTailGap h (d + u)) at hδ
  rw [sub_add_cancel v u] at hδ
  have hleading : scale *
      deriv (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) v =
        middleTailLeadingScore h u d (a u) (a v) := by
    rw [show scale = 2 / B * (Real.sqrt (C u) * Real.sqrt (C v)) from rfl,
      middleTailLeading_mixed_eq hp₀ hu huv]
    change (1 - B⁻¹ ^ 2) * _ + _ + _ = _
    unfold middleTailLeadingScore
    dsimp only
    rw [sub_add_cancel v u, hq, hδ]
  have hlinear : scale *
      deriv (fun y ↦ deriv (fun x ↦ middleTailLinearContribution p x y) u) v =
        middleTailLinearScore h u d (a u) (a v) := by
    rw [show scale = 2 / B * (Real.sqrt (C u) * Real.sqrt (C v)) from rfl,
      middleTailLinear_clearedMixed_eq hp₀ hu huv]
    unfold middleTailLinearScore
    dsimp only
    rw [sub_add_cancel v u]
  have hneg : deriv (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) v +
      deriv (fun y ↦ deriv (fun x ↦ middleTailLinearContribution p x y) u) v < 0 := by
    apply (mul_lt_mul_iff_right₀ hscale).mp
    rw [mul_add, hleading, hlinear, mul_zero]
    exact hscore
  rw [middleTail_kernel_mixed_eq hp₀ hu huv hv₁]
  exact add_neg hneg (middleTail_radical_mixed_neg hp₀ hu₀ hu₁ hd₀)

/-- The reflected half-logarithmic slope can be evaluated through the
regularized exponential weight at all positive coordinates. -/
theorem middleTail_reflectedSlope_eq {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h : ℝ := 3 / (p : ℝ)
    let k := 3 + 2 * h
    let f := upperTailGap h t
    let j := upperTailSlope h t
    let g := k * f - 1 + Real.exp (-(k * t))
    reflectedHalfLogSlope (compositionMoment p 0) t =
      ((1 - 2 * j) * g + k * (Real.exp (-(h * t)) - Real.exp (-(k * t)))) /
        (2 * shortGapWeight h t) := by
  intro h k f j g
  let c := (3 + h) * k / 2
  let C : ℝ → ℝ := fun x ↦ compositionMoment p 0 (-x)
  let W := shortGapWeight h
  let E := Real.exp (-t)
  let b := Real.exp (-(h * t))
  let e := Real.exp (-(k * t))
  have hh : 0 < h := by dsimp only [h]; positivity
  have hf : 0 < f := tail_gap_pos hh ht
  have hc : 0 < c := by dsimp only [c, k]; positivity
  have hC : 0 < C t := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  have hEq : W = fun x ↦ c * upperTailGap h x ^ 2 * Real.exp (-x) * C x := by
    funext x
    exact CompactGap.W_eq_reflected hp x
  have hF := hasDerivAt_upperTailGap (t := t) hh
  have hlog : b = j * f := by
    change Real.exp (-(h * t)) = _
    rw [← hF.deriv]
    exact (div_eq_iff hf.ne').mp (upperTailGap_logDeriv hh ht)
  have hCd : HasDerivAt C (deriv C t) t :=
    (((compositionMoment_marginal_smooth p).differentiable (by norm_num) (-t)).comp t
      differentiableAt_id.neg).hasDerivAt
  have hw := ((((hF.pow 2).const_mul c).mul (hasDerivAt_id' t).neg.exp).mul hCd).deriv
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.neg_apply, Nat.reduceSub, pow_one,
    Nat.cast_ofNat] at hw
  change deriv (fun x ↦ c * upperTailGap h x ^ 2 * Real.exp (-x) * C x) t =
    (c * (2 * f * b) * E + c * f ^ 2 * (E * -1)) * C t +
      c * f ^ 2 * E * deriv C t at hw
  rw [← hEq] at hw
  have hD := (hasDerivAt_shortGapWeight (t := t) hh).deriv
  change deriv W t = k * (b - e) + c * f * E * (f - 2 * b) at hD
  have hg : g = W t + c * f ^ 2 * E := by
    dsimp only [g, W, c, k, f, E, shortGapWeight]
    ring
  have hCleared : (1 - 2 * j) * g + k * (b - e) = c * f ^ 2 * E * deriv C t := by
    rw [hD] at hw
    rw [hg, congrFun hEq t]
    change (1 - 2 * j) * (c * f ^ 2 * E * C t + c * f ^ 2 * E) +
      k * (b - e) = c * f ^ 2 * E * deriv C t
    rw [hlog] at hw ⊢
    linear_combination hw
  change deriv C t / C t / 2 = ((1 - 2 * j) * g + k * (b - e)) / (2 * W t)
  rw [div_div, mul_comm (C t) 2]
  rw [hCleared, congrFun hEq t]
  change deriv C t / (2 * C t) = c * f ^ 2 * E * deriv C t / (2 * (c * f ^ 2 * E * C t))
  have hE : E ≠ 0 := (Real.exp_pos (-t)).ne'
  field_simp [hc.ne', hf.ne', hE, hC.ne'] <;> ring

end RefinedBMV.PositiveCenter
