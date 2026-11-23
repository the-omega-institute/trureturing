/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailLinearContribution
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed derivative of the normalized linear contribution from gap three. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailLinearGeometric
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet

/-! The linear summand of the separated positive-center kernel. -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private hasDerivAt_tailBeta from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet
open private compositionMoment_marginal_smooth reflectedHalfLogSlope_nonneg from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization

/-- The linear summand in the exact normalized kernel decomposition. -/
noncomputable def middleTailLinearContribution (p : ℕ) (u v : ℝ) : ℝ :=
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  upperTailBaseFactor p u d * upperTailLinearError h u d /
    Real.sqrt (upperTailNormalizer (p + 1) h (((p + 2).choose 2 : ℝ) / (p + 1)) v)

private theorem middleTailLinearContribution_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let β : ℝ → ℝ := fun t ↦ 1 - Real.exp (-(h * t))
    let k := h ^ 2 / ((3 + h) * (3 + 2 * h) / 2)
    middleTailLinearContribution p u v =
      k * (Real.exp ((2 + h) * u) * (Real.sqrt (C u))⁻¹) *
        (Real.exp (-((1 + h) * v)) * (Real.sqrt (C v))⁻¹ * (β v)⁻¹) *
        (middleTailLinearGeom (p + 1) h u -
          middleTailLinearLoss (p + 1) h u * (β d)⁻¹) := by
  intro h d C β k
  let N : ℝ := ((p + 2).choose 2 : ℝ) / (p + 1)
  let A := upperTailNormalizer (p + 1) h N
  let g := upperTailGap h d
  let ell := 1 - Real.exp (-u)
  let c := (3 + h) * (3 + 2 * h) / 2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have hv := hu.trans huv
  have hd : 0 < d := sub_pos.mpr huv
  have hβ (t : ℝ) (ht : 0 < t) : 0 < β t :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))
  have hg : 0 < g := upperTailLinear_gap_pos hh hd
  have hβd : β d = h * g := by
    change β d = h * (β d / h)
    field_simp [hh.ne'] <;> ring
  have hN : 0 < N := by
    have hchoose : 0 < ((p + 2).choose 2 : ℝ) := by
      exact_mod_cast (Nat.choose_pos (show 2 ≤ p + 2 by omega))
    dsimp only [N]
    positivity
  have hCv : 0 < C v := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hA : A v = N * (Real.exp (-v) * (β v * C v)) := by
    have hlo := upperTail_lower_weight hp v 0
    dsimp only at hlo
    simp only [zero_add, neg_zero, zero_div, Real.exp_zero, mul_zero] at hlo
    have hup := upperTail_upper_weight hp hv
    change (1 - (Real.exp (-v / (p : ℝ))) ^ 3) *
      DimThree.defect p (Real.exp (-v / (p : ℝ))) 1 1 = (p + 1 : ℝ) * A v at hup
    rw [hlo, (tail_cube_pow hp v).1] at hup
    have hn : (p + 1 : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    change (p + 1 : ℝ) * A v =
      (p + 1 : ℝ) * (((p + 2).choose 2 : ℝ) / (p + 1) * (Real.exp (-v) * (β v * C v)))
    rw [← hup]
    change β v * (((p + 2).choose 2 : ℝ) * Real.exp (-v) * C v) = _
    field_simp [hn] <;> ring
  have hexpRoot : Real.sqrt (Real.exp (-v)) = Real.exp (-v / 2) := by
    rw [show Real.exp (-v) = (Real.exp (-v / 2)) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring, Real.sqrt_sq (Real.exp_pos _).le]
  have hroot : Real.sqrt (A v) =
      Real.sqrt N * (Real.exp (-v / 2) * (Real.sqrt (β v) * Real.sqrt (C v))) := by
    rw [hA, Real.sqrt_mul hN.le, Real.sqrt_mul (Real.exp_pos _).le,
      Real.sqrt_mul (hβ v hv).le, hexpRoot]
  have he : Real.exp (-d / 2) * Real.exp (u / 2) =
      Real.exp u * Real.exp (-v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  have he' : Real.exp ((2 + h) * u) * Real.exp (-((1 + h) * v)) =
      Real.exp u * Real.exp (-((1 + h) * d)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  obtain ⟨hD, hL⟩ := middleTailLinear_coefficients hp hu
  have hE := upperTailLinearError_eq_regularized hh hu hd
  change upperTailLinearError h u d =
    Real.exp (-((1 + h) * d)) *
      (upperTailLinearA h u - 1 + g * upperTailLinearA1 h u) / (c * g ^ 2 * ell ^ 2) at hE
  rw [show upperTailLinearA h u - 1 = -2 * middleTailLinearLoss (p + 1) h u by
    linarith only [hL], hD] at hE
  let S := Real.sqrt (C u) * Real.sqrt (C v) * β v
  have hsu := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hsv := Real.sqrt_pos.mpr hCv
  have hb := Real.sqrt_pos.mpr (hβ v hv)
  have hsβ : (β v)⁻¹ = (Real.sqrt (β v))⁻¹ ^ 2 := by
    rw [inv_pow, Real.sq_sqrt (hβ v hv).le]
  have hBase : upperTailBaseFactor p u d / Real.sqrt (A v) =
      Real.exp u * (h * g * ell ^ 2 / (2 * S)) := by
    unfold upperTailBaseFactor
    change Real.sqrt N / 2 * Real.exp (-d / 2) *
      (β d / Real.sqrt (β (d + u))) *
      (Real.exp (u / 2) * ell ^ 2 / Real.sqrt (C u)) / Real.sqrt (A v) = _
    rw [show d + u = v by exact sub_add_cancel v u, hroot, hβd]
    calc
      _ = (Real.exp (-d / 2) * Real.exp (u / 2)) *
          (h * g * ell ^ 2 / (2 * S * Real.exp (-v / 2))) := by
        dsimp only [S]
        simp only [div_eq_mul_inv, mul_inv_rev, hsβ]
        field_simp [hsu.ne', hsv.ne', hb.ne', (Real.sqrt_pos.mpr hN).ne',
          (Real.exp_pos (-v / 2)).ne'] <;> ring
      _ = _ := by
        rw [he]
        field_simp [(Real.exp_pos (-v / 2)).ne'] <;> ring
  have hc : 0 < c := by dsimp only [c]; positivity
  have hk : k = h ^ 2 / c := rfl
  let D := middleTailLinearGeom (p + 1) h u
  let L := middleTailLinearLoss (p + 1) h u
  have hright :
      k * (Real.exp ((2 + h) * u) * (Real.sqrt (C u))⁻¹) *
        (Real.exp (-((1 + h) * v)) * (Real.sqrt (C v))⁻¹ * (β v)⁻¹) *
        (D - L * (β d)⁻¹) =
      (Real.exp u * Real.exp (-((1 + h) * d))) * (k / S * (D - L * (β d)⁻¹)) := by
    rw [← he']
    simp only [S, div_eq_mul_inv, mul_inv_rev]
    ring
  change upperTailBaseFactor p u d * upperTailLinearError h u d / Real.sqrt (A v) = _
  rw [mul_div_right_comm, hBase, hE, hright, hk, hβd]
  have hS : 0 < S := mul_pos (mul_pos hsu hsv) (hβ v hv)
  field_simp [hh.ne', hg.ne', hc.ne', hS.ne', (upperTailLinear_ell_pos hu).ne'] <;> ring

private theorem hasDerivAt_middleTail_invBeta {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let β : ℝ → ℝ := fun x ↦ 1 - Real.exp (-(h * x))
    HasDerivAt (fun x ↦ (β x)⁻¹) (-upperTailSlope h t * (β t)⁻¹) t := by
  intro β
  have hb : 0 < β t :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))
  have hβ : HasDerivAt β (upperTailSlope h t * β t) t := hasDerivAt_tailBeta hh ht
  refine (hβ.inv hb.ne').congr_deriv ?_
  field_simp [hb.ne'] <;> ring

private theorem hasDerivAt_middleTail_invMarginal {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let C : ℝ → ℝ := fun x ↦ compositionMoment p 0 (-x)
    HasDerivAt (fun x ↦ (Real.sqrt (C x))⁻¹)
      (-reflectedHalfLogSlope (compositionMoment p 0) t * (Real.sqrt (C t))⁻¹) t := by
  intro C
  have hC : 0 < C t := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  have hs := Real.sqrt_pos.mpr hC
  have hd : DifferentiableAt ℝ C t :=
    ((compositionMoment_marginal_smooth p).differentiable (by norm_num) (-t)).comp t
      differentiableAt_id.neg
  refine ((hd.hasDerivAt.sqrt hC.ne').inv hs.ne').congr_deriv ?_
  change -(deriv C t / (2 * Real.sqrt (C t))) / Real.sqrt (C t) ^ 2 =
    -(deriv C t / C t / 2) * (Real.sqrt (C t))⁻¹
  rw [show deriv C t / C t = deriv C t / Real.sqrt (C t) ^ 2 by
    rw [Real.sq_sqrt hC.le]]
  field_simp [hs.ne'] <;> ring

/-- The normalized linear summand has strictly negative mixed derivative from gap three. -/
theorem middleTailLinearContribution_mixed_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (hgap : 3 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ middleTailLinearContribution p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let a := reflectedHalfLogSlope (compositionMoment p 0)
  let j := upperTailSlope h
  let η := j d * (h + j d)
  let β : ℝ → ℝ := fun t ↦ 1 - Real.exp (-(h * t))
  let W : ℝ → ℝ := fun t ↦ (β t)⁻¹
  let D := middleTailLinearGeom (p + 1) h
  let L := middleTailLinearLoss (p + 1) h
  let z := 2 + h - a u
  let y := 1 + h + j v + a v
  let s := z + deriv L u / L u
  let k := h ^ 2 / ((3 + h) * (3 + 2 * h) / 2)
  let P : ℝ → ℝ := fun t ↦ Real.exp ((2 + h) * t) * (Real.sqrt (compositionMoment p 0 (-t)))⁻¹
  let R : ℝ → ℝ := fun t ↦ Real.exp (-((1 + h) * t)) *
    (Real.sqrt (compositionMoment p 0 (-t)))⁻¹ * W t
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp only [h]; positivity
  have hle : h ≤ 3 / 11 := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 11)
    exact_mod_cast hp
  have hd : 0 < d := (by norm_num : (0 : ℝ) < 3).trans_le hgap
  have huv : u < v := sub_pos.mp hd
  have hv : 0 < v := hu.trans huv
  have hβ (t : ℝ) (ht : 0 < t) : 0 < β t :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))
  have hw : β d = h * upperTailGap h d := by
    change β d = h * (β d / h)
    field_simp [hh.ne'] <;> ring
  obtain ⟨hL, hD, hDL⟩ := middleTailLinear_geom_ge_and_logDeriv_ge
    (n := p + 1) (Nat.succ_pos p) hh hu
  have hc : (1 + h) / h = (((p + 1 : ℕ) : ℝ) + 2) / 3 := by
    dsimp only [h]
    push_cast
    field_simp [hpR.ne'] <;> ring
  have hjd := upperTailSlope_bounds hh hd
  have hj := hasDerivAt_upperTailSlope hh hd
  have hjupper : j d ≤ 1 / 3 :=
    hjd.2.1.trans (one_div_le_one_div_of_le (by norm_num) hgap)
  have heta : η ≤ 1 / 9 := by
    have H := hjd.2.2.2.1
    rw [hj.deriv, neg_neg] at H
    exact H.trans (by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hgap
      have hsq := pow_le_pow_left₀ (one_div_nonneg.mpr hd.le) h 2
      simpa only [one_div_pow, show (3 : ℝ) ^ 2 = 9 by norm_num] using hsq)
  have hy : 1 ≤ y := by
    dsimp only [y, j, a]
    linarith only [hh, (upperTailSlope_bounds hh hv).1, reflectedHalfLogSlope_nonneg hp₀ hv]
  have hLder := hasDerivAt_middleTailLinearLoss (p + 1) h u
  have hDder := hasDerivAt_middleTailLinearGeom (p + 1) h u
  have hLogL : 0 ≤ deriv L u / L u := by
    rw [show deriv L u = _ from hLder.deriv]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hh.le (mul_nonneg (Real.exp_pos _).le (hβ u hu).le))
        (by positivity)) hL.le
  have hs : 1 / 2 ≤ s := by
    have ha := upperTail_marginal_logDeriv hp₀ hu
    have hdiv : (2 : ℝ) / u = 2 * (1 / u) := by ring
    rw [hdiv] at ha
    have ha' : a u ≤ 1 / 2 + 1 / u := by
      unfold a reflectedHalfLogSlope
      linarith only [ha]
    have hlog := middleTailLinear_loss_logDeriv_ge (n := p + 1) (Nat.succ_pos p) hh hu
    have hrate : h * (((p + 1 : ℕ) : ℝ) + 1) = 3 + 2 * h := by
      dsimp only [h]
      push_cast
      field_simp [hpR.ne'] <;> ring
    rw [hrate] at hlog
    change 2 / u - (2 / 3) * (3 + 2 * h) ≤ deriv L u / L u at hlog
    rw [hdiv] at hlog
    dsimp only [s, z]
    by_cases hm : 1 / u ≤ 1 + h
    · linarith only [ha', hLogL, hm]
    · linarith only [ha', hlog, lt_of_not_ge hm, hh]
  have hcw : 5 / 2 < ((1 + h) / h) * β d := by
    rw [hw, show ((1 + h) / h) * (h * upperTailGap h d) =
      (1 + h) * upperTailGap h d by field_simp [hh.ne'] <;> ring]
    exact middleTailLinear_gap_weight_gt hh hle hgap
  have hscalar : -y * (z * D u + deriv D u) +
      L u * ((y + j d) * (s + j d) + η) / β d < 0 :=
    middleTailLinear_mixed_scalar_neg hL (hβ d hd) (by rw [hc]; exact hD) hDL
      hy hjd.1.le hjupper heta hs hcw
  have hP : HasDerivAt P (z * P u) u := by
    have he := ((hasDerivAt_id' u).const_mul (2 + h)).exp
    refine (he.mul (hasDerivAt_middleTail_invMarginal hp₀ hu)).congr_deriv ?_
    simp only [P, z, a, mul_one, Pi.mul_apply]
    ring
  have hR : HasDerivAt R (-y * R v) v := by
    refine (((hasDerivAt_upperTailLinearDecay (1 + h) v).mul
      (hasDerivAt_middleTail_invMarginal hp₀ hv)).mul
      (hasDerivAt_middleTail_invBeta hh hv)).congr_deriv ?_
    simp only [R, y, a, j, W, Pi.mul_apply]
    ring
  let B := z * D u + deriv D u
  let F : ℝ → ℝ := fun t ↦ k * P u * R t *
    (B - W (t - u) * (L u * (s + j (t - u))))
  have hfirst : (fun t ↦ deriv (fun x ↦ middleTailLinearContribution p x t) u) =ᶠ[𝓝 v] F := by
    filter_upwards [eventually_gt_nhds huv] with t ht
    have hW : HasDerivAt (fun x ↦ W (t - x)) (j (t - u) * W (t - u)) u := by
      have H := (hasDerivAt_middleTail_invBeta hh (sub_pos.mpr ht)).comp u
        ((hasDerivAt_const u t).fun_sub (hasDerivAt_id' u))
      simpa only [Function.comp_def, zero_sub, mul_neg, mul_one, neg_mul, neg_neg] using H
    have hmodel : (fun x ↦ middleTailLinearContribution p x t) =ᶠ[𝓝 u]
        fun x ↦ k * P x * R t * (D x - L x * W (t - x)) := by
      filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds ht] with x hx hxt
      exact middleTailLinearContribution_eq hp₀ hx hxt
    rw [hmodel.deriv_eq]
    have hD' : HasDerivAt D (deriv D u) u := hDder.differentiableAt.hasDerivAt
    have hL' : HasDerivAt L (deriv L u) u := hLder.differentiableAt.hasDerivAt
    have H := ((hP.const_mul k).mul_const (R t)).mul (hD'.sub (hL'.mul hW))
    change HasDerivAt (fun x ↦ k * P x * R t * (D x - L x * W (t - x))) _ u at H
    rw [H.deriv]
    simp only [F, B, s, Pi.mul_apply, Pi.sub_apply]
    field_simp [show L u ≠ 0 from hL.ne'] <;> ring
  rw [hfirst.deriv_eq]
  have hW : HasDerivAt (fun t ↦ W (t - u)) (-j d * W d) v := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_middleTail_invBeta hh hd).comp v ((hasDerivAt_id' v).sub_const u)
  have hJ : HasDerivAt (fun t ↦ j (t - u)) (-η) v := by
    simpa only [Function.comp_def, mul_one] using
      hj.comp v ((hasDerivAt_id' v).sub_const u)
  have hbracket := (hW.mul ((hJ.const_add s).const_mul (L u))).const_sub B
  have hF : HasDerivAt F
      ((k * P u * R v) * (-y * B + L u * ((y + j d) * (s + j d) + η) / β d)) v := by
    refine ((hR.const_mul (k * P u)).mul hbracket).congr_deriv ?_
    simp only [d, W, Pi.mul_apply, div_eq_mul_inv]
    ring
  rw [hF.deriv]
  have hPpos : 0 < P u :=
    mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.sqrt_pos.mpr
      (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr hu.ne'))))
  have hRpos : 0 < R v :=
    mul_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.sqrt_pos.mpr
      (compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr hv.ne'))))) (inv_pos.mpr (hβ v hv))
  exact mul_neg_of_pos_of_neg
    (mul_pos (mul_pos (show 0 < k by dsimp only [k]; positivity) hPpos) hRpos) hscalar

end RefinedBMV.PositiveCenter
