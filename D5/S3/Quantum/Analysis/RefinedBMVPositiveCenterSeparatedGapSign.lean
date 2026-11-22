/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterSeparatedGapSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The leading and linear terms of the normalized separated-gap kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSeparatedGapRadical
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripMarginal

namespace RefinedBMV.PositiveCenter

/-- The lower derivative is positive before multiplying by the decreasing
upper normalization. The positive linear summand only increases it. -/
theorem separatedGap_main_and_linear_lower_derivative
    {b L r s t E r₂ : ℝ}
    (hb : 12 / 25 ≤ b) (hL : L ≤ 1 / 6) (hr : 5 / 6 ≤ r) (hr₁ : r ≤ 1)
    (hs : 0 ≤ s) (ht₀ : 0 ≤ t) (ht : t ≤ 1 / 36)
    (hE₀ : 0 ≤ E) (hE : E ≤ 1 / 3200) (h₂ : r₂ ≤ b + 5) :
    0 < r ^ 2 * (b - L) + 2 * r * (s - t) - E * r₂ := by
  have hr₀ : 0 ≤ r := by linarith
  have hl : 0 ≤ b - 1 / 6 := by linarith
  have hsq : (5 / 6 : ℝ) ^ 2 ≤ r ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (by positivity : 0 ≤ r + 5 / 6)]
  have h1 := mul_le_mul_of_nonneg_right hsq hl
  have h2 := mul_le_mul_of_nonneg_left (show b - 1 / 6 ≤ b - L by linarith) (sq_nonneg r)
  have h3 := mul_le_mul_of_nonneg_right hr₁ ht₀
  have h4 := mul_nonneg hr₀ hs
  have h5 := (mul_le_mul_of_nonneg_left h₂ hE₀).trans
    (mul_le_mul_of_nonneg_right hE (show 0 ≤ b + 5 by linarith))
  nlinarith only [h1, h2, h3, h4, h5, hb, ht]

/-- The leading square dominates the potentially positive linear correction
on the separated strip. The other summands can be controlled by their signs. -/
theorem separatedGap_main_and_linear_upper
    {b w L q L₂ f s t r slopeGap E r₁ r₂ : ℝ}
    (hb : 12 / 25 ≤ b) (hw : w ≤ -1 / 3) (hL : L ≤ 1 / 6)
    (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 36)
    (hL₂ : L₂ ≤ (3 / 11 + 1 / 3) / 36)
    (hf₀ : 0 ≤ f) (hs : 0 ≤ s) (hslope : slopeGap ≤ 0)
    (ht : t = q * f) (hr : r = 1 - L * f) (hr₁ : r ≤ 1)
    (hE₀ : 0 ≤ E) (hE : E ≤ 1 / 3200)
    (h₁₀ : 0 ≤ r₁) (h₁ : r₁ ≤ 11 / 5) (h₂ : r₂ ≤ b + 5)
    (hu : (f ≤ 1 ∧ 3 / 4 ≤ b) ∨ f ≤ 3 / 5) :
    r ^ 2 * (w * (b - L) + q) +
        2 * r * ((b - L) * t + w * (s - t) + q * slopeGap + L₂ * f) +
        2 * (s - t) * t + E * (r₁ * r₂ + q) < -1 / 100 := by
  let l := b - L
  have hf : f ≤ 1 := hu.elim And.left (fun h ↦ by linarith)
  have hrt : 5 / 6 ≤ r := by
    have H := mul_le_mul_of_nonneg_right hL hf₀
    linarith only [hr, H, hf]
  have hr₀ : 0 ≤ r := by linarith
  have ht₀ : 0 ≤ t := by rw [ht]; exact mul_nonneg hq₀ hf₀
  have ht₁ : t ≤ f / 36 := by
    rw [ht]
    linarith only [mul_le_mul_of_nonneg_right hq hf₀]
  have htt : t ≤ 1 / 36 := by linarith
  have hl : 1 / 4 ≤ l := by dsimp only [l]; linarith
  have hl₀ : 0 ≤ l := by linarith
  have hsw : r * w + t ≤ 0 := by
    have H := mul_le_mul_of_nonneg_left hw hr₀
    nlinarith only [H, hrt, htt]
  have hcoeffW : 0 ≤ r ^ 2 * l - 2 * r * t := by
    have hrl := mul_le_mul_of_nonneg_left hl hr₀
    have hInner : 0 ≤ r * l - 2 * t := by nlinarith only [hrl, hrt, htt]
    nlinarith only [mul_nonneg hr₀ hInner]
  have hW := mul_le_mul_of_nonneg_right hw hcoeffW
  have hS := mul_nonpos_of_nonneg_of_nonpos hs hsw
  have hSlope := mul_nonpos_of_nonneg_of_nonpos hq₀ hslope
  have hSlope' := mul_nonpos_of_nonneg_of_nonpos hr₀ hSlope
  have hqR : q * r ^ 2 ≤ 1 / 36 := by
    have hrsq : r ^ 2 ≤ 1 := by nlinarith [mul_nonneg hr₀ (sub_nonneg.mpr hr₁)]
    exact (mul_le_mul_of_nonneg_left hrsq hq₀).trans (by simpa using hq)
  have hrt' : r * t ≤ f / 36 := by
    exact (mul_le_mul_of_nonneg_right hr₁ ht₀).trans (by simpa using ht₁)
  have hL₂f : r * L₂ * f ≤ ((3 / 11 + 1 / 3) / 36) * f := by
    have hL₂r := mul_le_mul_of_nonneg_left hL₂ hr₀
    have hbnd : r * L₂ ≤ (3 / 11 + 1 / 3) / 36 := hL₂r.trans (by
      have H := mul_le_mul_of_nonneg_right hr₁
        (by norm_num : (0 : ℝ) ≤ (3 / 11 + 1 / 3) / 36)
      simpa using H)
    exact mul_le_mul_of_nonneg_right hbnd hf₀
  have hEe : E * (r₁ * r₂ + q) ≤ ((11 / 5) * (b + 5) + 1 / 36) / 3200 := by
    have hb' : 0 ≤ b + 5 := by linarith
    have h12 := (mul_le_mul_of_nonneg_left h₂ h₁₀).trans (mul_le_mul_of_nonneg_right h₁ hb')
    have hq12 : r₁ * r₂ + q ≤ (11 / 5) * (b + 5) + 1 / 36 := by linarith
    have H := (mul_le_mul_of_nonneg_left hq12 hE₀).trans
      (mul_le_mul_of_nonneg_right hE (by positivity))
    convert H using 1 <;> ring
  have hbound {F : ℝ} (hfF : f ≤ F) (hF : 0 ≤ F) (hF₁ : F ≤ 1) :
      r ^ 2 * (w * l + q) + 2 * r * (l * t + w * (s - t) + q * slopeGap + L₂ * f) +
          2 * (s - t) * t + E * (r₁ * r₂ + q) ≤
        (b - 1 / 6) * (-(1 - F / 6) ^ 2 / 3 + 2 * F / 36) +
          (1 + 2 * F / 3) / 36 + 2 * ((3 / 11 + 1 / 3) / 36) * F +
          ((11 / 5) * (b + 5) + 1 / 36) / 3200 := by
    have hrf : 1 - F / 6 ≤ r := by
      have H := mul_le_mul_of_nonneg_right hL hf₀
      linarith only [hr, H, hfF]
    have hrsq : (1 - F / 6) ^ 2 ≤ r ^ 2 := by
      have H := mul_nonneg (sub_nonneg.mpr hrf) (show 0 ≤ r + (1 - F / 6) by linarith)
      nlinarith only [H]
    have hlead := mul_le_mul_of_nonneg_right hrsq hl₀
    have htf : r * t ≤ F / 36 := by linarith only [hrt', hfF]
    have htf' := mul_le_mul_of_nonneg_right htf hl₀
    have hL₂F := hL₂f.trans
      (mul_le_mul_of_nonneg_left hfF (by norm_num : (0 : ℝ) ≤ (3 / 11 + 1 / 3) / 36))
    have hF2 : (5 / 6 : ℝ) ^ 2 ≤ (1 - F / 6) ^ 2 := by nlinarith
    have hC : -(1 - F / 6) ^ 2 / 3 + 2 * F / 36 ≤ 0 := by nlinarith only [hF2, hF₁]
    have hlC := mul_le_mul_of_nonpos_right
      (show b - 1 / 6 ≤ l by dsimp only [l]; linarith) hC
    nlinarith only [hW, hS, hSlope', hqR, htf, htf', hL₂F, hEe, hlead, hlC, sq_nonneg t]
  change r ^ 2 * (w * l + q) + 2 * r * (l * t + w * (s - t) + q * slopeGap + L₂ * f) +
      2 * (s - t) * t + E * (r₁ * r₂ + q) < -1 / 100
  rcases hu with ⟨hf', hb'⟩ | hf'
  · have H := hbound hf' (by norm_num : (0 : ℝ) ≤ 1) (by norm_num)
    norm_num at H
    linarith only [H, hb']
  · have H := hbound hf' (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num)
    norm_num at H
    linarith only [H, hb]

theorem separatedGap_negative_linear_size {h u d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 0 < u) (hd : 6 ≤ d) :
    let c : ℝ := (3 + h) * (3 + 2 * h) / 2
    let E := upperTailLinearP0 h u * upperTailLinearW h 2 d / c
    0 < E ∧ E ≤ 1 / 3200 := by
  let c : ℝ := (3 + h) * (3 + 2 * h) / 2
  let a := upperTailGap h d
  let W := upperTailLinearW h 2 d
  have hc : 0 < c := by dsimp only [c]; positivity
  have ha := separatedGap_gap_gt hh hhmax hd
  have ha₀ : 0 < a := by linarith
  have hW : 0 < W := div_pos (Real.exp_pos _) (sq_pos_of_pos ha₀)
  have hcp := (upperTailLinear_value_bounds hh hu).1
  refine ⟨div_pos (mul_pos hcp.1 hW) hc, ?_⟩
  change upperTailLinearP0 h u * W / c ≤ 1 / 3200
  calc
    _ ≤ W := (div_le_iff₀ hc).2 (by
      simpa only [mul_comm W c] using mul_le_mul_of_nonneg_right hcp.2 hW.le)
    _ ≤ _ := by
      have he : (380 : ℝ) < Real.exp 6 := by
        have h := Real.exp_one_gt_d9
        have he' : (27 / 10 : ℝ) < Real.exp 1 := by linarith only [h]
        have H := pow_lt_pow_left₀ he' (by norm_num : (0 : ℝ) ≤ 27 / 10) (by decide : 6 ≠ 0)
        norm_num at H
        linarith only [H]
      have he₁ : Real.exp (-6 : ℝ) ≤ 1 / 380 := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 380) he.le
      have he₂ : Real.exp (-((1 + h) * d)) ≤ 1 / 380 :=
        (Real.exp_le_exp.mpr (by nlinarith only [hd, mul_nonneg hh.le (show 0 ≤ d by linarith)])).trans he₁
      change Real.exp (-((1 + h) * d)) / a ^ 2 ≤ 1 / 3200
      apply (div_le_iff₀ (sq_pos_of_pos ha₀)).2
      have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 44 / 15) ha.le 2
      nlinarith only [he₂, hsq]

theorem separatedGap_positive_linear_slope {p : ℕ} (hp : 11 ≤ p) {u : ℝ} (hu : 0 < u) :
    let h : ℝ := 3 / (p : ℝ)
    let C := fun t ↦ compositionMoment p 0 (-t)
    let b := 1 + 2 / (Real.exp u - 1) - (deriv C u / C u) / 2
    let P := upperTailLinearP1 h
    0 ≤ b + (1 + h) + deriv P u / P u := by
  let h : ℝ := 3 / (p : ℝ)
  let C := fun t ↦ compositionMoment p 0 (-t)
  let A := upperTailLinearA1 h
  let P := upperTailLinearP1 h
  let e (t : ℝ) := 1 - Real.exp (-t)
  let E := Real.exp u - 1
  have hp₀ : 0 < p := by omega
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhmax : h ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hP : 0 < P u := (upperTailLinear_value_bounds hh hu).2.1
  have hE : 0 < E := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have he : 0 < e u := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have heq : P u = A u / e u ^ 2 := rfl
  have hA : 0 < A u := by
    rw [heq] at hP
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos he)).1 hP
  have hAd : DifferentiableAt ℝ A u := by
    have hne : (1 - Real.exp (-(h * u))) / h ≠ 0 := (tail_gap_pos hh hu).ne'
    unfold A upperTailLinearA1 upperTailGap
    fun_prop (disch := assumption)
  have hed : HasDerivAt e (Real.exp (-u)) u := by
    have he' := (((hasDerivAt_id' u).const_mul (-1 : ℝ)).exp).const_sub 1
    convert he' using 1 <;> simp [e]
  have he_exp : e u * Real.exp u = E := by
    dsimp only [e, E]
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have he_log : Real.exp (-u) / e u = 1 / E := by
    rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv_rev, he_exp, one_div]
  have hP_log : deriv P u / P u = deriv A u / A u - 2 / E := by
    have hd := (hAd.hasDerivAt.div (hed.pow 2) (pow_ne_zero _ he.ne')).deriv
    norm_num [Pi.pow_apply] at hd
    change deriv P u = _ at hd
    rw [hd, heq, show 2 / E = 2 * (Real.exp (-u) / e u) by rw [he_log]; ring]
    field_simp [hA.ne', he.ne'] <;> ring
  have hC := negativeMarginal_logDeriv_le_two_div_add_one hp₀ hu
  change deriv C u / C u ≤ 2 / u + 1 at hC
  change 0 ≤ 1 + 2 / E - (deriv C u / C u) / 2 + (1 + h) + deriv P u / P u
  rw [hP_log]
  by_cases hsmall : u ≤ 1
  · have hderiv := upperTailLinearA1_deriv_ge hh hu
    have H : 2 / u - ((3 + 2 * h) / 2 + h) ≤ deriv A u / A u :=
      (le_div_iff₀ hA).2 hderiv
    have hu_inv : 1 ≤ 1 / u := (le_div_iff₀ hu).2 (by simpa using hsmall)
    rw [show 2 / u = 2 * (1 / u) by ring] at hC H
    linarith only [hC, H, hu_inv, hhmax]
  · have hu_inv : 1 / u ≤ 1 := (div_le_iff₀ hu).2 (by linarith)
    have H : 0 ≤ deriv A u / A u :=
      div_nonneg (upperTailLinearA1_deriv_nonneg hp₀ hu) hA.le
    rw [show 2 / u = 2 * (1 / u) by ring] at hC
    linarith only [hC, H, hu_inv, hh]

end RefinedBMV.PositiveCenter
