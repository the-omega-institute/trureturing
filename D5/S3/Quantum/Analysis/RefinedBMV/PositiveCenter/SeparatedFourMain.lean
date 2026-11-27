/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourMain
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict signs of the normalized main derivatives on the central strip at gap four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourScalar
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourSlope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp

/-! # Main derivative signs on the central strip at gap four -/

namespace RefinedBMV.PositiveCenter

open private negativeMarginal_logDeriv_of_exponent_bound tilted_gap_slope_le
  exp_gap_two_sub_antitone from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripMarginal

open private decay_gap_quotient from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailLinearCoefficients

private noncomputable def separatedFourEnvelope (x b r : ℝ) : ℝ :=
  (b - 1 / 4) * (-(5 / 16) * r ^ 2 + 2 * r * (1 / 16) * x) +
    (1 / 16) * r ^ 2 + 2 * r * (5 / 16 - 27 / 50) * (1 / 16) * x +
    2 * r * (1 / 32) * x +
    (1 / 872) * ((14 / 11 + 1 / 2 + 3 / 8) * (b + (1 + 14 / 11 + 1 / 4)) + 1 / 16)

private theorem separatedFour_slope_floor {u : ℝ} (hu : 0 < u) (hu₄ : u ≤ 4) :
    let E := Real.exp u - 1
    (49 / 100 : ℝ) ≤ 1 + 2 / E - E / (2 * (E - u)) := by
  let E := Real.exp u - 1
  let T := u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 +
    u ^ 6 / 720 + u ^ 7 / 5040 + u ^ 8 / 40320
  have hEu : 0 < E - u := by dsimp only [E]; linarith only [Real.add_one_lt_exp hu.ne']
  have hE : 0 < E := by linarith only [hu, hEu]
  have hsum := Real.sum_le_exp_of_nonneg hu.le 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  have hTE : T ≤ E := by dsimp only [T, E]; linarith only [hsum]
  have huT : u ≤ T := by
    dsimp only [T]
    have H : 0 ≤ u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 +
        u ^ 6 / 720 + u ^ 7 / 5040 + u ^ 8 / 40320 := by positivity
    linarith only [H]
  have hmono := mul_nonneg (sub_nonneg.mpr hTE)
    (show 0 ≤ E + T + (200 - 51 * u) by linarith only [huT, huT.trans hTE, hu₄])
  have hrest : 0 ≤ (53 / 6) * u ^ 3 + (5 / 12) * u ^ 4 +
      (23 / 20160) * u ^ 8 + (17 / 120960) * u ^ 9 + (167 / 604800) * u ^ 10 +
      (29 / 604800) * u ^ 11 + (53 / 7257600) * u ^ 12 + (1 / 1036800) * u ^ 13 +
      (11 / 101606400) * u ^ 14 + (1 / 101606400) * u ^ 15 +
      (1 / 1625702400) * u ^ 16 := by positivity
  have hpoly : 50 * u ^ 2 - (5 / 24) * u ^ 5 - (11 / 180) * u ^ 6 -
        (31 / 5040) * u ^ 7 ≤ T ^ 2 + (200 - 51 * u) * T - 200 * u := by
    dsimp only [T]
    linarith only [hrest]
  have hpow (n : ℕ) : u ^ (n + 2) ≤ (4 : ℝ) ^ n * u ^ 2 := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.le hu₄ n) (sq_nonneg u)
  have h₅ : u ^ 5 ≤ 64 * u ^ 2 := by convert hpow 3 using 1 <;> norm_num
  have h₆ : u ^ 6 ≤ 256 * u ^ 2 := by convert hpow 4 using 1 <;> norm_num
  have h₇ : u ^ 7 ≤ 1024 * u ^ 2 := by convert hpow 5 using 1 <;> norm_num
  have hquad : 0 ≤ E ^ 2 + (200 - 51 * u) * E - 200 * u := by
    linarith only [hmono, hpoly, h₅, h₆, h₇, sq_nonneg u]
  change (49 / 100 : ℝ) ≤ 1 + 2 / E - E / (2 * (E - u))
  apply (mul_le_mul_iff_left₀ (mul_pos hE hEu)).mp
  field_simp [hE.ne', hEu.ne'] <;> linarith only [hquad]

private theorem separatedFour_slope_floor_le_sigma {p : ℕ} (hp : 0 < p) {u : ℝ}
    (hu : 0 < u) :
    let E := Real.exp u - 1
    1 + 2 / E - E / (2 * (E - u)) ≤
      1 + 2 / E - (deriv (fun t ↦ compositionMoment p 0 (-t)) u /
        compositionMoment p 0 (-u)) / 2 := by
  let E := Real.exp u - 1
  let K := E / (E - u)
  have hK : deriv (fun t ↦ compositionMoment p 0 (-t)) u /
      compositionMoment p 0 (-u) ≤ K := by
    refine negativeMarginal_logDeriv_of_exponent_bound hp hu (m := 1 - K * u) ?_
    intro x hx
    have h := tilted_gap_slope_le hu hx
    change x * (Real.exp (x * u) - 1) ≤ K * (Real.exp (x * u) - 1 - x * u) at h
    linarith only [h]
  change 1 + 2 / E - E / (2 * (E - u)) ≤
    1 + 2 / E - (deriv (fun t ↦ compositionMoment p 0 (-t)) u /
      compositionMoment p 0 (-u)) / 2
  rw [show E / (2 * (E - u)) = K / 2 by
    dsimp only [K]
    rw [div_div, mul_comm (E - u) 2]]
  linarith only [hK]

private theorem separatedFour_envelope_neg {u r : ℝ} (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4)
    (hr : 1 - (u / (Real.exp u - 1)) / 4 ≤ r) :
    let E := Real.exp u - 1
    separatedFourEnvelope (u / E) (1 + 2 / E - E / (2 * (E - u))) r < 0 := by
  let E := Real.exp u - 1
  let x := u / E
  let b := 1 + 2 / E - E / (2 * (E - u))
  let r₀ := 1 - x / 4
  let A : ℝ := 1 / 16 - (5 / 16) * (b - 1 / 4)
  have hu : 0 < u := by linarith only [hu₀]
  have hEu : 0 < E - u := by dsimp only [E]; linarith only [Real.add_one_lt_exp hu.ne']
  have hE : 0 < E := by linarith only [hu, hEu]
  have hfactor : -2 * E ^ 3 * (E - u) ≤ 0 := by
    have H := mul_pos (mul_pos (show (0 : ℝ) < 2 by norm_num) (pow_pos hE 3)) hEu
    linarith only [H]
  have hv : separatedFourEnvelope x b r₀ < 0 := by
    change separatedFourValue u E < 0
    exact neg_of_mul_pos_right (separatedFour_cleared_value_pos hu₀ hu₁) hfactor
  have hD : separatedFourDerivative u E < 0 :=
    neg_of_mul_pos_right (separatedFour_cleared_derivative_pos hu) hfactor
  have hb : (49 / 100 : ℝ) ≤ b := separatedFour_slope_floor hu hu₁
  have hA : A ≤ -(1 / 80) := by dsimp only [A]; linarith only [hb]
  have hdr : 0 ≤ r - r₀ := sub_nonneg.mpr hr
  -- The exact quadratic difference uses the derivative at the left endpoint.
  have hdecrease : (r - r₀) * (separatedFourDerivative u E + A * (r - r₀)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hdr
      (add_nonpos hD.le (mul_nonpos_of_nonpos_of_nonneg
        (hA.trans (by norm_num)) hdr))
  have hdiff : separatedFourEnvelope x b r - separatedFourEnvelope x b r₀ =
      (r - r₀) * (separatedFourDerivative u E + A * (r - r₀)) := by
    simp only [separatedFourEnvelope, separatedFourDerivative, A, r₀, x, b]
    ring
  change separatedFourEnvelope x b r < 0
  exact (sub_nonpos.mp (hdiff.trans_le hdecrease)).trans_lt hv

private theorem separatedFour_normalized_signs {u σ L q L₂ w f f₁ e₀ e₁ b₀ b₁ m₁ m₂ : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4)
    (hσ : let E := Real.exp u - 1; 1 + 2 / E - E / (2 * (E - u)) ≤ σ)
    (hL₀ : 0 ≤ L) (hL : L ≤ 1 / 4)
    (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 16) (hL₂ : L₂ ≤ 1 / 32) (hw : w ≤ -(5 / 16))
    (hf₀ : 0 ≤ f) (hf : f ≤ u / (Real.exp u - 1)) (hf₁ : f₁ ≤ -(27 / 50) * f)
    (he₀ : 0 ≤ e₀) (he₀' : e₀ ≤ 1 / 872) (he₁ : 0 ≤ e₁)
    (hb₀ : b₀ ≤ σ + (1 + 14 / 11 + 1 / 4)) (hb₁ : 0 ≤ b₁)
    (hm₁ : w - m₁ ≤ 0) (hm₂ : 0 ≤ m₂ - w) (hm₂' : m₂ - w ≤ 14 / 11 + 1 / 2 + 3 / 8) :
    let l := σ - L
    let r := 1 - L * f
    let s := -L * f₁
    let τ := q * f
    0 < r ^ 2 * l + 2 * r * (s - τ) - e₀ * b₀ + e₁ * b₁ ∧
      r ^ 2 * (w * l + q) + 2 * r * (l * τ + w * (s - τ) + q * f₁ + L₂ * f) +
        2 * (s - τ) * τ + e₀ * ((m₂ - w) * b₀ + q) + e₁ * ((w - m₁) * b₁) < 0 := by
  let E := Real.exp u - 1
  let x := u / E
  let b := 1 + 2 / E - E / (2 * (E - u))
  let l := σ - L
  let r := 1 - L * f
  let s := -L * f₁
  let τ := q * f
  have hu : 0 < u := by linarith only [hu₀]
  have hE : 0 < E := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hx₀ : 0 ≤ x := hf₀.trans hf
  have hx : x ≤ 4 / 5 := by
    have hsum := Real.sum_le_exp_of_nonneg hu.le 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    have hprod := mul_nonneg hu.le (show 0 ≤ u - 1 / 2 by linarith only [hu₀])
    change u / E ≤ 4 / 5
    apply (div_le_iff₀ hE).2
    dsimp only [E]
    linarith only [hsum, hprod]
  have hb : (49 / 100 : ℝ) ≤ b := separatedFour_slope_floor hu hu₁
  have hσmin : (49 / 100 : ℝ) ≤ σ := hb.trans hσ
  have hl : (6 / 25 : ℝ) ≤ l := by dsimp only [l]; linarith only [hσmin, hL]
  have hl' : σ - 1 / 4 ≤ l := sub_le_sub_left hL σ
  have hr : 1 - x / 4 ≤ r := by
    have hLf := mul_le_mul_of_nonneg_right hL hf₀
    dsimp only [r]
    change f ≤ x at hf
    linarith only [hLf, hf]
  have hrmin : (4 / 5 : ℝ) ≤ r := by linarith only [hr, hx]
  have hr₀ : 0 ≤ r := by linarith only [hrmin]
  have hr₁ : r ≤ 1 := sub_le_self _ (mul_nonneg hL₀ hf₀)
  have hrsq : (4 / 5 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hrmin 2
  have hs : 0 ≤ s := by
    have hf₁' := hf₁.trans (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hf₀)
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hL₀) hf₁'
  have hτ₀ : 0 ≤ τ := mul_nonneg hq₀ hf₀
  have hτ : τ ≤ (1 / 16) * x :=
    mul_le_mul hq hf hf₀ (by norm_num)
  have hQx : (1 / 16) * x ≤ 1 / 20 := by linarith only [hx]
  have hτmax : τ ≤ 1 / 20 := hτ.trans hQx
  have hRτ : r * τ ≤ 1 / 20 :=
    (mul_le_mul_of_nonneg_right hr₁ hτ₀).trans (by simpa only [one_mul] using hτmax)
  have hσoff : 0 ≤ σ + (1 + 14 / 11 + 1 / 4) := by linarith only [hσmin]
  change 0 < r ^ 2 * l + 2 * r * (s - τ) - e₀ * b₀ + e₁ * b₁ ∧
    r ^ 2 * (w * l + q) + 2 * r * (l * τ + w * (s - τ) + q * f₁ + L₂ * f) +
      2 * (s - τ) * τ + e₀ * ((m₂ - w) * b₀ + q) + e₁ * ((w - m₁) * b₁) < 0
  constructor
  · have hσcoeff : 0 ≤ r ^ 2 - (1 / 872 : ℝ) := by linarith only [hrsq]
    have hσterm := mul_nonneg (sub_nonneg.mpr hσmin) hσcoeff
    have hlead := mul_le_mul_of_nonneg_left hl' (sq_nonneg r)
    have hlead' := mul_le_mul_of_nonneg_right hrsq (by norm_num : (0 : ℝ) ≤ 49 / 100 - 1 / 4)
    have herr := (mul_le_mul_of_nonneg_left hb₀ he₀).trans
      (mul_le_mul_of_nonneg_right he₀' hσoff)
    have hmargin : (601239 / 11990000 : ℝ) ≤
        r ^ 2 * l + 2 * r * (s - τ) - e₀ * b₀ + e₁ * b₁ := by
      linarith only [hσterm, hlead, hlead', hRτ, herr, mul_nonneg hr₀ hs, mul_nonneg he₁ hb₁]
    exact (by norm_num : (0 : ℝ) < 601239 / 11990000).trans_le hmargin
  · have hrl : (4 / 5 : ℝ) * (6 / 25) ≤ r * l :=
      mul_le_mul hrmin hl (by norm_num) hr₀
    -- Collect the terms in w that are independent of s before bounding w.
    have hW := mul_le_mul_of_nonneg_right hw
      (mul_nonneg hr₀ (show 0 ≤ r * l - 2 * τ by linarith only [hrl, hτmax]))
    have hrw := mul_le_mul_of_nonneg_left hw hr₀
    have hS := mul_nonpos_of_nonneg_of_nonpos hs
      (show r * w + τ ≤ 0 by linarith only [hrw, hrmin, hτmax])
    have hdecay : q * f₁ ≤ -(27 / 50) * τ := by
      have H := mul_le_mul_of_nonneg_left hf₁ hq₀
      dsimp only [τ]
      linarith only [H]
    have hSlope := mul_le_mul_of_nonneg_left hdecay hr₀
    have hCurv := mul_le_mul_of_nonneg_left
      (mul_le_mul hL₂ hf hf₀ (by norm_num : (0 : ℝ) ≤ 1 / 32)) hr₀
    have hQ := mul_le_mul_of_nonneg_right hq (sq_nonneg r)
    have hCoeffτ : 0 ≤ r * (l + 5 / 16 - 27 / 50) :=
      mul_nonneg hr₀ (by linarith only [hl])
    have hIncreaseτ := mul_le_mul_of_nonneg_left hτ hCoeffτ
    have hPositiveLinear := mul_nonpos_of_nonneg_of_nonpos he₁
      (mul_nonpos_of_nonpos_of_nonneg hm₁ hb₁)
    have herr : e₀ * ((m₂ - w) * b₀ + q) ≤
        (1 / 872) * ((14 / 11 + 1 / 2 + 3 / 8) * (σ + (1 + 14 / 11 + 1 / 4)) + 1 / 16) := by
      have H := (mul_le_mul_of_nonneg_left hb₀ hm₂).trans
        (mul_le_mul_of_nonneg_right hm₂' hσoff)
      have hUpper := add_le_add H hq
      exact (mul_le_mul_of_nonneg_left hUpper he₀).trans
        (mul_le_mul_of_nonneg_right he₀'
          (add_nonneg (mul_nonneg (by norm_num) hσoff) (by norm_num)))
    let k : ℝ := -(5 / 16) * r ^ 2 + 2 * r * (1 / 16) * x
    have hk : k ≤ -(1 / 10) := by
      have H := (mul_le_mul_of_nonneg_right hr₁
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) hx₀)).trans
        (show 1 * ((1 / 16) * x) ≤ 1 / 20 by simpa only [one_mul] using hQx)
      dsimp only [k]
      linarith only [hrsq, H]
    have hReplaceL : l * k ≤ (σ - 1 / 4) * k :=
      mul_le_mul_of_nonpos_right hl' (hk.trans (by norm_num))
    have hσcoeff : k + (1 / 872) * (14 / 11 + 1 / 2 + 3 / 8) ≤ -(37423 / 383680) := by
      linarith only [hk]
    have hReplaceσ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (show b ≤ σ from hσ))
      (hσcoeff.trans (by norm_num))
    calc
      _ ≤ l * k + (1 / 16) * r ^ 2 + 2 * r * (5 / 16 - 27 / 50) * (1 / 16) * x +
          2 * r * (1 / 32) * x +
          (1 / 872) * ((14 / 11 + 1 / 2 + 3 / 8) * (σ + (1 + 14 / 11 + 1 / 4)) + 1 / 16) := by
        dsimp only [k]
        linarith only [hW, hS, hSlope, hCurv, hQ, hIncreaseτ, hPositiveLinear, herr, sq_nonneg τ]
      _ ≤ separatedFourEnvelope x σ r := by
        unfold separatedFourEnvelope
        dsimp only [k] at hReplaceL ⊢
        linarith only [hReplaceL]
      _ ≤ separatedFourEnvelope x b r := by
        unfold separatedFourEnvelope
        dsimp only [k] at hReplaceσ
        linarith only [hReplaceσ]
      _ < 0 := separatedFour_envelope_neg hu₀ hu₁ hr

private theorem separatedFour_P0_logDeriv_le {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    deriv (upperTailLinearP0 h) u / upperTailLinearP0 h u ≤ 1 := by
  let a (t : ℝ) := 1 - upperTailLinearA h t
  let β (t : ℝ) := 1 - Real.exp (-t)
  let F (t : ℝ) := Real.exp (-((3 + h) * t)) * upperTailGap h t
  let c : ℝ := (3 + h) * (3 + 2 * h)
  let E := Real.exp u - 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hE : 0 < E := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hβ : 0 < β u := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hP : 0 < upperTailLinearP0 h u := (upperTailLinear_value_bounds hh hu).1.1
  have ha : 0 < a u := by
    change 0 < a u / β u ^ 2 at hP
    exact (div_pos_iff_of_pos_right (pow_pos hβ 2)).mp hP
  have hcont : Continuous F := by unfold F upperTailGap; fun_prop
  -- The decay of F(t)/t bounds the integral from below by its endpoint scale.
  have hcompare : (∫ t in (0 : ℝ)..u, (F u / u) * t) ≤ ∫ t in (0 : ℝ)..u, F t := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hu.le
      (Continuous.intervalIntegrable (by fun_prop) _ _) (hcont.intervalIntegrable ..) ?_
    intro t ht
    have ht₀ : 0 < t := ht.1
    have hgap : upperTailGap h u / u ≤ upperTailGap h t / t :=
      (decay_gap_quotient hh ht₀ ht.2.le).2
    have hexp : Real.exp (-((3 + h) * u)) ≤ Real.exp (-((3 + h) * t)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ht.2.le (by positivity)))
    have H := mul_le_mul hexp hgap (div_nonneg (tail_gap_pos hh hu).le hu.le)
      (Real.exp_pos _).le
    calc
      (F u / u) * t = (Real.exp (-((3 + h) * u)) * (upperTailGap h u / u)) * t := by
        simp only [F, mul_div_assoc]
      _ ≤ (Real.exp (-((3 + h) * t)) * (upperTailGap h t / t)) * t :=
        mul_le_mul_of_nonneg_right H ht₀.le
      _ = F t := by
        rw [mul_assoc, div_mul_cancel₀ _ ht₀.ne'] <;> rfl
  rw [intervalIntegral.integral_const_mul, integral_id, zero_pow (by decide : (2 : ℕ) ≠ 0),
    sub_zero] at hcompare
  have hI : u * F u / 2 ≤ ∫ t in (0 : ℝ)..u, F t := by
    convert hcompare using 1
    field_simp [hu.ne'] <;> ring
  have hA : a u = c * ∫ t in (0 : ℝ)..u, F t :=
    one_sub_upperTailLinearA_eq_integral hh u
  have hAd : HasDerivAt a (c * F u) u := by
    have heq : a = fun z ↦ c * ∫ t in (0 : ℝ)..z, F t :=
      funext (one_sub_upperTailLinearA_eq_integral hh)
    rw [heq]
    exact ((hcont.integral_hasStrictDerivAt 0 u).hasDerivAt.const_mul c)
  have hAl : deriv a u / a u ≤ 2 / u := by
    apply (div_le_div_iff₀ ha hu).2
    rw [hAd.deriv, hA]
    have H := mul_le_mul_of_nonneg_left hI hc.le
    linarith only [H]
  have hbD : HasDerivAt β (Real.exp (-u)) u := by
    have H := (((hasDerivAt_id' u).const_mul (-1 : ℝ)).exp).const_sub 1
    convert H using 1 <;> simp [β]
  have hbLog : Real.exp (-u) / β u = 1 / E := by
    have hprod : β u * Real.exp u = E := by
      dsimp only [β, E]
      rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv_rev, hprod, one_div]
  have hLog : deriv (upperTailLinearP0 h) u / upperTailLinearP0 h u =
      deriv a u / a u - 2 / E := by
    have hd := (hAd.differentiableAt.hasDerivAt.div (hbD.pow 2) (pow_ne_zero _ hβ.ne')).deriv
    norm_num [Pi.pow_apply] at hd
    change deriv (upperTailLinearP0 h) u = _ at hd
    rw [hd, show upperTailLinearP0 h u = a u / β u ^ 2 from rfl,
      show 2 / E = 2 * (Real.exp (-u) / β u) by rw [hbLog]; ring]
    field_simp [ha.ne', hβ.ne'] <;> ring
  have hrecip : 2 / u - 2 / E ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hu hE)).mp
    field_simp [hu.ne', hE.ne']
    have H := exp_gap_two_sub_antitone hu.le
    norm_num [Real.exp_zero] at H
    have hEE : Real.exp u = E + 1 := by dsimp only [E]; ring
    rw [hEE] at H
    linarith only [H]
  rw [hLog]
  linarith only [hAl, hrecip]

private theorem separatedFour_W_two_eq {h d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    upperTailLinearW h 2 d =
      Real.exp (-d) * (upperTailSlope h d * (h + upperTailSlope h d)) := by
  let E := Real.exp (h * d)
  have hE : E ≠ 0 := (Real.exp_pos _).ne'
  have hsub : E - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh hd))).ne'
  have hgap : 1 - E⁻¹ = (E - 1) / E := by
    rw [sub_div, div_self hE, one_div]
  have hsum : h + h / (E - 1) = h * E / (E - 1) := by
    apply (eq_div_iff hsub).2
    rw [add_mul, div_mul_cancel₀ _ hsub]
    ring
  unfold upperTailLinearW upperTailSlope upperTailGap
  rw [show -((1 + h) * d) = -d + -(h * d) by ring, Real.exp_add, Real.exp_neg (h * d)]
  change Real.exp (-d) * E⁻¹ / ((1 - E⁻¹) / h) ^ 2 =
    Real.exp (-d) * (h / (E - 1) * (h + h / (E - 1)))
  rw [hgap, div_div, div_pow, div_div_eq_mul_div, hsum, div_mul_div_comm,
    ← pow_two (E - 1), ← mul_div_assoc]
  apply congrArg (fun numerator : ℝ ↦ numerator / (E - 1) ^ 2)
  rw [mul_pow]
  calc
    Real.exp (-d) * E⁻¹ * (E ^ 2 * h ^ 2) =
        (E⁻¹ * E) * (Real.exp (-d) * (h * (h * E))) := by ring
    _ = Real.exp (-d) * (h * (h * E)) := by rw [inv_mul_cancel₀ hE, one_mul]

/-- The two normalized main-jet entries in independent lower and upper
coordinates have strict signs when the lower coordinate is in `[1/2, 4]`
and the gap is at least four. -/
theorem separatedFour_main_signs {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4) (hgap : 4 ≤ v - u) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let L := upperTailSlope h d
    let q := L * (h + L)
    let L₂ := deriv (deriv (upperTailSlope h)) d
    let σ := 1 + 2 / (Real.exp u - 1) -
      (deriv (fun t ↦ compositionMoment p 0 (-t)) u / compositionMoment p 0 (-u)) / 2
    let l := σ - L
    let w := -1 / 2 + L - upperTailSlope h v / 2
    let f := upperTailRatio h u
    let f₁ := deriv (upperTailRatio h) u
    let r := 1 - L * f
    let s := -L * f₁
    let τ := q * f
    let c : ℝ := (3 + h) * (3 + 2 * h) / 2
    let e₀ := upperTailLinearP0 h u * upperTailLinearW h 2 d / c
    let e₁ := upperTailLinearP1 h u * upperTailLinearW h 1 d / c
    let m₁ := 1 + h + L
    let m₂ := 1 + h + 2 * L
    let b₀ := l + deriv (upperTailLinearP0 h) u / upperTailLinearP0 h u + m₂
    let b₁ := l + deriv (upperTailLinearP1 h) u / upperTailLinearP1 h u + m₁
    0 < r ^ 2 * l + 2 * r * (s - τ) - e₀ * b₀ + e₁ * b₁ ∧
      r ^ 2 * (w * l + q) + 2 * r * (l * τ + w * (s - τ) + q * f₁ + L₂ * f) +
        2 * (s - τ) * τ + e₀ * ((m₂ - w) * b₀ + q) + e₁ * ((w - m₁) * b₁) < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let L := upperTailSlope h d
  let q := L * (h + L)
  let L₂ := deriv (deriv (upperTailSlope h)) d
  let σ := 1 + 2 / (Real.exp u - 1) -
    (deriv (fun t ↦ compositionMoment p 0 (-t)) u / compositionMoment p 0 (-u)) / 2
  let l := σ - L
  let w := -1 / 2 + L - upperTailSlope h v / 2
  let f := upperTailRatio h u
  let f₁ := deriv (upperTailRatio h) u
  let c : ℝ := (3 + h) * (3 + 2 * h) / 2
  let e₀ := upperTailLinearP0 h u * upperTailLinearW h 2 d / c
  let e₁ := upperTailLinearP1 h u * upperTailLinearW h 1 d / c
  let m₁ := 1 + h + L
  let m₂ := 1 + h + 2 * L
  let b₀ := l + deriv (upperTailLinearP0 h) u / upperTailLinearP0 h u + m₂
  let b₁ := l + deriv (upperTailLinearP1 h) u / upperTailLinearP1 h u + m₁
  have hp₀ : 0 < p := by omega
  have hh : 0 < h := div_pos (by norm_num) (by exact_mod_cast hp₀)
  have hh₁ : h ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hu : 0 < u := by linarith only [hu₀]
  have hd₀ : 0 < d := (by norm_num : (0 : ℝ) < 4).trans_le hgap
  have hv₄ : 4 ≤ v := by linarith only [hu, hgap]
  have hv : 0 < v := (by norm_num : (0 : ℝ) < 4).trans_le hv₄
  have huv : d + u = v := by dsimp only [d]; ring
  have hLpos : 0 < L := (upperTailSlope_bounds hh hd₀).1
  have hL : L ≤ 1 / 4 := (upperTailSlope_bounds hh hd₀).2.1.trans
    (one_div_le_one_div_of_le (by norm_num) hgap)
  have hLvpos := (upperTailSlope_bounds hh hv).1
  have hLv : upperTailSlope h v ≤ 1 / 4 := (upperTailSlope_bounds hh hv).2.1.trans
    (one_div_le_one_div_of_le (by norm_num) hv₄)
  have hq₀ : 0 ≤ q := mul_nonneg hLpos.le (add_nonneg hh.le hLpos.le)
  have hq : q ≤ 1 / 16 := by
    have H := (upperTailSlope_bounds hh hd₀).2.2.2.1
    rw [(hasDerivAt_upperTailSlope hh hd₀).deriv, neg_neg] at H
    have hdSq : (4 : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by norm_num) hgap 2
    exact H.trans ((one_div_le_one_div_of_le (by norm_num) hdSq).trans (by norm_num))
  have hL₂ : L₂ ≤ 1 / 32 := by
    have hdCube : (4 : ℝ) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (by norm_num) hgap 3
    exact (upperTailSlope_second_deriv_le hh hd₀).trans
      ((div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdCube).trans (by norm_num))
  have hw : w ≤ -(5 / 16) := by
    have H := upperTailSlope_correlated_le hh hgap hu.le hu₁
    rw [huv] at H
    exact H
  have hf₀ : 0 ≤ f := (upperTailRatio_bounds hh hu).1.le
  have hE : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hf : f ≤ u / (Real.exp u - 1) :=
    div_le_div_of_nonneg_right (upperTailGap_le hh) hE.le
  have hf₁ : f₁ ≤ -(27 / 50) * f := upperTailRatio_deriv_le_neg_mul hh hu₀
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨⟨hP₀, hP₀max⟩, ⟨hP₁, _⟩⟩ := upperTailLinear_value_bounds hh hu
  have hW (n : ℕ) : 0 < upperTailLinearW h n d :=
    div_pos (Real.exp_pos _) (pow_pos (tail_gap_pos hh hd₀) n)
  have he₀ : 0 ≤ e₀ := (div_pos (mul_pos hP₀ (hW 2)) hc).le
  have he₁ : 0 ≤ e₁ := (div_pos (mul_pos hP₁ (hW 1)) hc).le
  have he₀' : e₀ ≤ 1 / 872 := by
    have hExp4 : (109 / 2 : ℝ) ≤ Real.exp 4 := by
      have H := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 12
      norm_num [Finset.sum_range_succ, Nat.factorial] at H
      linarith only [H]
    have hExp : Real.exp (-d) ≤ 1 / (109 / 2) := by
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 109 / 2)
        (hExp4.trans (Real.exp_le_exp.mpr hgap))
    calc
      e₀ ≤ upperTailLinearW h 2 d := (div_le_iff₀ hc).2 (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hP₀max (hW 2).le)
      _ = Real.exp (-d) * q := separatedFour_W_two_eq hh hd₀
      _ ≤ (1 / (109 / 2)) * (1 / 16) :=
        mul_le_mul hExp hq hq₀ (by norm_num)
      _ = 1 / 872 := by norm_num
  have hb₀ : b₀ ≤ σ + (1 + 14 / 11 + 1 / 4) := by
    dsimp only [b₀, l, m₂]
    linarith only [separatedFour_P0_logDeriv_le hh hu, hh₁, hL]
  have hb₁ : 0 ≤ b₁ := by
    have H := separatedGap_positive_linear_slope hp hu
    change 0 ≤ σ + (1 + h) + deriv (upperTailLinearP1 h) u / upperTailLinearP1 h u at H
    dsimp only [b₁, l, m₁]
    linarith only [H]
  have hm₁ : w - m₁ ≤ 0 := by dsimp only [m₁]; linarith only [hw, hh, hLpos]
  have hm₂ : 0 ≤ m₂ - w := by dsimp only [m₂, w]; linarith only [hh, hLpos, hLvpos]
  have hm₂' : m₂ - w ≤ 14 / 11 + 1 / 2 + 3 / 8 := by
    dsimp only [m₂, w]
    linarith only [hh₁, hL, hLv]
  exact separatedFour_normalized_signs hu₀ hu₁ (separatedFour_slope_floor_le_sigma hp₀ hu)
    hLpos.le hL hq₀ hq hL₂ hw hf₀ hf hf₁ he₀ he₀' he₁ hb₀ hb₁ hm₁ hm₂ hm₂'

end RefinedBMV.PositiveCenter
