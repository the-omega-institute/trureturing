/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SteppedLinearRatio
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact derivative ratio and strict sign of the central linear correction. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailLinear
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripMarginal
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailFormula
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp

/-! # The central positive-center linear correction -/

open Filter MeasureTheory Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private gap_pos gap_nonneg gap_mono continuous_gap hasDerivAt_decay exp_decay_add
  decay_gap_quotient hasDerivAt_one_sub_upperTailLinearA hasDerivAt_upperTailLinearA1 from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailLinear

open private exp_gap_two_sub_antitone from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripMarginal

open private hasDerivAt_negativeMarginal negativeMarginalDerivative negativeMarginalDerivative_zero
  gapCount gapCount_pos exponent from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftLimit

local notation "F" => upperTailGap
local notation "s(" h ")" => (3 + h)
local notation "k(" h ")" => (3 + 2 * h)
local notation "m(" h ")" => (3 + 3 * h)
local notation "j(" h ")" => (1 + h)
local notation "A(" h ")" => (fun t ↦ 1 - upperTailLinearA h t)
local notation "A₁(" h ")" => (upperTailLinearA1 h)

attribute [local fun_prop] continuous_gap

private theorem stepped_LA_prime_pos {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    0 < deriv A(h) u := by
  rw [(hasDerivAt_one_sub_upperTailLinearA hh u).deriv]
  exact mul_pos (by positivity) (mul_pos (Real.exp_pos _) (gap_pos hh hu))

private theorem stepped_LA_pos {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    0 < A(h) u := by
  change 0 < 1 - upperTailLinearA h u
  rw [one_sub_upperTailLinearA_eq_integral hh]
  refine mul_pos (by positivity) (intervalIntegral.integral_pos hu
    (Continuous.continuousOn (by fun_prop)) (fun t ht ↦ ?_) ?_)
  · exact mul_nonneg (Real.exp_pos _).le (gap_nonneg hh ht.1.le)
  · exact ⟨u / 2, ⟨by linarith, by linarith⟩,
      mul_pos (Real.exp_pos _) (gap_pos hh (by linarith))⟩

private noncomputable def steppedLinearPrimitive (h t : ℝ) : ℝ :=
  2 * (1 - Real.exp (-(k(h) * t))) -
    k(h) * (Real.exp (-(s(h) * t)) * F h t * (s(h) * F h t + 2))

private theorem hasDerivAt_steppedLinearPrimitive {h : ℝ} (hh : 0 < h) (t : ℝ) :
    HasDerivAt (steppedLinearPrimitive h)
      (s(h) * k(h) * m(h) * (Real.exp (-(s(h) * t)) * F h t ^ 2)) t := by
  have hF := hasDerivAt_upperTailGap (t := t) hh
  have h1 := ((hasDerivAt_decay k(h) t).const_sub 1).const_mul 2
  have h2 := (((hasDerivAt_decay s(h) t).mul hF).mul
    ((hF.const_mul s(h)).add_const 2)).const_mul k(h)
  apply (h1.sub h2).congr_deriv
  simp only [Pi.mul_apply]
  have hE : Real.exp (-(k(h) * t)) =
      Real.exp (-(s(h) * t)) * Real.exp (-(h * t)) := by
    rw [exp_decay_add, show s(h) + h = k(h) by ring]
  have hgap : Real.exp (-(h * t)) = 1 - h * F h t := by
    unfold upperTailGap
    field_simp [hh.ne'] <;> ring
  rw [hE, hgap]
  ring

private theorem steppedLinearPrimitive_eq_integral {h : ℝ} (hh : 0 < h) (u : ℝ) :
    steppedLinearPrimitive h u =
      s(h) * k(h) * m(h) * ∫ t in (0 : ℝ)..u, Real.exp (-(s(h) * t)) * F h t ^ 2 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_steppedLinearPrimitive hh t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [steppedLinearPrimitive, upperTailGap]

/-- The exact coefficient derivative ratio with the change of variables
written on the original interval and with its positive denominator cleared. -/
theorem steppedLinear_deriv_ratio_integral {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    F h u ^ 3 * Real.exp (-(3 * u)) * (deriv A₁(h) u / deriv A(h) u) =
      m(h) * ∫ t in (0 : ℝ)..u, Real.exp (-(s(h) * t)) * F h t ^ 2 := by
  have hF := gap_pos hh hu
  have hs : 0 < s(h) := by positivity
  have hk : 0 < k(h) := by positivity
  have hE : Real.exp (-(k(h) * u)) =
      Real.exp (-(s(h) * u)) * Real.exp (-(h * u)) := by
    rw [exp_decay_add, show s(h) + h = k(h) by ring]
  have hEs : Real.exp (-(s(h) * u)) = Real.exp (-(3 * u)) * Real.exp (-(h * u)) := by
    rw [exp_decay_add]
  have hInv : Real.exp (-(k(h) * u)) * Real.exp (k(h) * u) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hL : upperTailSlope h u = Real.exp (-(h * u)) / F h u := by
    rw [← upperTailGap_logDeriv hh hu, (hasDerivAt_upperTailGap hh).deriv]
  have hA₁ : F h u ^ 2 * deriv A₁(h) u = Real.exp (-(h * u)) *
      steppedLinearPrimitive h u := by
    rw [(hasDerivAt_upperTailLinearA1 hh hu).deriv, hL]
    calc
      _ = 2 * Real.exp (-(h * u)) *
            (Real.exp (-(k(h) * u)) * Real.exp (k(h) * u) - Real.exp (-(k(h) * u))) -
          Real.exp (-(k(h) * u)) * k(h) * F h u * (s(h) * F h u + 2) := by
        field_simp [hF.ne'] <;> ring
      _ = _ := by
        unfold steppedLinearPrimitive
        rw [hInv, hE]
        ring
  rw [(hasDerivAt_one_sub_upperTailLinearA hh u).deriv]
  calc
    _ = (F h u ^ 2 * deriv A₁(h) u) / (s(h) * k(h) * Real.exp (-(h * u))) := by
      rw [hEs]
      field_simp [hF.ne', hs.ne', hk.ne', (Real.exp_pos _).ne'] <;> ring
    _ = steppedLinearPrimitive h u / (s(h) * k(h)) := by
      rw [hA₁]
      field_simp [hs.ne', hk.ne', (Real.exp_pos _).ne'] <;> ring
    _ = _ := by
      rw [steppedLinearPrimitive_eq_integral hh]
      field_simp [hs.ne', hk.ne'] <;> ring

private theorem steppedLinear_integral_parts {h : ℝ} (hh : 0 < h) (u : ℝ) :
    3 * (∫ t in (0 : ℝ)..u, Real.exp (-(s(h) * t)) * F h t ^ 2) =
    Real.exp (-(3 * u)) * F h u ^ 3 +
      3 * ∫ t in (0 : ℝ)..u, Real.exp (-(3 * t)) * F h t ^ 3 := by
  let P (t : ℝ) := Real.exp (-(3 * t)) * F h t ^ 3
  have hd (t : ℝ) : HasDerivAt P
      (3 * (Real.exp (-(s(h) * t)) * F h t ^ 2) - 3 * P t) t := by
    apply ((hasDerivAt_decay 3 t).mul ((hasDerivAt_upperTailGap hh).pow 3)).congr_deriv
    dsimp only [P]
    rw [show Real.exp (-(s(h) * t)) =
      Real.exp (-(3 * t)) * Real.exp (-(h * t)) by rw [exp_decay_add]]
    norm_num <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hd t) (Continuous.intervalIntegrable (by unfold P; fun_prop) 0 u)
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by unfold P; fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have h0 : P 0 = 0 := by simp [P, upperTailGap]
  rw [h0, sub_zero] at hi
  dsimp only [P] at hi
  linarith only [hi]

private theorem steppedLinear_ratio_eq {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    deriv A₁(h) u / deriv A(h) u = j(h) *
      (1 + 3 * ∫ t in (0 : ℝ)..u,
        Real.exp (3 * (u - t)) * (F h t / F h u) ^ 3) := by
  let D := F h u ^ 3 * Real.exp (-(3 * u))
  let W (t : ℝ) := Real.exp (3 * (u - t)) * (F h t / F h u) ^ 3
  have hF := gap_pos hh hu
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDW (t : ℝ) : D * W t = Real.exp (-(3 * t)) * F h t ^ 3 := by
    have he : Real.exp (-(3 * u)) * Real.exp (3 * (u - t)) = Real.exp (-(3 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [D, W]
    calc
      _ = (Real.exp (-(3 * u)) * Real.exp (3 * (u - t))) * F h t ^ 3 := by
        field_simp [hF.ne'] <;> ring
      _ = _ := by rw [he]
  have hI : D * (∫ t in (0 : ℝ)..u, W t) =
      ∫ t in (0 : ℝ)..u, Real.exp (-(3 * t)) * F h t ^ 3 := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [hDW]
  apply (mul_left_cancel₀ hD.ne')
  change D * (deriv A₁(h) u / deriv A(h) u) =
    D * (j(h) * (1 + 3 * ∫ t in (0 : ℝ)..u, W t))
  rw [show D * (j(h) * (1 + 3 * ∫ t in (0 : ℝ)..u, W t)) =
    j(h) * (D + 3 * (D * ∫ t in (0 : ℝ)..u, W t)) by ring, hI]
  have hp := steppedLinear_integral_parts hh u
  have hp' : j(h) * (D + 3 * ∫ t in (0 : ℝ)..u, Real.exp (-(3 * t)) * F h t ^ 3) =
      m(h) * ∫ t in (0 : ℝ)..u, Real.exp (-(s(h) * t)) * F h t ^ 2 := by
    dsimp only [D]
    rw [mul_comm (F h u ^ 3), ← hp]
    ring
  rw [hp']
  exact steppedLinear_deriv_ratio_integral hh hu

private theorem steppedLinear_gap_sub_ratio {h u v a : ℝ} (hh : 0 < h) (hu : 0 < u)
    (huv : u ≤ v) (ha : 0 ≤ a) :
    F h (u - a) / F h u ≤ F h (v - a) / F h v := by
  have hp (x : ℝ) : F h a + Real.exp (-(h * a)) * F h (x - a) = F h x := by
    unfold upperTailGap
    have he : Real.exp (-(h * a)) * Real.exp (-(h * (x - a))) = Real.exp (-(h * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    field_simp [hh.ne']
    linear_combination -he
  have he : Real.exp (h * a) * Real.exp (-(h * a)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hquot (x : ℝ) (hx : 0 < x) : F h (x - a) / F h x =
      Real.exp (h * a) * (1 - F h a / F h x) := by
    have H : F h (x - a) = Real.exp (h * a) * (F h x - F h a) := by
      rw [← hp x, add_sub_cancel_left, ← mul_assoc, he, one_mul]
    rw [H, mul_div_assoc, sub_div, div_self (gap_pos hh hx).ne']
  have hv := hu.trans_le huv
  rw [hquot u hu, hquot v hv]
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (div_le_div_of_nonneg_left (gap_nonneg hh ha)
      (gap_pos hh hu) (gap_mono hh huv)) _) (Real.exp_pos _).le

/-- The derivative ratio is increasing on the entire positive axis. -/
theorem steppedLinear_deriv_ratio_monotone {h : ℝ} (hh : 0 < h) :
    MonotoneOn (fun u ↦ deriv A₁(h) u / deriv A(h) u) (Ioi 0) := by
  intro u hu v hv huv
  have hu₀ : 0 < u := hu
  have hv₀ : 0 < v := hv
  change deriv A₁(h) u / deriv A(h) u ≤ deriv A₁(h) v / deriv A(h) v
  rw [steppedLinear_ratio_eq hh hu₀, steppedLinear_ratio_eq hh hv₀]
  have hreflect (x : ℝ) : (∫ t in (0 : ℝ)..x,
        Real.exp (3 * (x - t)) * (F h t / F h x) ^ 3) =
      ∫ a in (0 : ℝ)..x, Real.exp (3 * a) * (F h (x - a) / F h x) ^ 3 := by
    have H := intervalIntegral.integral_comp_sub_left
      (fun a ↦ Real.exp (3 * a) * (F h (x - a) / F h x) ^ 3)
      (a := (0 : ℝ)) (b := x) x
    simpa only [sub_self, sub_zero, sub_sub_cancel] using H
  rw [hreflect, hreflect]
  have hcont (x : ℝ) :
      Continuous (fun a ↦ Real.exp (3 * a) * (F h (x - a) / F h x) ^ 3) := by fun_prop
  have hle : (∫ a in (0 : ℝ)..u, Real.exp (3 * a) * (F h (u - a) / F h u) ^ 3) ≤
      ∫ a in (0 : ℝ)..v, Real.exp (3 * a) * (F h (v - a) / F h v) ^ 3 := by
    calc
      _ ≤ ∫ a in (0 : ℝ)..u, Real.exp (3 * a) * (F h (v - a) / F h v) ^ 3 := by
        refine intervalIntegral.integral_mono_on hu₀.le ((hcont u).intervalIntegrable ..)
          ((hcont v).intervalIntegrable ..) (fun a ha ↦ ?_)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg (gap_nonneg hh (sub_nonneg.mpr ha.2))
            (gap_pos hh hu₀).le) (steppedLinear_gap_sub_ratio hh hu₀ huv ha.1) 3)
          (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          ((hcont v).intervalIntegrable 0 u) ((hcont v).intervalIntegrable u v)]
        refine le_add_of_nonneg_right (intervalIntegral.integral_nonneg huv (fun a ha ↦ ?_))
        have ha' : 0 ≤ F h (v - a) := gap_nonneg hh (sub_nonneg.mpr ha.2)
        have hf' := (gap_pos hh hv₀).le
        positivity
  gcongr

/-- A pointwise lower bound for the exact derivative ratio. -/
theorem steppedLinear_deriv_ratio_lower {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    j(h) * (1 + 3 * u / 4) ≤ deriv A₁(h) u / deriv A(h) u := by
  rw [steppedLinear_ratio_eq hh hu]
  have hcompare : (∫ t in (0 : ℝ)..u, t ^ 3 / u ^ 3) ≤
      ∫ t in (0 : ℝ)..u, Real.exp (3 * (u - t)) * (F h t / F h u) ^ 3 := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hu.le
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t ht ↦ ?_)
    have hfrac : t / u ≤ F h t / F h u := by
      have H := (decay_gap_quotient hh ht.1 ht.2.le).2
      have H' := (div_le_div_iff₀ hu ht.1).1 H
      exact (div_le_div_iff₀ hu (gap_pos hh hu)).2 (by simpa [mul_comm] using H')
    have hE : 1 ≤ Real.exp (3 * (u - t)) := Real.one_le_exp (by linarith [ht.2])
    rw [← div_pow]
    calc
      _ ≤ (F h t / F h u) ^ 3 := pow_le_pow_left₀ (div_nonneg ht.1.le hu.le) hfrac 3
    _ ≤ _ := le_mul_of_one_le_left
      (pow_nonneg (div_nonneg (gap_nonneg hh ht.1.le) (gap_pos hh hu).le) 3) hE
  rw [intervalIntegral.integral_div, integral_pow] at hcompare
  norm_num at hcompare
  have hcalc : u ^ 4 / 4 / u ^ 3 = u / 4 := by field_simp [hu.ne'] <;> ring
  rw [hcalc] at hcompare
  have H := mul_le_mul_of_nonneg_left hcompare (show 0 ≤ j(h) * 3 by positivity)
  linarith only [H]

private theorem steppedLinear_weight_reflect {h r t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hr : 0 < r) (hrt : r ≤ t) (hrsum : r + t = 1 / 2) :
    Real.exp (-(s(h) * r)) * F h r ≤ Real.exp (-(s(h) * t)) * F h t := by
  let z := 4 * (t - r)
  have hz : 0 ≤ z := by dsimp only [z]; linarith
  have hz₁ : 2 - z = 8 * r := by dsimp only [z]; linarith
  have hz₂ : 2 + z = 8 * t := by dsimp only [z]; linarith
  have hp := exp_gap_two_sub_antitone hz
  norm_num at hp
  have htr : Real.exp (k(h) * (t - r)) * r ≤ t := by
    calc
      _ ≤ Real.exp z * r := by
        apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hr.le
        exact mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hrt)
      _ ≤ _ := by
        have H : (2 - z) * Real.exp z ≤ 2 + z := by linarith only [hp]
        rw [hz₁, hz₂] at H
        linarith only [H]
  have hF := (decay_gap_quotient hh hr hrt).1
  have ht := hr.trans_le hrt
  have hFt : Real.exp (-(h * (t - r))) * (F h r / r) * t ≤ F h t := by
    simpa only [div_mul_cancel₀ _ ht.ne'] using mul_le_mul_of_nonneg_right hF ht.le
  have hR : Real.exp (-(k(h) * (t - r))) * t ≥ r := by
    have H := (le_div_iff₀ (Real.exp_pos (k(h) * (t - r)))).2
      (show r * Real.exp (k(h) * (t - r)) ≤ t by simpa only [mul_comm] using htr)
    simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using H
  calc
    _ = Real.exp (-(s(h) * r)) * (F h r / r) * r := by
      field_simp [hr.ne']
    _ ≤ (Real.exp (-(s(h) * r)) * (F h r / r)) *
        (Real.exp (-(k(h) * (t - r))) * t) :=
      mul_le_mul_of_nonneg_left hR (by have := gap_nonneg hh hr.le; positivity)
    _ = Real.exp (-(s(h) * t)) * (Real.exp (-(h * (t - r))) * (F h r / r) * t) := by
      have he : Real.exp (-(s(h) * r)) * Real.exp (-(k(h) * (t - r))) =
          Real.exp (-(s(h) * t)) * Real.exp (-(h * (t - r))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp (-(s(h) * r)) * Real.exp (-(k(h) * (t - r)))) *
            (F h r / r) * t := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hFt (Real.exp_pos _).le

private theorem steppedLinear_centered_integral_nonneg {h : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11) :
    0 ≤ ∫ t in (0 : ℝ)..(1 / 2),
      (t - 1 / 4) * (s(h) * k(h) * (Real.exp (-(s(h) * t)) * F h t)) := by
  let W (t : ℝ) := s(h) * k(h) * (Real.exp (-(s(h) * t)) * F h t)
  let H (t : ℝ) := (t - 1 / 4) * W t
  have hH : Continuous H := by unfold H W; fun_prop
  have hc : Continuous (fun t : ℝ ↦ -H (1 / 2 - t)) := by fun_prop
  have hcompare : (∫ t in (1 / 4 : ℝ)..(1 / 2), -H (1 / 2 - t)) ≤
      ∫ t in (1 / 4 : ℝ)..(1 / 2), H t := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hc.intervalIntegrable ..) (hH.intervalIntegrable ..) (fun t ht ↦ ?_)
    have hw := steppedLinear_weight_reflect hh hhmax (r := 1 / 2 - t) (t := t)
      (by linarith [ht.2]) (by linarith [ht.1]) (by ring)
    have hw' : W (1 / 2 - t) ≤ W t :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    change -((1 / 2 - t - 1 / 4) * W (1 / 2 - t)) ≤ (t - 1 / 4) * W t
    rw [show -( (1 / 2 - t - 1 / 4) * W (1 / 2 - t)) =
      (t - 1 / 4) * W (1 / 2 - t) by ring]
    exact mul_le_mul_of_nonneg_left hw' (sub_nonneg.mpr ht.1.le)
  have hreflect : (∫ t in (1 / 4 : ℝ)..(1 / 2), H (1 / 2 - t)) =
      ∫ t in (0 : ℝ)..(1 / 4), H t := by
    convert intervalIntegral.integral_comp_sub_left H
      (a := (1 / 4 : ℝ)) (b := (1 / 2 : ℝ)) (1 / 2) using 1 <;> norm_num
  rw [intervalIntegral.integral_neg, hreflect] at hcompare
  change 0 ≤ ∫ t in (0 : ℝ)..(1 / 2), H t
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hH.intervalIntegrable 0 (1 / 4)) (hH.intervalIntegrable (1 / 4) (1 / 2))]
  linarith only [hcompare]

private noncomputable def steppedLinearA1AtZero (h t : ℝ) : ℝ :=
  if 0 < t then A₁(h) t else 0

private theorem hasDerivAt_steppedLinearA1AtZero {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (steppedLinearA1AtZero h) (deriv A₁(h) t) t := by
  apply (hasDerivAt_upperTailLinearA1 hh ht).differentiableAt.hasDerivAt.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with x hx
  simp only [steppedLinearA1AtZero, if_pos hx]

private theorem continuous_steppedLinearA1AtZero {h : ℝ} (hh : 0 < h) :
    Continuous (steppedLinearA1AtZero h) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hEq : steppedLinearA1AtZero h =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact if_neg (not_lt.mpr (le_of_lt hx))
    exact continuousAt_const.congr hEq.symm
  · let U (x : ℝ) := (s(h) * k(h) * m(h) / 2) * (1 - Real.exp (-x)) ^ 2
    have hU : Continuous U := by unfold U; fun_prop
    have hU0 : U 0 = 0 := by simp [U]
    have hLim := hU.continuousAt (x := (0 : ℝ))
    change Tendsto U (𝓝 0) (𝓝 (U 0)) at hLim
    rw [hU0] at hLim
    have hBounds (x : ℝ) : 0 ≤ steppedLinearA1AtZero h x ∧ steppedLinearA1AtZero h x ≤ U x := by
      by_cases hx : 0 < x
      · have he : 0 < (1 - Real.exp (-x)) ^ 2 :=
          pow_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))) 2
        obtain ⟨hpos, hle⟩ := (upperTailLinear_value_bounds hh hx).2
        unfold upperTailLinearP1 at hpos hle
        rw [steppedLinearA1AtZero, if_pos hx]
        refine ⟨((div_pos_iff_of_pos_right he).mp hpos).le, ?_⟩
        have H := (div_le_iff₀ he).mp hle
        dsimp only [U]
        convert H using 1 <;> ring
      · rw [steppedLinearA1AtZero, if_neg hx]
        exact ⟨le_rfl, by unfold U; positivity⟩
    change Tendsto (steppedLinearA1AtZero h) (𝓝 0) (𝓝 (steppedLinearA1AtZero h 0))
    rw [show steppedLinearA1AtZero h 0 = 0 by simp [steppedLinearA1AtZero]]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim
      (fun x ↦ (hBounds x).1) (fun x ↦ (hBounds x).2)
  · exact (hasDerivAt_steppedLinearA1AtZero hh ht).continuousAt

private theorem steppedLinear_compare_from_zero {u : ℝ} (hu : 0 < u)
    {f g f' g' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 u)) (hg : ContinuousOn g (Icc 0 u)) (h0 : f 0 = g 0)
    (hfd : ∀ t ∈ Ioo 0 u, HasDerivAt f (f' t) t)
    (hgd : ∀ t ∈ Ioo 0 u, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Ioo 0 u, f' t ≤ g' t) : f u ≤ g u := by
  have hd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) u)) :
      HasDerivWithinAt (fun x ↦ g x - f x) (g' t - f' t) (interior (Icc 0 u)) t := by
    have ht' : t ∈ Ioo (0 : ℝ) u := by simpa only [interior_Icc] using ht
    exact ((hgd t ht').sub (hfd t ht')).hasDerivWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) u)
    (hg.sub hf) hd (fun t ht ↦ sub_nonneg.mpr (hle t (by simpa only [interior_Icc] using ht)))
  have H := hm (left_mem_Icc.mpr hu.le) (right_mem_Icc.mpr hu.le) hu.le
  change g 0 - f 0 ≤ g u - f u at H
  rwa [← h0, sub_self, sub_nonneg] at H

private theorem steppedLinear_at_half {h : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11) :
    (19 / 16) * j(h) * A(h) (1 / 2) ≤ A₁(h) (1 / 2) := by
  let W (t : ℝ) := (t - 1 / 4) * (s(h) * k(h) * (Real.exp (-(s(h) * t)) * F h t))
  let I (x : ℝ) := ∫ t in (0 : ℝ)..x, W t
  let b : ℝ := (19 / 16) * j(h)
  let e : ℝ := (3 / 4) * j(h)
  have hc : Continuous W := by unfold W; fun_prop
  have hI (t : ℝ) : HasDerivAt I (W t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hD (t : ℝ) : HasDerivAt (fun x ↦ b * A(h) x + e * I x)
      (b * deriv A(h) t + e * W t) t := by
    exact (((hasDerivAt_one_sub_upperTailLinearA hh t).differentiableAt.hasDerivAt).const_mul b).add
      ((hI t).const_mul e)
  have H := steppedLinear_compare_from_zero (u := 1 / 2) (by norm_num)
    (f := fun x ↦ b * A(h) x + e * I x) (g := steppedLinearA1AtZero h)
    (continuous_iff_continuousAt.2 (fun t ↦ (hD t).continuousAt)).continuousOn
    (continuous_steppedLinearA1AtZero hh).continuousOn
    (by simp [I, steppedLinearA1AtZero, upperTailLinearA, upperTailGap])
    (fun t _ ↦ hD t) (fun _ ht ↦ hasDerivAt_steppedLinearA1AtZero hh ht.1) (by
      intro t ht
      have hd := stepped_LA_prime_pos hh ht.1
      have hl := (le_div_iff₀ hd).mp (steppedLinear_deriv_ratio_lower hh ht.1)
      calc
        _ = (j(h) * (1 + 3 * t / 4)) * deriv A(h) t := by
          dsimp only [b, e, W]
          rw [(hasDerivAt_one_sub_upperTailLinearA hh t).deriv]
          ring
        _ ≤ _ := hl)
  have hI₀ : 0 ≤ I (1 / 2) := steppedLinear_centered_integral_nonneg hh hhmax
  have he : 0 ≤ e := by dsimp only [e]; positivity
  rw [steppedLinearA1AtZero, if_pos (by norm_num : (0 : ℝ) < 1 / 2)] at H
  exact (le_add_of_nonneg_right (mul_nonneg he hI₀)).trans H

private theorem steppedLinear_ratio_tangent {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    (A₁(h) u / A(h) u) * deriv A(h) u ≤ deriv A₁(h) u := by
  let r := deriv A₁(h) u / deriv A(h) u
  have hd (t : ℝ) : HasDerivAt (fun x ↦ r * A(h) x) (r * deriv A(h) t) t :=
    (hasDerivAt_one_sub_upperTailLinearA hh t).differentiableAt.hasDerivAt.const_mul r
  have H := steppedLinear_compare_from_zero hu
    (f := steppedLinearA1AtZero h) (g := fun t ↦ r * A(h) t)
    (continuous_steppedLinearA1AtZero hh).continuousOn
    (continuous_iff_continuousAt.2 (fun t ↦ (hd t).continuousAt)).continuousOn
    (by simp [steppedLinearA1AtZero, upperTailLinearA, upperTailGap])
    (fun _ ht ↦ hasDerivAt_steppedLinearA1AtZero hh ht.1) (fun t _ ↦ hd t) (by
      intro t ht
      have ht' := stepped_LA_prime_pos hh ht.1
      have hmono := steppedLinear_deriv_ratio_monotone hh (show t ∈ Ioi 0 from ht.1)
        (show u ∈ Ioi 0 from hu) ht.2.le
      exact (div_le_iff₀ ht').1 hmono)
  rw [steppedLinearA1AtZero, if_pos hu] at H
  have hr := (div_le_iff₀ (stepped_LA_pos hh hu)).2 H
  exact (mul_le_mul_of_nonneg_right hr (stepped_LA_prime_pos hh hu).le).trans_eq
    (div_mul_cancel₀ _ (stepped_LA_prime_pos hh hu).ne')

/-- The quotient of the original, unnormalized coefficients is increasing. -/
theorem steppedLinear_value_ratio_monotone {h : ℝ} (hh : 0 < h) :
    MonotoneOn (fun t ↦ A₁(h) t / A(h) t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :=
    (hasDerivAt_upperTailLinearA1 hh ht).differentiableAt.hasDerivAt.div
      (hasDerivAt_one_sub_upperTailLinearA hh t).differentiableAt.hasDerivAt
      (stepped_LA_pos hh ht).ne'
  refine monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ ?_)
  have ht' : 0 < t := interior_subset ht
  change 0 ≤ deriv (A₁(h) / A(h)) t
  rw [(hd t ht').deriv]
  apply div_nonneg _ (sq_nonneg _)
  have hA := stepped_LA_pos hh ht'
  have H := mul_le_mul_of_nonneg_right (steppedLinear_ratio_tangent hh ht') hA.le
  have he : (A₁(h) t / A(h) t * deriv A(h) t) * A(h) t =
      A₁(h) t * deriv A(h) t := by
    field_simp [hA.ne'] <;> ring
  rw [he] at H
  exact sub_nonneg.mpr H

/-- The value ratio transports the half-interval bound to all larger arguments. -/
theorem steppedLinear_value_ratio_lower {h u : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hu : 1 / 2 ≤ u) :
    (19 / 16) * j(h) ≤ A₁(h) u / A(h) u := by
  have hu₀ : 0 < u := by linarith
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  exact ((le_div_iff₀ (stepped_LA_pos hh hhalf)).2 (steppedLinear_at_half hh hhmax)).trans
    (steppedLinear_value_ratio_monotone hh hhalf hu₀ hu)

/-- The same positive normalization can be used on both coefficients.
Only positivity of the normalizing factor and a nonnegative derivative of the
normalized marginal deficit are needed for the derivative comparison. -/
theorem steppedLinear_normalized_deriv_lower {h u : ℝ} {g : ℝ → ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 1 / 2 ≤ u)
    (hg : 0 ≤ g u) (hgD : DifferentiableAt ℝ g u)
    (hT : 0 ≤ deriv (fun t ↦ g t * A(h) t) u) :
    (19 / 16) * j(h) * deriv (fun t ↦ g t * A(h) t) u ≤
      deriv (fun t ↦ g t * A₁(h) t) u := by
  have hu₀ : 0 < u := by linarith
  let r := A₁(h) u / A(h) u
  have hr : r * A(h) u = A₁(h) u := div_mul_cancel₀ _ (stepped_LA_pos hh hu₀).ne'
  have hdT := hgD.hasDerivAt.mul
    (hasDerivAt_one_sub_upperTailLinearA hh u).differentiableAt.hasDerivAt
  have hdS := hgD.hasDerivAt.mul
    (hasDerivAt_upperTailLinearA1 hh hu₀).differentiableAt.hasDerivAt
  calc
    _ ≤ r * deriv (fun t ↦ g t * A(h) t) u :=
      mul_le_mul_of_nonneg_right (steppedLinear_value_ratio_lower hh hhmax hu) hT
    _ ≤ _ := by
      change r * deriv (g * A(h)) u ≤ deriv (g * A₁(h)) u
      rw [hdT.deriv, hdS.deriv]
      have H := mul_le_mul_of_nonneg_left (steppedLinear_ratio_tangent hh hu₀) hg
      calc
        _ = deriv g u * A₁(h) u + g u * (r * deriv A(h) u) := by rw [← hr]; ring
        _ ≤ _ := add_le_add_right H _

/-- Lower bound for the original ratio of normalized coefficient derivatives. -/
theorem steppedLinear_normalized_deriv_ratio_lower {h u : ℝ} {g : ℝ → ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 1 / 2 ≤ u)
    (hg : 0 ≤ g u) (hgD : DifferentiableAt ℝ g u)
    (hT : 0 < deriv (fun t ↦ g t * A(h) t) u) :
    (19 / 16) * j(h) ≤
      deriv (fun t ↦ g t * A₁(h) t) u / deriv (fun t ↦ g t * A(h) t) u :=
  (le_div_iff₀ hT).2 (steppedLinear_normalized_deriv_lower hh hhmax hu hg hgD hT.le)

private theorem steppedLinear_marginal_slope {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    (2 / u - (2 + h)) * A(h) u ≤ deriv A(h) u := by
  let W (t : ℝ) := Real.exp (-(s(h) * t)) * F h t
  let e : ℝ := s(h) + h / 2
  have hW : Continuous W := by unfold W; fun_prop
  have hnorm (r t : ℝ) (hr : 0 < r) (hrt : r ≤ t) : W t / t ≤ W r / r := by
    simp only [W, mul_div_assoc]
    exact mul_le_mul
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hrt (by positivity))))
      (decay_gap_quotient hh hr hrt).2
      (div_nonneg (gap_nonneg hh (hr.le.trans hrt)) (hr.le.trans hrt))
      (Real.exp_pos _).le
  let b := 2 * u / 3
  have hb : 0 < b := by dsimp only [b]; positivity
  have hmoment : (∫ t in (0 : ℝ)..u, t * W t) ≤ b * ∫ t in (0 : ℝ)..u, W t := by
    have H : (∫ t in (0 : ℝ)..u, (t - b) * W t) ≤
        ∫ t in (0 : ℝ)..u, (W b / b) * (t ^ 2 - b * t) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hu.le
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t ht ↦ ?_)
      have hrew : (W b / b) * (t ^ 2 - b * t) = (t - b) * ((W b / b) * t) := by ring
      rw [hrew]
      rcases le_total t b with htb | hbt
      · have H := mul_le_mul_of_nonneg_right (hnorm t b ht.1 htb) ht.1.le
        rw [div_mul_cancel₀ _ ht.1.ne'] at H
        exact mul_le_mul_of_nonpos_left H (sub_nonpos.mpr htb)
      · have H := mul_le_mul_of_nonneg_right (hnorm b t hb hbt) ht.1.le
        rw [div_mul_cancel₀ _ ht.1.ne'] at H
        exact mul_le_mul_of_nonneg_left H (sub_nonneg.mpr hbt)
    have hzero : (∫ t in (0 : ℝ)..u, (W b / b) * (t ^ 2 - b * t)) = 0 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
        integral_pow, integral_id]
      refine mul_eq_zero.mpr (Or.inr ?_)
      dsimp only [b]
      norm_num <;> ring
    simp_rw [sub_mul] at H
    rw [hzero, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
      sub_nonpos] at H
    exact H
  have hgap (t : ℝ) (ht : 0 ≤ t) :
      (1 - h * t / 2) * F h t ≤ t * Real.exp (-(h * t)) := by
    have H := exp_gap_two_sub_antitone (mul_nonneg hh.le ht)
    norm_num at H
    have hE : Real.exp (h * t) * Real.exp (-(h * t)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have H' : (2 - h * t) ≤ (2 + h * t) * Real.exp (-(h * t)) := by
      have H₀ : (2 - h * t) * Real.exp (h * t) ≤ 2 + h * t := by linarith only [H]
      have H₁ := mul_le_mul_of_nonneg_right H₀ (Real.exp_pos (-(h * t))).le
      rwa [mul_assoc, hE, mul_one] at H₁
    unfold upperTailGap
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hh).2
    nlinarith only [H']
  let P (t : ℝ) := t * W t
  let B (t : ℝ) := 2 * W t - e * (t * W t)
  let D (t : ℝ) := W t + t * (-(s(h) * W t) + Real.exp (-(s(h) * t)) * Real.exp (-(h * t)))
  have hd (t : ℝ) : HasDerivAt P (D t) t := by
    apply ((hasDerivAt_id' t).mul
      ((hasDerivAt_decay s(h) t).mul (hasDerivAt_upperTailGap hh))).congr_deriv
    dsimp only [D, W, id_eq, Pi.mul_apply]
    ring
  have hBD : (∫ t in (0 : ℝ)..u, B t) ≤ ∫ t in (0 : ℝ)..u, D t := by
    refine intervalIntegral.integral_mono_on hu.le
      (Continuous.intervalIntegrable (by unfold B; fun_prop) _ _)
      (Continuous.intervalIntegrable (by unfold D; fun_prop) _ _) (fun t ht ↦ ?_)
    have H := mul_le_mul_of_nonneg_left (hgap t ht.1) (Real.exp_pos (-(s(h) * t))).le
    dsimp only [B, D, e, W]
    linarith only [H]
  have hP := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (Continuous.intervalIntegrable (by unfold D; fun_prop) 0 u)
  rw [hP] at hBD
  change (∫ t in (0 : ℝ)..u, 2 * W t - e * (t * W t)) ≤ P u - P 0 at hBD
  have hP0 : P 0 = 0 := by simp [P]
  rw [hP0, sub_zero, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hBD
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have H := mul_le_mul_of_nonneg_left hmoment he
  change 2 * (∫ t in (0 : ℝ)..u, W t) - e * _ ≤ u * W u at hBD
  have hsum : (2 - (2 + h) * u) * (∫ t in (0 : ℝ)..u, W t) ≤ u * W u := by
    dsimp only [e, b] at H hBD
    linarith only [H, hBD]
  change (2 / u - (2 + h)) * (1 - upperTailLinearA h u) ≤ deriv A(h) u
  rw [one_sub_upperTailLinearA_eq_integral hh, (hasDerivAt_one_sub_upperTailLinearA hh u).deriv]
  apply (mul_le_mul_iff_right₀ hu).1
  change u * ((2 / u - (2 + h)) * (s(h) * k(h) * (∫ t in (0 : ℝ)..u, W t))) ≤
    u * (s(h) * k(h) * W u)
  have hclear : u * (2 / u - (2 + h)) = 2 - (2 + h) * u := by
    field_simp [hu.ne']
  calc
    _ = (s(h) * k(h)) * ((u * (2 / u - (2 + h))) * (∫ t in (0 : ℝ)..u, W t)) := by ring
    _ ≤ _ := by
      rw [hclear, show u * (s(h) * k(h) * W u) = (s(h) * k(h)) * (u * W u) by ring]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

private theorem steppedLinear_scalar_bound {h L q T Td Sd : ℝ} (hh : 0 < h)
    (hhmax : h ≤ 3 / 11) (hL : 0 ≤ L) (hLmax : L ≤ 1 / 3) (hq : j(h) ≤ q)
    (hT : 0 < T) (hTd : T / 2 ≤ Td) (hSd : (19 / 16) * j(h) ≤ Sd / Td) :
    -q * Sd + (h + L) * (q + L) * Td +
      (h + L) * L * (q + h + 2 * L) * T ≤ -(67 / 1512) * (q * Td) := by
  have hj : 0 < j(h) := by positivity
  have hq₀ := hj.trans_le hq
  have hTd₀ : 0 < Td := (by positivity : 0 < T / 2).trans_le hTd
  have hpoly :
      (h + L) * (j(h) + (3 + 4 * h) * L + 4 * L ^ 2) ≤
        ((19 / 16) * j(h) - 67 / 1512) * j(h) := by
    have hup : (h + L) * (j(h) + (3 + 4 * h) * L + 4 * L ^ 2) ≤
        (h + 1 / 3) * (j(h) + (3 + 4 * h) / 3 + 4 / 9) := by
      calc
        _ ≤ (h + 1 / 3) * (j(h) + (3 + 4 * h) * (1 / 3) + 4 * (1 / 3) ^ 2) := by
          gcongr
        _ = _ := by ring
    have hsq := pow_le_pow_left₀ hh.le hhmax 2
    have hmargin : 67 / 1188 ≤ (161 - 366 * h - 495 * h ^ 2) / 432 := by
      linarith only [hhmax, hsq]
    have hid : (19 / 16) * j(h) ^ 2 -
        (h + 1 / 3) * (j(h) + (3 + 4 * h) / 3 + 4 / 9) =
          (161 - 366 * h - 495 * h ^ 2) / 432 := by ring
    have hjmargin : (67 / 1512 : ℝ) * j(h) ≤ 67 / 1188 := by linarith only [hhmax]
    linarith only [hup, hmargin, hid, hjmargin]
  have hqpoly : j(h) * (q + L + 2 * L * (q + h + 2 * L)) ≤
      q * (j(h) + (3 + 4 * h) * L + 4 * L ^ 2) := by
    have H := mul_nonneg (sub_nonneg.mpr hq)
      (show 0 ≤ L + 2 * h * L + 4 * L ^ 2 by positivity)
    linarith only [H]
  have hcoef : (h + L) * (q + L + 2 * L * (q + h + 2 * L)) ≤
      q * ((19 / 16) * j(h) - 67 / 1512) := by
    apply (mul_le_mul_iff_right₀ hj).1
    have H₀ := mul_le_mul_of_nonneg_left hqpoly (by positivity : 0 ≤ h + L)
    have H₁ := mul_le_mul_of_nonneg_left hpoly hq₀.le
    linarith only [H₀, H₁]
  have hsign := mul_le_mul_of_nonneg_right hcoef hTd₀.le
  have hs := mul_le_mul_of_nonneg_left ((le_div_iff₀ hTd₀).mp hSd) hq₀.le
  have ht := mul_le_mul_of_nonneg_left (show T ≤ 2 * Td by linarith only [hTd])
    (show 0 ≤ (h + L) * L * (q + h + 2 * L) by positivity)
  linarith only [hsign, hs, ht]

private theorem steppedLinear_hasDerivAt_recip {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (fun x ↦ (F h x)⁻¹) (-(h + upperTailSlope h t) * upperTailSlope h t) t := by
  have hF := gap_pos hh ht
  have hD := hasDerivAt_upperTailGap (t := t) hh
  have hLog := (div_eq_iff hF.ne').1 (upperTailGap_logDeriv hh ht)
  rw [hD.deriv] at hLog
  have hsum : (h + upperTailSlope h t) * F h t = 1 := by
    rw [add_mul, ← hLog]
    unfold upperTailGap
    field_simp [hh.ne'] <;> ring
  apply (hD.inv hF.ne').congr_deriv
  rw [hLog]
  symm
  apply (eq_div_iff (pow_ne_zero 2 hF.ne')).2
  linear_combination -(upperTailSlope h t * F h t) * hsum

private theorem steppedLinear_gap_inv_eq {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    (F h t)⁻¹ = h + upperTailSlope h t := by
  have hF := gap_pos hh ht
  have hD := hasDerivAt_upperTailGap (t := t) hh
  have hLog := (div_eq_iff hF.ne').1 (upperTailGap_logDeriv hh ht)
  rw [hD.deriv] at hLog
  rw [← one_div]
  symm
  apply (eq_div_iff hF.ne').2
  rw [add_mul, ← hLog]
  unfold upperTailGap
  field_simp [hh.ne'] <;> ring

private theorem steppedLinear_mixed_formula {h u v : ℝ} {S T Q : ℝ → ℝ}
    (hh : 0 < h) (hd : 0 < v - u)
    (hS : DifferentiableAt ℝ S u) (hT : DifferentiableAt ℝ T u)
    {q : ℝ} (hQ : HasDerivAt Q (-q * Q v) v) :
    let L := upperTailSlope h (v - u)
    deriv (fun y ↦ deriv (fun x ↦ Q y / (s(h) * k(h)) *
      (S x - (F h (y - x))⁻¹ * T x)) u) v =
    Q v / (s(h) * k(h)) *
      (-q * deriv S u + (h + L) * (q + L) * deriv T u +
        (h + L) * L * (q + h + 2 * L) * T u) := by
  dsimp only
  let L (t : ℝ) := upperTailSlope h (t - u)
  let M (t : ℝ) := h + L t
  let B (t : ℝ) := deriv S u - M t * deriv T u - (M t * L t) * T u
  have hnear : (fun y ↦ deriv (fun x ↦ Q y / (s(h) * k(h)) *
      (S x - (F h (y - x))⁻¹ * T x)) u) =ᶠ[𝓝 v]
      fun y ↦ Q y / (s(h) * k(h)) * B y := by
    have hu : u < v := sub_pos.mp hd
    filter_upwards [eventually_gt_nhds hu] with y hy
    have hdiff : 0 < y - u := sub_pos.mpr hy
    have hdu : HasDerivAt (fun x ↦ y - x) (-1 : ℝ) u := (hasDerivAt_id' u).const_sub y
    have hR : HasDerivAt (fun x ↦ (F h (y - x))⁻¹) (M y * L y) u := by
      apply ((steppedLinear_hasDerivAt_recip hh hdiff).comp u hdu).congr_deriv
      dsimp only [M, L]
      ring
    have hDer := (hS.hasDerivAt.sub (hR.mul hT.hasDerivAt)).const_mul (Q y / (s(h) * k(h)))
    change deriv (fun x ↦ Q y / (s(h) * k(h)) *
      (S - (fun x ↦ (F h (y - x))⁻¹) * T) x) u = _
    rw [hDer.deriv, steppedLinear_gap_inv_eq hh hdiff]
    dsimp only [B, M, L]
    ring
  rw [hnear.deriv_eq]
  have hshift : HasDerivAt (fun y ↦ y - u) (1 : ℝ) v := (hasDerivAt_id' v).sub_const u
  have hL : HasDerivAt L (-(L v * M v)) v := by
    apply ((hasDerivAt_upperTailSlope hh hd).comp v hshift).congr_deriv
    dsimp only [L, M]
    ring
  have hM := hL.const_add h
  have hB : HasDerivAt B
      (-(-(L v * M v) * deriv T u) -
        (-(L v * M v) * L v + M v * -(L v * M v)) * T u) v :=
    ((hM.mul_const (deriv T u)).const_sub (deriv S u)).sub
      ((hM.mul hL).mul_const (T u))
  have hDer : HasDerivAt (fun y ↦ Q y / (s(h) * k(h)) * B y)
      _ v := (hQ.div_const (s(h) * k(h))).mul hB
  rw [hDer.deriv]
  dsimp only [M, B, L]
  ring

private theorem steppedLinear_negativeMarginal_deriv_nonneg {p : ℕ} (hp : 0 < p)
    {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ deriv (fun t ↦ compositionMoment p 0 (-t)) v := by
  rw [(hasDerivAt_negativeMarginal p v).deriv, ← negativeMarginalDerivative_zero hp]
  unfold negativeMarginalDerivative
  apply div_le_div_of_nonneg_right _ (gapCount_pos p).le
  have hsum (l : List (ℕ × ℕ × ℕ)) :
      (l.map (fun g ↦ -exponent p g.2.2 * Real.exp (-exponent p g.2.2 * 0))).sum ≤
      (l.map (fun g ↦ -exponent p g.2.2 * Real.exp (-exponent p g.2.2 * v))).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add _ ih
      simp only [mul_zero, Real.exp_zero, mul_one]
      let a := -exponent p g.2.2
      change a ≤ a * Real.exp (a * v)
      by_cases ha : 0 ≤ a
      · exact le_mul_of_one_le_right ha (Real.one_le_exp (mul_nonneg ha hv))
      · have ha' := le_of_not_ge ha
        simpa only [mul_one] using mul_le_mul_of_nonpos_left
          (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ha' hv)) ha'
  exact hsum _

private theorem steppedLinear_hasDerivAt_root {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let C := fun x ↦ compositionMoment p 0 (-x)
    HasDerivAt (fun x ↦ Real.sqrt (C x))
      ((deriv C t / C t / 2) * Real.sqrt (C t)) t := by
  dsimp only
  let C := fun x ↦ compositionMoment p 0 (-x)
  have hc : 0 < C t := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  have hR : 0 < Real.sqrt (C t) := Real.sqrt_pos.2 hc
  have hD : HasDerivAt C (deriv C t) t :=
    (hasDerivAt_negativeMarginal p t).differentiableAt.hasDerivAt
  apply (hD.sqrt hc.ne').congr_deriv
  change deriv C t / (2 * Real.sqrt (C t)) =
    (deriv C t / C t / 2) * Real.sqrt (C t)
  rw [← Real.sq_sqrt hc.le]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg (C t))]
  field_simp [hR.ne'] <;> ring

/-- The linear summand in independent lower and upper coordinates,
with the original positive-center marginal factors. -/
noncomputable def steppedLinearCorrection (p : ℕ) (u v : ℝ) : ℝ :=
  let h : ℝ := 3 / (p : ℝ)
  let C := fun t ↦ compositionMoment p 0 (-t)
  let g := fun t ↦ Real.exp ((2 + h) * t) / Real.sqrt (C t)
  let Q := fun t ↦ Real.exp (-(j(h) * t)) / (F h t * Real.sqrt (C t))
  Q v / (s(h) * k(h)) * (g u * A₁(h) u - (F h (v - u))⁻¹ * (g u * A(h) u))

/-- Quantitative mixed-derivative bound for the original linear correction.
The scale is the positive product of the upper coefficient, its logarithmic
decay rate, and the derivative of the lower marginal deficit. -/
theorem steppedLinearCorrection_mixed_bound {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 1 / 2 ≤ u) (hd : 3 ≤ v - u) :
    let h : ℝ := 3 / (p : ℝ)
    let C := fun t ↦ compositionMoment p 0 (-t)
    let R := fun t ↦ Real.sqrt (C t)
    let g := fun t ↦ Real.exp ((2 + h) * t) / R t
    let T := fun t ↦ g t * A(h) t
    let Q := fun t ↦ Real.exp (-(j(h) * t)) / (F h t * R t)
    let l := fun t ↦ deriv C t / C t / 2
    let q := j(h) + upperTailSlope h v + l v
    let scale := (Q v / (s(h) * k(h))) * (q * deriv T u)
    0 < scale ∧
      deriv (fun y ↦ deriv (fun x ↦ steppedLinearCorrection p x y) u) v ≤
        -(67 / 1512) * scale := by
  let h : ℝ := 3 / (p : ℝ)
  let C := fun t ↦ compositionMoment p 0 (-t)
  let R := fun t ↦ Real.sqrt (C t)
  let g := fun t ↦ Real.exp ((2 + h) * t) / R t
  let T := fun t ↦ g t * A(h) t
  let S := fun t ↦ g t * A₁(h) t
  let Q := fun t ↦ Real.exp (-(j(h) * t)) / (F h t * R t)
  let l := fun t ↦ deriv C t / C t / 2
  let q := j(h) + upperTailSlope h v + l v
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhmax : h ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hu₀ : 0 < u := by linarith
  have hd₀ : 0 < v - u := by linarith
  have hv : 0 < v := by linarith
  have hC (t : ℝ) (ht : 0 < t) : 0 < C t :=
    compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr ht.ne')
  have hR (t : ℝ) (ht : 0 < t) : 0 < R t := Real.sqrt_pos.2 (hC t ht)
  have hg : 0 < g u := div_pos (Real.exp_pos _) (hR u hu₀)
  have hT : 0 < T u := mul_pos hg (stepped_LA_pos hh hu₀)
  have hQ : 0 < Q v := div_pos (Real.exp_pos _) (mul_pos (gap_pos hh hv) (hR v hv))
  have hRuD : HasDerivAt R (l u * R u) u := steppedLinear_hasDerivAt_root hp₀ hu₀
  have hRvD : HasDerivAt R (l v * R v) v := steppedLinear_hasDerivAt_root hp₀ hv
  have hguD : HasDerivAt g ((2 + h - l u) * g u) u := by
    have hExp : HasDerivAt (fun x ↦ Real.exp ((2 + h) * x))
        ((2 + h) * Real.exp ((2 + h) * u)) u := by
      simpa only [neg_mul, neg_neg] using hasDerivAt_decay (-(2 + h)) u
    apply (hExp.div hRuD (hR u hu₀).ne').congr_deriv
    dsimp only [g]
    field_simp [(hR u hu₀).ne'] <;> ring
  have hTvD : HasDerivAt T ((2 + h - l u) * g u * A(h) u + g u * deriv A(h) u) u :=
    hguD.mul (hasDerivAt_one_sub_upperTailLinearA hh u).differentiableAt.hasDerivAt
  have hTd : T u / 2 ≤ deriv T u := by
    rw [hTvD.deriv]
    have hCl := negativeMarginal_logDeriv_le_two_div_add_one hp₀ hu₀
    change deriv C u / C u ≤ 2 / u + 1 at hCl
    have hAl : 1 / 2 ≤ 2 + h - l u + deriv A(h) u / A(h) u := by
      dsimp only [l]
      by_cases hs : u ≤ 1
      · have huInv : 1 ≤ 1 / u := (le_div_iff₀ hu₀).2 (by simpa using hs)
        have hA := (le_div_iff₀ (stepped_LA_pos hh hu₀)).2 (steppedLinear_marginal_slope hh hu₀)
        rw [show 2 / u = 2 * (1 / u) by ring] at hCl hA
        linarith only [hCl, hA, huInv]
      · have huInv : 1 / u ≤ 1 := (div_le_iff₀ hu₀).2 (by linarith)
        have hA := div_nonneg (stepped_LA_prime_pos hh hu₀).le (stepped_LA_pos hh hu₀).le
        rw [show 2 / u = 2 * (1 / u) by ring] at hCl
        linarith only [hCl, hA, huInv, hh]
    have H := mul_le_mul_of_nonneg_right
      ((le_div_iff₀ (stepped_LA_pos hh hu₀)).mp (show
        1 / 2 ≤ ((2 + h - l u) * A(h) u + deriv A(h) u) / A(h) u by
        rw [add_div, mul_div_cancel_right₀ _ (stepped_LA_pos hh hu₀).ne']
        exact hAl)) hg.le
    dsimp only [T] at *
    linarith only [H]
  have hTd₀ : 0 < deriv T u := (by positivity : 0 < T u / 2).trans_le hTd
  have hSd : (19 / 16) * j(h) ≤ deriv S u / deriv T u :=
    steppedLinear_normalized_deriv_ratio_lower hh hhmax hu hg.le
      hguD.differentiableAt hTd₀
  have hL := upperTailSlope_bounds hh hd₀
  have hLv := upperTailSlope_bounds hh hv
  have hq : j(h) ≤ q := by
    have hl : 0 ≤ l v :=
      div_nonneg (div_nonneg (steppedLinear_negativeMarginal_deriv_nonneg hp₀ hv.le)
        (hC v hv).le) (by norm_num)
    dsimp only [q]
    linarith only [hLv.1, hl]
  have hF := gap_pos hh hv
  have hFD := hasDerivAt_upperTailGap (t := v) hh
  have hLog := (div_eq_iff hF.ne').1 (upperTailGap_logDeriv hh hv)
  rw [hFD.deriv] at hLog
  have hQD : HasDerivAt Q (-q * Q v) v := by
    apply ((hasDerivAt_decay j(h) v).div (hFD.mul hRvD) (mul_ne_zero hF.ne' (hR v hv).ne')).congr_deriv
    change _ = _
    dsimp only [q, Q, Pi.mul_apply]
    rw [hLog]
    field_simp [hF.ne', (hR v hv).ne'] <;> ring
  have hSD := hguD.mul (hasDerivAt_upperTailLinearA1 hh hu₀).differentiableAt.hasDerivAt
  have hscale : 0 < Q v / (s(h) * k(h)) := div_pos hQ (by positivity)
  have hq₀ : 0 < q := (by positivity : 0 < j(h)).trans_le hq
  refine ⟨mul_pos hscale (mul_pos hq₀ hTd₀), ?_⟩
  change deriv (fun y ↦ deriv (fun x ↦ Q y / (s(h) * k(h)) *
    (S x - (F h (y - x))⁻¹ * T x)) u) v ≤
      -(67 / 1512) * ((Q v / (s(h) * k(h))) * (q * deriv T u))
  rw [steppedLinear_mixed_formula (S := S) (T := T) hh hd₀
    hSD.differentiableAt hTvD.differentiableAt hQD]
  have hLmax : upperTailSlope h (v - u) ≤ 1 / 3 :=
    hL.2.1.trans (one_div_le_one_div_of_le (by norm_num) hd)
  have H := mul_le_mul_of_nonneg_left
    (steppedLinear_scalar_bound hh hhmax hL.1.le hLmax hq hT hTd hSd) hscale.le
  linarith only [H]

/-- The original linear correction has strictly negative mixed derivative
for every degree at least eleven and every gap at least three. -/
theorem steppedLinearCorrection_mixed_neg {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 1 / 2 ≤ u) (hd : 3 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ steppedLinearCorrection p x y) u) v < 0 := by
  obtain ⟨hpos, hbound⟩ := steppedLinearCorrection_mixed_bound hp hu hd
  exact hbound.trans_lt (mul_neg_of_neg_of_pos (by norm_num) hpos)

/-- This summand equals the linear term of the existing kernel decomposition,
including the two original marginal normalizers. -/
theorem steppedLinearCorrection_eq_tail_decomposition {p : ℕ} (hp : 0 < p)
    {u d : ℝ} (hu : 0 < u) (hd : 0 < d) :
    let h : ℝ := 3 / (p : ℝ)
    let n : ℝ := (p + 2).choose 2
    steppedLinearCorrection p u (d + u) =
      (1 / Real.sqrt (upperTailNormalizer (p + 1) h (n / (p + 1)) (d + u))) *
        upperTailBaseFactor p u d * upperTailLinearError h u d := by
  let h : ℝ := 3 / (p : ℝ)
  let v := d + u
  let n : ℝ := (p + 2).choose 2
  let c := n / ((p : ℝ) + 1)
  let C (t : ℝ) := compositionMoment p 0 (-t)
  let α (t : ℝ) := 1 - Real.exp (-(h * t))
  let a := Real.exp (-v / (p : ℝ))
  have hv : 0 < v := by dsimp only [v]; linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have hn : 0 < n := by
    have hn' : 0 < (p + 2).choose 2 := Nat.choose_pos (by omega)
    dsimp only [n]
    exact_mod_cast hn'
  have hc : 0 < c := by dsimp only [c]; positivity
  have hCu : 0 < C u := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  have hCv : 0 < C v := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hα (t : ℝ) : α t = h * F h t := by
    unfold α upperTailGap
    field_simp [hh.ne']
  have hαv : 0 < α v := by rw [hα]; exact mul_pos hh (gap_pos hh hv)
  have hLo : DimThree.defect p a 1 1 = n * Real.exp (-v) * C v := by
    have H := upperTail_lower_weight hp v 0
    simpa only [zero_add, neg_zero, zero_div, Real.exp_zero, mul_zero, a, n, C] using H
  have hA : upperTailNormalizer (p + 1) h c v = c * α v * Real.exp (-v) * C v := by
    have H := upperTail_upper_weight hp hv
    dsimp only at H
    change (1 - a ^ 3) * DimThree.defect p a 1 1 =
      ((p : ℝ) + 1) * upperTailNormalizer (p + 1) h c v at H
    rw [show a ^ 3 = Real.exp (-(h * v)) from (tail_cube_pow hp v).1, hLo] at H
    change α v * (n * Real.exp (-v) * C v) = _ at H
    have hnp : (p : ℝ) + 1 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hnp)
    calc
      _ = α v * (n * Real.exp (-v) * C v) := H.symm
      _ = _ := by dsimp only [c]; field_simp [hnp] <;> ring
  have hroot : Real.sqrt (upperTailNormalizer (p + 1) h c v) =
      Real.sqrt c * Real.sqrt (α v) * Real.exp (-v / 2) * Real.sqrt (C v) := by
    rw [hA, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hc.le]
    have hExp : Real.exp (-v) = Real.exp (-v / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hExp, Real.sqrt_sq (Real.exp_pos _).le]
  let e := 1 - Real.exp (-u)
  have he : 0 < e := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hFv := gap_pos hh hv
  have hFd := gap_pos hh hd
  have hbase : (1 / Real.sqrt (upperTailNormalizer (p + 1) h c v)) *
      upperTailBaseFactor p u d =
      Real.exp u * F h d * e ^ 2 / (2 * F h v * Real.sqrt (C u) * Real.sqrt (C v)) := by
    have hE : Real.exp (-d / 2) * Real.exp (u / 2) = Real.exp (-v / 2) * Real.exp u := by
      rw [← Real.exp_add, ← Real.exp_add]
      dsimp only [v]
      congr 1
      ring
    change (1 / Real.sqrt (upperTailNormalizer (p + 1) h c v)) *
      (Real.sqrt c / 2 * Real.exp (-d / 2) *
        (α d / Real.sqrt (α v)) * (Real.exp (u / 2) * e ^ 2 / Real.sqrt (C u))) = _
    rw [hroot]
    calc
      _ = (Real.exp (-d / 2) * Real.exp (u / 2)) * α d * e ^ 2 /
          (2 * Real.exp (-v / 2) * (Real.sqrt (α v) * Real.sqrt (α v)) *
            Real.sqrt (C u) * Real.sqrt (C v)) := by
        field_simp [(Real.sqrt_pos.2 hc).ne', (Real.sqrt_pos.2 hαv).ne',
          (Real.sqrt_pos.2 hCu).ne', (Real.sqrt_pos.2 hCv).ne', (Real.exp_pos (-v / 2)).ne'] <;> ring
      _ = _ := by
        rw [hE, Real.mul_self_sqrt hαv.le, hα d, hα v]
        field_simp [hh.ne', (Real.exp_pos (-v / 2)).ne', hFv.ne',
          (Real.sqrt_pos.2 hCu).ne', (Real.sqrt_pos.2 hCv).ne'] <;> ring
  change steppedLinearCorrection p u v =
    (1 / Real.sqrt (upperTailNormalizer (p + 1) h c v)) *
      upperTailBaseFactor p u d * upperTailLinearError h u d
  rw [hbase, upperTailLinearError_eq_regularized hh hu hd]
  have hE : Real.exp (-(j(h) * v)) * Real.exp ((2 + h) * u) =
      Real.exp u * Real.exp (-(j(h) * d)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [v]
    ring
  change (Real.exp (-(j(h) * v)) / (F h v * Real.sqrt (C v))) / (s(h) * k(h)) *
    ((Real.exp ((2 + h) * u) / Real.sqrt (C u)) * A₁(h) u -
      (F h (v - u))⁻¹ * ((Real.exp ((2 + h) * u) / Real.sqrt (C u)) * A(h) u)) = _
  rw [show v - u = d by dsimp only [v]; ring]
  have hs : 0 < s(h) := by positivity
  have hk : 0 < k(h) := by positivity
  calc
    _ = (Real.exp (-(j(h) * v)) * Real.exp ((2 + h) * u)) *
        (F h d * A₁(h) u - A(h) u) /
          (s(h) * k(h) * F h d * F h v * Real.sqrt (C u) * Real.sqrt (C v)) := by
      field_simp [hFd.ne', hFv.ne', (Real.sqrt_pos.2 hCu).ne', (Real.sqrt_pos.2 hCv).ne',
        hs.ne', hk.ne'] <;> ring
    _ = _ := by
      rw [hE]
      change _ = Real.exp u * F h d * e ^ 2 /
        (2 * F h v * Real.sqrt (C u) * Real.sqrt (C v)) *
        (Real.exp (-(j(h) * d)) * (upperTailLinearA h u - 1 + F h d * A₁(h) u) /
          (s(h) * k(h) / 2 * F h d ^ 2 * e ^ 2))
      field_simp [hFd.ne', hFv.ne', (Real.sqrt_pos.2 hCu).ne', (Real.sqrt_pos.2 hCv).ne',
        hs.ne', hk.ne', he.ne'] <;> ring

#print axioms steppedLinear_deriv_ratio_integral
#print axioms steppedLinear_normalized_deriv_ratio_lower
#print axioms steppedLinearCorrection_mixed_bound
#print axioms steppedLinearCorrection_mixed_neg
#print axioms steppedLinearCorrection_eq_tail_decomposition

end RefinedBMV.PositiveCenter
