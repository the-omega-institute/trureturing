/- GID: D5/S3/Estimation/DataProcessing/StrictPeakAnalyticLower
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/StrictPeakAnalyticLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quadratic obstacle estimate gives a sharp lower surface for bounded peak tails. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
namespace D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
open MeasureTheory Set intervalIntegral
noncomputable section

/-- Tail of a continuous uniform source at a valley of quantile u. -/
def cap (u : ℝ) : ℝ := (1-u^2)/2

/-- The determinant obtained from the first two moments of a valley tail. -/
def determinant (G : ℝ → ℝ) : ℝ :=
  (1 - ∫ u in (0 : ℝ)..1, G u) * (∫ u in (0 : ℝ)..1, G u ^ 2) -
    (∫ u in (0 : ℝ)..1, G u)^2

private theorem quartic_integral (a b A B C : ℝ) :
    (∫ u in a..b, A+B*u^2+C*u^4) =
      A*(b-a)+B*(b^3-a^3)/3+C*(b^5-a^5)/5 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => A) volume a b := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun u : ℝ => B*u^2) volume a b :=
    (by fun_prop : Continuous (fun u : ℝ => B*u^2)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun u : ℝ => C*u^4) volume a b :=
    (by fun_prop : Continuous (fun u : ℝ => C*u^4)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0.add h2) h4, intervalIntegral.integral_add h0 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num
  ring

private theorem cap_integral : (∫ u in (0 : ℝ)..1, cap u) = 1/3 := by
  have he : cap = (fun u : ℝ => (1/2 : ℝ)+(-1/2)*u^2+0*u^4) := by
    funext u; unfold cap; ring
  rw [he, quartic_integral]
  norm_num

private theorem cap_square_integral : (∫ u in (0 : ℝ)..1, cap u ^ 2) = 2/15 := by
  have he : (fun u : ℝ => cap u ^ 2) =
      (fun u : ℝ => (1/4 : ℝ)+(-1/2)*u^2+(1/4)*u^4) := by
    funext u; unfold cap; ring
  rw [he, quartic_integral]
  norm_num

private theorem obstacle_integral (s : ℝ) :
    (∫ u in (0 : ℝ)..s, (s^2-u^2)^2/4) = 2*s^5/15 := by
  have he : (fun u : ℝ => (s^2-u^2)^2/4) =
      (fun u : ℝ => s^4/4+(-s^2/2)*u^2+(1/4)*u^4) := by
    funext u; ring
  rw [he, quartic_integral]
  norm_num
  ring

/-- The nonnegative obstacle gives a quadratic estimate with a freely chosen cutoff. -/
private theorem quadratic_obstacle (H : ℝ → ℝ)
    (hH : IntervalIntegrable H volume 0 1)
    (hH2 : IntervalIntegrable (fun u => H u ^ 2) volume 0 1)
    (hn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ H u)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    s^2*(∫ u in (0 : ℝ)..1, H u) - 2*s^5/15 ≤
      (∫ u in (0 : ℝ)..1, H u ^ 2) + (∫ u in (0 : ℝ)..1, u^2*H u) := by
  have hw : IntervalIntegrable (fun u => u^2*H u) volume 0 1 :=
    hH.continuousOn_mul (by fun_prop)
  let F := fun u => H u ^ 2 + u^2*H u - s^2*H u
  have hF : IntervalIntegrable F volume 0 1 := (hH2.add hw).sub (hH.const_mul _)
  have leftSub : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hs.2
  have rightSub : uIcc s (1 : ℝ) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hs.1 le_rfl
  have hpoly : IntervalIntegrable (fun u : ℝ => -((s^2-u^2)^2/4)) volume 0 s :=
    (by fun_prop : Continuous (fun u : ℝ => -((s^2-u^2)^2/4))).intervalIntegrable _ _
  have hl := integral_mono_on hs.1 hpoly (hF.mono_set leftSub) (fun u _ => by
    dsimp [F]
    nlinarith [sq_nonneg (H u + (u^2-s^2)/2)])
  have hr : 0 ≤ ∫ u in s..(1 : ℝ), F u := by
    apply integral_nonneg hs.2
    intro u hu
    have hn' := hn u ⟨hs.1.trans hu.1, hu.2⟩
    have hu' : s^2 ≤ u^2 := pow_le_pow_left₀ hs.1 hu.1 2
    dsimp [F]
    nlinarith [sq_nonneg (H u), mul_nonneg (sub_nonneg.mpr hu') hn']
  rw [intervalIntegral.integral_neg, obstacle_integral] at hl
  have hadj := integral_add_adjacent_intervals (hF.mono_set leftSub) (hF.mono_set rightSub)
  have hfull : (∫ u in (0 : ℝ)..1, F u) =
      (∫ u in (0 : ℝ)..1, H u ^ 2) + (∫ u in (0 : ℝ)..1, u^2*H u) -
        s^2*(∫ u in (0 : ℝ)..1, H u) := by
    dsimp [F]
    rw [intervalIntegral.integral_sub (hH2.add hw) (hH.const_mul _), intervalIntegral.integral_add hH2 hw,
      intervalIntegral.integral_const_mul]
  rw [hfull] at hadj
  linarith

/-- W1: every integrable tail between zero and the continuous tail satisfies the
sharp refined determinant lower bound. The cubic cutoff and strict interior
inequality are retained explicitly. No source-law correspondence is assumed. -/
theorem bounded_tail_lower_surface (G : ℝ → ℝ)
    (hG : IntervalIntegrable G volume 0 1)
    (hG2 : IntervalIntegrable (fun u => G u ^ 2) volume 0 1)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G u ∧ G u ≤ cap u) :
    let X := ∫ u in (0 : ℝ)..1, G u
    0 ≤ X ∧ X ≤ 1/3 ∧
    ∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*X ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ determinant G+X/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ∧
      -X/15 ≤ determinant G ∧
      (0 < X → X < 1/3 → -X/15 < determinant G) := by
  dsimp only
  let X := ∫ u in (0 : ℝ)..1, G u
  let H := fun u => cap u - G u
  let h := ∫ u in (0 : ℝ)..1, H u
  let b := ∫ u in (0 : ℝ)..1, H u ^ 2
  let c := ∫ u in (0 : ℝ)..1, u^2*H u
  have hc : IntervalIntegrable cap volume 0 1 :=
    (by unfold cap; fun_prop : Continuous cap).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun u => cap u ^ 2) volume 0 1 :=
    (by unfold cap; fun_prop : Continuous (fun u => cap u ^ 2)).intervalIntegrable _ _
  have hcG : IntervalIntegrable (fun u => cap u * G u) volume 0 1 :=
    hG.continuousOn_mul (by unfold cap; fun_prop)
  have hH : IntervalIntegrable H volume 0 1 := hc.sub hG
  have hH2 : IntervalIntegrable (fun u => H u ^ 2) volume 0 1 := by
    have he : (fun u => H u ^ 2) = (fun u => cap u ^ 2 - 2*(cap u*G u) + G u ^ 2) := by
      funext u; dsimp [H]; ring
    rw [he]
    exact (hc2.sub (hcG.const_mul _)).add hG2
  have hwH : IntervalIntegrable (fun u => u^2*H u) volume 0 1 :=
    hH.continuousOn_mul (by fun_prop)
  have hHcap : IntervalIntegrable (fun u => cap u * H u) volume 0 1 :=
    hH.continuousOn_mul (by unfold cap; fun_prop)
  have hn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ H u := by
    intro u hu; exact sub_nonneg.mpr (hbound u hu).2
  have hX0 : 0 ≤ X := integral_nonneg (by norm_num) (fun u hu => (hbound u hu).1)
  have hX1 : X ≤ 1/3 := by
    rw [← cap_integral]
    exact integral_mono_on (by norm_num) hG hc (fun u hu => (hbound u hu).2)
  have hh : h = 1/3-X := by
    dsimp [h,H]
    rw [intervalIntegral.integral_sub hc hG, cap_integral]
  have hcross : (∫ u in (0 : ℝ)..1, cap u * H u) = (h-c)/2 := by
    have he : (fun u => cap u * H u) = (fun u => (1/2 : ℝ)*H u - (1/2)*(u^2*H u)) := by
      funext u; unfold cap; ring
    rw [he, intervalIntegral.integral_sub (hH.const_mul _) (hwH.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    dsimp [h,c]
    ring
  have hmoment : (∫ u in (0 : ℝ)..1, G u ^ 2) = 2/15-h+c+b := by
    have he : (fun u => G u ^ 2) = (fun u => cap u ^ 2 - 2*(cap u*H u) + H u ^ 2) := by
      funext u; dsimp [H]; ring
    rw [he, intervalIntegral.integral_add (hc2.sub (hHcap.const_mul _)) hH2,
      intervalIntegral.integral_sub hc2 (hHcap.const_mul _), intervalIntegral.integral_const_mul, cap_square_integral, hcross]
    dsimp [b]
    ring
  have hid : determinant G = -1/45+2*h/15+(2/3+h)*(b+c)-2*h^2 := by
    unfold determinant
    rw [hmoment]
    change (1-X)*(2/15-h+c+b)-X^2 = _
    rw [hh]
    ring
  obtain ⟨s, hs, hs3⟩ := (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (by fun_prop : ContinuousOn (fun s : ℝ => s^3) (Icc 0 1)))
      (show 3*h ∈ Icc ((0 : ℝ)^3) ((1 : ℝ)^3) by rw [hh]; constructor <;> nlinarith)
  have hquad := quadratic_obstacle H hH hH2 hn s hs
  change s^2*h-2*s^5/15 ≤ b+c at hquad
  have hpoly : 1+s+7*s^2-3*s^3-3*s^4 ≥ 1+s+s^2 := by
    have hs2 : s^2 ≤ 1 := by nlinarith [sq_nonneg (1-s)]
    have h3 : s^3 ≤ s^2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs.2)]
    have h4 : s^4 ≤ s^2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs2)]
    linarith
  have hpolypos : 0 < 1+s+7*s^2-3*s^3-3*s^4 := by nlinarith [sq_nonneg s, hs.1]
  have hcor0 : 0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) := by
    apply mul_nonneg
    · exact mul_nonneg (div_nonneg (pow_nonneg hs.1 _) (by norm_num)) (sub_nonneg.mpr hs.2)
    · exact hpolypos.le
  have hfactor : 0 ≤ 2/3+h := by rw [hh]; linarith
  have hcor : s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ determinant G+X/15 := by
    have hq := mul_le_mul_of_nonneg_left hquad hfactor
    have he : (-1/45+2*h/15+(2/3+h)*(s^2*h-2*s^5/15)-2*h^2)+X/15 =
        s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) := by
      have hh' : h = s^3/3 := by linarith [hs3]
      have hX' : X = (1-s^3)/3 := by linarith [hh, hs3]
      rw [hh',hX']
      ring
    rw [hid]
    linarith
  refine ⟨hX0,hX1,s,hs,?_,hcor,hcor0,by linarith,?_⟩
  · linarith [hh,hs3]
  · intro hx0 hx1
    have hs0 : 0 < s := by by_contra h; have : s = 0 := le_antisymm (not_lt.mp h) hs.1; subst s; norm_num at hs3; linarith
    have hs1 : s < 1 := by by_contra h; have : s = 1 := le_antisymm hs.2 (not_lt.mp h); subst s; norm_num at hs3; linarith
    have hcorpos : 0 < s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) :=
      mul_pos (mul_pos (div_pos (pow_pos hs0 _) (by norm_num)) (sub_pos.mpr hs1)) hpolypos
    linarith

#print axioms bounded_tail_lower_surface
end
end D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower
