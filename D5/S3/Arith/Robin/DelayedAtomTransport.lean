/- GID: D5/S3/Arith/Robin/DelayedAtomTransport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/DelayedAtomTransport
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Compatible insertion excludes short delayed atoms and transports signed kernel mass. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Arith.Robin.DelayedAtomTransport

open Set MeasureTheory

/-- Regularity and order of the price used by an insertion comparison. -/
structure PriceCurve (price weight : ℝ → ℝ) : Prop where
  derivative : ∀ x, 1 < x → HasDerivAt price (-weight x) x
  continuous_weight : ContinuousOn weight (Ioi 1)
  positive_weight : ∀ x, 1 < x → 0 < weight x
  antitone_weight : AntitoneOn weight (Ioi 1)

private theorem curve_continuous {price weight : ℝ → ℝ} (K : PriceCurve price weight) :
    ContinuousOn price (Ioi 1) :=
  fun x hx => (K.derivative x hx).continuousAt.continuousWithinAt

private theorem curve_integrable {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable weight volume a b ∧ IntervalIntegrable price volume a b := by
  have hsub : Icc a b ⊆ Ioi 1 := fun x hx => ha.trans_le hx.1
  exact ⟨(K.continuous_weight.mono hsub).intervalIntegrable_of_Icc hab,
    ((curve_continuous K).mono hsub).intervalIntegrable_of_Icc hab⟩

theorem curve_difference {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    price a - price b = ∫ x in a..b, weight x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => K.derivative x (ha.trans_le
      (show a ≤ x from (by rwa [uIcc_of_le hab] at hx : x ∈ Icc a b).1)))
    (curve_integrable K ha hab).1.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem curve_slope_bounds {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b-a)*weight b ≤ price a-price b ∧ price a-price b ≤ (b-a)*weight a := by
  rw [curve_difference K ha hab]
  have hi := (curve_integrable K ha hab).1
  constructor
  · have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
      (fun x hx => K.antitone_weight (ha.trans_le hx.1) (ha.trans_le hab) hx.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  · have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      (fun x hx => K.antitone_weight ha (ha.trans_le hx.1) hx.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

private theorem curve_average_deficit {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {t h : ℝ} (ht : 1 < t) (hh : 0 < h) :
    (∫ x in t..t+h, price x) ≤ h*price t-h^2/2*weight (t+h) := by
  have hth : t ≤ t+h := by linarith
  have hlinear : IntervalIntegrable (fun x => price t - (x-t)*weight (t+h)) volume t (t+h) :=
    (continuous_const.sub ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable
      _ _
  have hbound := intervalIntegral.integral_mono_on hth (curve_integrable K ht hth).2 hlinear
    (fun x hx => by
      have hs := (curve_slope_bounds K ht hx.1).1
      have hw := K.antitone_weight (ht.trans_le hx.1) (ht.trans_le hth) hx.2
      have hm := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hx.1)
      linarith)
  have heq : (∫ x in t..t+h, price t - (x-t)*weight (t+h)) =
      h*price t-h^2/2*weight (t+h) := by
    have hil : IntervalIntegrable (fun x : ℝ => (x-t)*weight (t+h)) volume t (t+h) := by
      exact (show Continuous (fun x : ℝ => (x-t)*weight (t+h)) from by fun_prop).intervalIntegrable
        _ _
    have hid : IntervalIntegrable (fun x : ℝ => x-t) volume t (t+h) := by
      exact (show Continuous (fun x : ℝ => x-t) from by fun_prop).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const hil,
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ => t)
        (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
      integral_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  exact hbound.trans_eq heq

/-- An actual insertion comparison at a later center and a paid density bound
exclude every contact with the closed short pulse. The center is not a maximizer
at the interpolated contact. -/
theorem delayed_atom_exclusion {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {a y t C h : ℝ} (hya : y < a + 1)
    (ht : 1 < t) (hh : 0 < h) (htC : t ≤ C)
    (hcompatible : h * price y ≤ ∫ u in C..C + h, price u)
    (hdensity : 2 * weight t < h * weight (t + h)) : t ∉ Icc a y := by
  intro hcontact
  have hty : t ≤ y := hcontact.2
  have hyt : y < t+1 := by linarith [hcontact.1]
  have hmono : AntitoneOn price (Ioi 1) := by
    intro x hx z hz hxz
    have hs := (curve_slope_bounds K hx hxz).1
    have hw := K.positive_weight z hz
    nlinarith
  have hshift : (∫ u in C..C+h, price u) ≤ ∫ u in t..t+h, price u := by
    have hC : 1 < C := ht.trans_le htC
    have hiC := (curve_integrable K hC (by linarith : C ≤ C+h)).2
    have hit := (curve_integrable K ht (by linarith : t ≤ t+h)).2
    have eC := intervalIntegral.integral_comp_add_right (f := price) C (a := 0) (b := h)
    have et := intervalIntegral.integral_comp_add_right (f := price) t (a := 0) (b := h)
    simp only [zero_add, add_comm h] at eC et
    rw [← eC, ← et]
    apply intervalIntegral.integral_mono_on hh.le
    · simpa only [sub_self, add_sub_cancel_left] using hiC.comp_add_right C
    · simpa only [sub_self, add_sub_cancel_left] using hit.comp_add_right t
    · intro u hu
      exact hmono (show 1 < u+t by linarith [hu.1])
        (show 1 < u+C by linarith [hu.1]) (by linarith)
  have hdef := curve_average_deficit K ht hh
  have hupper := (curve_slope_bounds K ht hty).2
  have hw := K.positive_weight t ht
  have hshort : price t-price y < weight t := by nlinarith
  have hcomb := hcompatible.trans hshift |>.trans hdef
  nlinarith [mul_pos hh (sub_pos.mpr hdensity)]

/-- Reference and strict actual initial atoms use different endpoints. -/
def referenceKernel (price : ℝ → ℝ) (t B D z : ℝ) : ℝ :=
  if t < z ∧ z ≤ B then (price z-price B)/D else 0

def actualKernel (price : ℝ → ℝ) (t B D z : ℝ) : ℝ :=
  if t ≤ z ∧ z ≤ B then (price z-price B)/D else 0

end D5.S3.Arith.Robin.DelayedAtomTransport
