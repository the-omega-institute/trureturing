/- GID: D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: The reciprocal Möbius prefix inverts the finite floor convolution. -/

import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The finite reciprocal Möbius floor inverse

This module contains the ordinary interval inverse and its absolute mass.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse

local notation "Q" => D5.S3.Arith.MoebiusLogarithmic.reciprocalSum
local notation "μℝ" => (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))

theorem measurable_reciprocalSum : Measurable Q := by
  let prefixSum : ℕ → ℝ := fun k => ∑ n ∈ Finset.Ioc 0 k, μℝ n / n
  exact (measurable_of_countable prefixSum).comp Nat.measurable_floor

theorem bounded_intervalIntegrable {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : Measurable f) (hC : ∀ t ∈ Ioc a b, |f t| ≤ C) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.norm_eq_abs] using hC t ht

theorem measurable_floorRatio (x : ℝ) :
    Measurable (fun u : ℝ => (Nat.floor (x / u) : ℝ)) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_const.div measurable_id).nat_floor

theorem floorRatio_bound {x u : ℝ} (hx : 0 ≤ x) (hu : 1 ≤ u) :
    |(Nat.floor (x / u) : ℝ)| ≤ x := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact (Nat.floor_le (div_nonneg hx (zero_le_one.trans hu))).trans (div_le_self hx hu)

theorem floorRatio_intervalIntegrable {x a b : ℝ}
    (hx : 0 ≤ x) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (Nat.floor (x / u) : ℝ)) volume a b :=
  bounded_intervalIntegrable hab (measurable_floorRatio x)
    (fun _ hu => floorRatio_bound hx (ha.trans hu.1.le))

private theorem cutoff_floorRatio_integral {x a P : ℝ}
    (hx : 0 ≤ x) (ha : 1 ≤ a) (haP : a ≤ P) :
    (∫ u in (1 : ℝ)..P, (Ici a).indicator (fun v => (Nat.floor (x / v) : ℝ)) u) =
      ∫ u in a..P, (Nat.floor (x / u) : ℝ) := by
  let g : ℝ → ℝ := fun u => Nat.floor (x / u)
  have hcut {b c : ℝ} (hb : 1 ≤ b) (hbc : b ≤ c) :
      IntervalIntegrable ((Ici a).indicator g) volume b c := by
    refine bounded_intervalIntegrable (C := x) hbc
      ((measurable_floorRatio x).indicator measurableSet_Ici) ?_
    intro u hu
    by_cases hua : u ∈ Ici a
    · rw [indicator_of_mem hua]
      exact floorRatio_bound hx (hb.trans hu.1.le)
    · rw [indicator_of_notMem hua, abs_zero]
      exact hx
  have hleft : (∫ u in (1 : ℝ)..a, (Ici a).indicator g u) = 0 := by
    calc
      _ = ∫ _u in (1 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha
        intro u hu
        exact indicator_of_notMem (show u ∉ Ici a from not_le_of_gt hu.2) _
      _ = 0 := intervalIntegral.integral_zero
  have hright : (∫ u in a..P, (Ici a).indicator g u) = ∫ u in a..P, g u := by
    apply intervalIntegral.integral_congr_Ioo_of_le haP
    intro u hu
    exact indicator_of_mem (show u ∈ Ici a from hu.1.le) _
  change (∫ u in (1 : ℝ)..P, (Ici a).indicator g u) = ∫ u in a..P, g u
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcut le_rfl ha) (hcut ha haP),
    hleft, zero_add, hright]

private theorem floorRatio_integral_scale {x a P : ℝ}
    (hx : 0 ≤ x) (hxP : x ≤ P) (ha : 1 ≤ a) (haP : a ≤ P) :
    (∫ u in a..P, (Nat.floor (x / u) : ℝ)) =
      a * (∫ v in (1 : ℝ)..P, (Nat.floor ((x / a) / v) : ℝ)) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hPa : 1 ≤ P / a := (one_le_div ha0).2 haP
  have hcut : P / a ≤ P := div_le_self (hx.trans hxP) ha
  have hx' : 0 ≤ x / a := div_nonneg hx ha0.le
  let g : ℝ → ℝ := fun u => Nat.floor (x / u)
  let gScaled : ℝ → ℝ := fun v => Nat.floor ((x / a) / v)
  have hscale : a * (∫ v in (1 : ℝ)..(P / a), gScaled v) = ∫ u in a..P, g u := by
    have h := intervalIntegral.smul_integral_comp_mul_right
      (a := (1 : ℝ)) (b := P / a) g a
    simpa only [g, gScaled, smul_eq_mul, one_mul, div_mul_cancel₀ P ha0.ne',
      div_div, mul_comm a] using h
  have htail : (∫ v in (P / a)..P, gScaled v) = 0 := by
    calc
      _ = ∫ _v in (P / a)..P, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hcut
        intro v hv
        have hv0 : 0 < v := (zero_lt_one.trans_le hPa).trans hv.1
        have hsmall : (x / a) / v < 1 := (div_lt_one hv0).2
          ((div_le_div_of_nonneg_right hxP ha0.le).trans_lt hv.1)
        simp only [gScaled, Nat.floor_eq_zero.2 hsmall, Nat.cast_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hext : (∫ v in (1 : ℝ)..P, gScaled v) =
      ∫ v in (1 : ℝ)..(P / a), gScaled v := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (floorRatio_intervalIntegrable hx' le_rfl hPa)
      (floorRatio_intervalIntegrable hx' hPa hcut), htail, add_zero]
  exact hscale.symm.trans (congrArg (fun y : ℝ => a * y) hext.symm)

private theorem finite_floor_cancellation {P y : ℝ} (hy : 0 ≤ y) (hyP : y ≤ P) :
    (∑ n ∈ Finset.Ioc 0 (Nat.floor P), μℝ n * (Nat.floor (y / n) : ℝ)) =
      if 1 ≤ y then 1 else 0 := by
  have hsub : Finset.Ioc 0 (Nat.floor y) ⊆ Finset.Ioc 0 (Nat.floor P) := by
    intro n hn
    obtain ⟨hn0, hny⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn0, hny.trans (Nat.floor_mono hyP)⟩
  have hsum : (∑ n ∈ Finset.Ioc 0 (Nat.floor y), μℝ n * (Nat.floor (y / n) : ℝ)) =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor P), μℝ n * (Nat.floor (y / n) : ℝ) := by
    apply Finset.sum_subset hsub
    intro n hn hyn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    have hny : y < (n : ℝ) := lt_of_not_ge fun h =>
      hyn (Finset.mem_Ioc.mpr ⟨hn0, (Nat.le_floor_iff hy).2 h⟩)
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
    rw [Nat.floor_eq_zero.2 ((div_lt_one hnpos).2 hny), Nat.cast_zero, mul_zero]
  rw [← hsum]
  by_cases h : 1 ≤ y
  · rw [ite_eq_left h]
    exact D5.S3.Arith.MoebiusLogarithmic.floor_cancellation h
  · simp [h, Nat.floor_eq_zero.2 (lt_of_not_ge h)]

/-- An ordinary interval integral of the reciprocal Möbius prefix inverts the finite
floor sum for every real pair of cutoffs in the stated range. -/
theorem floorIntegral_eq {P x : ℝ} (hP : 1 ≤ P) (hx : 0 ≤ x) (hxP : x ≤ P) :
    (∫ u in (1 : ℝ)..P, Q u * (Nat.floor (x / u) : ℝ)) = max (x - 1) 0 := by
  let s := Finset.Ioc 0 (Nat.floor P)
  let g : ℝ → ℝ := fun u => Nat.floor (x / u)
  let c : ℕ → ℝ := fun n => μℝ n / n
  let cut : ℕ → ℝ → ℝ := fun n u => (Ici (n : ℝ)).indicator g u
  have hprefix : (Ioo (1 : ℝ) P).EqOn
      (fun u => Q u * g u) (fun u => ∑ n ∈ s, c n * cut n u) := by
    intro u hu
    have hu0 : 0 ≤ u := zero_le_one.trans hu.1.le
    have hsub : Finset.Ioc 0 (Nat.floor u) ⊆ s := by
      intro n hn
      obtain ⟨hn0, hnu⟩ := Finset.mem_Ioc.mp hn
      exact Finset.mem_Ioc.mpr ⟨hn0, hnu.trans (Nat.floor_mono hu.2.le)⟩
    change (∑ n ∈ Finset.Ioc 0 (Nat.floor u), c n) * g u = ∑ n ∈ s, c n * cut n u
    rw [Finset.sum_mul]
    calc
      _ = ∑ n ∈ Finset.Ioc 0 (Nat.floor u), c n * cut n u := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnu := (Nat.le_floor_iff hu0).1 (Finset.mem_Ioc.mp hn).2
        rw [show cut n u = g u from indicator_of_mem (show u ∈ Ici (n : ℝ) from hnu) _]
      _ = _ := by
        apply Finset.sum_subset hsub
        intro n hn hnu
        have hn0 := (Finset.mem_Ioc.mp hn).1
        have hnot : u ∉ Ici (n : ℝ) := fun hl =>
          hnu (Finset.mem_Ioc.mpr ⟨hn0, (Nat.le_floor_iff hu0).2 hl⟩)
        rw [show cut n u = 0 from indicator_of_notMem hnot _, mul_zero]
  have hcut (n : ℕ) (_hn : n ∈ s) :
      IntervalIntegrable (fun u => c n * cut n u) volume 1 P := by
    refine IntervalIntegrable.const_mul ?_ (c n)
    refine bounded_intervalIntegrable (C := x) hP
      ((measurable_floorRatio x).indicator measurableSet_Ici) ?_
    intro u hu
    change |(Ici (n : ℝ)).indicator g u| ≤ x
    by_cases h : u ∈ Ici (n : ℝ)
    · rw [indicator_of_mem h]
      exact floorRatio_bound hx hu.1.le
    · rw [indicator_of_notMem h, abs_zero]
      exact hx
  have hratio (n : ℕ) (hn : n ∈ s) :
      IntervalIntegrable (fun v => μℝ n * (Nat.floor ((x / v) / n) : ℝ)) volume 1 P := by
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
    have heq (v : ℝ) : (x / v) / (n : ℝ) = (x / (n : ℝ)) / v := by
      simp only [div_div, mul_comm v]
    simp_rw [heq]
    exact (floorRatio_intervalIntegrable (div_nonneg hx hn0.le) le_rfl hP).const_mul _
  calc
    _ = ∫ u in (1 : ℝ)..P, ∑ n ∈ s, c n * cut n u :=
      intervalIntegral.integral_congr_Ioo_of_le hP hprefix
    _ = ∑ n ∈ s, ∫ u in (1 : ℝ)..P, c n * cut n u :=
      intervalIntegral.integral_finsetSum hcut
    _ = ∑ n ∈ s, ∫ v in (1 : ℝ)..P, μℝ n * (Nat.floor ((x / v) / n) : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn0, hnP⟩ := Finset.mem_Ioc.mp hn
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n from hn0)
      have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
      have hnP' : (n : ℝ) ≤ P := (Nat.le_floor_iff (zero_le_one.trans hP)).1 hnP
      have heq (v : ℝ) : (x / v) / (n : ℝ) = (x / (n : ℝ)) / v := by
        simp only [div_div, mul_comm v]
      simp_rw [heq]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      change (μℝ n / (n : ℝ)) *
          (∫ u in (1 : ℝ)..P, (Ici (n : ℝ)).indicator g u) = _
      rw [cutoff_floorRatio_integral hx hn1 hnP', floorRatio_integral_scale hx hxP hn1 hnP',
        ← mul_assoc, div_mul_cancel₀ _ hnpos.ne']
    _ = ∫ v in (1 : ℝ)..P, ∑ n ∈ s, μℝ n * (Nat.floor ((x / v) / n) : ℝ) :=
      (intervalIntegral.integral_finsetSum hratio).symm
    _ = ∫ v in (1 : ℝ)..P, (Iic x).indicator (fun _ => (1 : ℝ)) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le hP
      intro v hv
      have hv0 : 0 < v := zero_lt_one.trans hv.1
      change (∑ n ∈ Finset.Ioc 0 (Nat.floor P), μℝ n *
          (Nat.floor ((x / v) / n) : ℝ)) = _
      rw [finite_floor_cancellation (div_nonneg hx hv0.le)
        ((div_le_self hx hv.1.le).trans hxP)]
      simp only [one_le_div hv0]
      by_cases hvx : v ≤ x
      · rw [ite_eq_left hvx, indicator_of_mem (show v ∈ Iic x from hvx)]
      · rw [if_neg hvx, indicator_of_notMem (show v ∉ Iic x from hvx)]
    _ = max (x - 1) 0 := by
      by_cases hx1 : 1 ≤ x
      · change (∫ v in (1 : ℝ)..P, {z | z ≤ x}.indicator (fun _ => (1 : ℝ)) v) = _
        rw [intervalIntegral.integral_indicator (f := fun _ => (1 : ℝ))
            (show x ∈ Icc (1 : ℝ) P from ⟨hx1, hxP⟩),
          intervalIntegral.integral_const, max_eq_left (sub_nonneg.mpr hx1), smul_eq_mul, mul_one]
      · have hz : (∫ v in (1 : ℝ)..P, (Iic x).indicator (fun _ => (1 : ℝ)) v) = 0 := by
          calc
            _ = ∫ _v in (1 : ℝ)..P, (0 : ℝ) := by
              apply intervalIntegral.integral_congr_Ioo_of_le hP
              intro v hv
              exact indicator_of_notMem (show v ∉ Iic x from fun h =>
                hx1 (hv.1.le.trans h)) _
            _ = 0 := intervalIntegral.integral_zero
        rw [hz, max_eq_right (sub_nonpos.mpr (le_of_not_ge hx1))]

/-- The atom of mass one together with the absolute reciprocal Möbius density up to the cutoff. -/
def reciprocalMoebiusMass (P : ℝ) : ℝ := 1 + ∫ u in (1 : ℝ)..P, |Q u|

end D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
