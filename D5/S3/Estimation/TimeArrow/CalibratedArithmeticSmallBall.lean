/- GID: D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A monotone moving center has a finite arithmetic small-ball bound. -/

import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
noncomputable section

/-- Finite conditional mass for an integer-valued count variable. -/
def eventMass (p : ℤ → ℝ) (S : Finset ℤ) : ℝ := ∑ t ∈ S, p t

/-- A lattice band uses the same center for every integer target. -/
def latticeBand (g : ℤ → ℝ) (h : ℝ) (z : ℤ) (I : Finset ℤ) : Finset ℤ :=
  I.filter (fun t => |g t - z| ≤ h)

/-- The finite central small-ball event. The outer set contains the full
integer range attainable by the moving center on the central interval. -/
def arithmeticEvent (g : ℤ → ℝ) (h : ℝ) (I Z : Finset ℤ) : Finset ℤ :=
  I.filter (fun t => ∃ z ∈ Z, |g t - z| ≤ h)

private theorem integer_set_card_le_width (S : Finset ℤ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ x ∈ S, ∀ y ∈ S, ((y - x : ℤ) : ℝ) ≤ W) :
    (S.card : ℝ) ≤ W + 1 := by
  classical
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    let b := S.max' hn
    have ha : a ∈ S := S.min'_mem hn
    have hb : b ∈ S := S.max'_mem hn
    have hab : a ≤ b := S.min'_le b hb
    have hsub : S ⊆ Icc a b := by
      intro t ht
      exact mem_Icc.mpr ⟨S.min'_le t ht, S.le_max' t ht⟩
    have hc : (S.card : ℝ) ≤ ((Icc a b).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have hi : ((Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
      exact_mod_cast Int.card_Icc_of_le (by omega : a ≤ b + 1)
    rw [hi] at hc
    have hd := hw a ha b hb
    push_cast at hd
    linarith
  · simp only [not_nonempty_iff_eq_empty.mp hn, card_empty, Nat.cast_zero]
    linarith

private theorem lattice_band_card_le (g : ℤ → ℝ) (s h : ℝ) (I : Finset ℤ)
    (hs : 0 < s) (hh : 0 ≤ h)
    (hg : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x)
    (z : ℤ) :
    ((latticeBand g h z I).card : ℝ) ≤ 2 * h / s + 1 := by
  apply integer_set_card_le_width _ _ (by positivity)
  intro x hx y hy
  have hx' := mem_filter.mp hx
  have hy' := mem_filter.mp hy
  by_cases hxy : x ≤ y
  · have hd := hg x hx'.1 y hy'.1 hxy
    have hxlo := (abs_le.mp hx'.2).1
    have hyhi := (abs_le.mp hy'.2).2
    apply (le_div_iff₀ hs).mpr
    nlinarith
  · have hn : ((y - x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : y - x ≤ 0)
    exact hn.trans (by positivity)

/-- The central event is covered by the individual integer bands. This
retains the same count realization and never replaces it by independent phases. -/
theorem arithmetic_central_mass_bound (p g : ℤ → ℝ) (I Z : Finset ℤ)
    (s h a : ℝ) (hs : 0 < s) (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hp : ∀ t ∈ I, 0 ≤ p t) (hmax : ∀ t ∈ I, p t ≤ a)
    (hg : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x) :
    eventMass p (arithmeticEvent g h I Z) ≤
      a * (Z.card : ℝ) * (2 * h / s + 1) := by
  classical
  have he : arithmeticEvent g h I Z = Z.biUnion (fun z => latticeBand g h z I) := by
    ext t
    simp only [arithmeticEvent, latticeBand, mem_filter, mem_biUnion]
    aesop
  rw [eventMass, he]
  calc
    ∑ t ∈ Z.biUnion (fun z => latticeBand g h z I), p t ≤
        ∑ z ∈ Z, ∑ t ∈ latticeBand g h z I, p t :=
      sum_biUnion_le (fun z _ t ht => hp t (mem_filter.mp ht).1)
    _ ≤ ∑ z ∈ Z, ((latticeBand g h z I).card : ℝ) * a := by
      apply sum_le_sum
      intro z _
      exact (sum_le_sum fun t ht => hmax t (mem_filter.mp ht).1).trans_eq (by simp)
    _ ≤ ∑ _z ∈ Z, (2 * h / s + 1) * a := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right (lattice_band_card_le g s h I hs hh hg z) ha
    _ = a * (Z.card : ℝ) * (2 * h / s + 1) := by simp; ring

end
end D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
