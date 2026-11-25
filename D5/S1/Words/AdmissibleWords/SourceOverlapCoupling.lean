/- GID: D5/S1/Words/AdmissibleWords/SourceOverlapCoupling
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/SourceOverlapCoupling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two intervals realize compatible source overlaps and prescribed inclusions. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! A split of the unit interval realizes overlaps with a fixed source event. -/

open Set MeasureTheory

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.SourceOverlapCoupling

/-- Prescribed source overlaps are realizable when the masses inside and outside the source
each respect every required inclusion. -/
theorem exists_nested_events {V : Type*} (R : V → V → Prop) (q overlap : V → ℝ) (s : V)
    (source : q s ∈ Icc 0 1) (anchor : overlap s = q s)
    (left : ∀ v, overlap v ∈ Icc 0 (q s))
    (right : ∀ v, q v - overlap v ∈ Icc 0 (1 - q s))
    (monotone : ∀ ⦃u v⦄, R u v →
      overlap u ≤ overlap v ∧ q u - overlap u ≤ q v - overlap v) :
    ∃ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) ∧
      (∀ ⦃u v⦄, R u v → A u ⊆ A v) ∧
      ∀ v, volume.real (A s \ A v) = q s - overlap v := by
  let A (v : V) := Ico 0 (overlap v) ∪ Ico (q s) (q s + (q v - overlap v))
  refine ⟨A, ?_, ?_, ?_⟩
  · intro v
    have disjointIntervals :
        Disjoint (Ico 0 (overlap v)) (Ico (q s) (q s + (q v - overlap v))) :=
      disjoint_left.mpr fun _ hx hy => (not_lt_of_ge ((left v).2.trans hy.1)) hx.2
    refine ⟨measurableSet_Ico.union measurableSet_Ico, union_subset ?_ ?_, ?_⟩
    · exact Ico_subset_Ico le_rfl ((left v).2.trans source.2)
    · exact Ico_subset_Ico source.1 (by linarith [(right v).2])
    · change volume.real (_ ∪ _) = _
      rw [measureReal_union disjointIntervals measurableSet_Ico (by simp) (by simp),
        Real.volume_real_Ico_of_le (left v).1,
        Real.volume_real_Ico_of_le (le_add_of_nonneg_right (right v).1)]
      linarith
  · intro u v edge
    exact union_subset_union (Ico_subset_Ico_right (monotone edge).1)
      (Ico_subset_Ico_right (add_le_add_right (monotone edge).2 _))
  · intro v
    have diff : A s \ A v = Ico (overlap v) (q s) := by
      have hv := (left v).1
      have hs := (left v).2
      simp only [A, anchor, sub_self, add_zero, Ico_self, union_empty]
      ext x
      simp only [mem_sdiff, mem_Ico, mem_union, not_or, not_and_or, not_le, not_lt]
      grind
    rw [diff, Real.volume_real_Ico_of_le (left v).2]

end D5.S1.Words.AdmissibleWords.SourceOverlapCoupling
