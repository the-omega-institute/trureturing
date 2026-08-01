/- GID: D5/S1/Recurrence/CyclicGapsPartition
   generality: G
   mirror-B: D5/B/S1/Recurrence/CyclicGapsPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cyclic successor gaps are positive and partition the unit circle. -/

import D5.S1.Recurrence.CyclicNearestReturn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S1.Recurrence.CyclicGapsPartition

open D5.S1.Recurrence.CyclicNearestReturn

/-- The clockwise gap from `x` to its cyclic successor on the unit circle. -/
noncomputable def gap (S : Finset ℝ) (hS : S.Nonempty) (x : ℝ) : ℝ :=
  if x = S.max' hS then (1 - x) + S.min' hS else cyclicSucc S hS x - x

/-- Cyclic gaps remain on the carrier, are positive, and sum to one. -/
theorem cyclic_gaps_partition_circle (S : Finset ℝ)
    (hUnit : (↑S : Set ℝ) ⊆ Set.Ico 0 1)
    (hS : S.Nonempty) :
    (∀ x ∈ S, cyclicSucc S hS x ∈ S) ∧
    (∀ x ∈ S, 0 < gap S hS x) ∧
    ∑ x ∈ S, gap S hS x = 1 := by
  rcases cyclic_nearest_return_spec S hS with
    ⟨succ_mem, pred_mem, pred_succ, succ_pred, _, _, succ_wrap, _⟩
  have gap_pos : ∀ x ∈ S, 0 < gap S hS x := by
    intro x hx
    by_cases hxMax : x = S.max' hS
    · have hMaxUnit := hUnit (S.max'_mem hS)
      have hMinUnit := hUnit (S.min'_mem hS)
      rw [gap, if_pos hxMax]
      rw [hxMax]
      linarith [hMaxUnit.2, hMinUnit.1]
    · have hxLtMax : x < S.max' hS := by
        exact lt_of_le_of_ne (Finset.le_max' S x hx) hxMax
      have hAbove : (S.filter (x < ·)).Nonempty :=
        ⟨S.max' hS, Finset.mem_filter.mpr ⟨S.max'_mem hS, hxLtMax⟩⟩
      have hSuccData := Finset.mem_filter.mp (Finset.min'_mem _ hAbove)
      rw [gap, if_neg hxMax, cyclicSucc, dif_pos hAbove]
      linarith
  have hSuccSum : ∑ x ∈ S, cyclicSucc S hS x = ∑ x ∈ S, x := by
    exact Finset.sum_nbij' (cyclicSucc S hS) (cyclicPred S hS) succ_mem pred_mem
      pred_succ succ_pred (by intro x hx; rfl)
  have gap_as_correction : ∀ x ∈ S,
      gap S hS x = cyclicSucc S hS x - x + if x = S.max' hS then 1 else 0 := by
    intro x hx
    by_cases hxMax : x = S.max' hS
    · simp only [gap, hxMax, if_pos, succ_wrap]
      ring
    · simp [gap, hxMax]
  have gap_sum : ∑ x ∈ S, gap S hS x = 1 := by
    have hCorrection :
        ∑ x ∈ S, (if x = S.max' hS then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single (S.max' hS)]
      · simp
      · intro b hb hbMax
        simp [hbMax]
      · exact fun hMax ↦ (hMax (S.max'_mem hS)).elim
    calc
      ∑ x ∈ S, gap S hS x =
          ∑ x ∈ S, (cyclicSucc S hS x - x + if x = S.max' hS then 1 else 0) :=
        Finset.sum_congr rfl gap_as_correction
      _ = (∑ x ∈ S, (cyclicSucc S hS x - x)) +
          ∑ x ∈ S, if x = S.max' hS then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = 1 := by
        rw [Finset.sum_sub_distrib, hSuccSum, sub_self, zero_add]
        exact hCorrection
  exact ⟨succ_mem, gap_pos, gap_sum⟩

-- Non-vacuity witness: a two-point carrier exercises both branches of `gap` -- the
-- non-maximal point resolves through `cyclicSucc`, the maximal one through the wrap --
-- and the two gaps still partition the circle.
example (S : Finset ℝ) (hSdef : S = {0, 1 / 2}) (hS : S.Nonempty) :
    gap S hS 0 = 1 / 2 ∧ gap S hS (1 / 2) = 1 / 2 ∧ ∑ x ∈ S, gap S hS x = 1 := by
  subst hSdef
  have hMem : ∀ y : ℝ, y ∈ ({0, 1 / 2} : Finset ℝ) ↔ y = 0 ∨ y = 1 / 2 := by
    intro y; simp
  have hMax : ({0, 1 / 2} : Finset ℝ).max' hS = 1 / 2 := by
    refine le_antisymm (Finset.max'_le _ hS _ ?_) (Finset.le_max' _ (1 / 2) ?_)
    · intro y hy
      rcases (hMem y).mp hy with rfl | rfl <;> norm_num
    · exact (hMem (1 / 2)).mpr (Or.inr rfl)
  have hMin : ({0, 1 / 2} : Finset ℝ).min' hS = 0 := by
    refine le_antisymm (Finset.min'_le _ 0 ?_) (Finset.le_min' _ hS _ ?_)
    · exact (hMem 0).mpr (Or.inl rfl)
    · intro y hy
      rcases (hMem y).mp hy with rfl | rfl <;> norm_num
  have hFilter :
      ({0, 1 / 2} : Finset ℝ).filter (fun y => (0 : ℝ) < y) = {1 / 2} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hpos⟩
      rcases (hMem y).mp hy with rfl | rfl
      · exact absurd hpos (by norm_num)
      · rfl
    · rintro rfl
      exact ⟨(hMem (1 / 2)).mpr (Or.inr rfl), by norm_num⟩
  have hAbove :
      (({0, 1 / 2} : Finset ℝ).filter (fun y => (0 : ℝ) < y)).Nonempty := by
    rw [hFilter]; exact ⟨1 / 2, Finset.mem_singleton_self _⟩
  have hSucc : cyclicSucc ({0, 1 / 2} : Finset ℝ) hS 0 = 1 / 2 := by
    rw [cyclicSucc, dif_pos hAbove]
    -- `min'` carries a proof of nonemptiness, so rewriting the filtered set under it is
    -- not type correct; pin the value by antisymmetry on membership instead.
    refine le_antisymm (Finset.min'_le _ _ ?_) (Finset.le_min' _ _ _ ?_)
    · rw [hFilter]; exact Finset.mem_singleton_self _
    · intro y hy
      have hy' : y ∈ ({1 / 2} : Finset ℝ) := by rw [← hFilter]; exact hy
      have hyEq : y = 1 / 2 := Finset.mem_singleton.mp hy'
      exact le_of_eq hyEq.symm
  have hGapZero : gap ({0, 1 / 2} : Finset ℝ) hS 0 = 1 / 2 := by
    rw [gap, if_neg (by rw [hMax]; norm_num), hSucc]
    norm_num
  have hGapHalf : gap ({0, 1 / 2} : Finset ℝ) hS (1 / 2) = 1 / 2 := by
    rw [gap, if_pos hMax.symm, hMin]
    norm_num
  refine ⟨hGapZero, hGapHalf, ?_⟩
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton, hGapZero, hGapHalf]
  norm_num

end D5.S1.Recurrence.CyclicGapsPartition
