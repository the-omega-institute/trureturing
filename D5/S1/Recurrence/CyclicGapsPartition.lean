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

example :
    let S : Finset ℝ := {0}
    let hS : S.Nonempty := Finset.singleton_nonempty 0
    gap S hS 0 = 1 ∧ ∑ x ∈ S, gap S hS x = 1 := by
  dsimp only
  let S : Finset ℝ := {0}
  let hS : S.Nonempty := Finset.singleton_nonempty 0
  have hUnit : (↑S : Set ℝ) ⊆ Set.Ico 0 1 := by
    intro x hx
    have hx : x = 0 := Finset.mem_singleton.mp hx
    subst x
    norm_num
  have hPartition := cyclic_gaps_partition_circle S hUnit hS
  refine ⟨?_, hPartition.2.2⟩
  norm_num [S, gap]

end D5.S1.Recurrence.CyclicGapsPartition
