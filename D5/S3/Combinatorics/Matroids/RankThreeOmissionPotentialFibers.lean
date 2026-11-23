/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Point-potential evaluations have equally sized fibers in a ternary affine space. -/

import D5.S3.Combinatorics.Matroids.RankThreeOmissionRelations
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers

open Finset Function

private theorem third_index (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧ ({a, b, c} : Finset (Fin 3)) = univ := by
  let pair : Finset (Fin 3) := {a, b}
  have hpair : pair.card = 2 := by simp [pair, hab]
  obtain ⟨c, _, hc⟩ := exists_mem_notMem_of_card_lt_card
    (s := pair) (t := univ) (by simp [hpair])
  have hca : c ≠ a := fun h => hc (by simp [pair, h])
  have hcb : c ≠ b := fun h => hc (by simp [pair, h])
  refine ⟨c, hca, hcb, eq_univ_of_card _ ?_⟩
  simpa using (card_eq_three.mpr ⟨a, b, c, hab, hca.symm, hcb.symm, rfl⟩)

private theorem value_third {I T V : Type*} [AddCommGroup V]
    (points : T → Fin 3 → I) (value : I → V)
    (hline : ∀ t, ∑ j, value (points t j) = 0) (t : T) (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧
      value (points t c) = -(value (points t a) + value (points t b)) := by
  obtain ⟨c, hca, hcb, hall⟩ := third_index a b hab
  have hbc : b ∉ ({c} : Finset (Fin 3)) := by simp [hcb.symm]
  have ha : a ∉ ({b, c} : Finset (Fin 3)) := by simp [hab, hca.symm]
  have h := hline t
  rw [← hall, sum_insert ha, sum_insert hbc, sum_singleton] at h
  refine ⟨c, hca, hcb, eq_neg_of_add_eq_zero_left ?_⟩
  calc
    value (points t c) + (value (points t a) + value (points t b)) =
      value (points t a) + (value (points t b) + value (points t c)) := by abel
    _ = 0 := h

/-- If a ternary labeling sums to zero on every listed triple and every pair
with different labels is covered, its image is closed under negative sums. -/
theorem evaluation_range_neg_add {I T V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (points : T → Fin 3 → I) (value : I → V)
    (hline : ∀ t, ∑ j, value (points t j) = 0)
    (hcovered : ∀ i j, value i ≠ value j → ∃ t a b, points t a = i ∧ points t b = j)
    {x y : V} (hx : x ∈ Set.range value) (hy : y ∈ Set.range value) :
    -(x + y) ∈ Set.range value := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  by_cases h : value i = value j
  · have hx := ZModModule.char_nsmul_eq_zero 3 (value i)
    have eq : -(value i + value i) = value i := by
      apply neg_eq_of_add_eq_zero_left
      simpa [three_nsmul, add_assoc] using hx
    rw [← h, eq]
    exact ⟨i, rfl⟩
  · obtain ⟨t, a, b, ha, hb⟩ := hcovered i j h
    have hab : a ≠ b := fun eq => h (congrArg value (ha.symm.trans (eq ▸ hb)))
    obtain ⟨c, _, _, hc⟩ := value_third points value hline t a b hab
    exact ⟨points t c, by simpa [ha, hb] using hc⟩

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers
