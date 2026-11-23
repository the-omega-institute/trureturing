/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Point-potential evaluations have equally sized fibers in a ternary affine space. -/

import D5.S3.Combinatorics.Matroids.RankThreeOmissionRelations
import Mathlib.Algebra.Field.ZMod
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

/-- Independent point-potential coordinates realize every ternary vector. -/
theorem evaluation_surjective {I T J : Type*} [Fintype J]
    (points : T → Fin 3 → I) (value : I → J → ZMod 3)
    (anchor : I) (hanchor : value anchor = 0)
    (hline : ∀ t, ∑ j, value (points t j) = 0)
    (hcovered : ∀ i j, value i ≠ value j → ∃ t a b, points t a = i ∧ points t b = j)
    (hindependent : LinearIndependent (ZMod 3) (fun j i => value i j)) :
    Surjective value := by
  classical
  have zeroMem : (0 : J → ZMod 3) ∈ Set.range value := ⟨anchor, hanchor⟩
  have closed {x y : J → ZMod 3} (hx : x ∈ Set.range value) (hy : y ∈ Set.range value) :
      -(x + y) ∈ Set.range value :=
    evaluation_range_neg_add points value hline hcovered hx hy
  have negMem (x : J → ZMod 3) (hx : x ∈ Set.range value) : -x ∈ Set.range value := by
    simpa only [add_zero] using closed hx zeroMem
  let S : AddSubgroup (J → ZMod 3) :=
    { carrier := Set.range value
      zero_mem' := zeroMem
      add_mem' := fun hx hy => by simpa only [neg_neg] using negMem _ (closed hx hy)
      neg_mem' := negMem _ }
  let W := AddSubgroup.toZModSubmodule 3 S
  suffices hW : W = ⊤ by
    intro y
    have hy : y ∈ W := hW.symm ▸ Submodule.mem_top
    exact hy
  apply (Submodule.dualAnnihilator_eq_bot_iff (W := W)).mp
  rw [Submodule.eq_bot_iff]
  intro φ hφ
  let b := Pi.basisFun (ZMod 3) J
  let c (j : J) := φ (b j)
  have hcomb : (∑ j, c j • fun i => value i j) = (0 : I → ZMod 3) := by
    funext i
    have h := (W.mem_dualAnnihilator φ).mp hφ (value i) (show value i ∈ W from ⟨i, rfl⟩)
    have expand : value i = ∑ j, value i j • b j := by
      funext k
      simp [b, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
    rw [expand, map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_comm] using h
  have zeros := (Fintype.linearIndependent_iff.mp hindependent) c hcomb
  exact b.ext fun j => zeros j

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers
