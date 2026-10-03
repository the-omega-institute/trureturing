/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding
   mirror-E: none(waiver:cycle-folding)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Folding the even cycle preserves walks with unique lifts from each starting vertex. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkFolding

open scoped BigOperators
open CiglerCycleWalkDefs CiglerCycleWalkTransfer

noncomputable def cycleAdj (vertices : ℕ) [NeZero vertices] :
    Matrix (ZMod vertices) (ZMod vertices) ℤ :=
  Matrix.of fun start target =>
    (if start + 1 = target then 1 else 0) + (if start - 1 = target then 1 else 0)

def fold (vertices : ℕ) (positive : 1 ≤ vertices) (vertex : ZMod (2 * vertices)) :
    Fin vertices := by
  let : NeZero (2 * vertices) := ⟨by omega⟩
  refine ⟨min vertex.val (2 * vertices - 1 - vertex.val), ?_⟩
  have bounded := ZMod.val_lt vertex
  rcases le_total vertex.val (2 * vertices - 1 - vertex.val) with left | right
  · rw [min_eq_left left]
    omega
  · rw [min_eq_right right]
    omega

theorem folded_moment_eq_walkCount (vertices size : ℕ) (positive : 2 ≤ vertices) :
    (foldedAdj vertices ^ size) ⟨0, by omega⟩ ⟨0, by omega⟩ =
      (walkCount (2 * vertices) size 0 : ℤ) + walkCount (2 * vertices) size (-1) := by
  classical
  let : NeZero (2 * vertices) := ⟨by omega⟩
  let : Fact (1 < 2 * vertices) := ⟨by omega⟩
  let zero : Fin vertices := ⟨0, by omega⟩
  let projection : Matrix (ZMod (2 * vertices)) (Fin vertices) ℤ :=
    Matrix.of fun vertex target => if fold vertices (by omega) vertex = target then 1 else 0
  have fiber (vertex : ZMod (2 * vertices)) (target : Fin vertices) :
      fold vertices (by omega) vertex = target ↔
        vertex.val = target.val ∨ vertex.val + target.val + 1 = 2 * vertices := by
    rw [Fin.ext_iff]
    change min vertex.val (2 * vertices - 1 - vertex.val) = target.val ↔ _
    have vertex_bound := ZMod.val_lt vertex
    have target_bound := target.isLt
    rw [min_def]
    split_ifs <;> omega
  have plus_value (vertex : ZMod (2 * vertices)) :
      (vertex + 1).val =
        if vertex.val + 1 < 2 * vertices then vertex.val + 1 else 0 := by
    rw [ZMod.val_add, ZMod.val_one]
    have bounded := ZMod.val_lt vertex
    split_ifs with interior
    · exact Nat.mod_eq_of_lt interior
    · have last : vertex.val + 1 = 2 * vertices := by omega
      simp [last]
  have minus_value (vertex : ZMod (2 * vertices)) :
      (vertex - 1).val =
        if vertex.val = 0 then 2 * vertices - 1 else vertex.val - 1 := by
    by_cases bottom : vertex.val = 0
    · have is_zero : vertex = 0 := (ZMod.val_eq_zero vertex).mp bottom
      rw [if_pos bottom, is_zero, zero_sub, ZMod.neg_val, ZMod.val_one]
      simp
    · rw [if_neg bottom, ZMod.val_sub (by rw [ZMod.val_one]; omega)]
      rw [ZMod.val_one]
  have neighbors (vertex : ZMod (2 * vertices)) (target : Fin vertices) :
      (if fold vertices (by omega) (vertex + 1) = target then (1 : ℤ) else 0) +
        (if fold vertices (by omega) (vertex - 1) = target then 1 else 0) =
      foldedAdj vertices (fold vertices (by omega) vertex) target := by
    simp only [fiber, foldedAdj, Matrix.of_apply, Fin.ext_iff]
    change (if (vertex + 1).val = target.val ∨
        (vertex + 1).val + target.val + 1 = 2 * vertices then (1 : ℤ) else 0) +
      (if (vertex - 1).val = target.val ∨
        (vertex - 1).val + target.val + 1 = 2 * vertices then 1 else 0) =
      if min vertex.val (2 * vertices - 1 - vertex.val) + 1 = target.val ∨
          target.val + 1 = min vertex.val (2 * vertices - 1 - vertex.val) then 1
      else if min vertex.val (2 * vertices - 1 - vertex.val) = target.val ∧
          (min vertex.val (2 * vertices - 1 - vertex.val) = 0 ∨
            min vertex.val (2 * vertices - 1 - vertex.val) + 1 = vertices) then 1 else 0
    rw [plus_value, minus_value, min_def]
    have vertex_bound := ZMod.val_lt vertex
    have target_bound := target.isLt
    split_ifs <;> norm_num <;> omega
  have intertwining : cycleAdj (2 * vertices) * projection =
      projection * foldedAdj vertices := by
    ext vertex target
    simp only [Matrix.mul_apply, cycleAdj, Matrix.of_apply, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_mul]
    simp only [projection, Matrix.of_apply, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_mul]
    exact neighbors vertex target
  have powers (length : ℕ) :
      cycleAdj (2 * vertices) ^ length * projection =
        projection * foldedAdj vertices ^ length := by
    induction length with
    | zero => simp
    | succ length induction_hyp =>
      rw [pow_succ', pow_succ', Matrix.mul_assoc, induction_hyp,
        ← Matrix.mul_assoc, intertwining, Matrix.mul_assoc]
  have negative_one_value : (-1 : ZMod (2 * vertices)).val = 2 * vertices - 1 := by
    rw [ZMod.neg_val, ZMod.val_one]
    simp
  have endpoints (vertex : ZMod (2 * vertices)) :
      projection vertex zero =
        (if vertex = 0 then 1 else 0) + (if vertex = -1 then 1 else 0) := by
    have characterized : fold vertices (by omega) vertex = zero ↔
        vertex = 0 ∨ vertex = -1 := by
      rw [fiber]
      simp only [zero, Nat.add_zero]
      constructor
      · intro hypothesis
        rcases hypothesis with bottom | top
        · exact Or.inl ((ZMod.val_eq_zero vertex).mp bottom)
        · exact Or.inr ((ZMod.val_injective _)
            (by rw [negative_one_value]; omega))
      · intro hypothesis
        rcases hypothesis with bottom | top
        · subst vertex
          exact Or.inl (ZMod.val_zero)
        · subst vertex
          exact Or.inr (by rw [negative_one_value]; omega)
    simp only [projection, Matrix.of_apply, characterized]
    by_cases bottom : vertex = 0
    · simp [bottom]
    · by_cases top : vertex = -1 <;> simp [bottom, top]
  have origin : fold vertices (by omega) (0 : ZMod (2 * vertices)) = zero := by
    apply Fin.ext
    simp [fold, zero]
  have moment := congrArg (fun matrix => matrix (0 : ZMod (2 * vertices)) zero) (powers size)
  simp only [Matrix.mul_apply] at moment
  simp_rw [endpoints, mul_add, mul_ite, mul_one, mul_zero] at moment
  simp only [Finset.sum_add_distrib] at moment
  simp only [projection, Matrix.of_apply, origin, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at moment
  have cycle_count (target : ZMod (2 * vertices)) :
      (cycleAdj (2 * vertices) ^ size) 0 target = walkCount (2 * vertices) size target := by
    let next (start : ZMod (2 * vertices)) (label : Bool) :=
      start + if label then 1 else -1
    have words (word : List Bool) (start : ZMod (2 * vertices)) :
        wordContribution next (fun _ _ => 1) target start word =
          if start + (word.map fun label => if label then 1 else -1).sum = target
            then 1 else 0 := by
      induction word generalizing start with
      | nil => simp [wordContribution]
      | cons label rest induction_hyp =>
        simp only [wordContribution, one_mul, induction_hyp, List.map_cons, List.sum_cons]
        simp [next, add_assoc]
    have transfer : (Matrix.of fun start destination =>
        ∑ label : Bool, if next start label = destination then (1 : ℤ) else 0) =
        cycleAdj (2 * vertices) := by
      ext start destination
      simp only [next, Fintype.sum_bool, cycleAdj, Matrix.of_apply, sub_eq_add_neg,
        Bool.false_eq_true, if_true, if_false]
    rw [← transfer, ← weighted_walks_eq_pow next (fun _ _ => 1) size 0 target]
    simp_rw [words]
    simp only [List.map_ofFn, List.sum_ofFn, zero_add]
    exact (Finset.natCast_card_filter _ _).symm
  rw [cycle_count, cycle_count] at moment
  exact moment.symm

end D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkFolding
