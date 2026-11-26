/- GID: D5/S3/Combinatorics/Graph/StarForming/FiniteMasks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/FiniteMasks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise, mathlib/module/Mathlib.Data.Fintype.EquivFin]
   utility: none
   digest: Every selection of a finite ordinal has an exact bounded bit-mask representation. -/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.FinRange

/-! Exact masks encode all subsets of the stated finite ordinal. They do not
replace a theorem quantified over unbounded graph sizes by a finite search. -/

namespace D5.S3.Combinatorics.Graph.StarForming.FiniteMasks

def bits (n : ℕ) (mask : Fin (2 ^ n)) (v : Fin n) : Bool := mask.val.testBit v.val

/-- Distinct bounded masks give different finite bit functions. -/
theorem bits_injective (n : ℕ) : Function.Injective (bits n) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact congrFun h ⟨i,hi⟩
  · have hni : n ≤ i := by omega
    have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hni
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (b.isLt.trans_le hp)]

/-- Every finite Boolean selection occurs, including the empty ordinal. -/
theorem bits_surjective (n : ℕ) : Function.Surjective (bits n) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨bits_injective n,?_⟩).2
  simp

/-- An arbitrary finite set is represented exactly, without a size assumption. -/
theorem selection_mask {n : ℕ} (S : Finset (Fin n)) :
    ∃ mask : Fin (2 ^ n), ∀ v, mask.val.testBit v.val = true ↔ v ∈ S := by
  obtain ⟨mask,hm⟩ := bits_surjective n (fun v => decide (v ∈ S))
  refine ⟨mask,fun v => ?_⟩
  change bits n mask v = true ↔ v ∈ S
  rw [congrFun hm v]
  simp

/-- The original supplier list count is the actual finite-set cardinality. -/
theorem list_count {n : ℕ} (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (Finset.univ.filter (fun v => p v = true)).card := by
  have hn : ((List.finRange n).filter p).Nodup := (List.nodup_finRange n).filter p
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext v
  simp

end D5.S3.Combinatorics.Graph.StarForming.FiniteMasks
