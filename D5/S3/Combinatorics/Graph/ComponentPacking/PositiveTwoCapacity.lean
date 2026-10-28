/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/PositiveTwoCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/PositiveTwoCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Positive component lengths split between two inherited capacities. -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity

open scoped BigOperators

/-- Whole components with positive edge lengths fit into capacities d and d+1,
where d is their total edge length. Neither group is required to be nonempty. -/
theorem positive_two_capacity (C : ℕ) (ell : Fin C → ℕ)
    (positive : ∀ i, 1 ≤ ell i) :
    ∃ A : Finset (Fin C),
      (∑ i ∈ A, (ell i + 1)) ≤ (∑ i, ell i) ∧
      (∑ i ∈ Finset.univ \ A, (ell i + 1)) ≤ (∑ i, ell i) + 1 := by
  classical
  by_cases small : C ≤ 1
  · have cases : C = 0 ∨ C = 1 := by omega
    rcases cases with rfl | rfl
    · exact ⟨∅, by simp⟩
    · exact ⟨∅, by simp⟩
  have large : 2 ≤ C := by omega
  let d := ∑ i, ell i
  let size : Fin C → ℕ := fun i => ell i + 1
  change ∃ A : Finset (Fin C),
    (∑ i ∈ A, size i) ≤ d ∧ (∑ i ∈ Finset.univ \ A, size i) ≤ d + 1
  have total : (∑ i, size i) = d + C := by
    simp [size, d, Finset.sum_add_distrib]
  have item_bound (j : Fin C) : size j + (C - 1) ≤ d + 1 := by
    have lower : C - 1 ≤ ∑ i ∈ Finset.univ.erase j, ell i := by
      calc
        C - 1 = ∑ _i ∈ (Finset.univ.erase j : Finset (Fin C)), (1 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => positive i)
    have eq := Finset.sum_erase_add Finset.univ ell (Finset.mem_univ j)
    change (∑ i ∈ Finset.univ.erase j, ell i) + ell j = d at eq
    dsimp only [size]
    omega
  let candidates := Finset.univ.powerset.filter
    (fun A : Finset (Fin C) => C - 1 ≤ ∑ i ∈ A, size i)
  have feasible : candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
    rw [total]
    omega
  obtain ⟨A, hA, minimal⟩ := Finset.exists_min_image candidates Finset.card feasible
  have threshold : C - 1 ≤ ∑ i ∈ A, size i := (Finset.mem_filter.mp hA).2
  have nonempty : A.Nonempty := by
    by_contra empty
    have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
    simp only [this, Finset.sum_empty] at threshold
    omega
  obtain ⟨j, hj⟩ := nonempty
  have below : (∑ i ∈ A.erase j, size i) < C - 1 := by
    by_contra high
    have admissible : A.erase j ∈ candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), by omega⟩
    have bound := minimal (A.erase j) admissible
    have strict := Finset.card_erase_lt_of_mem hj
    omega
  have splitA := Finset.sum_erase_add A size hj
  have boundj := item_bound j
  have upper : (∑ i ∈ A, size i) ≤ d := by omega
  have complement := Finset.sum_sdiff (Finset.subset_univ A) (f := size)
  rw [total] at complement
  exact ⟨A, upper, by omega⟩

#check (fun C : ℕ => (⟨fun _ : Fin C => 1, fun _ => Nat.le_refl 1⟩ :
  {ell : Fin C → ℕ // ∀ i, 1 ≤ ell i}))
#print axioms positive_two_capacity

end D5.S3.Combinatorics.Graph.ComponentPacking.PositiveTwoCapacity
