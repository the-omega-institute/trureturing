/- GID: D5/S3/Combinatorics/Partitions/CommonBlockWeights
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/CommonBlockWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One clipped weight family allocates all compatible grouped demands. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

/-! Simultaneous grouped allocation by a fixed family of integer weights. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.CommonBlockWeights

open Finset

private theorem select_bounded_counts {I : Type*} [DecidableEq I]
    (s : Finset I) (capacity : I → ℕ) {N : ℕ} (enough : N ≤ ∑ i ∈ s, capacity i) :
    ∃ a : I → ℕ, (∀ i ∈ s, a i ≤ capacity i) ∧ ∑ i ∈ s, a i = N := by
  induction s using Finset.induction_on generalizing N with
  | empty =>
    have zero : N = 0 := Nat.eq_zero_of_le_zero (by simpa using enough)
    exact ⟨fun _ => 0, by simp, by simp [zero]⟩
  | @insert j s hjs ih =>
    let first := min N (capacity j)
    have remaining : N - first ≤ ∑ i ∈ s, capacity i := by
      rw [Finset.sum_insert hjs] at enough
      by_cases h : N ≤ capacity j
      · simp [first, min_eq_left h]
      · have eq : first = capacity j := min_eq_right (le_of_not_ge h)
        omega
    obtain ⟨rest, hrest, total⟩ := ih remaining
    let a := Function.update rest j first
    refine ⟨a, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with eq | hi
      · subst i
        simpa only [a, Function.update_self] using min_le_right N (capacity j)
      · have neq : i ≠ j := by
          intro eq
          exact hjs (by simpa only [eq] using hi)
        simpa only [a, Function.update_of_ne neq] using hrest i hi
    · rw [Finset.sum_insert hjs]
      have others : (∑ i ∈ s, a i) = ∑ i ∈ s, rest i :=
        Finset.sum_congr rfl fun i hi =>
          Function.update_of_ne (show i ≠ j by
            intro eq
            exact hjs (by simpa only [eq] using hi)) first rest
      rw [others, total]
      simp only [a, Function.update_self]
      exact Nat.add_sub_of_le (min_le_left N (capacity j))

/-- If the old total covers the maximal combined loss from rounding down capacities, then
all requested new equal-weight blocks fit within the target counts. -/
private theorem extend_block_allocation {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℕ) {d M old : ℕ} (positive : 0 < d)
    (threshold : (Fintype.card I - 1) * (d - 1) ≤ old)
    (total : ∑ i, x i = old + M * d) :
    ∃ a : I → ℕ, (∑ i, a i = M) ∧ (∀ i, a i * d ≤ x i) ∧
      ∑ i, (x i - a i * d) = old := by
  classical
  let C := ∑ i, x i / d
  let R := ∑ i, x i % d
  have equation : R + C * d = old + M * d := by
    dsimp only [R, C]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← total]
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa only [Nat.mul_comm (x i / d) d] using Nat.mod_add_div (x i) d
  have remainder : R ≤ Fintype.card I * (d - 1) := by
    calc
      R ≤ ∑ i : I, (d - 1) := Finset.sum_le_sum fun i _ => by
        have lt := Nat.mod_lt (x i) positive
        omega
      _ = Fintype.card I * (d - 1) := by simp
  have extra :
      Fintype.card I * (d - 1) = (Fintype.card I - 1) * (d - 1) + (d - 1) := by
    have card : 1 ≤ Fintype.card I := Fintype.card_pos
    conv_lhs => rw [← Nat.sub_add_cancel card]
    rw [Nat.add_mul, Nat.one_mul]
  have enough : M ≤ C := by
    by_contra h
    have multiple : C * d + d ≤ M * d := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right d (by omega)
    omega
  obtain ⟨a, ha, counts⟩ := select_bounded_counts (univ : Finset I) (fun i => x i / d) enough
  have follows (i : I) : a i * d ≤ x i :=
    (Nat.mul_le_mul_right _ (ha i (mem_univ _))).trans (Nat.div_mul_le_self _ _)
  refine ⟨a, counts, follows, ?_⟩
  have recover : (∑ i, (x i - a i * d)) + M * d = old + M * d := by
    have selected : (∑ i, a i * d) = M * d := by rw [← Finset.sum_mul, counts]
    rw [← selected, ← Finset.sum_add_distrib]
    have exactTotal : ∑ i, (x i - a i * d + a i * d) = ∑ i, x i :=
      Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (follows i)
    rw [exactTotal, total, selected]
  omega



/-- Exact allocations of all admissible grouped demands using shared block weights. -/
def CoversAllocations {n : ℕ} (k q : ℕ) (w : Fin n → ℕ) : Prop :=
  ∀ t U : ℕ, 0 < t → k * (t - 1) ≤ U → ∀ x : Fin t → ℕ, (∑ i, x i) = U * q →
    ∃ a : Fin n → Fin t → ℕ,
      (∀ j, ∑ i, a j i = U) ∧ (∀ i, ∑ j, a j i * w j = x i)

private theorem cover_by_capacity {k n q : ℕ} (bound : q ≤ (∑ i ∈ range n, (k + 1) ^ i)) :
    ∃ w : Fin n → ℕ, (∑ j, w j = q) ∧ CoversAllocations k q w := by
  induction n generalizing q with
  | zero =>
    have q0 : q = 0 := Nat.eq_zero_of_le_zero (by simpa using bound)
    subst q
    refine ⟨fun j => j.elim0, by simp, ?_⟩
    intro t U _ _ x sum
    refine ⟨fun j => j.elim0, fun j => j.elim0, ?_⟩
    intro i
    have le : x i ≤ ∑ j, x j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (x j)) (mem_univ i)
    simp only [Nat.mul_zero] at sum
    have eq : x i = 0 := by omega
    simp [eq]
  | succ n ih =>
    let old := min q (∑ i ∈ range n, (k + 1) ^ i)
    let d := q - old
    have totals : old + d = q := Nat.add_sub_of_le (min_le_left _ _)
    have dBound : d ≤ k * old + 1 := by
      by_cases fit : q ≤ (∑ i ∈ range n, (k + 1) ^ i)
      · simp [d, old, min_eq_left fit]
      · change q - min q (∑ i ∈ range n, (k + 1) ^ i) ≤ k * min q (∑ i ∈ range n, (k + 1) ^ i) + 1
        rw [min_eq_right (le_of_not_ge fit)]
        have b : q ≤ (k + 1) * (∑ i ∈ range n, (k + 1) ^ i) + 1 := by
          simpa only [geom_sum_succ] using bound
        rw [Nat.add_mul, Nat.one_mul] at b
        omega
    obtain ⟨w, sumW, covers⟩ := ih (min_le_right q (∑ i ∈ range n, (k + 1) ^ i))
    refine ⟨Fin.snoc w d, ?_, ?_⟩
    · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, sumW] using totals
    · intro t U tpos hblocks x xsum
      let _ : Nonempty (Fin t) := ⟨⟨0, tpos⟩⟩
      have xsum' : ∑ i, x i = U * old + U * d := by rw [← Nat.mul_add, totals, xsum]
      have step :
          ∃ a : Fin t → ℕ, (∑ i, a i = U) ∧ (∀ i, a i * d ≤ x i) ∧
            ∑ i, (x i - a i * d) = U * old := by
        by_cases z : d = 0
        · let a (i : Fin t) := if i = ⟨0, tpos⟩ then U else 0
          exact ⟨a, by simp [a], by simp [z], by simpa only [z, Nat.mul_zero, Nat.sub_zero, Nat.add_zero] using xsum'⟩
        · apply extend_block_allocation x (Nat.pos_of_ne_zero z) _ xsum'
          rw [Fintype.card_fin]
          calc
            (t - 1) * (d - 1) ≤ (t - 1) * (k * old) :=
              Nat.mul_le_mul_left _ (by omega)
            _ = (k * (t - 1)) * old := by rw [← Nat.mul_assoc, Nat.mul_comm (t - 1) k]
            _ ≤ U * old := Nat.mul_le_mul_right _ hblocks
      obtain ⟨a, count, fits, leftover⟩ := step
      obtain ⟨rest, hcount, hmass⟩ := covers t U tpos hblocks (fun i => x i - a i * d) leftover
      refine ⟨Fin.snoc rest a, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [Fin.snoc_last] using count
        · simpa only [Fin.snoc_castSucc] using hcount j
      · intro i
        simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hmass] using
          Nat.sub_add_cancel (fits i)

/-- One clipped weight family allocates every demand vector within each compatible block budget. -/
theorem common_weights_for_allocations {k n q : ℕ} (kpos : 0 < k)
    (budget : k * q + 1 ≤ (k + 1) ^ n) :
    ∃ w : Fin n → ℕ, (∑ j, w j = q) ∧ CoversAllocations k q w := by
  rw [← geom_sum_mul_add k n, Nat.mul_comm (∑ i ∈ range n, (k + 1) ^ i) k] at budget
  exact cover_by_capacity (Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right budget) kpos)

end D5.S3.Combinatorics.Partitions.CommonBlockWeights
