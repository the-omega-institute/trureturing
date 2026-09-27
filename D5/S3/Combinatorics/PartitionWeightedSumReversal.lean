/- GID: D5/S3/Combinatorics/PartitionWeightedSumReversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartitionWeightedSumReversal
   mirror-E: none(waiver:list-recursion-proof)
   anchors: []
   utility: none
   digest: A list and its reverse have weighted sums adding to length plus one times the total. -/

import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartitionWeightedSumReversal

/-- The one-based weighted sum of a list. -/
def weightedSum : List Nat -> Nat
  | [] => 0
  | x :: t => x + weightedSum t + t.sum

/-- A decreasing list of positive natural numbers whose sum is `n`. -/
def IsPartition (n : Nat) (y : List Nat) : Prop :=
  y.Pairwise (· ≥ ·) ∧ (∀ x ∈ y, 0 < x) ∧ y.sum = n

/-- Reversal preserves whether a partition's weighted sum is divisible by its total. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ y : List ℕ, IsPartition n y →
    (n ∣ weightedSum y ↔ n ∣ weightedSum y.reverse)

/-- The weighted-sum reversal conjecture for partitions. -/
theorem result : claim := by
  have append : ∀ l : List ℕ, ∀ x : ℕ,
      weightedSum (l ++ [x]) = weightedSum l + (l.length + 1) * x := by
    intro l
    induction l with
    | nil =>
        intro x
        simp [weightedSum]
    | cons a t ih =>
        intro x
        simp only [List.cons_append, weightedSum, List.sum_append, List.sum_cons,
          List.sum_nil, List.length_cons]
        rw [ih x]
        ring
  have reflect : ∀ y : List ℕ,
      weightedSum y + weightedSum y.reverse = (y.length + 1) * y.sum := by
    intro y
    induction y with
    | nil => simp [weightedSum]
    | cons x t ih =>
        simp only [weightedSum, List.reverse_cons, List.length_cons, List.sum_cons]
        rw [append t.reverse x, List.length_reverse]
        ring_nf at ih ⊢
        omega
  intro n y hy
  constructor
  · intro h
    apply (Nat.dvd_add_right h).mp
    refine ⟨y.length + 1, ?_⟩
    rw [reflect y, hy.2.2, Nat.mul_comm]
  · intro h
    apply (Nat.dvd_add_left h).mp
    refine ⟨y.length + 1, ?_⟩
    rw [reflect y, hy.2.2, Nat.mul_comm]
end D5.S3.Combinatorics.PartitionWeightedSumReversal
