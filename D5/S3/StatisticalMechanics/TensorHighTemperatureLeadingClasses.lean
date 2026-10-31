/- GID: D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Identity and transposition classes lead tensor high-temperature degrees. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Rat.Cast.Order

/-! Formal reading of the all-ones and transposition leading classes in (7.21). -/

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses

open Finset

set_option autoImplicit false

noncomputable section

/-- The degree in equation (7.21), summed over tuples of distinct partition parts. -/
def degree (s : ℕ) {n : ℕ} (p : Nat.Partition n) : ℚ :=
  ∑ t : Fin s → p.parts.toFinset,
    (∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)) /
      ((Finset.lcm (Finset.univ.image (fun j => (t j : ℕ))) id : ℕ) : ℚ)

/-- The partition `[1^n]`. -/
def identityClass (n : ℕ) : Nat.Partition n :=
  Nat.Partition.ofSums n (Multiset.replicate n 1) (by simp)

/-- The partition `[2,1^(n-2)]` when `n ≥ 2`, with a total extension below that range. -/
def transpositionClass (n : ℕ) : Nat.Partition n :=
  if h : 2 ≤ n then
    Nat.Partition.ofSums n (2 ::ₘ Multiset.replicate (n - 2) 1) (by simp [h])
  else Nat.Partition.indiscrete n

/-- The formal reading of the O'Connor--Ramgoolam leading-class assertion. -/
def claim : Prop :=
  ∀ n ≥ 2, ∀ s ≥ 1,
    degree s (identityClass n) = (n : ℚ) ^ s ∧
      degree s (transpositionClass n) =
        ((n : ℚ) ^ s + ((n - 2 : ℕ) : ℚ) ^ s) / 2 ∧
      degree s (transpositionClass n) < degree s (identityClass n) ∧
      ∀ p : Nat.Partition n,
        p ≠ identityClass n → p ≠ transpositionClass n →
          degree s p < degree s (transpositionClass n)

private theorem total_weight (s : ℕ) {n : ℕ} (p : Nat.Partition n) :
    (∑ t : Fin s → p.parts.toFinset,
      ∏ j, ((t j : ℕ) * p.parts.count (t j : ℕ) : ℚ)) = (n : ℚ) ^ s := by
  sorry

private theorem degree_le_from_one_count (s : ℕ) {n : ℕ} (p : Nat.Partition n)
    (hs : 1 ≤ s) :
    degree s p ≤ ((n : ℚ) ^ s + (p.parts.count 1 : ℚ) ^ s) / 2 := by
  sorry

private theorem identity_degree (s n : ℕ) (hn : 2 ≤ n) :
    degree s (identityClass n) = (n : ℚ) ^ s := by
  sorry

private theorem transposition_degree (s n : ℕ) (hn : 2 ≤ n) :
    degree s (transpositionClass n) =
      ((n : ℚ) ^ s + ((n - 2 : ℕ) : ℚ) ^ s) / 2 := by
  sorry

private theorem transposition_lt_identity (s n : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    degree s (transpositionClass n) < degree s (identityClass n) := by
  sorry

private theorem one_count_le_two_sub {n : ℕ} (p : Nat.Partition n) (hn : 2 ≤ n)
    (hp : p ≠ identityClass n) :
    p.parts.count 1 ≤ n - 2 := by
  sorry

private theorem one_count_eq_two_sub_iff {n : ℕ} (p : Nat.Partition n) (hn : 2 ≤ n)
    (hp : p ≠ identityClass n) :
    p.parts.count 1 = n - 2 ↔ p = transpositionClass n := by
  sorry

private theorem other_degree_lt (s n : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (p : Nat.Partition n) (hp₁ : p ≠ identityClass n)
    (hp₂ : p ≠ transpositionClass n) :
    degree s p < degree s (transpositionClass n) := by
  sorry

theorem result : claim := by
  intro n hn s hs
  have hid := identity_degree s n hn
  have htr := transposition_degree s n hn
  have hlt := transposition_lt_identity s n hn hs
  refine ⟨hid, htr, hlt, ?_⟩
  intro p hp₁ hp₂
  exact other_degree_lt s n hn hs p hp₁ hp₂

end
end D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
