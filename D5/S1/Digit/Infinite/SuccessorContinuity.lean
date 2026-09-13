/- GID: D5/S1/Digit/Infinite/SuccessorContinuity
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/SuccessorContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first adjacent zero erasure successor is continuous on infinite legal Boolean digits. -/

import Mathlib.Data.Nat.Find
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SuccessorContinuity

open scoped Topology

/-- Infinite Boolean digit sequences with no adjacent ones, with the product subspace topology. -/
abbrev LegalDigits := {x : ℕ → Bool // ∀ j, ¬ (x j = true ∧ x (j + 1) = true)}

/-- Erase all digits below the first adjacent zero pair and put a one at its first position;
if there is no adjacent zero pair, return the zero sequence. -/
noncomputable def next (x : ℕ → Bool) : ℕ → Bool := by
  classical
  exact if h : ∃ j, x j = false ∧ x (j + 1) = false then
    let j := Nat.find h
    fun i => if i < j then false else if i = j then true else x i
  else fun _ => false

/-- The first adjacent zero erasure map is continuous on the space of infinite legal digits. -/
theorem infinite_successor_continuous : Continuous (fun x : LegalDigits => next x.val) := by
  classical
  have prefix_control (N : ℕ) (x y : ℕ → Bool)
      (agree : ∀ k < N + 1, x k = y k) :
      ∀ i < N, next x i = next y i := by
    have pairs (j : ℕ) (hj : j < N) :
        (x j = false ∧ x (j + 1) = false) ↔
        (y j = false ∧ y (j + 1) = false) := by
      rw [agree j (by omega), agree (j + 1) (by omega)]
    by_cases early : ∃ j < N, x j = false ∧ x (j + 1) = false
    · obtain ⟨j, hj, hxj⟩ := early
      have hx : ∃ k, x k = false ∧ x (k + 1) = false := ⟨j, hxj⟩
      have hy : ∃ k, y k = false ∧ y (k + 1) = false :=
        ⟨j, (pairs j hj).mp hxj⟩
      have same : Nat.find hx = Nat.find hy :=
        Nat.find_congr hxj (fun k hk => pairs k (by omega))
      intro i hi
      simp only [next, dif_pos hx, dif_pos hy]
      rw [same, agree i (by omega)]
    · have zero_prefix (z : ℕ → Bool)
          (hz : ∀ j < N, ¬ (z j = false ∧ z (j + 1) = false)) :
          ∀ i < N, next z i = false := by
        intro i hi
        unfold next
        split
        · rename_i h
          have bound : N ≤ Nat.find h := by
            by_contra hn
            exact hz (Nat.find h) (by omega) (Nat.find_spec h)
          simp only [if_pos (show i < Nat.find h by omega)]
        · rfl
      have hx : ∀ j < N, ¬ (x j = false ∧ x (j + 1) = false) := by
        intro j hj hp
        exact early ⟨j, hj, hp⟩
      have hy : ∀ j < N, ¬ (y j = false ∧ y (j + 1) = false) := by
        intro j hj hp
        exact hx j hj ((pairs j hj).mpr hp)
      intro i hi
      exact (zero_prefix x hx i hi).trans (zero_prefix y hy i hi).symm
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_of_eventually_eq
  have neighborhood : ∀ᶠ y : LegalDigits in 𝓝 x,
      ∀ j ∈ Finset.range (i + 2), y.val j = x.val j := by
    apply (Filter.eventually_all_finset _).mpr
    intro j hj
    exact ((continuous_apply j).comp continuous_subtype_val).continuousAt
      ((isOpen_discrete {x.val j}).mem_nhds (Set.mem_singleton _))
  exact neighborhood.mono fun y hy =>
    prefix_control (i + 1) y.val x.val
      (fun k hk => hy k (Finset.mem_range.mpr (by omega))) i (by omega)

end D5.S1.Digit.Infinite.SuccessorContinuity
