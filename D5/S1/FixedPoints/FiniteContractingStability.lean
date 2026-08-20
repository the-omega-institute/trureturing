/- GID: D5/S1/FixedPoints/FiniteContractingStability
   generality: G
   mirror-B: D5/B/S1/FixedPoints/FiniteContractingStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite contracting set updates stabilize with a sharp strict-change bound. -/

import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Monotone.Basic

/- Library-search audit trail (2026-08-20):
   * Repository searches found no generic theorem giving both eventual stability
     and the strict-change count for contracting updates of finite sets.
   * Pinned Mathlib provides the exact cardinal-sequence stabilization theorem
     `Nat.stabilises_of_antitone` in `Mathlib.Order.Monotone.Basic`; the proof
     below applies it directly and then transfers equal cardinalities back to
     equal sets. -/

namespace D5.S1.FixedPoints.FiniteContractingStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A set update which only deletes states stabilizes on a finite state type,
and the number of strict updates is bounded by the initial number of states. -/
theorem finite_contracting_updates_stabilize
    {X : Type*} [Finite X]
    (U : Set X → Set X) (hU : ∀ A : Set X, U A ⊆ A)
    (S : ℕ → Set X) (hS : ∀ n : ℕ, S (n + 1) = U (S n)) :
    (∃ N ≤ (S 0).ncard, ∀ n : ℕ, N ≤ n → S n = S N) ∧
      {n : ℕ | S (n + 1) ≠ S n}.ncard ≤ (S 0).ncard := by
  have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
    rw [hS n]
    exact hU (S n)
  have hanti : Antitone S := antitone_nat_of_succ_le hstep
  have hcardAnti : Antitone (fun n : ℕ => (S n).ncard) :=
    fun _ _ hmn => Set.ncard_mono (hanti hmn)
  have hcardStep : ∀ n : ℕ, (S n).ncard = (S (n + 1)).ncard →
      (S (n + 1)).ncard = (S (n + 2)).ncard := by
    intro n hcard
    have hset : S (n + 1) = S n :=
      Set.eq_of_subset_of_ncard_le (hstep n) hcard.le
    have hnext : S (n + 2) = S (n + 1) := by
      calc
        S (n + 2) = U (S (n + 1)) := hS (n + 1)
        _ = U (S n) := congrArg U hset
        _ = S (n + 1) := (hS n).symm
    exact congrArg Set.ncard hnext.symm
  obtain ⟨N, hN, hcardStable⟩ :=
    Nat.stabilises_of_antitone hcardAnti hcardStep
  have hstable (n : ℕ) (hn : N ≤ n) : S n = S N := by
    apply Set.eq_of_subset_of_ncard_le (hanti hn)
    exact (hcardStable n hn).symm.le
  refine ⟨⟨N, hN, hstable⟩, ?_⟩
  have hchanges : {n : ℕ | S (n + 1) ≠ S n} ⊆ Set.Iio N := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Iio]
    by_contra hnot
    have hnN : N ≤ n := Nat.le_of_not_gt hnot
    have hsuccN : N ≤ n + 1 := hnN.trans (Nat.le_succ n)
    exact hn ((hstable (n + 1) hsuccN).trans (hstable n hnN).symm)
  exact (Set.ncard_le_ncard hchanges (Set.finite_Iio N)).trans
    ((Set.ncard_Iio_nat N).le.trans hN)

example :
    (∃ N ≤ ({0, 1} : Set (Fin 3)).ncard,
      ∀ n : ℕ, N ≤ n → (Nat.rec {0, 1} (fun _ _ => {0}) n : Set (Fin 3)) =
        Nat.rec {0, 1} (fun _ _ => {0}) N) ∧
      {n : ℕ |
        (Nat.rec {0, 1} (fun _ _ => {0}) (n + 1) : Set (Fin 3)) ≠
          Nat.rec {0, 1} (fun _ _ => {0}) n}.ncard ≤ ({0, 1} : Set (Fin 3)).ncard := by
  let U : Set (Fin 3) → Set (Fin 3) := fun A => A ∩ {0}
  let S : ℕ → Set (Fin 3) := fun n => Nat.rec {0, 1} (fun _ _ => {0}) n
  apply finite_contracting_updates_stabilize U (fun A => Set.inter_subset_left) S
  intro n
  cases n <;> ext x <;> simp [U, S]

#print axioms finite_contracting_updates_stabilize

end D5.S1.FixedPoints.FiniteContractingStability
