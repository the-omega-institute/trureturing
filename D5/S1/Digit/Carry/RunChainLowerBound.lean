/- GID: D5/S1/Digit/Carry/RunChainLowerBound
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/RunChainLowerBound
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Parity]
   utility: none
   digest: Consecutive unit digits admit carry chains of exactly floor(length squared / 4) steps. -/

import D5.S1.Digit.Carry.Successor
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S1.Digit

open Carry.Successor
open scoped BigOperators

theorem exists_carrySteps_consecutive_run (a L : ℕ) :
    ∃ t, Carry.Successor.CarrySteps (L * L / 4)
      (∑ k ∈ Finset.range L, Finsupp.single (a + k) 1) t := by
  let run : ℕ → ℕ → RawDigits :=
    fun b n => ∑ k ∈ Finset.range n, Finsupp.single (b + k) 1
  have run_succ : ∀ b n : ℕ,
      run b (n + 1) = run b n + Finsupp.single (b + n) 1 := by
    intro b n
    simp only [run, Finset.sum_range_succ]
  have carrySteps_add_right : ∀ {k : ℕ} {r s u : RawDigits},
      Carry.Successor.CarrySteps k r s → Carry.Successor.CarrySteps k (r + u) (s + u) := by
    intro k r s u h
    induction h with
    | zero => exact .zero _
    | succ chain step ih =>
        apply CarrySteps.succ ih
        cases step with
        | adjacent rest i =>
            simpa only [add_assoc, add_left_comm, add_comm] using
              CarryStep.adjacent (rest + u) i
        | double_zero rest =>
            simpa only [add_assoc, add_left_comm, add_comm] using
              CarryStep.double_zero (rest + u)
        | double_one rest =>
            simpa only [add_assoc, add_left_comm, add_comm] using
              CarryStep.double_one (rest + u)
        | double_succ rest i =>
            simpa only [add_assoc, add_left_comm, add_comm] using
              CarryStep.double_succ (rest + u) i
  have carrySteps_trans : ∀ {k m : ℕ} {r s t : RawDigits},
      CarrySteps k r s → CarrySteps m s t → CarrySteps (k + m) r t := by
    intro k m r s t h g
    induction g with
    | zero => simpa using h
    | succ chain step ih => simpa only [Nat.add_assoc] using CarrySteps.succ (ih h) step
  have run_block : ∀ b n : ℕ,
      CarrySteps (n + 1) (run b (n + 2))
        (run b n + Finsupp.single (b + n + 2) 1) := by
    intro b n
    induction n with
    | zero =>
        simpa [run, Finset.sum_range_succ] using
          (CarrySteps.succ (CarrySteps.zero _) (CarryStep.adjacent 0 b))
    | succ n ih =>
        have chain := carrySteps_add_right (u := Finsupp.single (b + n + 2) 1) ih
        have step : CarryStep
            (run b n + Finsupp.single (b + n + 2) 1 +
              Finsupp.single (b + n + 2) 1)
            (run b (n + 1) + Finsupp.single (b + (n + 1) + 2) 1) := by
          simpa only [run_succ, add_assoc, ← Finsupp.single_add] using
            CarryStep.double_succ (run b n) (b + n)
        simpa only [run_succ, Nat.add_assoc] using CarrySteps.succ chain step
  have run_count : ∀ n : ℕ,
      n + 1 + n * n / 4 = (n + 2) * (n + 2) / 4 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [show (2 * m) * (2 * m) = 4 * (m * m) by ring,
        show (2 * m + 2) * (2 * m + 2) = 4 * (m * m + 2 * m + 1) by ring]
      omega
    · rw [show (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 by ring,
        show (2 * m + 1 + 2) * (2 * m + 1 + 2) = 4 * (m * m + 3 * m + 2) + 1 by ring]
      omega
  induction L using Nat.strong_induction_on with
  | h L ih =>
      rcases L with _ | (_ | n)
      · exact ⟨run a 0, CarrySteps.zero _⟩
      · exact ⟨run a 1, CarrySteps.zero _⟩
      · obtain ⟨t, ht⟩ := ih n (by omega)
        refine ⟨t + Finsupp.single (a + n + 2) 1, ?_⟩
        have chain := carrySteps_trans (run_block a n)
          (carrySteps_add_right (u := Finsupp.single (a + n + 2) 1) ht)
        simpa only [run_count] using chain

#print axioms exists_carrySteps_consecutive_run

end D5.S1.Digit
