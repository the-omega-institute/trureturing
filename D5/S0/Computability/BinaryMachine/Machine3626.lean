/- GID: D5/S0/Computability/BinaryMachine/Machine3626
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Machine3626
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Basic]
   utility: none
   digest: One-sided machine 3626 restores a zero block and crosses its right boundary in exact time. -/

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Omega

set_option autoImplicit false

namespace D5.S0.Computability.BinaryMachine.Machine3626

inductive State
  | A | B
  deriving DecidableEq

/-- The left list starts at the scanned cell; absent cells are blank zero.
The right list ends at the fixed right boundary. Both lists have unbounded length. -/
structure Cfg where
  state : State
  left : List Bool
  right : List Bool

/-- Write at the current cell and move one cell right; crossing the boundary halts. -/
def exitRight (writtenLeft right : List Bool) : Option Cfg :=
  match right with
  | [] => none
  | b :: rest => some ⟨.B, b :: writtenLeft, rest⟩

/-- Each application is one simultaneous read/write/state-change/move transition.
The two empty-left cases read an implicit blank cell on the infinite half-tape. -/
def step : Cfg → Option Cfg
  | ⟨.A, [], right⟩ => some ⟨.A, [], false :: right⟩
  | ⟨.A, false :: left, right⟩ => some ⟨.A, left, false :: right⟩
  | ⟨.A, true :: left, right⟩ => exitRight (true :: left) right
  | ⟨.B, [], right⟩ => some ⟨.A, [], true :: right⟩
  | ⟨.B, false :: left, right⟩ => some ⟨.A, left, true :: right⟩
  | ⟨.B, true :: left, right⟩ => exitRight (false :: left) right

/-- A trace may stop at its current configuration or at the first boundary crossing.
There is no constructor that continues after a crossing; the crossing counts one step. -/
inductive Trace : ℕ → Cfg → Option Cfg → Prop
  | zero (c : Cfg) : Trace 0 c (some c)
  | cons {t : ℕ} {c d : Cfg} {result : Option Cfg}
      (transition : step c = some d) (rest : Trace t d result) :
      Trace (t + 1) c result
  | crossing {c : Cfg} (transition : step c = none) : Trace 1 c none

private theorem trace_trans {s t : ℕ} {c d : Cfg} {result : Option Cfg}
    (h : Trace s c (some d)) (j : Trace t d result) : Trace (s + t) c result := by
  induction h with
  | zero => simpa using j
  | cons transition rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons transition ih

/-- A zero block followed by its first one and arbitrary higher cells. -/
def block (k : ℕ) (higher : List Bool) : List Bool :=
  List.replicate k false ++ true :: higher

private def blockTime : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * blockTime k + 3

private theorem block_trace (k : ℕ) (higher right : List Bool) :
    Trace (blockTime k) ⟨.A, block k higher, right⟩
      (exitRight (block k higher) right) := by
  induction k generalizing right with
  | zero =>
    cases right with
    | nil => exact Trace.crossing rfl
    | cons b rest => exact Trace.cons rfl (Trace.zero _)
  | succ k ih =>
    have hleft : Trace (blockTime k) ⟨.A, block k higher, false :: right⟩
        (some ⟨.B, false :: block k higher, right⟩) := by
      simpa [exitRight] using ih (false :: right)
    have hright : Trace (blockTime k) ⟨.A, block k higher, true :: right⟩
        (some ⟨.B, true :: block k higher, right⟩) := by
      simpa [exitRight] using ih (true :: right)
    have hlast : Trace 1 ⟨.B, true :: block k higher, right⟩
        (exitRight (false :: block k higher) right) := by
      cases right with
      | nil => exact Trace.crossing rfl
      | cons b rest => exact Trace.cons rfl (Trace.zero _)
    have hmiddle := trace_trans hleft
      (Trace.cons (by rfl) (trace_trans hright hlast))
    have hfull := Trace.cons (c := ⟨.A, false :: block k higher, right⟩)
      (by rfl) hmiddle
    convert hfull using 1 <;>
      simp [blockTime, block, List.replicate_succ] <;> omega

/-- Every zero block followed by one crosses the actual right boundary for the first time
in exactly the stated number of transitions, independently of all higher cells. -/
theorem block_first_crossing (k : ℕ) (higher : List Bool) :
    Trace (4 * 2 ^ k - 3) ⟨.A, block k higher, []⟩ none := by
  have htime : ∀ j, blockTime j + 3 = 4 * 2 ^ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp only [blockTime, pow_succ]; omega
  have ht : blockTime k = 4 * 2 ^ k - 3 := by have := htime k; omega
  simpa only [ht, exitRight] using block_trace k higher []

#print axioms block_first_crossing

end D5.S0.Computability.BinaryMachine.Machine3626
