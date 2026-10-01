/- GID: D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A seam-preserving atomic action restores the complete modular state capacity. -/

import D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
import D5.S0.Automata.DFAOStateLowerBound
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
open D5.S0.Automata.DFAOStateLowerBound

inductive Action
  | window (b : Window)
  | mu
  deriving DecidableEq

instance : Fintype Action where
  elems := {.window .zero, .window .low, .window .middle, .window .ends,
    .window .high, .mu}
  complete a := by
    cases a with
    | window b => cases b <;> simp
    | mu => simp

def atomicTransition {m : ℕ} : RawState m → Action → RawState m
  | q, .window b => rawTransition q b
  | none, .mu => none
  | some (s, x), .mu => some (s, step x)

def atomicMachine (m : ℕ) : DFAO Action (Option (ZMod m)) (RawState m) where
  step := atomicTransition
  start := some (false, (0, 0))
  accept := ∅
  output := rawOutput

def atomicTask (m : ℕ) (w : List Action) : Option (ZMod m) :=
  (atomicMachine m).evalOutput w

def capacity (m : ℕ) : ℕ := 2 * m ^ 2 + 1

/- The added action keeps the seam and applies one Fibonacci matrix step. -/
theorem result (m : ℕ) (hm : 2 ≤ m) :
    Finite (RawState m) ∧
    Nat.card (RawState m) = capacity m ∧
    (∃ machine : DFAO Action (Option (ZMod m)) (RawState m),
      machine.CorrectOn Set.univ (atomicTask m) ∧
      ∀ q : RawState m, ∃ w : List Action, machine.toDFA.eval w = q) ∧
    (∀ (State : Type) [Fintype State]
      (machine : DFAO Action (Option (ZMod m)) State),
      machine.CorrectOn Set.univ (atomicTask m) → capacity m ≤ Fintype.card State) := by
  classical
  let : NeZero m := ⟨by omega⟩
  have eval_lift_from (q : RawState m) (w : List Window) :
      (atomicMachine m).toDFA.evalFrom q (w.map Action.window) =
        (rawMachine m).toDFA.evalFrom q w := by
    simpa [DFA.evalFrom, DFA.comap, atomicMachine, rawMachine, atomicTransition] using
      ((atomicMachine m).toDFA.evalFrom_comap Action.window q w).symm
  have eval_lift (w : List Window) :
      (atomicMachine m).toDFA.eval (w.map Action.window) =
        (rawMachine m).toDFA.eval w := by
    exact eval_lift_from _ w
  have reachable (q : RawState m) :
      ∃ w : List Action, (atomicMachine m).toDFA.eval w = q := by
    obtain ⟨w, hw⟩ := raw_reachable m q
    exact ⟨w.map Action.window, by rw [eval_lift, hw]⟩
  have hcard : Nat.card (RawState m) = capacity m := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_prod,
      Fintype.card_bool, ZMod.card]
    unfold capacity
    ring
  have correct : (atomicMachine m).CorrectOn Set.univ (atomicTask m) := by
    intro w _
    rfl
  have observation_onto : Function.Surjective
      (GraftAffineClosure.observe (A := ZMod m)) := by
    rcases GraftAffineClosure.result.2 m (by omega) (0, 0) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, inverse, _⟩
    intro z
    exact ⟨(5 * z.1 - 3 * z.2, -3 * z.1 + 2 * z.2), inverse z⟩
  have observation_injective := Finite.injective_iff_surjective.mpr observation_onto
  have distinguish (q r : RawState m) (hne : q ≠ r) :
      ∃ w : List Action,
        rawOutput ((atomicMachine m).toDFA.evalFrom q w) ≠
          rawOutput ((atomicMachine m).toDFA.evalFrom r w) := by
    cases q with
    | none =>
      cases r with
      | none => exact (hne rfl).elim
      | some r => exact ⟨[], by simp [atomicMachine, rawOutput]⟩
    | some q =>
      cases r with
      | none => exact ⟨[], by simp [atomicMachine, rawOutput]⟩
      | some r =>
        rcases q with ⟨s, x⟩
        rcases r with ⟨t, y⟩
        by_cases h0 : quantity x = quantity y
        · by_cases h1 : quantity (step x) = quantity (step y)
          · have hxy : x = y := observation_injective (Prod.ext h0 h1)
            have hst : s ≠ t := by
              intro hst
              apply hne
              simp [hst, hxy]
            refine ⟨[.window .high], ?_⟩
            cases s <;> cases t <;>
              simp [atomicMachine, atomicTransition,
                rawTransition, rawOutput, first, last, hxy] at hst ⊢
          · exact ⟨[.mu], by
              simpa [atomicMachine, atomicTransition, rawOutput,
                step, quantity] using h1⟩
        · exact ⟨[], by
            simpa [atomicMachine, rawOutput] using h0⟩
  let history (q : RawState m) := Classical.choose (reachable q)
  have hp (q : RawState m) :
      (atomicMachine m).toDFA.eval (history q) = q :=
    Classical.choose_spec (reachable q)
  have sep (q r : RawState m) : ∃ w : List Action, q ≠ r →
      rawOutput ((atomicMachine m).toDFA.evalFrom q w) ≠
        rawOutput ((atomicMachine m).toDFA.evalFrom r w) := by
    by_cases h : q = r
    · exact ⟨[], fun hn => (hn h).elim⟩
    · obtain ⟨w, hw⟩ := distinguish q r h
      exact ⟨w, fun _ => hw⟩
  have history_output (q : RawState m) (w : List Action) :
      atomicTask m (history q ++ w) =
        rawOutput ((atomicMachine m).toDFA.evalFrom q w) := by
    rw [← correct (Set.mem_univ _)]
    change rawOutput ((atomicMachine m).toDFA.evalFrom _ (history q ++ w)) = _
    rw [DFA.evalFrom_of_append]
    change rawOutput ((atomicMachine m).toDFA.evalFrom
      ((atomicMachine m).toDFA.eval (history q)) w) = _
    rw [hp]
  let certificate : DistinguishingFamily Set.univ (atomicTask m) (RawState m) := {
    witnessPrefix := history
    continuation q r := Classical.choose (sep q r)
    left_mem := by intro q r _; exact Set.mem_univ _
    right_mem := by intro q r _; exact Set.mem_univ _
    target_ne := by
      intro q r hne
      rw [history_output, history_output]
      exact Classical.choose_spec (sep q r) hne
  }
  refine ⟨inferInstance, hcard, ⟨atomicMachine m, correct, reachable⟩, ?_⟩
  intro State _ machine hmachine
  rw [← hcard, Nat.card_eq_fintype_card]
  exact state_lower_bound_of_distinguishing_family machine Set.univ (atomicTask m)
    certificate hmachine

end D5.S3.Arith.FibonacciAtomic.AtomicActionStateCapacity
