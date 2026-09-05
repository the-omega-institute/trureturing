/- GID: D5/S1/Digit/GoldenBase4IntervalMachine
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4IntervalMachine
   mirror-E: none(waiver:explicit-interval-automaton)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   digest: An explicit typed twenty-one-state table preserves a golden-error invariant and computes the radix-four floor difference on every legal Fibonacci-weighted word. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast

/- The existing TypedPartialDFAO and runTransition remain the machine semantics.
   fibPair below evaluates an arbitrary word using the upstream Nat.fib weights;
   it is not a second canonical Zeckendorf encoder. This file does not claim the
   M01 dense-word transport theorem or power-restricted minimality.
   Endpoint images and output strips were separately checked with exact rational
   arithmetic. Pinned Lean elaboration has not been executed in this session. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4IntervalMachine

open D5.S0.Automata.TypedPartialDFAOOverBase

/-- Value of a word and of its one-position Fibonacci shift. -/
def fibPair : List (Fin 2) → Nat × Nat
  | [] => (0, 0)
  | a :: w =>
      (a.val * Nat.fib (w.length + 2) + (fibPair w).1,
       a.val * Nat.fib (w.length + 3) + (fibPair w).2)

/-- Appending a digit obeys the two-register Fibonacci recurrence. -/
theorem fibPair_append_digit (w : List (Fin 2)) (a : Fin 2) :
    fibPair (w ++ [a]) =
      ((fibPair w).2 + a.val,
       (fibPair w).1 + (fibPair w).2 + 2 * a.val) := by
  induction w with
  | nil => simp [fibPair, Nat.fib, Nat.mul_comm]
  | cons d w ih =>
      simp only [List.cons_append, fibPair, List.length_append,
        List.length_singleton, List.length_cons, ih]
      have hf : Nat.fib (w.length + 1 + 3) =
          Nat.fib (w.length + 2) + Nat.fib (w.length + 3) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.fib_add_two (n := w.length + 2)
      rw [hf]
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> ring

/-- Error after a word, in the standard real golden coordinate. -/
noncomputable def error (w : List (Fin 2)) : Real :=
  Real.goldenRatio * (fibPair w).1 - (fibPair w).2

/-- The single-symbol affine action on that error. -/
noncomputable def errorStep (a : Fin 2) (e : Real) : Real :=
  (1 - Real.goldenRatio) * e - (a.val : Real) * (1 - Real.goldenRatio) ^ 2

/-- Arithmetic input evaluation and the affine error action agree exactly. -/
theorem error_append_digit (w : List (Fin 2)) (a : Fin 2) :
    error (w ++ [a]) = errorStep a (error w) := by
  simp only [error, fibPair_append_digit, Prod.fst, Prod.snd, errorStep]
  push_cast
  linear_combination
    (((fibPair w).1 : Real) + (a.val : Real)) * Real.goldenRatio_sq

/-- Zero successors of the fixed table. -/
def zeroTarget : Fin 21 → Fin 21 :=
  ![0,9,8,7,7,6,5,5,4,4,3,2,2,1,13,12,12,11,10,9,9]

/-- One successors; entries on the previous-one fiber are not used. -/
def oneTarget : Fin 21 → Fin 21 :=
  ![18,20,19,19,18,18,18,17,17,16,15,15,14,14,0,0,0,0,0,0,0]

/-- Four-valued Moore outputs. -/
def output : Fin 21 → Fin 4 :=
  ![0,3,3,3,3,3,0,0,0,0,0,1,1,1,1,1,2,2,2,2,3]

/-- The first fourteen states lie over previousZero. -/
def stateType (q : Fin 21) : BinaryZeckendorfState :=
  if q.val < 14 then .previousZero else .previousOne

/-- Illegal consecutive ones stay undefined. -/
def step (q : Fin 21) (a : Fin 2) : Option (Fin 21) :=
  if a = 0 then some (zeroTarget q)
  else if q.val < 14 then some (oneTarget q) else none

/-- The candidate is an instance of the existing typed partial DFAO. -/
def machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 21) where
  start := 0
  stateType := stateType
  step := step
  output := output
  start_type := rfl
  step_type := by
    decide

/-- Endpoints are encoded as (a + b*phi)/4. -/
noncomputable def point (p : Int × Int) : Real :=
  ((p.1 : Real) + (p.2 : Real) * Real.goldenRatio) / 4

/-- Lower endpoints; state zero is the singleton {0}. -/
def lowerPair : Fin 21 → Int × Int :=
  ![(0,0),(12,-8),(4,-3),(1,-1),(6,-4),(3,-2),(0,0),
    (5,-3),(2,-1),(7,-4),(4,-2),(1,0),(6,-3),(3,-1),
    (4,-4),(1,-2),(-2,0),(3,-3),(0,-1),(2,-2),(-1,0)]

/-- Upper endpoints. -/
def upperPair : Fin 21 → Int × Int :=
  ![(0,0),(4,-3),(1,-1),(6,-4),(3,-2),(0,0),(5,-3),
    (2,-1),(7,-4),(4,-2),(1,0),(6,-3),(3,-1),(8,-4),
    (1,-2),(-2,0),(3,-3),(0,-1),(2,-2),(-1,0),(12,-8)]

/-- The error invariant of a state. All noninitial cells are open intervals. -/
def Cell (q : Fin 21) (e : Real) : Prop :=
  if q = 0 then e = 0 else point (lowerPair q) < e ∧ e < point (upperPair q)

private theorem phi_bounds :
    (8 / 5 : Real) < Real.goldenRatio ∧ Real.goldenRatio < (13 / 8 : Real) := by
  have hs := Real.goldenRatio_sq
  have hp := Real.one_lt_goldenRatio
  constructor
  · by_contra h
    have h1 : 0 ≤ (8 / 5 : Real) - Real.goldenRatio := by linarith
    have h2 : 0 ≤ Real.goldenRatio + (8 / 5 : Real) - 1 := by linarith
    nlinarith [mul_nonneg h1 h2]
  · by_contra h
    have h1 : 0 ≤ Real.goldenRatio - (13 / 8 : Real) := by linarith
    have h2 : 0 ≤ Real.goldenRatio + (13 / 8 : Real) - 1 := by linarith
    nlinarith [mul_nonneg h1 h2]

private theorem errorStep_strictAnti (a : Fin 2) {x y : Real} (h : x < y) :
    errorStep a y < errorStep a x := by
  have hn : 1 - Real.goldenRatio < 0 := by linarith [Real.one_lt_goldenRatio]
  exact sub_lt_sub_right (mul_lt_mul_of_neg_left h hn) _

/-- The finite table sends entire source intervals into destination intervals. -/
theorem endpoint_certificate (q : Fin 21) (a : Fin 2) (t : Fin 21)
    (h : step q a = some t) (hq : q ≠ 0) :
    t ≠ 0 ∧
      point (lowerPair t) ≤ errorStep a (point (upperPair q)) ∧
      errorStep a (point (lowerPair q)) ≤ point (upperPair t) := by
  obtain ⟨hl, hu⟩ := phi_bounds
  have hs := Real.goldenRatio_sq
  fin_cases q <;> fin_cases a <;>
    norm_num [step, zeroTarget, oneTarget] at h hq
  all_goals subst t
  all_goals
    norm_num [lowerPair, upperPair, point, errorStep]
    first
    | constructor <;> nlinarith only [hl, hu, hs]
    | nlinarith only [hl, hu, hs]

/-- A defined transition preserves the error invariant, including the zero point. -/
theorem step_preserves_cell {q t : Fin 21} {a : Fin 2} {e : Real}
    (h : step q a = some t) (he : Cell q e) : Cell t (errorStep a e) := by
  by_cases hq : q = 0
  · subst q
    have he0 : e = 0 := by simpa [Cell] using he
    subst e
    obtain ⟨hl, hu⟩ := phi_bounds
    have hs := Real.goldenRatio_sq
    fin_cases a <;> norm_num [step, zeroTarget, oneTarget] at h
    all_goals subst t
    · simp [Cell, errorStep]
    · norm_num [Cell, point, lowerPair, upperPair, errorStep]
      constructor <;> nlinarith only [hl, hu, hs]
  · obtain ⟨ht, hlo, hhi⟩ := endpoint_certificate q a t h hq
    obtain ⟨he1, he2⟩ := (show point (lowerPair q) < e ∧
      e < point (upperPair q) from by simpa [Cell, hq] using he)
    simp only [Cell, if_neg ht]
    exact ⟨lt_of_le_of_lt hlo (errorStep_strictAnti a he2),
      lt_of_lt_of_le (errorStep_strictAnti a he1) hhi⟩

/-- Integer strip containing the error at each state. -/
def strip : Fin 21 → Int :=
  ![0,-1,-1,-1,-1,-1,0,0,0,0,0,0,0,0,-1,-1,-1,-1,-1,-1,-1]

/-- Each whole state cell lies in its assigned radix-four output strip. -/
theorem cell_output_strip {q : Fin 21} {e : Real} (he : Cell q e) :
    (strip q : Real) + ((output q).val : Real) / 4 ≤ e ∧
      e < (strip q : Real) + (((output q).val : Real) + 1) / 4 := by
  obtain ⟨hl, hu⟩ := phi_bounds
  fin_cases q <;>
    norm_num [Cell, point, lowerPair, upperPair, strip, output] at he ⊢
  all_goals constructor <;> linarith

/-- State membership gives both integer floors, without fractional-part approximation. -/
theorem cell_floor_values {q : Fin 21} {e : Real} (he : Cell q e) :
    ⌊e⌋ = strip q ∧ ⌊4 * e⌋ = 4 * strip q + ((output q).val : Int) := by
  obtain ⟨hlo, hhi⟩ := cell_output_strip he
  have hd0 : (0 : Real) ≤ (output q).val := Nat.cast_nonneg _
  have hd3 : ((output q).val : Real) ≤ 3 := by
    have h : (output q).val ≤ 3 := Nat.le_of_lt_succ (output q).isLt
    exact_mod_cast h
  constructor
  · apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

/-- The invariant directly determines the floor difference for the represented integer. -/
theorem cell_digit (q : Fin 21) (v z : Nat)
    (he : Cell q (Real.goldenRatio * v - z)) :
    ⌊4 * (Real.goldenRatio * v)⌋ - 4 * ⌊Real.goldenRatio * v⌋ =
      ((output q).val : Int) := by
  obtain ⟨hl, hu⟩ := cell_output_strip he
  have hd0 : (0 : Real) ≤ (output q).val := Nat.cast_nonneg _
  have hd3 : ((output q).val : Real) ≤ 3 := by
    have h : (output q).val ≤ 3 := Nat.le_of_lt_succ (output q).isLt
    exact_mod_cast h
  have f1 : ⌊Real.goldenRatio * v⌋ = (z : Int) + strip q := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have f4 : ⌊4 * (Real.goldenRatio * v)⌋ =
      4 * ((z : Int) + strip q) + ((output q).val : Int) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  rw [f1, f4]
  ring

/-- The zero start state satisfies the invariant before any input is read. -/
theorem initial_cell : Cell 0 (error []) := by simp [Cell, error, fibPair]

/-- The invariant follows every successful run in the existing run semantics. -/
theorem runFrom_cell (word : List (Fin 2)) (prefix : List (Fin 2))
    (q t : Fin 21) (hq : Cell q (error prefix))
    (hr : machine.runFrom q word = some t) : Cell t (error (prefix ++ word)) := by
  induction word generalizing prefix q with
  | nil =>
      have hqt : q = t := by simpa [TypedPartialDFAO.runFrom, runTransition] using hr
      subst t
      simpa using hq
  | cons a word ih =>
      cases hs : step q a with
      | none => simp [TypedPartialDFAO.runFrom, runTransition, machine, hs] at hr
      | some m =>
          have hm : Cell m (error (prefix ++ [a])) := by
            rw [error_append_digit]
            exact step_preserves_cell hs hq
          have ht : machine.runFrom m word = some t := by
            simpa [TypedPartialDFAO.runFrom, runTransition, machine, hs] using hr
          simpa [List.append_assoc] using ih (prefix ++ [a]) m hm ht

/-- Every successful input returns the exact radix-four floor difference of its
Fibonacci-weighted value. No finite test extent occurs in this statement. -/
theorem successful_run_digit (word : List (Fin 2)) (q : Fin 21)
    (hr : machine.run word = some q) :
    ⌊4 * (Real.goldenRatio * (fibPair word).1)⌋ -
      4 * ⌊Real.goldenRatio * (fibPair word).1⌋ = ((output q).val : Int) := by
  have hc : Cell q (error word) := by
    simpa using runFrom_cell word [] 0 q initial_cell hr
  exact cell_digit q (fibPair word).1 (fibPair word).2 hc

/-- The table defines every transition permitted by its base type. -/
theorem legal_step_exists (q : Fin 21) (a : Fin 2) (b : BinaryZeckendorfState)
    (hb : binaryZeckendorfBase.step (stateType q) a = some b) :
    ∃ t, step q a = some t := by
  fin_cases q <;> fin_cases a <;>
    simp_all [binaryZeckendorfBase, stateType, step]

/-- Every legal base run has a successful run of the twenty-one-state machine. -/
theorem legal_run_exists (word : List (Fin 2)) (q : Fin 21)
    (b : BinaryZeckendorfState)
    (hb : binaryZeckendorfBase.evalFrom (stateType q) word = some b) :
    ∃ t, machine.runFrom q word = some t := by
  induction word generalizing q with
  | nil => exact ⟨q, rfl⟩
  | cons a word ih =>
      cases hs : binaryZeckendorfBase.step (stateType q) a with
      | none => simp [PartialDFA.evalFrom, runTransition, hs] at hb
      | some c =>
          obtain ⟨t, ht⟩ := legal_step_exists q a c hs
          have htType : stateType t = c := by
            have typed := machine.step_type ht
            rw [hs] at typed
            exact (Option.some.inj typed).symm
          have hbTail : binaryZeckendorfBase.evalFrom (stateType t) word = some b := by
            rw [htType]
            simpa [PartialDFA.evalFrom, runTransition, hs] using hb
          obtain ⟨u, hu⟩ := ih t hbTail
          refine ⟨u, ?_⟩
          simpa [TypedPartialDFAO.runFrom, runTransition, machine, ht] using hu

/-- Explicit global-input correctness with the original typed base and standard
Fibonacci weights. This is an upper construction, not a sparse minimality theorem. -/
theorem every_legal_word_correct (word : List (Fin 2)) (b : BinaryZeckendorfState)
    (hb : binaryZeckendorfBase.eval word = some b) :
    ∃ q : Fin 21, machine.run word = some q ∧
      ⌊4 * (Real.goldenRatio * (fibPair word).1)⌋ -
        4 * ⌊Real.goldenRatio * (fibPair word).1⌋ = ((output q).val : Int) := by
  obtain ⟨q, hq⟩ := legal_run_exists word 0 b hb
  exact ⟨q, hq, successful_run_digit word q hq⟩

/-- Leading zeroes are handled by the already-proved upstream theorem. -/
theorem leading_zero_invariant (n : Nat) (w : List (Fin 2)) :
    machine.evalOutput (List.replicate n 0 ++ w) = machine.evalOutput w :=
  machine.leading_zero_invariant 0 rfl n w

#print axioms error_append_digit
#print axioms step_preserves_cell
#print axioms every_legal_word_correct

end D5.S1.Digit.GoldenBase4IntervalMachine
