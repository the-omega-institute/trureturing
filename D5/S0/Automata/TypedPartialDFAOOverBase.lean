/- GID: D5/S0/Automata/TypedPartialDFAOOverBase
   generality: G
   mirror-B: D5/B/S0/Automata/TypedPartialDFAOOverBase
   mirror-E: none(waiver:proof-carrying-partial-automata)
   anchors: [mathlib/module/Mathlib.Computability.DFA]
   digest: Typed partial DFAOs preserve an underlying numeration automaton and separate global correctness from finite-prefix fitting. -/

import D5.S0.Automata.DFAOStateLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TypedPartialDFAOOverBase

universe u v w x

/-- A deterministic transition system in which illegal symbols may have no successor. -/
structure PartialDFA (Alphabet : Type u) (State : Type v) where
  start : State
  step : State → Alphabet → Option State

/-- Run a partial transition table from an explicitly supplied state. -/
def runTransition {Alphabet : Type u} {State : Type v}
    (step : State → Alphabet → Option State) :
    State → List Alphabet → Option State
  | state, [] => some state
  | state, symbol :: word =>
      match step state symbol with
      | none => none
      | some next => runTransition step next word

namespace PartialDFA

/-- Run a word from a chosen base-automaton state. -/
def evalFrom {Alphabet : Type u} {State : Type v}
    (base : PartialDFA Alphabet State) (state : State)
    (word : List Alphabet) : Option State :=
  runTransition base.step state word

/-- Run a word from the base start state. -/
def eval {Alphabet : Type u} {State : Type v}
    (base : PartialDFA Alphabet State) (word : List Alphabet) : Option State :=
  base.evalFrom base.start word

/-- Partial runs compose by `Option.bind` across word concatenation. -/
theorem evalFrom_append {Alphabet : Type u} {State : Type v}
    (base : PartialDFA Alphabet State) (state : State)
    (left right : List Alphabet) :
    base.evalFrom state (left ++ right) =
      (base.evalFrom state left).bind
        (fun reached => base.evalFrom reached right) := by
  induction left generalizing state with
  | nil => rfl
  | cons symbol left ih =>
      simp only [List.cons_append, evalFrom, runTransition]
      cases hstep : base.step state symbol with
      | none => rfl
      | some next =>
          simpa [evalFrom, runTransition, hstep] using ih next

end PartialDFA

/-- A partial DFAO whose states are typed by states of an underlying
numeration automaton. Every defined transition must project to a legal base
transition. -/
structure TypedPartialDFAO
    {Alphabet : Type u} {BaseState : Type v}
    (base : PartialDFA Alphabet BaseState)
    (Output : Type w) (State : Type x) where
  start : State
  stateType : State → BaseState
  step : State → Alphabet → Option State
  output : State → Output
  start_type : stateType start = base.start
  step_type :
    ∀ ⦃state symbol next⦄,
      step state symbol = some next →
        base.step (stateType state) symbol = some (stateType next)

namespace TypedPartialDFAO

/-- Run a typed partial DFAO from a selected state. -/
def runFrom {Alphabet : Type u} {BaseState : Type v}
    {Output : Type w} {State : Type x}
    {base : PartialDFA Alphabet BaseState}
    (machine : TypedPartialDFAO base Output State)
    (state : State) (word : List Alphabet) : Option State :=
  runTransition machine.step state word

/-- Run from the machine start state. -/
def run {Alphabet : Type u} {BaseState : Type v}
    {Output : Type w} {State : Type x}
    {base : PartialDFA Alphabet BaseState}
    (machine : TypedPartialDFAO base Output State)
    (word : List Alphabet) : Option State :=
  machine.runFrom machine.start word

/-- Read the output when the partial run is defined. -/
def evalOutput {Alphabet : Type u} {BaseState : Type v}
    {Output : Type w} {State : Type x}
    {base : PartialDFA Alphabet BaseState}
    (machine : TypedPartialDFAO base Output State)
    (word : List Alphabet) : Option Output :=
  (machine.run word).map machine.output

/-- Typed partial runs compose across concatenation. -/
theorem runFrom_append {Alphabet : Type u} {BaseState : Type v}
    {Output : Type w} {State : Type x}
    {base : PartialDFA Alphabet BaseState}
    (machine : TypedPartialDFAO base Output State)
    (state : State) (left right : List Alphabet) :
    machine.runFrom state (left ++ right) =
      (machine.runFrom state left).bind
        (fun reached => machine.runFrom reached right) := by
  exact PartialDFA.evalFrom_append
    { start := state, step := machine.step } state left right

/-- Every defined machine run projects to the corresponding legal run of the
underlying numeration automaton. -/
theorem runFrom_type {Alphabet : Type u} {BaseState : Type v}
    {Output : Type w} {State : Type x}
    {base : PartialDFA Alphabet BaseState}
    (machine : TypedPartialDFAO base Output State)
    {state next : State} {word : List Alphabet}
    (defined : machine.runFrom state word = some next) :
    base.evalFrom (machine.stateType state) word =
      some (machine.stateType next) := by
  induction word generalizing state with
  | nil =>
      simp [runFrom, runTransition] at defined ⊢
      subst next
      rfl
  | cons symbol word ih =>
      simp only [runFrom, runTransition] at defined
      cases hstep : machine.step state symbol with
      | none =>
          simp [hstep] at defined
      | some middle =>
          have htail : machine.runFrom middle word = some next := by
            simpa [runFrom, runTransition, hstep] using defined
          have hbase := machine.step_type hstep
          have hrec := ih htail
          simp only [PartialDFA.evalFrom, runTransition, hbase]
          simpa [PartialDFA.evalFrom] using hrec

/-- A typed machine ignores an arbitrary finite zero prefix when its start
state has a zero self-loop. -/
theorem leading_zero_invariant {Alphabet : Type u} {BaseState : Type v}
    {Output : Type w} {State : Type x}
    {base : PartialDFA Alphabet BaseState}
    (machine : TypedPartialDFAO base Output State)
    (zero : Alphabet)
    (zeroLoop : machine.step machine.start zero = some machine.start)
    (count : Nat) (word : List Alphabet) :
    machine.evalOutput (List.replicate count zero ++ word) =
      machine.evalOutput word := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hstep :
          machine.evalOutput
              (zero :: (List.replicate count zero ++ word)) =
            machine.evalOutput (List.replicate count zero ++ word) := by
        simp [evalOutput, run, runFrom, runTransition, zeroLoop]
      calc machine.evalOutput (List.replicate (count + 1) zero ++ word)
          = machine.evalOutput
              (zero :: (List.replicate count zero ++ word)) := by
            simp [List.replicate_succ]
        _ = machine.evalOutput (List.replicate count zero ++ word) := hstep
        _ = machine.evalOutput word := ih

end TypedPartialDFAO

/-- A sparse output problem supplies one legal-input address and one desired
output for every natural index. -/
structure SparseProblem
    (Alphabet : Type u) (Output : Type w) (BaseState : Type v) where
  base : PartialDFA Alphabet BaseState
  input : Nat → List Alphabet
  target : Nat → Output

namespace SparseProblem

/-- Correctness on the entire sparse sequence. -/
def Correct {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    {State : Type x}
    (machine : TypedPartialDFAO problem.base Output State) : Prop :=
  ∀ index, machine.evalOutput (problem.input index) =
    some (problem.target index)

/-- Correctness on the first `extent` sparse addresses. -/
def FitsPrefix {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    (extent : Nat) {State : Type x}
    (machine : TypedPartialDFAO problem.base Output State) : Prop :=
  ∀ index, index < extent →
    machine.evalOutput (problem.input index) =
      some (problem.target index)

/-- Global correctness implies every finite-prefix fitting obligation. -/
theorem correct_implies_fitsPrefix
    {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    {State : Type x}
    (machine : TypedPartialDFAO problem.base Output State)
    (correct : problem.Correct machine) (extent : Nat) :
    problem.FitsPrefix extent machine := by
  intro index _
  exact correct index

/-- Existence of a globally correct machine with exactly `states` named
states. -/
def HasGlobalModel
    {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    (states : Nat) : Prop :=
  ∃ machine : TypedPartialDFAO problem.base Output (Fin states),
    problem.Correct machine

/-- Existence of a globally correct machine using at most `bound` states. -/
def HasGlobalModelAtMost
    {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    (bound : Nat) : Prop :=
  ∃ states, states ≤ bound ∧ problem.HasGlobalModel states

/-- Existence of a finite-prefix model using at most `bound` states. -/
def HasPrefixModelAtMost
    {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    (extent bound : Nat) : Prop :=
  ∃ states, states ≤ bound ∧
    ∃ machine : TypedPartialDFAO problem.base Output (Fin states),
      problem.FitsPrefix extent machine

/-- Every global bounded-state model induces a model of every finite prefix. -/
theorem global_model_at_most_implies_prefix_model_at_most
    {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    {extent bound : Nat} :
    problem.HasGlobalModelAtMost bound →
      problem.HasPrefixModelAtMost extent bound := by
  rintro ⟨states, hstates, machine, correct⟩
  exact ⟨states, hstates, machine,
    problem.correct_implies_fitsPrefix machine correct extent⟩

end SparseProblem

/-- Top-level restatement: every global bounded-state model induces a model of
every finite prefix. -/
theorem sparse_global_model_implies_prefix_model
    {Alphabet : Type u} {Output : Type w} {BaseState : Type v}
    (problem : SparseProblem Alphabet Output BaseState)
    {extent bound : Nat} :
    problem.HasGlobalModelAtMost bound →
      problem.HasPrefixModelAtMost extent bound :=
  SparseProblem.global_model_at_most_implies_prefix_model_at_most problem

#print axioms sparse_global_model_implies_prefix_model

/-- The two live states of the most-significant-first binary
no-adjacent-ones automaton. -/
inductive BinaryZeckendorfState
  | previousZero
  | previousOne
  deriving DecidableEq

instance : Fintype BinaryZeckendorfState where
  elems := {BinaryZeckendorfState.previousZero, BinaryZeckendorfState.previousOne}
  complete := by intro x; cases x <;> simp

/-- The partial base automaton for binary words with no adjacent ones.
A zero always resets the previous-bit state; a one after a one is illegal. -/
def binaryZeckendorfBase :
    PartialDFA (Fin 2) BinaryZeckendorfState where
  start := .previousZero
  step state digit :=
    if digit = 0 then
      some .previousZero
    else
      match state with
      | .previousZero => some .previousOne
      | .previousOne => none

#print axioms TypedPartialDFAO.runFrom_type
#print axioms SparseProblem.global_model_at_most_implies_prefix_model_at_most

end D5.S0.Automata.TypedPartialDFAOOverBase
