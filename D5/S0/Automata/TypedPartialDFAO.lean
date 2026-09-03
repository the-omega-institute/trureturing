/- GID: D5/S0/Automata/TypedPartialDFAO
   generality: G
   mirror-B: D5/B/S0/Automata/TypedPartialDFAO
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Partial output automata can be typed over a base automaton with exact transition projection and leading-zero invariance. -/

import D5.S0.Automata.DFAOStateLowerBound

/- Library-search audit trail (2026-09-01):
   * The frozen DFAO node supplies total Moore-machine semantics on Mathlib DFA.
   * The sparse Ostrowski identification problem additionally needs partial
     transitions and a state typing over the representation-validity automaton.
   * The exact projection equation below excludes transitions forbidden by the
     base automaton and requires every defined machine transition to carry the
     prescribed base-state type. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TypedPartialDFAO

universe u v w z

/-- A partial deterministic base automaton. `none` marks an illegal symbol from
that base state. -/
structure BaseAutomaton (Alphabet : Type u) (State : Type v) where
  start : State
  step : State → Alphabet → Option State

namespace BaseAutomaton

/-- Partial execution from an arbitrary base state. -/
def runFrom {Alphabet : Type u} {State : Type v}
    (base : BaseAutomaton Alphabet State) : State → List Alphabet → Option State
  | state, [] => some state
  | state, symbol :: tail =>
      (base.step state symbol).bind fun next => base.runFrom next tail

/-- Partial execution from the distinguished base start state. -/
def run {Alphabet : Type u} {State : Type v}
    (base : BaseAutomaton Alphabet State) (word : List Alphabet) : Option State :=
  base.runFrom base.start word

end BaseAutomaton

/-- A partial DFAO whose states project exactly to states of a base validity
automaton. -/
structure Machine (Alphabet : Type u) (Output : Type v)
    (BaseState : Type w) (State : Type z) where
  base : BaseAutomaton Alphabet BaseState
  start : State
  step : State → Alphabet → Option State
  output : State → Output
  stateType : State → BaseState
  start_type : stateType start = base.start
  type_preserving : ∀ state symbol,
    Option.map stateType (step state symbol) =
      base.step (stateType state) symbol
  zero : Alphabet
  start_zero_loop : step start zero = some start

namespace Machine

/-- Partial execution from an arbitrary machine state. -/
def runFrom {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State) :
    State → List Alphabet → Option State
  | state, [] => some state
  | state, symbol :: tail =>
      (machine.step state symbol).bind fun next => machine.runFrom next tail

/-- Partial execution from the machine start state. -/
def run {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (word : List Alphabet) : Option State :=
  machine.runFrom machine.start word

/-- Read an output exactly when the whole input has a defined run. -/
def evalOutput {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (word : List Alphabet) : Option Output :=
  Option.map machine.output (machine.run word)

/-- Correctness on an explicitly declared sparse domain. -/
def CorrectOn {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (domain : Set (List Alphabet)) (target : List Alphabet → Output) : Prop :=
  ∀ ⦃word⦄, word ∈ domain → machine.evalOutput word = some (target word)

/-- Execution respects concatenation. -/
theorem runFrom_append {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (state : State) (left right : List Alphabet) :
    machine.runFrom state (left ++ right) =
      (machine.runFrom state left).bind
        (fun next => machine.runFrom next right) := by
  induction left generalizing state with
  | nil => simp [runFrom]
  | cons symbol tail ih =>
      simp only [List.cons_append, runFrom]
      cases transition : machine.step state symbol with
      | none => simp [transition]
      | some next => simp [transition, ih]

/-- The machine run projects to the run of the base validity automaton. -/
theorem runFrom_type {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (state : State) (word : List Alphabet) :
    Option.map machine.stateType (machine.runFrom state word) =
      machine.base.runFrom (machine.stateType state) word := by
  induction word generalizing state with
  | nil => rfl
  | cons symbol tail ih =>
      simp only [runFrom, BaseAutomaton.runFrom]
      rw [← machine.type_preserving state symbol]
      cases transition : machine.step state symbol with
      | none => simp [transition]
      | some next => simp [transition, ih]

/-- A leading zero at the distinguished start state does not change execution. -/
@[simp]
theorem run_zero_cons {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (word : List Alphabet) :
    machine.run (machine.zero :: word) = machine.run word := by
  simp [run, runFrom, machine.start_zero_loop]

/-- The start-state type and transition projection imply that every successful
machine run has exactly the base state obtained by reading the same word. -/
theorem run_type {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (word : List Alphabet) :
    Option.map machine.stateType (machine.run word) = machine.base.run word := by
  rw [run, BaseAutomaton.run, machine.runFrom_type, machine.start_type]

#print axioms Machine.runFrom_append
#print axioms Machine.runFrom_type
#print axioms Machine.run_zero_cons
#print axioms Machine.run_type

end Machine

/-- Top-level restatement: every successful typed run projects to the base
automaton run on the same word. -/
theorem machine_run_type {Alphabet : Type u} {Output : Type v}
    {BaseState : Type w} {State : Type z}
    (machine : Machine Alphabet Output BaseState State)
    (word : List Alphabet) :
    Option.map machine.stateType (machine.run word) =
      machine.base.run word :=
  Machine.run_type machine word

#print axioms machine_run_type

end D5.S0.Automata.TypedPartialDFAO
