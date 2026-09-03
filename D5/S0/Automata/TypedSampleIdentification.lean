/- GID: D5/S0/Automata/TypedSampleIdentification
   generality: G
   mirror-B: D5/B/S0/Automata/TypedSampleIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Computability.DFA]
   digest: Finite typed sample obstructions imply global DFAO state lower bounds. -/

import D5.S0.Automata.DFAOStateLowerBound
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TypedSampleIdentification

open D5.S0.Automata.DFAOStateLowerBound

universe u v w x

/-- A deterministic partial automaton describing the legal input numeration language. -/
structure PartialBaseAutomaton (Alphabet : Type u) (BaseState : Type v) where
  start : BaseState
  step : BaseState → Alphabet → Option BaseState

namespace PartialBaseAutomaton

/-- Run a partial base automaton from a supplied state. -/
def evalFrom? {Alphabet : Type u} {BaseState : Type v}
    (base : PartialBaseAutomaton Alphabet BaseState) :
    BaseState → List Alphabet → Option BaseState
  | state, [] => some state
  | state, symbol :: word =>
      match base.step state symbol with
      | none => none
      | some next => base.evalFrom? next word

/-- Run a partial base automaton from its distinguished start state. -/
def eval? {Alphabet : Type u} {BaseState : Type v}
    (base : PartialBaseAutomaton Alphabet BaseState)
    (word : List Alphabet) : Option BaseState :=
  base.evalFrom? base.start word

@[simp] theorem evalFrom?_nil {Alphabet : Type u} {BaseState : Type v}
    (base : PartialBaseAutomaton Alphabet BaseState) (state : BaseState) :
    base.evalFrom? state [] = some state := rfl

@[simp] theorem eval?_nil {Alphabet : Type u} {BaseState : Type v}
    (base : PartialBaseAutomaton Alphabet BaseState) :
    base.eval? [] = some base.start := rfl

end PartialBaseAutomaton

/-- A finite or infinite labeled collection of input words. -/
structure LabeledSample (Alphabet : Type u) (Output : Type v) (Index : Type w) where
  word : Index → List Alphabet
  label : Index → Output

namespace LabeledSample

/-- Pull a sample back along an index map. Finite sample prefixes are obtained with `Fin.val`. -/
def reindex {Alphabet : Type u} {Output : Type v} {Index : Type w} {Index' : Type x}
    (sample : LabeledSample Alphabet Output Index) (f : Index' → Index) :
    LabeledSample Alphabet Output Index' where
  word i := sample.word (f i)
  label i := sample.label (f i)

end LabeledSample

/-- A total DFAO whose state typing follows a partial base automaton on every legal transition. -/
structure TypedDFAO
    {Alphabet : Type u} {BaseState : Type v}
    (base : PartialBaseAutomaton Alphabet BaseState)
    (Output : Type w) (State : Type x)
    extends DFAO Alphabet Output State where
  stateType : State → BaseState
  start_type : stateType toDFA.start = base.start
  step_type : ∀ state symbol nextType,
    base.step (stateType state) symbol = some nextType →
      stateType (toDFA.step state symbol) = nextType

namespace TypedDFAO

/-- Exact agreement with every labeled word in a declared sample. -/
def Fits
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {State : Type x} {Index : Type*}
    {base : PartialBaseAutomaton Alphabet BaseState}
    (machine : TypedDFAO base Output State)
    (sample : LabeledSample Alphabet Output Index) : Prop :=
  ∀ i, machine.toDFAO.evalOutput (sample.word i) = sample.label i

/-- State typing is transported along every legal partial-base run. -/
theorem stateType_evalFrom_of_legal
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {State : Type x} {base : PartialBaseAutomaton Alphabet BaseState}
    (machine : TypedDFAO base Output State)
    {state : State} {baseState finalBaseState : BaseState}
    {word : List Alphabet}
    (state_type : machine.stateType state = baseState)
    (legal : base.evalFrom? baseState word = some finalBaseState) :
    machine.stateType (machine.toDFA.evalFrom state word) = finalBaseState := by
  induction word generalizing state baseState finalBaseState with
  | nil =>
      simp only [PartialBaseAutomaton.evalFrom?_nil] at legal
      exact state_type.trans (Option.some.inj legal)
  | cons symbol tail inductionHypothesis =>
      simp only [PartialBaseAutomaton.evalFrom?] at legal
      cases transition : base.step baseState symbol with
      | none => simp [transition] at legal
      | some nextBaseState =>
          rw [transition] at legal
          have next_type :
              machine.stateType (machine.toDFA.step state symbol) = nextBaseState := by
            apply machine.step_type state symbol nextBaseState
            simpa [state_type] using transition
          exact inductionHypothesis next_type legal

/-- A globally fitting machine fits every reindexed finite sub-sample. -/
theorem fits_reindex
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {State : Type x} {Index Index' : Type*}
    {base : PartialBaseAutomaton Alphabet BaseState}
    (machine : TypedDFAO base Output State)
    (sample : LabeledSample Alphabet Output Index)
    (f : Index' → Index) (fits : machine.Fits sample) :
    machine.Fits (sample.reindex f) := by
  intro i
  exact fits (f i)

end TypedDFAO

/-- A typed `k`-state model fitting a labeled sample. This is the semantic target of a
future APTA/CNF encoding; it is independent of any particular solver representation. -/
structure FiniteTypedModel
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w} {Index : Type x}
    (base : PartialBaseAutomaton Alphabet BaseState)
    (sample : LabeledSample Alphabet Output Index) (k : Nat) where
  start : Fin k
  step : Fin k → Alphabet → Fin k
  output : Fin k → Output
  stateType : Fin k → BaseState
  start_type : stateType start = base.start
  step_type : ∀ state symbol nextType,
    base.step (stateType state) symbol = some nextType →
      stateType (step state symbol) = nextType
  fits : ∀ i, output (List.foldl step start (sample.word i)) = sample.label i

namespace FiniteTypedModel

/-- Every finite typed model is an actual typed DFAO on `Fin k`. -/
def toTypedDFAO
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w} {Index : Type x}
    {base : PartialBaseAutomaton Alphabet BaseState}
    {sample : LabeledSample Alphabet Output Index} {k : Nat}
    (model : FiniteTypedModel base sample k) :
    TypedDFAO base Output (Fin k) where
  toDFAO :=
    { step := model.step
      start := model.start
      accept := Set.univ
      output := model.output }
  stateType := model.stateType
  start_type := model.start_type
  step_type := model.step_type

/-- The model produced above fits its defining sample. -/
theorem toTypedDFAO_fits
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w} {Index : Type x}
    {base : PartialBaseAutomaton Alphabet BaseState}
    {sample : LabeledSample Alphabet Output Index} {k : Nat}
    (model : FiniteTypedModel base sample k) :
    model.toTypedDFAO.Fits sample := by
  intro i
  exact model.fits i

end FiniteTypedModel

/-- Reindex any finite-state typed DFAO onto `Fin (card State)` and retain exact sample fit. -/
noncomputable def finiteModelOfTypedDFAO
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {State : Type x} [Fintype State] {Index : Type*}
    {base : PartialBaseAutomaton Alphabet BaseState}
    (machine : TypedDFAO base Output State)
    (sample : LabeledSample Alphabet Output Index)
    (fits : machine.Fits sample) :
    FiniteTypedModel base sample (Fintype.card State) := by
  let equivalence : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  let transportedStep : Fin (Fintype.card State) → Alphabet → Fin (Fintype.card State) :=
    fun state symbol => equivalence (machine.toDFA.step (equivalence.symm state) symbol)
  have run_transport : ∀ (word : List Alphabet) (state : State),
      List.foldl transportedStep (equivalence state) word =
        equivalence (machine.toDFA.evalFrom state word) := by
    intro word
    induction word with
    | nil => intro state; rfl
    | cons symbol tail inductionHypothesis =>
        intro state
        simp only [List.foldl_cons, transportedStep]
        simpa using inductionHypothesis (machine.toDFA.step state symbol)
  exact
    { start := equivalence machine.toDFA.start
      step := transportedStep
      output := fun state => machine.output (equivalence.symm state)
      stateType := fun state => machine.stateType (equivalence.symm state)
      start_type := by simpa using machine.start_type
      step_type := by
        intro state symbol nextType legal
        have originalLegal :
            base.step (machine.stateType (equivalence.symm state)) symbol =
              some nextType := by simpa using legal
        simpa [transportedStep] using
          machine.step_type (equivalence.symm state) symbol nextType originalLegal
      fits := by
        intro i
        rw [run_transport]
        simpa [DFAO.evalOutput, DFA.eval] using fits i }

/-- A finite obstruction at every size at most `k` gives a strict global state lower bound.
This is the finite-UNSAT-to-infinite-correctness bridge used by sparse DFAO problems. -/
theorem no_small_model_implies_state_lower_bound
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {State : Type x} [Fintype State] {Index : Type*}
    {base : PartialBaseAutomaton Alphabet BaseState}
    (sample : LabeledSample Alphabet Output Index) (k : Nat)
    (obstruction : ∀ n, n ≤ k → FiniteTypedModel base sample n → False)
    (machine : TypedDFAO base Output State) (fits : machine.Fits sample) :
    k < Fintype.card State := by
  by_contra notLowerBound
  have small : Fintype.card State ≤ k := Nat.le_of_not_gt notLowerBound
  exact obstruction (Fintype.card State) small
    (finiteModelOfTypedDFAO machine sample fits)

#print axioms no_small_model_implies_state_lower_bound

end D5.S0.Automata.TypedSampleIdentification
