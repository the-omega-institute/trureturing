/- GID: D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Append-generated records preserve state collapse and conditional record separation. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-02):
   * Repository append-only ledgers use `List` extension and `List.IsPrefix`,
     but no existing carrier combines that record law with Definition 45.1's
     controlled update, first readout, second readout, and generated history.
   * Pinned Lean supplies `List.prefix_append`; pinned Mathlib supplies
     `Setoid.ker_def`. Both exact hits are applied below.
   * Loogle confirmed the prefix API. LeanSearch returned no result, while
     GitHub code search and Reservoir rejected the attempted public endpoints.
     The full receipt is `/tmp/SEARCH-dep0902m.md`. -/

namespace D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The named record carrier from Definition 45.1. The operational transition
below changes its list of readings only through `append`. -/
structure AppendOnlyRecord (Reading : Type*) where
  entries : List Reading
deriving DecidableEq, Repr

namespace AppendOnlyRecord

/-- The empty append-only record. -/
def empty {Reading : Type*} : AppendOnlyRecord Reading :=
  ⟨[]⟩

/-- Append the current first-layer reading `q1 x` to the record. -/
def append {Reading : Type*}
    (record : AppendOnlyRecord Reading) (reading : Reading) : AppendOnlyRecord Reading :=
  ⟨record.entries ++ [reading]⟩

/-- Record-column monotonicity is the prefix order on stored readings. -/
def IsPrefix {Reading : Type*}
    (earlier later : AppendOnlyRecord Reading) : Prop :=
  earlier.entries <+: later.entries

/-- One append preserves the entire old record as a prefix. -/
theorem prefix_append {Reading : Type*}
    (record : AppendOnlyRecord Reading) (reading : Reading) :
    IsPrefix record (append record reading) := by
  exact List.prefix_append record.entries [reading]

end AppendOnlyRecord

/-- Definition 45.1's one-layer observer with record, controlled update, and
second-layer readout. The controlled update has the exact domain `X x Y2`. -/
structure RecordedObserver (State Reading SecondOutput : Type*) where
  q1 : Concept State Reading
  controlledUpdate : State × SecondOutput → State
  q2 : Concept (AppendOnlyRecord Reading) SecondOutput

/-- The augmented state `(x, lambda)` from Definition 45.1. -/
abbrev AugmentedState (State Reading : Type*) :=
  State × AppendOnlyRecord Reading

/-- The source one-step evolution
`(x, lambda) |-> (controlledUpdate (x, z), lambda.append (q1 x))`. -/
def step {State Reading SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput)
    (current : AugmentedState State Reading) (z : SecondOutput) :
    AugmentedState State Reading :=
  (observer.controlledUpdate (current.1, z), current.2.append (observer.q1 current.1))

/-- A finite history is operational data: an augmented initial state followed
by the second-layer inputs used by the fixed controlled update in one round. -/
structure ObserverHistory (State Reading SecondOutput : Type*) where
  initial : AugmentedState State Reading
  inputs : List SecondOutput

/-- Run Definition 45.1's one-step evolution along the entire history. -/
def finalState {State Reading SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput)
    (history : ObserverHistory State Reading SecondOutput) :
    AugmentedState State Reading :=
  history.inputs.foldl (step observer) history.initial

/-- The endpoint of a generated observer history. -/
def endpoint {State Reading SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput) :
    Concept (ObserverHistory State Reading SecondOutput) State :=
  fun history => (finalState observer history).1

/-- The record image is computed by repeated `append`; it is not caller-supplied. -/
def recordImage {State Reading SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput) :
    Concept (ObserverHistory State Reading SecondOutput) (AppendOnlyRecord Reading) :=
  fun history => (finalState observer history).2

private theorem foldl_record_prefix {State Reading SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput)
    (inputs : List SecondOutput) (current : AugmentedState State Reading) :
    current.2.IsPrefix (inputs.foldl (step observer) current).2 := by
  induction inputs generalizing current with
  | nil => exact List.prefix_rfl
  | cons z rest inductionHypothesis =>
      rw [List.foldl_cons]
      exact (AppendOnlyRecord.prefix_append current.2 (observer.q1 current.1)).trans
        (inductionHypothesis (current := step observer current z))

/-- Every generated history has a monotone record column: its initial record is
a prefix of its final record image. -/
theorem history_record_prefix {State Reading SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput)
    (history : ObserverHistory State Reading SecondOutput) :
    history.initial.2.IsPrefix (recordImage observer history) := by
  change history.initial.2.IsPrefix
    (history.inputs.foldl (step observer) history.initial).2
  exact foldl_record_prefix observer history.inputs history.initial

/-- Generated histories with one endpoint are equal under every state-only
readout, while `q2` distinguishes their append-only record images exactly when
its two outputs differ. Source: QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md,
Definition 45.1 at lines 47031-47039 and Proposition 45.4 at lines 47063-47072. -/
theorem state_record_readout_distinguishability
    {State Reading StateOutput SecondOutput : Type*}
    (observer : RecordedObserver State Reading SecondOutput)
    (first second : ObserverHistory State Reading SecondOutput)
    (x : State) (lambda lambdaPrime : AppendOnlyRecord Reading)
    (historyData :
      endpoint observer first = x ∧ endpoint observer second = x ∧
        recordImage observer first = lambda ∧
          recordImage observer second = lambdaPrime ∧
          lambda ≠ lambdaPrime) :
    (∀ stateReadout : Concept State StateOutput,
      stateReadout (endpoint observer first) = stateReadout (endpoint observer second)) ∧
      ((¬Setoid.ker (observer.q2 ∘ recordImage observer) first second) ↔
        observer.q2 lambda ≠ observer.q2 lambdaPrime) := by
  rcases historyData with
    ⟨firstEndsAtX, secondEndsAtX, firstRecord, secondRecord, _recordsDifferent⟩
  constructor
  · intro stateReadout
    exact congrArg stateReadout (firstEndsAtX.trans secondEndsAtX.symm)
  · change
      (observer.q2 (recordImage observer first) ≠
          observer.q2 (recordImage observer second)) ↔
        observer.q2 lambda ≠ observer.q2 lambdaPrime
    rw [firstRecord, secondRecord]

/-- Regression probe: the pre-fix API accepted arbitrary Boolean endpoint and
record-image functions without an append operation or a generated-history carrier. -/
example : True := by
  fail_if_success
    have _oldCarrierCall :=
      state_record_readout_distinguishability (StateOutput := Unit)
        (fun _ : Bool => ()) (fun value : Bool => value) (fun value : Bool => value)
        false true () false true
          ⟨rfl, rfl, rfl, rfl, Bool.false_ne_true⟩
  trivial

/-- Reverse probe for CAS-A3 on two histories generated by append-only evolution. -/
example :
    let observer : RecordedObserver Unit Bool Bool :=
      ⟨fun _ => true, fun _ => (), fun record => record.entries.any id⟩
    let first : ObserverHistory Unit Bool Bool :=
      ⟨((), AppendOnlyRecord.empty), []⟩
    let second : ObserverHistory Unit Bool Bool :=
      ⟨((), AppendOnlyRecord.empty), [false]⟩
    ¬Setoid.ker (observer.q2 ∘ recordImage observer) first second := by
  let observer : RecordedObserver Unit Bool Bool :=
    ⟨fun _ => true, fun _ => (), fun record => record.entries.any id⟩
  let first : ObserverHistory Unit Bool Bool :=
    ⟨((), AppendOnlyRecord.empty), []⟩
  let second : ObserverHistory Unit Bool Bool :=
    ⟨((), AppendOnlyRecord.empty), [false]⟩
  have result :=
    state_record_readout_distinguishability (StateOutput := Unit)
      observer first second () AppendOnlyRecord.empty ⟨[true]⟩
        ⟨rfl, rfl, rfl, rfl, by decide⟩
  exact result.2.mpr (by decide)

/-- Append-only monotonicity remains nontrivial even when every reading is `Unit`. -/
example :
    (AppendOnlyRecord.empty : AppendOnlyRecord Unit) ≠
      (AppendOnlyRecord.empty : AppendOnlyRecord Unit).append () := by
  decide

/-- A constant record readout is allowed: both sides of the conditional
distinguishability equivalence are false. -/
example :
    let observer : RecordedObserver Unit Bool Unit :=
      ⟨fun _ => true, fun _ => (), fun _ => ()⟩
    let first : ObserverHistory Unit Bool Unit :=
      ⟨((), AppendOnlyRecord.empty), []⟩
    let second : ObserverHistory Unit Bool Unit :=
      ⟨((), AppendOnlyRecord.empty), [()]⟩
    Setoid.ker (observer.q2 ∘ recordImage observer) first second ∧
      ¬(observer.q2 AppendOnlyRecord.empty ≠ observer.q2 ⟨[true]⟩) := by
  simp [Setoid.ker_def]

#print axioms state_record_readout_distinguishability

end D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability
