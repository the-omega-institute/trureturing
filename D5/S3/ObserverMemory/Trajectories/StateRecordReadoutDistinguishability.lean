/- GID: D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Append-generated records preserve state collapse and conditional record separation. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-02):
   * No repository declaration combines an abstract append-only record carrier
     with Definition 45.1's controlled update and generated histories.
   * Pinned Mathlib supplies the exact `Setoid.ker_def` kernel characterization.
     Core `congrArg` supplies transport through an arbitrary state readout.
   * Loogle confirmed `Setoid.ker_def`; GitHub search found no matching observer
     theorem. LeanSearch's attempted API returned 404. The full ordered receipt
     and the local/external search boundaries are `/tmp/SEARCH-dep0902m.md`. -/

namespace D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Definition 45.1's abstract append-only record structure. It specifies only
the append operation, the monotonicity relation, and preservation by one append;
it does not choose a representation, an empty record, or strict growth. -/
structure AppendOnlyOps (Record Reading : Type*) where
  append : Record → Reading → Record
  IsPrefix : Record → Record → Prop
  prefix_append : ∀ record reading, IsPrefix record (append record reading)

/-- Definition 45.1's one-layer observer with record, controlled update, and
second-layer readout. The controlled update has the exact domain `X x Y2`. -/
structure RecordedObserver
    (State Record Reading SecondOutput : Type*)
    (recordOps : AppendOnlyOps Record Reading) where
  q1 : Concept State Reading
  controlledUpdate : State × SecondOutput → State
  q2 : Concept Record SecondOutput

/-- The augmented state `(x, lambda)` from Definition 45.1. -/
abbrev AugmentedState (State Record : Type*) := State × Record

/-- The source one-step evolution
`(x, lambda) |-> (controlledUpdate (x, z), lambda.append (q1 x))`. -/
def step {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps)
    (current : AugmentedState State Record) (z : SecondOutput) :
    AugmentedState State Record :=
  (observer.controlledUpdate (current.1, z),
    recordOps.append current.2 (observer.q1 current.1))

universe uState uRecord uReading uSecondOutput

/-- A history is generated freely from an augmented initial state by repeated
applications of Definition 45.1's controlled step. No input-list carrier is
part of its public representation. -/
inductive ObserverHistory
    (State : Type uState) (Record : Type uRecord) (Reading : Type uReading)
    (SecondOutput : Type uSecondOutput)
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps) :
    Type (max (max uState uRecord) (max uReading uSecondOutput)) where
  | initial (initialState : AugmentedState State Record)
  | next
      (history : ObserverHistory State Record Reading SecondOutput recordOps observer)
      (z : SecondOutput)

namespace ObserverHistory

/-- Fold a generated history through a supplied one-step evolution. -/
def fold {State Record Reading SecondOutput : Type*}
    {recordOps : AppendOnlyOps Record Reading}
    {observer : RecordedObserver State Record Reading SecondOutput recordOps}
    (advance : AugmentedState State Record → SecondOutput → AugmentedState State Record) :
    ObserverHistory State Record Reading SecondOutput recordOps observer →
      AugmentedState State Record
  | .initial initialState => initialState
  | .next history z => advance (fold advance history) z

/-- The augmented state at which a generated history starts. -/
def start {State Record Reading SecondOutput : Type*}
    {recordOps : AppendOnlyOps Record Reading}
    {observer : RecordedObserver State Record Reading SecondOutput recordOps} :
    ObserverHistory State Record Reading SecondOutput recordOps observer →
      AugmentedState State Record
  | .initial initialState => initialState
  | .next history _ => start history

end ObserverHistory

/-- Fold Definition 45.1's one-step evolution along the generated history. -/
def finalState {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps)
    (history : ObserverHistory State Record Reading SecondOutput recordOps observer) :
    AugmentedState State Record :=
  ObserverHistory.fold (step recordOps observer) history

/-- The endpoint of a generated observer history. -/
def endpoint {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps) :
    Concept (ObserverHistory State Record Reading SecondOutput recordOps observer) State :=
  fun history => (finalState recordOps observer history).1

/-- The record image is computed by repeated `append`; it is not caller-supplied. -/
def recordImage {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps) :
    Concept (ObserverHistory State Record Reading SecondOutput recordOps observer) Record :=
  fun history => (finalState recordOps observer history).2

/-- Every generated history has a monotone record column: its initial record is
a prefix of its final record image. -/
theorem history_record_prefix {State Record Reading SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps)
    (prefixRefl : ∀ record, recordOps.IsPrefix record record)
    (prefixTrans : ∀ {first middle last},
      recordOps.IsPrefix first middle → recordOps.IsPrefix middle last →
        recordOps.IsPrefix first last)
    (history : ObserverHistory State Record Reading SecondOutput recordOps observer) :
    recordOps.IsPrefix (ObserverHistory.start history).2
      (recordImage recordOps observer history) := by
  induction history with
  | initial initialState => exact prefixRefl initialState.2
  | next history z inductionHypothesis =>
      exact prefixTrans inductionHypothesis
        (recordOps.prefix_append (finalState recordOps observer history).2
          (observer.q1 (finalState recordOps observer history).1))

/-- Generated histories with one endpoint are equal under every state-only
readout, while `q2` distinguishes their append-only record images exactly when
its two outputs differ. Source: QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md,
Definition 45.1 at lines 47031-47039 and Proposition 45.4 at lines 47063-47072. -/
theorem state_record_readout_distinguishability
    {State Record Reading StateOutput SecondOutput : Type*}
    (recordOps : AppendOnlyOps Record Reading)
    (observer : RecordedObserver State Record Reading SecondOutput recordOps)
    (first second : ObserverHistory State Record Reading SecondOutput recordOps observer)
    (x : State) (lambda lambdaPrime : Record)
    (historyData :
      endpoint recordOps observer first = x ∧ endpoint recordOps observer second = x ∧
        recordImage recordOps observer first = lambda ∧
          recordImage recordOps observer second = lambdaPrime ∧
          lambda ≠ lambdaPrime) :
    (∀ stateReadout : Concept State StateOutput,
      stateReadout (endpoint recordOps observer first) =
        stateReadout (endpoint recordOps observer second)) ∧
      ((¬Setoid.ker (observer.q2 ∘ recordImage recordOps observer) first second) ↔
        observer.q2 lambda ≠ observer.q2 lambdaPrime) := by
  rcases historyData with
    ⟨firstEndsAtX, secondEndsAtX, firstRecord, secondRecord, _recordsDifferent⟩
  constructor
  · intro stateReadout
    exact congrArg stateReadout (firstEndsAtX.trans secondEndsAtX.symm)
  · change
      (observer.q2 (recordImage recordOps observer first) ≠
          observer.q2 (recordImage recordOps observer second)) ↔
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

/-- A non-list record carrier used to verify that the public theorem accepts
alternative append-only representations. -/
private structure ChunkedRecord (Reading : Type*) where
  chunks : List (List Reading)
deriving DecidableEq

private def chunkedOps (Reading : Type*) : AppendOnlyOps (ChunkedRecord Reading) Reading where
  append record reading := ⟨record.chunks ++ [[reading]]⟩
  IsPrefix earlier later := earlier.chunks <+: later.chunks
  prefix_append record reading := List.prefix_append record.chunks [[reading]]

/-- B3 acceptance and CAS-A3 reverse probe: an alternative record carrier is
accepted by the public theorem, and unequal outputs imply record distinction. -/
example :
    let recordOps := chunkedOps Bool
    let observer : RecordedObserver Unit (ChunkedRecord Bool) Bool Bool recordOps :=
      ⟨fun _ => true, fun _ => (), fun record => record.chunks.isEmpty⟩
    let first : ObserverHistory Unit (ChunkedRecord Bool) Bool Bool recordOps observer :=
      .initial ((), ⟨[]⟩)
    let second : ObserverHistory Unit (ChunkedRecord Bool) Bool Bool recordOps observer :=
      .next first false
    ¬Setoid.ker (observer.q2 ∘ recordImage recordOps observer) first second := by
  let recordOps := chunkedOps Bool
  let observer : RecordedObserver Unit (ChunkedRecord Bool) Bool Bool recordOps :=
    ⟨fun _ => true, fun _ => (), fun record => record.chunks.isEmpty⟩
  let first : ObserverHistory Unit (ChunkedRecord Bool) Bool Bool recordOps observer :=
    .initial ((), ⟨[]⟩)
  let second : ObserverHistory Unit (ChunkedRecord Bool) Bool Bool recordOps observer :=
    .next first false
  have result :=
    state_record_readout_distinguishability (StateOutput := Unit)
      recordOps observer first second () ⟨[]⟩ ⟨[[true]]⟩
        ⟨rfl, rfl, rfl, rfl, by decide⟩
  exact result.2.mpr (by decide)

/-- The distinct-record premise remains satisfiable when every reading is `Unit`. -/
example :
    (⟨[]⟩ : ChunkedRecord Unit) ≠ (⟨[[()]]⟩ : ChunkedRecord Unit) := by
  decide

/-- A constant record readout is allowed: both sides of the conditional
distinguishability equivalence are false. -/
example :
    let recordOps := chunkedOps Unit
    let observer : RecordedObserver Unit (ChunkedRecord Unit) Unit Unit recordOps :=
      ⟨fun _ => (), fun _ => (), fun _ => ()⟩
    let first : ObserverHistory Unit (ChunkedRecord Unit) Unit Unit recordOps observer :=
      .initial ((), ⟨[]⟩)
    let second : ObserverHistory Unit (ChunkedRecord Unit) Unit Unit recordOps observer :=
      .next first ()
    Setoid.ker (observer.q2 ∘ recordImage recordOps observer) first second ∧
      ¬(observer.q2 ⟨[]⟩ ≠ observer.q2 ⟨[[()]]⟩) := by
  simp [Setoid.ker_def]

#print axioms state_record_readout_distinguishability

end D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability
