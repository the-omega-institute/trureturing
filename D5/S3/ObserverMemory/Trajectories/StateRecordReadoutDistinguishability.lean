/- GID: D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: State readouts merge equal endpoints; record readouts separate exactly by output. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-02):
   * Exact repository hit `Concept` is the canonical generic readout carrier;
     it is imported for the endpoint, record image, and both readouts.
   * The adjacent frozen history-sensitive reduction modules use the same
     endpoint/readout carrier and equality kernels, but do not state these two
     clauses, so no theorem wrapper is available.
   * Exact pinned-Mathlib hit `Setoid.ker_def` identifies a readout's equality
     kernel with equality of its outputs and is applied directly below.
   * Loogle confirmed that exact Mathlib declaration. LeanSearch, GitHub code
     search, Reservoir, and grep.app were unavailable at their attempted public
     endpoints; the full receipt is `/tmp/SEARCH-dep0902m.md`. -/

namespace D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Histories with one endpoint are equal under every state-only readout, while
the readout of their record images distinguishes them exactly when its two
outputs differ. Source: QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md,
lines 47063-47072. -/
theorem state_record_readout_distinguishability
    {History State Record StateOutput RecordOutput : Type*}
    (endpoint : Concept History State)
    (recordImage : Concept History Record)
    (recordReadout : Concept Record RecordOutput)
    (first second : History) (x : State) (lambda lambdaPrime : Record)
    (historyData :
      endpoint first = x ∧ endpoint second = x ∧
        recordImage first = lambda ∧ recordImage second = lambdaPrime ∧
          lambda ≠ lambdaPrime) :
    (∀ stateReadout : Concept State StateOutput,
      stateReadout (endpoint first) = stateReadout (endpoint second)) ∧
      ((¬Setoid.ker (recordReadout ∘ recordImage) first second) ↔
        recordReadout lambda ≠ recordReadout lambdaPrime) := by
  rcases historyData with
    ⟨firstEndsAtX, secondEndsAtX, firstRecord, secondRecord, _recordsDifferent⟩
  constructor
  · intro stateReadout
    exact congrArg stateReadout (firstEndsAtX.trans secondEndsAtX.symm)
  · change
      (recordReadout (recordImage first) ≠ recordReadout (recordImage second)) ↔
        recordReadout lambda ≠ recordReadout lambdaPrime
    rw [firstRecord, secondRecord]

/-- Reverse probe for the record-separation direction of the public theorem. -/
example :
    let recordImage : Concept Bool Bool := id
    let recordReadout : Concept Bool Bool := id
    ¬Setoid.ker (recordReadout ∘ recordImage) false true := by
  let endpoint : Concept Bool Unit := fun _ => ()
  let recordImage : Concept Bool Bool := id
  let recordReadout : Concept Bool Bool := id
  have result :=
    state_record_readout_distinguishability (StateOutput := Unit)
      endpoint recordImage recordReadout false true () false true
        ⟨rfl, rfl, rfl, rfl, Bool.false_ne_true⟩
  exact result.2.mpr Bool.false_ne_true

/-- The all-`Unit` carrier cannot satisfy the source's distinct-record premise. -/
example (endpoint : Concept Unit Unit) (recordImage : Concept Unit Unit) :
    ¬∃ x lambda lambdaPrime : Unit,
      endpoint () = x ∧ endpoint () = x ∧
        recordImage () = lambda ∧ recordImage () = lambdaPrime ∧
          lambda ≠ lambdaPrime := by
  simp

/-- A constant record readout is allowed: both sides of the conditional
distinguishability equivalence are false. -/
example :
    let recordImage : Concept Bool Bool := id
    let recordReadout : Concept Bool Unit := fun _ => ()
    Setoid.ker (recordReadout ∘ recordImage) false true ∧
      ¬(recordReadout false ≠ recordReadout true) := by
  simp [Setoid.ker_def]

#print axioms state_record_readout_distinguishability

end D5.S3.ObserverMemory.Trajectories.StateRecordReadoutDistinguishability
