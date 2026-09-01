/- GID: D5/S3/ConceptDynamics/ObservationOrder/PureReadoutOrderIndependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/PureReadoutOrderIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identity observation updates exclude order effects from two static readouts. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-21):
   * Searches of D5 and the active frozen ledger for pure readouts, observation
     instruments, and order effects found no exact theorem or canonical
     two-instrument interface.
   * Canonical family declarations `Concept` and `conceptJoin` are imported and
     used for the source readouts and their paired output; no sibling readout
     or joined-concept type is declared.
   * Pinned Mathlib hits `Function.Semiconj.id_left`,
     `Function.Semiconj.id_right`, `Function.Commute.id_left`, and
     `Function.Commute.id_right` are adjacent identity laws, but none states
     the paired observation claim. Core function evaluation and equality
     reduction give the thinnest proof of the exact source statement.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationOrder.PureReadoutOrderIndependence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- The application classes explicitly listed for the generic order-effect
consequence. -/
inductive ApplicationDomain where
  | quantumMeasurement
  | surveyOrder
  | judicialInquiry
  | medicalDiagnosis
  | psychologicalPriming
  | institutionalClassification
  deriving DecidableEq

/-- Observe `C` first, update the state, and then observe `D`. -/
def forwardJoint
    {X C D : Type*} (observeC : Concept X C) (observeD : Concept X D)
    (updateC : X -> X) : Concept X (C × D) :=
  conceptJoin observeC (observeD ∘ updateC)

/-- Observe `D` first, update the state, and return the coordinates in `C,D`
order. -/
def reverseJoint
    {X C D : Type*} (observeC : Concept X C) (observeD : Concept X D)
    (updateD : X -> X) : Concept X (C × D) :=
  conceptJoin (observeC ∘ updateD) observeD

/-- An order effect occurs when some state produces different joint results in
the two observation orders. -/
def hasOrderEffect
    {X C D : Type*} (forward reverse : Concept X (C × D)) : Prop :=
  exists state, forward state ≠ reverse state

/-- Pure identity updates exclude order effects. Consequently, whenever a
reported effect in any listed application is witnessed by the ordered joint
readouts, at least one observation must have a nonidentity state update. -/
theorem pure_readout_order_independence
    {X C D : Type*} (observeC : Concept X C) (observeD : Concept X D)
    (updateC updateD : X -> X)
    (applicationHasEffect : ApplicationDomain -> Prop)
    (effectIsObserved : forall application,
      applicationHasEffect application ->
        hasOrderEffect (forwardJoint observeC observeD updateC)
          (reverseJoint observeC observeD updateD)) :
    (((updateC = id ∧ updateD = id) ->
        Not (hasOrderEffect (forwardJoint observeC observeD updateC)
          (reverseJoint observeC observeD updateD))) ∧
      (forall application, applicationHasEffect application ->
        updateC ≠ id ∨ updateD ≠ id)) := by
  have pureNoEffect : (updateC = id ∧ updateD = id) ->
      Not (hasOrderEffect (forwardJoint observeC observeD updateC)
        (reverseJoint observeC observeD updateD)) := by
    rintro ⟨updateCIdentity, updateDIdentity⟩ ⟨state, different⟩
    apply different
    rw [updateCIdentity, updateDIdentity]
    rfl
  refine ⟨pureNoEffect, ?_⟩
  intro application hasEffect
  by_cases updateCIdentity : updateC = id
  · right
    intro updateDIdentity
    exact pureNoEffect ⟨updateCIdentity, updateDIdentity⟩
      (effectIsObserved application hasEffect)
  · exact Or.inl updateCIdentity

/-- A nonidentity first update can create an order effect from otherwise
static Boolean and unit readouts. -/
example :
    hasOrderEffect
      (forwardJoint (fun _ : Bool => ()) (id : Concept Bool Bool) not)
      (reverseJoint (fun _ : Bool => ()) (id : Concept Bool Bool) id) := by
  exact ⟨false, by decide⟩

/-- Identity updates realize the pure-readout hypothesis for every application
class simultaneously. -/
example :
    let observe : Concept Bool Bool := id
    Not (hasOrderEffect (forwardJoint observe observe id)
      (reverseJoint observe observe id)) := by
  let noReportedEffect : ApplicationDomain -> Prop := fun _ => False
  have result := pure_readout_order_independence
    (id : Concept Bool Bool) (id : Concept Bool Bool) id id noReportedEffect
    (by intro application impossible; exact False.elim impossible)
  exact result.1 ⟨rfl, rfl⟩

#print axioms pure_readout_order_independence

end D5.S3.ConceptDynamics.ObservationOrder.PureReadoutOrderIndependence
