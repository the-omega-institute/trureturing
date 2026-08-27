/- GID: D5/S3/ConceptDynamics/Fibers/ObserverConceptReadoutCorrespondence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/ObserverConceptReadoutCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concept and observer readouts retain identity under embedding and quotienting. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * Body-shape searches found the canonical `Concept` and dependent
     `jointReadout`; both are imported rather than redeclared.
   * `GlobalProfileQuotientUniversality` has the adjacent same-universe quotient
     projection. The statement below uses Mathlib's canonical `Quotient.mk` on
     `Setoid.ker (jointReadout ...)`, retaining independent universes for states,
     readout indices, and readout values.
   * Searches for an observer structure carrying a readout family, admissibility,
     an accepted anchor, and the three forgetting countermodels found no D5 hit.
     Pinned Mathlib supplies `Setoid.ker`, `Quotient.eq`, and function extensionality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.ObserverConceptReadoutCorrespondence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- An observer carries a family of readouts, an admissibility predicate on the
joint readout, and an actual anchor whose readout is admissible. -/
structure ObserverStructure (X : Type u) (Index : Type v)
    (Value : Index -> Type w) where
  readout : forall index, X -> Value index
  admissible : (forall index, Value index) -> Prop
  anchor : X
  anchorAdmissible : admissible (jointReadout readout anchor)

/-- A concept embeds canonically as a singleton-readout observer with universal
admissibility and the supplied anchor. -/
def conceptObserver {X : Type u} {C : Type z} (q : Concept X C) (anchor : X) :
    ObserverStructure X Unit (fun _ => C) where
  readout _ := q
  admissible _ := True
  anchor := anchor
  anchorAdmissible := True.intro

/-- The singleton embedding preserves concept identity, while the canonical
kernel quotient preserves exactly observer indistinguishability. The quotient
forgets admissibility, the anchor, and the decomposition of a joint readout into
coordinates, as witnessed by three countermodels on the same constructions. -/
theorem observer_concept_readout_correspondence
    {X : Type u} {C : Type z} {Index : Type v} {Value : Index -> Type w}
    (q : Concept X C) (anchor : X)
    (observer : ObserverStructure X Index Value) :
    let embedded := conceptObserver q anchor
    let forgotten : Concept X
        (Quotient (Setoid.ker (jointReadout observer.readout))) :=
      Quotient.mk (Setoid.ker (jointReadout observer.readout))
    (embedded.readout () = q ∧
      embedded.admissible = (fun _ => True) ∧
      embedded.anchor = anchor) ∧
    (forall x y,
      jointReadout embedded.readout x = jointReadout embedded.readout y ↔
        q x = q y) ∧
    (forall x y,
      forgotten x = forgotten y ↔
        jointReadout observer.readout x = jointReadout observer.readout y) ∧
    (exists first second : ObserverStructure Bool Unit (fun _ => Bool),
      first.admissible ≠ second.admissible ∧
        Setoid.ker (jointReadout first.readout) =
          Setoid.ker (jointReadout second.readout)) ∧
    (exists first second : ObserverStructure Bool Unit (fun _ => Unit),
      first.anchor ≠ second.anchor ∧
        Setoid.ker (jointReadout first.readout) =
          Setoid.ker (jointReadout second.readout)) ∧
    (exists first second : forall _ : Bool, Bool -> Bool,
      first ≠ second ∧
        Setoid.ker (jointReadout first) = Setoid.ker (jointReadout second)) := by
  dsimp only
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    constructor
    · intro sameProfile
      exact congrFun sameProfile ()
    · intro sameReading
      funext index
      cases index
      exact sameReading
  · intro x y
    exact Quotient.eq
  · let first : ObserverStructure Bool Unit (fun _ => Bool) :=
      { readout := fun _ _ => false
        admissible := fun _ => True
        anchor := false
        anchorAdmissible := True.intro }
    let second : ObserverStructure Bool Unit (fun _ => Bool) :=
      { readout := fun _ _ => false
        admissible := fun profile => profile () = false
        anchor := false
        anchorAdmissible := rfl }
    refine ⟨first, second, ?_, rfl⟩
    intro sameAdmissible
    have impossible := congrFun sameAdmissible (fun _ : Unit => true)
    simp [first, second] at impossible
  · let first : ObserverStructure Bool Unit (fun _ => Unit) :=
      { readout := fun _ _ => ()
        admissible := fun _ => True
        anchor := false
        anchorAdmissible := True.intro }
    let second : ObserverStructure Bool Unit (fun _ => Unit) :=
      { readout := fun _ _ => ()
        admissible := fun _ => True
        anchor := true
        anchorAdmissible := True.intro }
    exact ⟨first, second, Bool.false_ne_true, rfl⟩
  · let first : forall _ : Bool, Bool -> Bool := fun index state =>
      if index then false else state
    let second : forall _ : Bool, Bool -> Bool := fun index state =>
      if index then state else false
    refine ⟨first, second, ?_, ?_⟩
    · intro sameFamily
      have impossible := congrFun (congrFun sameFamily false) true
      simp [first, second] at impossible
    · apply Setoid.ext
      intro x y
      constructor
      · intro sameFirst
        have sameState := congrFun sameFirst false
        simp [jointReadout, first] at sameState
        subst y
        rfl
      · intro sameSecond
        have sameState := congrFun sameSecond true
        simp [jointReadout, second] at sameState
        subst y
        rfl

/-- The observer carrier is inhabited without adding any extra premise beyond
an anchored state and a universally admissible readout. -/
example : ObserverStructure Bool Unit (fun _ => Bool) :=
  conceptObserver (id : Concept Bool Bool) false

#print axioms conceptObserver
#print axioms observer_concept_readout_correspondence

end D5.S3.ConceptDynamics.Fibers.ObserverConceptReadoutCorrespondence
