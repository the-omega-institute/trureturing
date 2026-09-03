/- GID: D5/S3/ConceptDynamics/TransportValidity/PredicateRestrictedValidity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TransportValidity/PredicateRestrictedValidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Restricting admission by a predicate makes that predicate valid. -/

import D5.S3.ConceptDynamics.TransportValidity.AdmittedValidityReflection

/- Library-search audit trail (2026-09-03):
   * Repository searches found no existing definition of the predicate-updated
     admission domain and no theorem with the exact source type.
   * Nearby transport-validity theorems require maps or admitted surjectivity,
     neither of which occurs in the source statement, so they are not applied.
   * The pinned environment provides the exact conjunction eliminator
     `And.right`, which is applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TransportValidity.PredicateRestrictedValidity

universe u

/-- The predicate update `A_P(x) = A(x) and P(x)` from source lines
13849-13858. -/
def predicateRestrictedAdmission {X : Sort u}
    (A P : X -> Prop) (x : X) : Prop :=
  A x ∧ P x

/-- Every state admitted after the predicate update satisfies that predicate;
source lines 13860-13873. -/
theorem predicate_valid_on_restricted_admission
    {X : Sort u} (A P : X -> Prop) :
    forall x, predicateRestrictedAdmission A P x -> P x := by
  intro x admitted
  exact And.right admitted

/-- Reverse probe for CAS-A1: the public theorem recovers the concrete target
predicate from updated admission. -/
example (x : Bool)
    (admitted : predicateRestrictedAdmission
      (fun _ : Bool => True) (fun y => y = true) x) :
    x = true :=
  predicate_valid_on_restricted_admission
    (fun _ : Bool => True) (fun y => y = true) x admitted

/-- The source definition is not a constant admission predicate. -/
example :
    predicateRestrictedAdmission
        (fun _ : Bool => True) (fun y => y = true) true ∧
      ¬predicateRestrictedAdmission
        (fun _ : Bool => True) (fun y => y = true) false := by
  simp [predicateRestrictedAdmission]

#print axioms predicate_valid_on_restricted_admission

end D5.S3.ConceptDynamics.TransportValidity.PredicateRestrictedValidity
