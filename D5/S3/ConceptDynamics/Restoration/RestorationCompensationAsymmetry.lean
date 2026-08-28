/- GID: D5/S3/ConceptDynamics/Restoration/RestorationCompensationAsymmetry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Restoration/RestorationCompensationAsymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identity restoration implies compensation, while the converse can fail. -/

import D5.S3.ConceptDynamics.Restoration.RestorationImpliesCompensation

/- Library-search audit trail (2026-08-26):
   * Exact repository hit `identity_restoration_implies_value_compensation`
     supplies the forward implication on the canonical `Concept` and `Refines`
     carriers and is applied directly.
   * Repository searches for a value-compensation countermodel and for the
     converse of identity restoration found no existing theorem.
   * The countermodel uses only `Bool`, `Unit`, identity, negation, and the
     imported canonical refinement relation; pinned Mathlib adds no thinner hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Restoration.RestorationCompensationAsymmetry

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Restoration.RestorationImpliesCompensation

/-- Identity restoration preserves every value determined by identity. The
converse fails on a tied Boolean model: negation changes identity while the
constant unit-valued concept is still exactly compensated. -/
theorem identity_restoration_implies_compensation_with_converse_countermodel
    {X IdentityValue FunctionalValue : Type*}
    (identity : Concept X IdentityValue)
    (value : Concept X FunctionalValue)
    (harm repair : X -> X)
    (valueDeterminedByIdentity : Refines value identity) :
    ((forall x, identity (repair (harm x)) = identity x) ->
        forall x, value (repair (harm x)) = value x) /\
      (let counterIdentity : Concept Bool Bool := id
       let counterValue : Concept Bool Unit := fun _ => ()
       let counterHarm : Bool -> Bool := Bool.not
       let counterRepair : Bool -> Bool := id
       Refines counterValue counterIdentity /\
         (forall x, counterValue (counterRepair (counterHarm x)) = counterValue x) /\
         Not (forall x,
           counterIdentity (counterRepair (counterHarm x)) = counterIdentity x)) := by
  constructor
  · exact identity_restoration_implies_value_compensation identity value harm repair
      valueDeterminedByIdentity
  · dsimp
    refine ⟨⟨fun _ => (), rfl⟩, ?_, ?_⟩
    · intro x
      rfl
    · intro restored
      exact Bool.false_ne_true (restored false).symm

#print axioms identity_restoration_implies_compensation_with_converse_countermodel

end D5.S3.ConceptDynamics.Restoration.RestorationCompensationAsymmetry
