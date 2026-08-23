/- GID: D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identity/ConceptRelativeIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A concept kernel can identify strictly more pairs than equality does. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'concept_identity_strictly_coarser_than_equality' D5
     Golden/Frozen/accepted` returned no matches.
   * The requested searches for `Setoid.ker`, `Function.onFun`, `ConceptIdentity`,
     relative identity, and `Refines` found many kernel users and the canonical
     `ConceptJoinUniversal.Refines`, but no definition or theorem covering this claim.
   * A broader repository search found `relative_identity_refinement` and
     `not_injective_on_image_iff_strictly_coarser`; they concern quotient descent and
     injectivity on a sender image, respectively, and provide no equality-versus-kernel
     witness.
   * Pinned Mathlib provides `Setoid.ker`, reused below. It also provides
     `Function.not_injective_iff`, but the required closed witness is constructed
     directly with a constant `Bool -> Unit` readout and needs no classical conversion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identity.ConceptRelativeIdentity

universe u v

/-- Two objects are identical relative to a concept when the concept reads them equally.
Structural, orbit, and legal identity use the same kernel pattern with different readouts;
they remain distinct interpretations rather than additional structures in this module. -/
def ConceptIdentity {X : Type u} {C : Type v} (q : X -> C) (x y : X) : Prop :=
  q x = q y

/-- Concept-relative identity is reflexive, symmetric, and transitive. -/
theorem concept_identity_equivalence {X : Type u} {C : Type v} (q : X -> C) :
    Equivalence (ConceptIdentity q) := by
  exact (Setoid.ker q).iseqv

/-- Equality always implies concept-relative identity, while a constant concept gives
a concrete pair that is concept-identical but unequal. -/
theorem concept_identity_strictly_coarser_than_equality :
    (forall {X : Type u} {C : Type v} (q : X -> C) {x y : X},
      x = y -> ConceptIdentity q x y) ∧
      exists (q : Bool -> Unit) (x y : Bool), ConceptIdentity q x y ∧ x ≠ y := by
  constructor
  · intro X C q x y hxy
    subst y
    rfl
  · exact ⟨fun _ => (), false, true, rfl, Bool.false_ne_true⟩

example : ConceptIdentity (fun _ : Bool => ()) false true ∧ false ≠ true := by
  exact ⟨rfl, Bool.false_ne_true⟩

#print axioms concept_identity_strictly_coarser_than_equality

end D5.S3.ConceptDynamics.Identity.ConceptRelativeIdentity
