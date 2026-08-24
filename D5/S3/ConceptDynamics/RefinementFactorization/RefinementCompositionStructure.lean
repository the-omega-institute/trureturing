/- GID: D5/S3/ConceptDynamics/RefinementFactorization/RefinementCompositionStructure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/RefinementCompositionStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement composes, forms a factorization category, and descends to a preorder. -/

import D5.S3.ConceptDynamics.Refinement.RefinementReflexivity
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ObserverMemory.Refinement.FactorizationCategory
import Mathlib.Order.Antisymmetrization

/- Library-search audit trail (2026-08-25):
   * Exact family hits `refinement_transitive` and `refinement_reflexive` prove
     the first two source clauses and are applied directly.
   * `fixedCodomainFactorizationCategory` is the existing source-semantic
     category object: its morphisms are factor maps with commuting proofs.
     This statement exposes that named object's computation and law fields.
   * Repository search found the existing all-concept `Readout` carrier and an
     effective-presentation-only `ConceptClass`, but no mutual-refinement
     quotient on all readouts.  `ReadoutRefinementClass` therefore applies
     Mathlib `Antisymmetrization` directly to the source's canonical `Refines`
     test.  `toAntisymmetrization_le_toAntisymmetrization_iff` identifies the
     resulting order with refinement before quotienting. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.RefinementCompositionStructure

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Refinement.RefinementReflexivity
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ObserverMemory.Refinement.FactorizationCategory

universe u

/-- The order on bundled readouts forgets concrete factor witnesses and keeps
only the canonical refinement proposition. -/
instance {X : Type u} : LE (Readout X) where
  le left right :=
    D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines
      left.readout right.readout

private theorem readout_refines_refl {X : Type u} (reading : Readout X) :
    reading <= reading :=
  refinement_reflexive reading.readout

private theorem readout_refines_trans {X : Type u}
    (left middle right : Readout X) :
    left <= middle -> middle <= right -> left <= right := by
  intro hLeft hRight
  exact refinement_transitive
    left.readout middle.readout right.readout hRight hLeft

instance {X : Type u} : Preorder (Readout X) where
  le_refl := readout_refines_refl
  le_trans := readout_refines_trans

/-- All concept readouts modulo mutual refinement, using the source's own
refinement test as the antisymmetrization relation. -/
abbrev ReadoutRefinementClass (X : Type u) :=
  Antisymmetrization (Readout X) (fun left right => left <= right)

/-- Canonical refinement is transitive and reflexive.  Its explicit factor maps
carry the named factorization-category operations and laws, while quotienting
all readout presentations by mutual refinement carries the induced preorder. -/
theorem refinement_composition_category_and_quotient_preorder
    {X B_C B_D B_E : Type u}
    (C : Concept X B_C) (D : Concept X B_D) (E : Concept X B_E) :
    (D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines C D ->
      D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines D E ->
      D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines C E) ∧
    D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines C C ∧
    ((∀ r : Readout X,
        (fixedCodomainFactorizationCategory (X := X)).identity r =
          identityRefinement r.readout) ∧
      (∀ {r₀ r₁ r₂ : Readout X}
          (h₀ : Refines r₀.readout r₁.readout)
          (h₁ : Refines r₁.readout r₂.readout),
        (fixedCodomainFactorizationCategory (X := X)).compose h₀ h₁ =
          composeRefinement h₁ h₀) ∧
      (∀ {r₀ r₁ : Readout X} (h : Refines r₀.readout r₁.readout),
        (fixedCodomainFactorizationCategory (X := X)).compose
          ((fixedCodomainFactorizationCategory (X := X)).identity r₀) h = h) ∧
      (∀ {r₀ r₁ : Readout X} (h : Refines r₀.readout r₁.readout),
        (fixedCodomainFactorizationCategory (X := X)).compose h
          ((fixedCodomainFactorizationCategory (X := X)).identity r₁) = h) ∧
      (∀ {r₀ r₁ r₂ r₃ : Readout X}
          (h₀ : Refines r₀.readout r₁.readout)
          (h₁ : Refines r₁.readout r₂.readout)
          (h₂ : Refines r₂.readout r₃.readout),
        (fixedCodomainFactorizationCategory (X := X)).compose
            ((fixedCodomainFactorizationCategory (X := X)).compose h₀ h₁) h₂ =
          (fixedCodomainFactorizationCategory (X := X)).compose h₀
            ((fixedCodomainFactorizationCategory (X := X)).compose h₁ h₂))) ∧
    ((∀ A B : Readout X,
        toAntisymmetrization
            (fun P Q : Readout X => P <= Q) A <=
          toAntisymmetrization
            (fun P Q : Readout X => P <= Q) B ↔
          D5.S3.ConceptDynamics.ConceptJoinUniversal.Refines
            A.readout B.readout) ∧
      (∀ conceptClass : ReadoutRefinementClass X,
        conceptClass <= conceptClass) ∧
      (∀ {left middle right : ReadoutRefinementClass X},
        left <= middle -> middle <= right -> left <= right)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hCD hDE
    exact refinement_transitive C D E hDE hCD
  · exact refinement_reflexive C
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r
      rfl
    · intro r₀ r₁ r₂ h₀ h₁
      rfl
    · intro r₀ r₁ h
      exact (fixedCodomainFactorizationCategory (X := X)).left_identity h
    · intro r₀ r₁ h
      exact (fixedCodomainFactorizationCategory (X := X)).right_identity h
    · intro r₀ r₁ r₂ r₃ h₀ h₁ h₂
      exact (fixedCodomainFactorizationCategory (X := X)).associative h₀ h₁ h₂
  · refine ⟨?_, ?_, ?_⟩
    · intro A B
      change
        toAntisymmetrization
            (fun P Q : Readout X => P <= Q) A <=
          toAntisymmetrization
            (fun P Q : Readout X => P <= Q) B ↔ A <= B
      exact toAntisymmetrization_le_toAntisymmetrization_iff
    · intro conceptClass
      exact le_rfl
    · intro left middle right hLeft hRight
      exact le_trans hLeft hRight

#print axioms refinement_composition_category_and_quotient_preorder

end D5.S3.ConceptDynamics.RefinementFactorization.RefinementCompositionStructure
