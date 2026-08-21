/- GID: D5/S3/ConceptDynamics/Coding/DiagonalNoveltyInformationSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DiagonalNoveltyInformationSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Diagonal catalog escape need not strictly refine world-state information. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import D5.S3.ConceptDynamics.StrictRefinementCapability

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `escaped_of_fixedPointFree` proves that the canonical
     twisted diagonal is outside the expression catalog range and is applied
     directly below.
   * Exact repository hits `Concept`, `Refines`, `conceptJoin`,
     `concept_join_universal`, and `StrictRefinement` are the frozen concept
     family's carrier, order, join, universal property, and strict order. They
     are imported and applied rather than redeclared.
   * Searches for a theorem combining diagonal catalog escape with failure of
     strict world-state refinement found no exact repository or Mathlib result.
   * `loogle` and `leansearch` executables were absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.DiagonalNoveltyInformationSeparation

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.StrictRefinementCapability

/-- A fixed-point-free diagonal construction escapes its expression catalog.
Independently, if the escaped expression's world semantics still factors
through the current concept, adjoining it is not a strict refinement. -/
theorem diagonal_novelty_need_not_add_world_information
    {Address Symbol World CurrentInfo ExpressionInfo : Type*}
    (twist : Symbol → Symbol) (catalog : Address → Address → Symbol)
    (current : Concept World CurrentInfo)
    (expressionSemantics : (Address → Symbol) → Concept World ExpressionInfo) :
    ((∀ symbol, twist symbol ≠ symbol) →
      diagonal twist catalog ∉ Set.range catalog) ∧
    (Refines (expressionSemantics (diagonal twist catalog)) current →
      ¬StrictRefinement current
        (conceptJoin current (expressionSemantics (diagonal twist catalog)))) := by
  constructor
  · intro fixedPointFree
    exact escaped_of_fixedPointFree twist fixedPointFree catalog
  · intro semanticsFactors strictJoin
    apply strictJoin.2
    exact (concept_join_universal current
      (expressionSemantics (diagonal twist catalog)) current).2.2
        ⟨id, rfl⟩ semanticsFactors

/-- Boolean negation and constant world semantics jointly witness the two
independent premise classes. -/
example :
    let twist : Bool → Bool := fun symbol => !symbol
    let catalog : Unit → Unit → Bool := fun _ _ => true
    let current : Concept Bool Unit := fun _ => ()
    let expressionSemantics : (Unit → Bool) → Concept Bool Unit :=
      fun _ _ => ()
    (∀ symbol, twist symbol ≠ symbol) ∧
      Refines (expressionSemantics (diagonal twist catalog)) current := by
  dsimp
  constructor
  · decide
  · exact ⟨id, rfl⟩

#print axioms diagonal_novelty_need_not_add_world_information

end D5.S3.ConceptDynamics.Coding.DiagonalNoveltyInformationSeparation
