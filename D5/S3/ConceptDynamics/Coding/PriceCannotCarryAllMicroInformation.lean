/- GID: D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A price strictly coarser than joint information necessarily misses a target. -/

import D5.S3.ConceptDynamics.StrictRefinementCapability
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'strictly_coarser_price_misses_some_target' D5
     Golden/Frozen/accepted` returned no matches.
   * Repository searches for `conceptJoin`, `Refines`, and strict coarsening found
     `ConceptJoinUniversal`, `StrictRefinementCapability`, and
     `Coding/LosslessEncodingCriterion`. The first two supply the canonical join,
     factorization order, and strict-refinement relation, which are reused here.
   * `LosslessEncodingCriterion.lost_distinction_importance_depends_on_target`
     covers prices explicitly presented as a lossy encoder after a sender readout;
     it does not state the abstract strict-refinement result or its faithful converse.
   * `AnswerabilityCriterion` and pinned Mathlib's `Function.factorsThrough_iff`
     characterize factorization by fiber constancy. They are not needed because the
     strict premise already contains the required non-factorization. The faithful
     direction reuses the exact repository theorem `refinement_transitive`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PriceCannotCarryAllMicroInformation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.StrictRefinementCapability
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

/-- A concrete price that reports only the first of two Boolean micro-coordinates. -/
def coordinatePrice : Concept (Bool × Bool) Bool :=
  Prod.fst

/-- If price is strictly coarser than the joint readout, the joint readout itself is
a constructively specified target that the price misses. -/
theorem strictly_coarser_price_misses_some_target
    {X Price C₁ C₂ : Type*}
    (price : Concept X Price) (concept₁ : Concept X C₁) (concept₂ : Concept X C₂)
    (strict : StrictRefinement price (conceptJoin concept₁ concept₂)) :
    ∃ target : Concept X (C₁ × C₂),
      Refines target (conceptJoin concept₁ concept₂) ∧ ¬Refines target price := by
  refine ⟨conceptJoin concept₁ concept₂, ⟨id, rfl⟩, ?_⟩
  exact strict.2

/-- A faithful price loses no target determined by the joint micro-information. -/
theorem faithful_price_carries_every_join_target
    {X Price C₁ C₂ Target : Type*}
    (price : Concept X Price) (concept₁ : Concept X C₁) (concept₂ : Concept X C₂)
    (faithful : Refines (conceptJoin concept₁ concept₂) price)
    (target : Concept X Target)
    (targetFromJoin : Refines target (conceptJoin concept₁ concept₂)) :
    Refines target price := by
  exact refinement_transitive target (conceptJoin concept₁ concept₂) price
    faithful targetFromJoin

/-- First-coordinate price is genuinely strictly coarser than the joint Boolean readout. -/
theorem coordinate_price_strictly_coarser :
    StrictRefinement coordinatePrice
      (conceptJoin coordinatePrice (Prod.snd : Bool × Bool → Bool)) := by
  constructor
  · exact
      (concept_join_universal coordinatePrice (Prod.snd : Bool × Bool → Bool)
        coordinatePrice).1
  · rintro ⟨factor, factors⟩
    have collapsed :
        conceptJoin coordinatePrice (Prod.snd : Bool × Bool → Bool) (false, false) =
          conceptJoin coordinatePrice (Prod.snd : Bool × Bool → Bool) (false, true) := by
      rw [factors]
      rfl
    exact Bool.false_ne_true (congrArg Prod.snd collapsed)

example :
    ∃ target : Concept (Bool × Bool) (Bool × Bool),
      Refines target (conceptJoin coordinatePrice (Prod.snd : Bool × Bool → Bool)) ∧
        ¬Refines target coordinatePrice :=
  strictly_coarser_price_misses_some_target coordinatePrice
    (Prod.fst : Bool × Bool → Bool) (Prod.snd : Bool × Bool → Bool)
    coordinate_price_strictly_coarser

#print axioms strictly_coarser_price_misses_some_target

end D5.S3.ConceptDynamics.Coding.PriceCannotCarryAllMicroInformation
