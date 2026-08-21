/- GID: D5/S3/ConceptDynamics/Refinement/InductiveSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/InductiveSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite history determines a prediction exactly when the prediction factors through its image. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-21):
   * `rg "preceq|refin|FactorsThrough|factors through|descent"
     D5/S3/ConceptDynamics -g '*.lean'` found the exact repository refinement predicate
     `ConceptJoinUniversal.Refines`; it is imported and used as the source relation below.
   * `rg "FactorsThrough|factorsThrough_iff" .lake/packages/mathlib/Mathlib/ -g '*.lean'`
     found the exact fiber-constancy predicate `Function.FactorsThrough` and its whole-codomain
     factorization theorem `Function.factorsThrough_iff`. The predicate is reused below; the latter
     theorem is not applied because its whole-codomain conclusion requires `Nonempty Prediction`,
     while the source factors through the realized image and needs no such extra assumption.
   * `rg "rangeFactorization" .lake/packages/mathlib/Mathlib/ -g '*.lean'` found the exact
     image-valued map `Set.rangeFactorization`, its surjectivity theorem, and its equality API;
     the image-valued map is reused below. The pinned source contains no single theorem combining
     this image factorization with the explicit counterexample witnesses. -/

namespace D5.S3.ConceptDynamics.Refinement.InductiveSufficiency

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A prediction is constant on every finite-history fiber exactly when it descends to the
realized-history image. Failure is exactly witnessed by two states with the same history and
different predictions. The theorem is stronger than the finite decidable case: neither
finiteness nor decidable equality is needed for the logical criterion. -/
theorem inductive_sufficiency_criterion
    {X History Prediction : Type*}
    (history : Concept X History) (predict : Concept X Prediction) :
    (Function.FactorsThrough predict history <->
      Refines predict (Set.rangeFactorization history)) /\
    (Not (Refines predict (Set.rangeFactorization history)) <->
      exists x y, history x = history y /\ Not (predict x = predict y)) := by
  have fibers_iff_image_factor :
      Function.FactorsThrough predict history <->
        Refines predict (Set.rangeFactorization history) := by
    constructor
    · intro factors
      let descend : Set.range history -> Prediction := fun value =>
        predict (Classical.choose value.property)
      refine ⟨descend, funext fun x => ?_⟩
      change predict x =
        predict (Classical.choose (Set.rangeFactorization history x).property)
      exact factors
        (Classical.choose_spec
          (Set.rangeFactorization history x).property).symm
    · rintro ⟨descend, factorization⟩ x y sameHistory
      rw [factorization]
      exact congrArg descend (Subtype.ext sameHistory)
  constructor
  · exact fibers_iff_image_factor
  · constructor
    · intro notRefines
      classical
      by_contra noWitness
      apply notRefines
      apply fibers_iff_image_factor.mp
      intro x y sameHistory
      by_contra different
      exact noWitness ⟨x, y, sameHistory, different⟩
    · rintro ⟨x, y, sameHistory, different⟩ refinement
      exact different (fibers_iff_image_factor.mpr refinement sameHistory)

#print axioms inductive_sufficiency_criterion

end D5.S3.ConceptDynamics.Refinement.InductiveSufficiency
