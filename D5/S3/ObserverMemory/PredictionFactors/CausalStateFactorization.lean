/- GID: D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/CausalStateFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predictively sufficient interfaces uniquely factor onto the causal-state image. -/

import D5.S3.ConceptDynamics.Refinement.InductiveSufficiency

/- Library-search audit trail (2026-08-21):
   * The repository's canonical `Concept` and `Refines` declarations are imported from the
     existing concept-dynamics family rather than redeclared.
   * Exact repository hit `inductive_sufficiency_criterion` converts fiber constancy into
     factorization through the realized interface image; it is applied directly below.
   * Exact pinned-Mathlib hits `Set.rangeFactorization`,
     `Set.rangeFactorization_surjective`, and `Function.Surjective.injective_comp_right`
     construct the image-valued maps and prove uniqueness.
   * Repository and pinned-Mathlib searches found no theorem packaging the unique
     image-to-image factor together with unequal-future-law separation. -/

namespace D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.InductiveSufficiency

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A prediction law that factors through an interface induces a unique map from the
realized interface image onto the canonical prediction-law image. The induced map agrees
with the supplied predictor, and distinct prediction laws require distinct interface values. -/
theorem causal_state_factorization
    {Past Interface FutureLaw : Type*}
    (interface : Concept Past Interface) (futureLaw : Concept Past FutureLaw)
    (predictor : Interface -> FutureLaw)
    (sufficient : futureLaw = predictor ∘ interface) :
    (∃! factor : Set.range interface -> Set.range futureLaw,
      Set.rangeFactorization futureLaw =
          factor ∘ Set.rangeFactorization interface ∧
        ∀ state, (factor state : FutureLaw) = predictor state.1) ∧
      ∀ past past', futureLaw past ≠ futureLaw past' ->
        interface past ≠ interface past' := by
  have fiber_constant : Function.FactorsThrough futureLaw interface := by
    intro past past' same_interface
    rw [sufficient]
    exact congrArg predictor same_interface
  have image_factor :=
    (inductive_sufficiency_criterion interface futureLaw).1.mp fiber_constant
  rcases image_factor with ⟨lawFactor, law_factors⟩
  let factor : Set.range interface -> Set.range futureLaw := fun state =>
    ⟨lawFactor state, by
      obtain ⟨past, hpast⟩ := state.property
      refine ⟨past, ?_⟩
      calc
        futureLaw past = lawFactor (Set.rangeFactorization interface past) := by
          simpa only [Function.comp_apply] using congrFun law_factors past
        _ = lawFactor state := congrArg lawFactor (Subtype.ext hpast)⟩
  have factor_factors :
      Set.rangeFactorization futureLaw =
        factor ∘ Set.rangeFactorization interface := by
    funext past
    apply Subtype.ext
    change futureLaw past = lawFactor (Set.rangeFactorization interface past)
    simpa only [Function.comp_apply] using congrFun law_factors past
  have factor_matches : ∀ state, (factor state : FutureLaw) = predictor state.1 := by
    intro state
    obtain ⟨past, hpast⟩ := state.property
    calc
      (factor state : FutureLaw) = lawFactor state := rfl
      _ = lawFactor (Set.rangeFactorization interface past) :=
        congrArg lawFactor (Subtype.ext hpast).symm
      _ = futureLaw past := by
        simpa only [Function.comp_apply] using (congrFun law_factors past).symm
      _ = predictor (interface past) := by
        exact congrFun sufficient past
      _ = predictor state.1 := congrArg predictor hpast
  constructor
  · refine ⟨factor, ⟨factor_factors, factor_matches⟩, ?_⟩
    intro candidate candidate_property
    apply Set.rangeFactorization_surjective.injective_comp_right
    exact candidate_property.1.symm.trans factor_factors
  · intro past past' different_laws same_interface
    exact different_laws (fiber_constant same_interface)

/-- A constant one-point interface cannot be sufficient for the two Boolean future laws. -/
example :
    ¬ ∃ predictor : Unit -> Bool,
      (id : Bool -> Bool) = predictor ∘ (fun _ : Bool => ()) := by
  rintro ⟨predictor, sufficient⟩
  have hfalse : false = predictor () := congrFun sufficient false
  have htrue : true = predictor () := congrFun sufficient true
  exact Bool.noConfusion (hfalse.trans htrue.symm)

#print axioms causal_state_factorization

end D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization
