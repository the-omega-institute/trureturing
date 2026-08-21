/- GID: D5/S3/ConceptDynamics/NormativeStructure/DescriptiveNormativeSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/DescriptiveNormativeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One descriptive structure admits incompatible normative extensions. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-21):
   * Repository searches found no descriptive/normative model-separation
     theorem or canonical normative-extension carrier. The imported `Concept`
     alias is the canonical family carrier for the source component `C`.
   * `InformedDisclosureDefect`, `AnswerabilityCriterion`, and
     `BlindNaturalityCountermodel` are adjacent readout results, but none
     constructs two normative models over the same descriptive tuple.
   * Pinned Mathlib's exact `congrFun` operation is applied twice to separate
     the two permission predicates at the source anchor and action witness.
     `Function.factorsThrough_iff` is an adjacent definability criterion, not
     the source's explicit two-model construction.
   * No exact pinned-Mathlib theorem packages all six public separation
     clauses. The `loogle` and `leansearch` executables were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.DescriptiveNormativeSeparation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The source's purely descriptive tuple: physical admissibility, process,
concept readout, and an anchored state. -/
structure DescriptiveStructure
    (State Action Description : Type*) where
  physicalAdmissible : State -> Action -> Prop
  process : State -> Action -> State
  concept : Concept State Description
  anchor : State

/-- A normative model adds a permission predicate to a fixed descriptive
structure without defining that predicate from the descriptive fields. -/
structure NormativeExtension
    (State Action Description : Type*) where
  descriptive : DescriptiveStructure State Action Description
  permitted : State -> Action -> Prop

/-- Holding every descriptive primitive fixed, the all-permitted and
none-permitted extensions are distinct, so one descriptive inference cannot
produce both normative structures. -/
theorem descriptive_structure_does_not_uniquely_determine_norms
    {State Action Description : Type*}
    (descriptive : DescriptiveStructure State Action Description)
    (action : Action) :
    ∃ first second : NormativeExtension State Action Description,
      first.descriptive = descriptive ∧
        second.descriptive = descriptive ∧
        (∀ state action, first.permitted state action) ∧
        (∀ state action, ¬ second.permitted state action) ∧
        first.permitted ≠ second.permitted ∧
        ∀ infer : DescriptiveStructure State Action Description ->
            (State -> Action -> Prop),
          ¬(infer descriptive = first.permitted ∧
            infer descriptive = second.permitted) := by
  let allowAll : NormativeExtension State Action Description :=
    { descriptive := descriptive
      permitted := fun _ _ => True }
  let forbidAll : NormativeExtension State Action Description :=
    { descriptive := descriptive
      permitted := fun _ _ => False }
  have differentPredicates : allowAll.permitted ≠ forbidAll.permitted := by
    intro samePredicate
    have sameAtWitness :=
      congrFun (congrFun samePredicate descriptive.anchor) action
    have allowed : allowAll.permitted descriptive.anchor action := by
      trivial
    rw [sameAtWitness] at allowed
    exact allowed
  refine ⟨allowAll, forbidAll, rfl, rfl, ?_, ?_, differentPredicates, ?_⟩
  · intro _ _
    trivial
  · intro _ _ forbidden
    exact forbidden
  · intro infer inferredBoth
    exact differentPredicates (inferredBoth.1.symm.trans inferredBoth.2)

/-- The descriptive tuple and action-domain witness have a concrete model. -/
example :
    let descriptive : DescriptiveStructure Unit Unit Unit :=
      { physicalAdmissible := fun _ _ => True
        process := fun state _ => state
        concept := fun _ => ()
        anchor := () }
    ∃ first second : NormativeExtension Unit Unit Unit,
      first.descriptive = descriptive ∧
        second.descriptive = descriptive ∧
        (∀ state action, first.permitted state action) ∧
        (∀ state action, ¬ second.permitted state action) ∧
        first.permitted ≠ second.permitted ∧
        ∀ infer : DescriptiveStructure Unit Unit Unit ->
            (Unit -> Unit -> Prop),
          ¬(infer descriptive = first.permitted ∧
            infer descriptive = second.permitted) := by
  dsimp
  exact descriptive_structure_does_not_uniquely_determine_norms
    { physicalAdmissible := fun _ _ => True
      process := fun state _ => state
      concept := fun _ => ()
      anchor := () }
    ()

#print axioms descriptive_structure_does_not_uniquely_determine_norms

end D5.S3.ConceptDynamics.NormativeStructure.DescriptiveNormativeSeparation
