/- GID: D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The dependent joint target is the coarsest concept sufficient for every target. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * Repository searches found the exact canonical `Concept` and `Refines`
     primitives, which are imported and used directly.
   * `ConceptJoinUniversal.concept_join_universal` is the binary product case.
     It does not construct or prove the universal property of the source's
     arbitrary dependent target family, so it is an adjacent special case rather
     than an exact theorem hit.
   * Searches of D5 and pinned Mathlib found no packaged dependent-family
     factorization equivalence. The proof uses component evaluation, function
     extensionality, and `Classical.choose` for the supplied factor witnesses.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u v w z

/-- The canonical joint target evaluates every member of a dependent target
family at the same source state. -/
def jointTarget {X : Type u} {I : Type v} {Y : I -> Type w}
    (targets : forall index, Concept X (Y index)) :
    Concept X (forall index, Y index) :=
  fun state index => targets index state

/-- A readout decides every target exactly when it decides their canonical
joint target. The joint target itself decides every component and is coarsest
among all concepts with that simultaneous sufficiency property. -/
theorem multi_target_minimal_sufficiency
    {X : Type u} {I : Type v} {Y : I -> Type w}
    (targets : forall index, Concept X (Y index))
    {C : Type z} (readout : Concept X C) :
    ((forall index, Refines (targets index) readout) <->
      Refines (jointTarget targets) readout) /\
    (forall index, Refines (targets index) (jointTarget targets)) /\
    (forall {D : Type z} (candidate : Concept X D),
      (forall index, Refines (targets index) candidate) ->
        Refines (jointTarget targets) candidate) := by
  classical
  have projections :
      forall index, Refines (targets index) (jointTarget targets) := by
    intro index
    refine ⟨fun values => values index, ?_⟩
    rfl
  have least :
      forall {D : Type z} (candidate : Concept X D),
        (forall index, Refines (targets index) candidate) ->
          Refines (jointTarget targets) candidate := by
    intro D candidate sufficient
    let factor : forall index, D -> Y index :=
      fun index => Classical.choose (sufficient index)
    have factor_spec : forall index,
        targets index = factor index ∘ candidate :=
      fun index => Classical.choose_spec (sufficient index)
    refine ⟨fun value index => factor index value, ?_⟩
    funext state index
    exact congrFun (factor_spec index) state
  refine ⟨?_, projections, least⟩
  constructor
  · intro sufficient
    exact least readout sufficient
  · rintro ⟨factor, factorizes⟩ index
    refine ⟨fun value => factor value index, ?_⟩
    funext state
    exact congrFun (congrFun factorizes state) index

/-- The canonical joint target computes pointwise, without a choice of section. -/
theorem jointTarget_apply
    {X : Type u} {I : Type v} {Y : I -> Type w}
    (targets : forall index, Concept X (Y index))
    (state : X) (index : I) :
    jointTarget targets state index = targets index state := rfl

#print axioms multi_target_minimal_sufficiency

end D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
