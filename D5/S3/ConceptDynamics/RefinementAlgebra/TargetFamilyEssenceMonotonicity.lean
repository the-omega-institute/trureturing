/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/TargetFamilyEssenceMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/TargetFamilyEssenceMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The minimally sufficient joint target becomes finer under target-family enlargement. -/

import D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

/- Library-search audit trail (2026-08-26):
   * The exact repository primitives `Concept`, `Refines`, and `jointTarget` and
     the frozen minimal-sufficiency theorem are imported rather than restated as
     new definitions.
   * Body-shape searches for `jointTarget` over a `Sum`-indexed enlarged family
     and for target-family monotonicity found no exact repository theorem.
   * The dependent match on `Sum` is the canonical family extension and supplies
     the two injection computation rules by reduction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.TargetFamilyEssenceMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

universe u v v' w z

/-- The canonical enlargement of two dependent target families. -/
def sumTarget {X : Type u} {I : Type v} {J : Type v'}
    {Y : I -> Type w} {Z : J -> Type w}
    (targets : forall index, Concept X (Y index))
    (additional : forall index, Concept X (Z index)) :
    forall index : Sum I J,
      Concept X (match index with
        | Sum.inl left => Y left
        | Sum.inr right => Z right) :=
  fun index =>
    match index with
    | Sum.inl left => targets left
    | Sum.inr right => additional right

@[simp] theorem sumTarget_inl
    {X : Type u} {I : Type v} {J : Type v'}
    {Y : I -> Type w} {Z : J -> Type w}
    (targets : forall index, Concept X (Y index))
    (additional : forall index, Concept X (Z index)) (index : I) :
    sumTarget targets additional (Sum.inl index) = targets index := rfl

@[simp] theorem sumTarget_inr
    {X : Type u} {I : Type v} {J : Type v'}
    {Y : I -> Type w} {Z : J -> Type w}
    (targets : forall index, Concept X (Y index))
    (additional : forall index, Concept X (Z index)) (index : J) :
    sumTarget targets additional (Sum.inr index) = additional index := rfl

/-- The joint target is sufficient exactly when every component is, is itself
componentwise sufficient, and is coarsest among simultaneous sufficient
concepts. Adding an arbitrary dependent family makes this canonical essence
finer, witnessed by restriction along `Sum.inl`. -/
theorem multi_target_essence_sufficiency_and_monotonicity
    {X : Type u} {I : Type v} {Y : I -> Type w}
    (targets : forall index, Concept X (Y index))
    {C : Type z} (readout : Concept X C) :
    (((forall index, Refines (targets index) readout) <->
        Refines (jointTarget targets) readout) /\
      (forall index, Refines (targets index) (jointTarget targets)) /\
      (forall {D : Type z} (candidate : Concept X D),
        (forall index, Refines (targets index) candidate) ->
          Refines (jointTarget targets) candidate)) /\
    (forall {J : Type v'} {Z : J -> Type w}
        (additional : forall index, Concept X (Z index)),
      Refines (jointTarget targets)
        (jointTarget (sumTarget targets additional))) := by
  constructor
  · exact multi_target_minimal_sufficiency targets readout
  · intro J Z additional
    refine ⟨fun values index => values (Sum.inl index), ?_⟩
    rfl

#print axioms multi_target_essence_sufficiency_and_monotonicity

end D5.S3.ConceptDynamics.RefinementAlgebra.TargetFamilyEssenceMonotonicity
