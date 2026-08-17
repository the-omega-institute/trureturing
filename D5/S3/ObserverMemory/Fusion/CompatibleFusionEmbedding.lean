/- GID: D5/S3/ObserverMemory/Fusion/CompatibleFusionEmbedding
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/CompatibleFusionEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Embed an intersection completion as the compatible component image. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import Mathlib.Logic.Equiv.Set

/- Library-search audit trail (2026-08-17):
   * Repository search found the adjacent two-relation universal property in
     `LeastCommonRefinement` and the product-fullness criterion in
     `JointPredictionProductFullness`, but neither states the family-indexed
     embedding, dynamics commutation, compatible image, and equivalence.
   * Pinned Mathlib has no theorem packaging the complete claim. Exact
     component hits `Quotient.map`, `Quotient.exact`, `Equiv.ofInjective`, and
     `Equiv.setCongr` supply the induced dynamics, injectivity criterion, and
     the equivalence with the compatible image; they are applied below.
   * Loogle returned no complete family-quotient embedding result. LeanSearch's
     search endpoint returned HTTP 404 and no usable result. -/

namespace D5.S3.ObserverMemory.Fusion.CompatibleFusionEmbedding

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The intersection of a family of equivalence relations. -/
def familyIntersectionSetoid {index state : Type*}
    (component : index -> Setoid state) : Setoid state where
  r left right := forall i, component i left right
  iseqv := {
    refl := fun state i => (component i).refl state
    symm := fun relation i => (component i).symm (relation i)
    trans := fun first second i => (component i).trans (first i) (second i) }

/-- States modulo simultaneous equivalence in every component. -/
abbrev FusionCompletion {index state : Type*}
    (component : index -> Setoid state) :=
  Quotient (familyIntersectionSetoid component)

/-- The canonical projection to one component completion. -/
def componentProjection {index state : Type*}
    (component : index -> Setoid state) (i : index) (stateValue : state) :
    Quotient (component i) :=
  Quotient.mk'' stateValue

/-- The canonical projection to the fused completion. -/
def fusionProjection {index state : Type*}
    (component : index -> Setoid state) (stateValue : state) :
    FusionCompletion component :=
  Quotient.mk'' stateValue

/-- Component tuples simultaneously represented by one underlying state. -/
def compatibleImage {index state : Type*}
    (component : index -> Setoid state) :
    Set (forall i, Quotient (component i)) :=
  {tuple | exists stateValue, forall i,
    componentProjection component i stateValue = tuple i}

/-- Send a fused class to all of its component classes. -/
def completionEmbedding {index state : Type*}
    (component : index -> Setoid state) :
    FusionCompletion component -> forall i, Quotient (component i) :=
  Quotient.lift
    (fun stateValue i => componentProjection component i stateValue)
    (by
      intro left right relation
      funext i
      exact Quotient.sound' (relation i))

/-- Dynamics induced on one component quotient. -/
def componentDynamics {index state : Type*}
    (component : index -> Setoid state) (update : state -> state)
    (preserves : forall i {left right},
      component i left right -> component i (update left) (update right))
    (i : index) : Quotient (component i) -> Quotient (component i) :=
  @Quotient.map state state (component i) (component i) update (by
    intro left right relation
    exact preserves i relation)

/-- Dynamics induced on the intersection quotient. -/
def fusionDynamics {index state : Type*}
    (component : index -> Setoid state) (update : state -> state)
    (preserves : forall i {left right},
      component i left right -> component i (update left) (update right)) :
    FusionCompletion component -> FusionCompletion component :=
  @Quotient.map state state
    (familyIntersectionSetoid component) (familyIntersectionSetoid component)
    update (by
      intro left right relation i
      exact preserves i (relation i))

/-- The intersection completion embeds into the product of its component
completions, intertwines all induced dynamics, has exactly the tuples with a
common representative as its image, and is canonically equivalent to that
compatible image. -/
private theorem family_intersection_embedding
    {index state : Type*} (component : index -> Setoid state)
    (update : state -> state)
    (preserves : forall i {left right},
      component i left right -> component i (update left) (update right)) :
    Function.Injective (completionEmbedding component) /\
      (forall fused,
        completionEmbedding component
            (fusionDynamics component update preserves fused) =
          fun i => componentDynamics component update preserves i
            (completionEmbedding component fused i)) /\
      Set.range (completionEmbedding component) = compatibleImage component /\
      exists equivalence : FusionCompletion component ≃ compatibleImage component,
        forall fused,
          (equivalence fused : forall i, Quotient (component i)) =
            completionEmbedding component fused := by
  have embeddingInjective : Function.Injective (completionEmbedding component) := by
    intro first second equalImages
    obtain ⟨left, rfl⟩ := Quotient.exists_rep first
    obtain ⟨right, rfl⟩ := Quotient.exists_rep second
    apply Quotient.sound'
    intro i
    exact Quotient.exact (congrFun equalImages i)
  have intertwines : forall fused,
      completionEmbedding component
          (fusionDynamics component update preserves fused) =
        fun i => componentDynamics component update preserves i
          (completionEmbedding component fused i) := by
    intro fused
    refine Quotient.inductionOn' fused (fun stateValue => ?_)
    rfl
  have exactImage :
      Set.range (completionEmbedding component) = compatibleImage component := by
    ext tuple
    constructor
    · rintro ⟨fused, rfl⟩
      obtain ⟨stateValue, rfl⟩ := Quotient.exists_rep fused
      exact ⟨stateValue, fun _ => rfl⟩
    · rintro ⟨stateValue, realizes⟩
      refine ⟨fusionProjection component stateValue, ?_⟩
      funext i
      exact realizes i
  let rangeEquivalence :=
    Equiv.ofInjective (completionEmbedding component) embeddingInjective
  let compatibleEquivalence := Equiv.setCongr exactImage
  refine ⟨embeddingInjective, intertwines, exactImage,
    rangeEquivalence.trans compatibleEquivalence, ?_⟩
  intro fused
  rfl

/-- Complete-future equivalence for one member of a readout family. -/
def componentCompletionRelation {index state : Type*} {output : index -> Type*}
    (update : state -> state) (readout : forall i, state -> output i)
    (i : index) : Setoid state :=
  Setoid.ker (completeItinerary update (readout i))

private theorem component_completion_relation_preserved
    {index state : Type*} {output : index -> Type*}
    (update : state -> state) (readout : forall i, state -> output i) :
    forall i {left right},
      componentCompletionRelation update readout i left right ->
        componentCompletionRelation update readout i (update left) (update right) := by
  intro i left right relation
  funext n
  simpa [componentCompletionRelation, completeItinerary,
    Function.iterate_succ_apply] using congrFun relation (n + 1)

/-- The update induced on one complete-future component quotient. -/
def completedComponentDynamics
    {index state : Type*} {output : index -> Type*}
    (update : state -> state) (readout : forall i, state -> output i)
    (i : index) :
    Quotient (componentCompletionRelation update readout i) ->
      Quotient (componentCompletionRelation update readout i) :=
  componentDynamics (componentCompletionRelation update readout) update
    (component_completion_relation_preserved update readout) i

/-- The update induced on the fused complete-future quotient. -/
def completedFusionDynamics
    {index state : Type*} {output : index -> Type*}
    (update : state -> state) (readout : forall i, state -> output i) :
    FusionCompletion (componentCompletionRelation update readout) ->
      FusionCompletion (componentCompletionRelation update readout) :=
  fusionDynamics (componentCompletionRelation update readout) update
    (component_completion_relation_preserved update readout)

/-- The complete-future quotient for a family of readouts embeds into the
product of the component complete-future quotients, intertwines their induced
dynamics, has exactly the tuples with a common state representative as its
image, and is canonically equivalent to that compatible image. -/
theorem compatible_fusion_embedding
    {index state : Type*} {output : index -> Type*}
    (update : state -> state) (readout : forall i, state -> output i) :
    Function.Injective
        (completionEmbedding (componentCompletionRelation update readout)) /\
      (forall fused,
        completionEmbedding (componentCompletionRelation update readout)
            (completedFusionDynamics update readout fused) =
          fun i => completedComponentDynamics update readout i
            (completionEmbedding (componentCompletionRelation update readout) fused i)) /\
      Set.range (completionEmbedding (componentCompletionRelation update readout)) =
        compatibleImage (componentCompletionRelation update readout) /\
      exists equivalence :
          FusionCompletion (componentCompletionRelation update readout) ≃
            compatibleImage (componentCompletionRelation update readout),
        forall fused,
          (equivalence fused : forall i,
              Quotient (componentCompletionRelation update readout i)) =
            completionEmbedding (componentCompletionRelation update readout) fused := by
  exact family_intersection_embedding
    (componentCompletionRelation update readout) update
    (component_completion_relation_preserved update readout)

example :
    FusionCompletion
      (componentCompletionRelation (id : Unit -> Unit) (fun _ : Unit => id)) :=
  fusionProjection
    (componentCompletionRelation (id : Unit -> Unit) (fun _ : Unit => id)) ()

#print axioms compatible_fusion_embedding

end D5.S3.ObserverMemory.Fusion.CompatibleFusionEmbedding
