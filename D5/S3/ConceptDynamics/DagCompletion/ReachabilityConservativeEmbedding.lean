/- GID: D5/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reachability-conservative embeddings preserve and reflect prerequisite and consequence closures. -/

import D5.S3.ConceptDynamics.DagCompletion.ConsequenceClosure
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace D5.S3.ConceptDynamics.DagCompletion.ReachabilityConservativeEmbedding

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
open D5.S3.ConceptDynamics.DagCompletion.ConsequenceClosure
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/-- An embedding is reachability-conservative when old reachability is preserved and reflected. -/
structure ReachabilityEmbedding
    {V : Type u} {W : Type v}
    (edgeV : V → V → Prop) (edgeW : W → W → Prop) where
  toFun : V → W
  injective : Function.Injective toFun
  map_reachable : ∀ ⦃first second : V⦄,
    Reachable edgeV first second → Reachable edgeW (toFun first) (toFun second)
  reflect_reachable : ∀ ⦃first second : V⦄,
    Reachable edgeW (toFun first) (toFun second) → Reachable edgeV first second

/-- Identity is reachability-conservative. -/
def ReachabilityEmbedding.refl
    {V : Type u} (edge : V → V → Prop) :
    ReachabilityEmbedding edge edge where
  toFun := id
  injective := Function.injective_id
  map_reachable := by intro first second path; exact path
  reflect_reachable := by intro first second path; exact path

/-- Reachability-conservative embeddings compose. -/
def ReachabilityEmbedding.comp
    {V : Type u} {W : Type v} {Z : Type w}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop} {edgeZ : Z → Z → Prop}
    (second : ReachabilityEmbedding edgeW edgeZ)
    (first : ReachabilityEmbedding edgeV edgeW) :
    ReachabilityEmbedding edgeV edgeZ where
  toFun := second.toFun ∘ first.toFun
  injective := second.injective.comp first.injective
  map_reachable := by
    intro source target path
    exact second.map_reachable (first.map_reachable path)
  reflect_reachable := by
    intro source target path
    exact first.reflect_reachable (second.reflect_reachable path)

/-- Prerequisite closure membership is preserved and reflected on the embedded image. -/
theorem mem_prerequisiteClosure_image_iff
    {V : Type u} {W : Type v}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop}
    (embedding : ReachabilityEmbedding edgeV edgeW)
    (targets : Set V) (node : V) :
    embedding.toFun node ∈
        prerequisiteClosure edgeW (embedding.toFun '' targets) ↔
      node ∈ prerequisiteClosure edgeV targets := by
  constructor
  · rintro ⟨targetImage, ⟨target, targetIn, targetEq⟩, path⟩
    subst targetImage
    exact ⟨target, targetIn, embedding.reflect_reachable path⟩
  · rintro ⟨target, targetIn, path⟩
    exact ⟨embedding.toFun target, ⟨target, targetIn, rfl⟩,
      embedding.map_reachable path⟩

/-- Consequence closure membership is preserved and reflected on the embedded image. -/
theorem mem_consequenceClosure_image_iff
    {V : Type u} {W : Type v}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop}
    (embedding : ReachabilityEmbedding edgeV edgeW)
    (sources : Set V) (node : V) :
    embedding.toFun node ∈
        consequenceClosure edgeW (embedding.toFun '' sources) ↔
      node ∈ consequenceClosure edgeV sources := by
  constructor
  · rintro ⟨sourceImage, ⟨source, sourceIn, sourceEq⟩, path⟩
    subst sourceImage
    exact ⟨source, sourceIn, embedding.reflect_reachable path⟩
  · rintro ⟨source, sourceIn, path⟩
    exact ⟨embedding.toFun source, ⟨source, sourceIn, rfl⟩,
      embedding.map_reachable path⟩

#print axioms mem_prerequisiteClosure_image_iff
#print axioms mem_consequenceClosure_image_iff

end D5.S3.ConceptDynamics.DagCompletion.ReachabilityConservativeEmbedding
