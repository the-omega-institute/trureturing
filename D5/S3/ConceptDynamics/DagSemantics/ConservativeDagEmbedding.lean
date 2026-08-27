/- GID: D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conservative DAG embeddings compose and preserve dependency reachability. -/

import Mathlib.Logic.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace D5.S3.ConceptDynamics.DagSemantics.ConservativeDagEmbedding

/-- A conservative embedding preserves and reflects direct edges among old nodes. -/
structure ConservativeEmbedding
    {V : Type u} {W : Type v}
    (edgeV : V → V → Prop) (edgeW : W → W → Prop) where
  toFun : V → W
  injective : Function.Injective toFun
  map_edge : ∀ ⦃first second : V⦄,
    edgeV first second → edgeW (toFun first) (toFun second)
  reflect_edge : ∀ ⦃first second : V⦄,
    edgeW (toFun first) (toFun second) → edgeV first second

/-- The identity map is conservative. -/
def ConservativeEmbedding.refl
    {V : Type u} (edge : V → V → Prop) :
    ConservativeEmbedding edge edge where
  toFun := id
  injective := Function.injective_id
  map_edge := by intro first second dependency; exact dependency
  reflect_edge := by intro first second dependency; exact dependency

/-- Conservative embeddings compose. -/
def ConservativeEmbedding.comp
    {V : Type u} {W : Type v} {Z : Type w}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop} {edgeZ : Z → Z → Prop}
    (second : ConservativeEmbedding edgeW edgeZ)
    (first : ConservativeEmbedding edgeV edgeW) :
    ConservativeEmbedding edgeV edgeZ where
  toFun := second.toFun ∘ first.toFun
  injective := second.injective.comp first.injective
  map_edge := by
    intro source target dependency
    exact second.map_edge (first.map_edge dependency)
  reflect_edge := by
    intro source target dependency
    exact first.reflect_edge (second.reflect_edge dependency)

/-- A conservative embedding maps every reflexive-transitive dependency path. -/
theorem ConservativeEmbedding.map_reachable
    {V : Type u} {W : Type v}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop}
    (embedding : ConservativeEmbedding edgeV edgeW)
    {first last : V}
    (path : Relation.ReflTransGen edgeV first last) :
    Relation.ReflTransGen edgeW (embedding.toFun first) (embedding.toFun last) := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edgeStep inductionHypothesis =>
      exact inductionHypothesis.tail (embedding.map_edge edgeStep)

/-- A conservative embedding maps every nonempty dependency path. -/
theorem ConservativeEmbedding.map_strictReachable
    {V : Type u} {W : Type v}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop}
    (embedding : ConservativeEmbedding edgeV edgeW)
    {first last : V}
    (path : Relation.TransGen edgeV first last) :
    Relation.TransGen edgeW (embedding.toFun first) (embedding.toFun last) := by
  induction path with
  | single edgeStep =>
      exact Relation.TransGen.single (embedding.map_edge edgeStep)
  | tail _ edgeStep inductionHypothesis =>
      exact inductionHypothesis.tail (embedding.map_edge edgeStep)

/-- Composition maps reachability exactly as successive mapping does. -/
theorem map_reachable_comp
    {V : Type u} {W : Type v} {Z : Type w}
    {edgeV : V → V → Prop} {edgeW : W → W → Prop} {edgeZ : Z → Z → Prop}
    (second : ConservativeEmbedding edgeW edgeZ)
    (first : ConservativeEmbedding edgeV edgeW)
    {source target : V}
    (path : Relation.ReflTransGen edgeV source target) :
    (second.comp first).map_reachable path =
      second.map_reachable (first.map_reachable path) := by
  apply Subsingleton.elim

#print axioms ConservativeEmbedding.map_reachable
#print axioms ConservativeEmbedding.comp

end D5.S3.ConceptDynamics.DagSemantics.ConservativeDagEmbedding
