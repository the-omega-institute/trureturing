/- GID: D5/S3/ObserverMemory/Knowledge/ReadoutCoarseningKnowledge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/ReadoutCoarseningKnowledge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coarsening a readout contravariantly shrinks its complex knowledge space. -/

import D5.S3.ObserverMemory.Knowledge.FiniteCapacity

/- Library-search audit trail (2026-08-20):
   * The repository exact hit `mem_knowledgeSpace_iff_factorsThrough` identifies
     complex knowledge-space membership with fiber constancy; it is applied in
     both directions below.
   * Pinned Mathlib's exact `Function.FactorsThrough` predicate is the fiber
     semantics used by that bridge and by the proof below.
   * The repository theorem
     `knows_of_later_readout_factors_through_earlier` is a same-codomain timed
     specialization, so it does not cover the source's general pair of readout
     codomains.
   * Repository and pinned-Mathlib shape searches found no theorem directly
     packaging this general knowledge-space inclusion. -/

namespace D5.S3.ObserverMemory.Knowledge.ReadoutCoarseningKnowledge

open D5.S3.ObserverMemory.Knowledge.FiniteCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If a later readout is obtained by postcomposing an earlier readout, every
complex observable pulled back from the later readout is already pulled back
from the earlier one. -/
theorem readout_coarsening_shrinks_knowledge
    {X Y₀ Y₁ : Type*} (q₀ : X -> Y₀) (q₁ : X -> Y₁)
    (forget : Y₀ -> Y₁) (hfactor : q₁ = forget ∘ q₀) :
    KnowledgeSpace q₁ ≤ KnowledgeSpace q₀ := by
  intro observable hobservable
  rw [mem_knowledgeSpace_iff_factorsThrough] at hobservable ⊢
  intro x y hsame
  apply hobservable
  calc
    q₁ x = forget (q₀ x) := congrFun hfactor x
    _ = forget (q₀ y) := congrArg forget hsame
    _ = q₁ y := (congrFun hfactor y).symm

/-- A two-world readout and its constant coarsening witness the quantified
domains and factorization hypothesis. -/
example :
    KnowledgeSpace (fun _ : Fin 2 => ()) ≤
      KnowledgeSpace (id : Fin 2 -> Fin 2) := by
  exact readout_coarsening_shrinks_knowledge
    (id : Fin 2 -> Fin 2) (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) rfl

#print axioms readout_coarsening_shrinks_knowledge

end D5.S3.ObserverMemory.Knowledge.ReadoutCoarseningKnowledge
