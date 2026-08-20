/- GID: D5/S3/ConceptDynamics/ContextRefinementConflictSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ContextRefinementConflictSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A refinement separates opposite support hidden by one coarse context. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-21):
   * `rg -n 'context.*conflict|coarse.*conflict|support.*fiber|P x.*¬ P y'
     D5 --glob '*.lean'` found no contextual-conflict theorem.
   * `rg -n 'conceptJoin.*≠|q_C x = q_C y' D5 --glob '*.lean'` found the
     canonical product readout and one private separating-pair argument, but no
     theorem exposing the source's joined-fiber and contextual-support clauses.
   * Pinned Mathlib provides `Function.Fiber`, while searches for a theorem
     combining fiber separation with opposite predicate support found no hit.
   * The canonical `Concept` and `conceptJoin` declarations are imported and
     applied directly; no sibling context or refinement types are redeclared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ContextRefinementConflictSeparation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Opposite support in one coarse coordinate is separated into distinct
refinement coordinates by the canonical joined readout. -/
theorem context_refinement_separates_conflict
    {X C D : Type*} (q_C : Concept X C) (q_D : Concept X D)
    (support : X → Prop) {x y : X}
    (sameCoarse : q_C x = q_C y)
    (positive : support x) (negative : ¬support y)
    (separated : q_D x ≠ q_D y) :
    conceptJoin q_C q_D x ≠ conceptJoin q_C q_D y ∧
      (¬∃ joinedContext : C × D,
        conceptJoin q_C q_D x = joinedContext ∧ support x ∧
          conceptJoin q_C q_D y = joinedContext ∧ ¬support y) ∧
      (∃ positiveContext negativeContext : D,
        positiveContext ≠ negativeContext ∧
          q_D x = positiveContext ∧ support x ∧
          q_D y = negativeContext ∧ ¬support y) ∧
      ∃ coarseContext : C, ∃ positiveContext negativeContext : D,
        positiveContext ≠ negativeContext ∧
          q_C x = coarseContext ∧ q_D x = positiveContext ∧ support x ∧
          q_C y = coarseContext ∧ q_D y = negativeContext ∧ ¬support y := by
  have joinedSeparated : conceptJoin q_C q_D x ≠ conceptJoin q_C q_D y := by
    intro joinedEqual
    exact separated (congrArg Prod.snd joinedEqual)
  refine ⟨joinedSeparated, ?_, ?_, ?_⟩
  · rintro ⟨joinedContext, hx, _, hy, _⟩
    exact joinedSeparated (hx.trans hy.symm)
  · exact ⟨q_D x, q_D y, separated, rfl, positive, rfl, negative⟩
  · exact ⟨q_C x, q_D x, q_D y, separated, rfl, rfl, positive,
      sameCoarse.symm, rfl, negative⟩

/-- A two-state model witnesses satisfiability of every source hypothesis. -/
example :
    ∃ (q_C : Concept Bool Unit) (q_D : Concept Bool Bool)
        (support : Bool → Prop) (x y : Bool),
      q_C x = q_C y ∧ support x ∧ ¬support y ∧ q_D x ≠ q_D y := by
  exact ⟨fun _ => (), id, fun state => state = false, false, true,
    rfl, rfl, by decide, by decide⟩

#print axioms context_refinement_separates_conflict

end D5.S3.ConceptDynamics.ContextRefinementConflictSeparation
