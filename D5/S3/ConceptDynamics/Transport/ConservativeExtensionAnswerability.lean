/- GID: D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Answerability of old questions is reflected and preserved by surjective pullback. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'answerability_transports_along_surjection' D5 Golden/Frozen/accepted`
     returned no matches.
   * Repository searches for `Refines`, surjective factorization, pullback, and
     answerability found `DynamicsDescent.dynamics_descends_iff`,
     `AnswerabilityCriterion.answerability_criterion`, and the nearby transport family,
     but no theorem with this pullback equivalence or its nonsurjective counterexample.
   * Pinned Mathlib contains the exact equality-reflection lemma
     `Function.Surjective.injective_comp_right`; the reverse implication reuses it.
   * The forward implication uses the same factor map and associativity of composition;
     the counterexample uses only Boolean discrimination and function extensionality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.ConservativeExtensionAnswerability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A one-state extension sees only the old Boolean state `false`. -/
def nonSurjectiveProjection : Unit -> Bool := fun _ => false

/-- The old concept in the counterexample identifies both Boolean states. -/
def constantOldConcept : Bool -> Unit := fun _ => ()

/-- Pullback along a surjective new-to-old state projection preserves and reflects
factorization of an old target through an old concept. -/
theorem answerability_transports_along_surjection
    {X Y Cval Tval : Type*}
    (p : Y -> X) (hp : Function.Surjective p)
    (C : Concept X Cval) (T : Concept X Tval) :
    Refines T C <-> Refines (T ∘ p) (C ∘ p) := by
  constructor
  · rintro ⟨factor, hfactor⟩
    refine ⟨factor, ?_⟩
    rw [hfactor]
    rfl
  · rintro ⟨factor, hfactor⟩
    refine ⟨factor, ?_⟩
    apply hp.injective_comp_right
    exact hfactor

/-- Without surjectivity, pulled-back answerability need not reflect old-state
answerability: the one-state extension cannot see the distinction in `Bool`. -/
theorem nonsurjective_pullback_can_hide_unanswerability :
    ¬Function.Surjective nonSurjectiveProjection ∧
      Refines (id ∘ nonSurjectiveProjection)
        (constantOldConcept ∘ nonSurjectiveProjection) ∧
      ¬Refines (id : Bool -> Bool) constantOldConcept := by
  constructor
  · intro hSurjective
    obtain ⟨u, hu⟩ := hSurjective true
    cases u
    cases hu
  constructor
  · refine ⟨fun _ => false, ?_⟩
    funext u
    cases u
    rfl
  · rintro ⟨factor, hfactor⟩
    have hfalse : false = factor () := by
      simpa [constantOldConcept] using congrFun hfactor false
    have htrue : true = factor () := by
      simpa [constantOldConcept] using congrFun hfactor true
    exact Bool.noConfusion (hfalse.trans htrue.symm)

example :
    Refines (id : Bool -> Bool) id <->
      Refines ((id : Bool -> Bool) ∘ id) (id ∘ id) :=
  answerability_transports_along_surjection id Function.surjective_id id id

#print axioms answerability_transports_along_surjection

end D5.S3.ConceptDynamics.Transport.ConservativeExtensionAnswerability
