/- GID: D5/S3/ConceptDynamics/StrictRefinementCapability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/StrictRefinementCapability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective strict refinement creates a new question and a new differentiating policy. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `ConceptJoinUniversal.Refines` is the established
     factorization order and is used directly in the strictness definition.
   * Pinned Mathlib's `Function.factorsThrough_iff` is adjacent, but does not
     construct both requested separating maps or their unique factors.
   * Searches for strict refinement capability, separating questions, and
     differentiating policies found no declaration packaging both clauses;
     searches for a surjective unique-factor lemma also missed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.StrictRefinementCapability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A readout is strictly finer when it refines the coarse readout and the
coarse readout does not refine it back. -/
def StrictRefinement {X C D : Type*} (q_C : Concept X C) (q_D : Concept X D) : Prop :=
  Refines q_C q_D ∧ ¬Refines q_D q_C

/-- Effective strict refinement produces both a Boolean question and a policy
that factor uniquely through the finer readout but do not factor through the
coarser one. -/
theorem strict_refinement_capability
    {X C D U : Type*} (q_C : Concept X C) (q_D : Concept X D)
    (effective_C : Function.Surjective q_C)
    (effective_D : Function.Surjective q_D)
    (strict : StrictRefinement q_C q_D)
    (distinctActions : ∃ u₀ u₁ : U, u₀ ≠ u₁) :
    (∃ question : X → Bool,
      (∃! answer : D → Bool, question = answer ∘ q_D) ∧
        ¬∃ answer : C → Bool, question = answer ∘ q_C) ∧
      ∃ policy : X → U,
        (∃! action : D → U, policy = action ∘ q_D) ∧
          ¬∃ action : C → U, policy = action ∘ q_C := by
  classical
  rcases strict with ⟨_, hnotReverse⟩
  obtain ⟨x, y, hsame, hdifferent⟩ :
      ∃ x y : X, q_C x = q_C y ∧ q_D x ≠ q_D y := by
    by_contra hnone
    apply hnotReverse
    have hfiber : ∀ ⦃left right : X⦄,
        q_C left = q_C right → q_D left = q_D right := by
      intro left right hequal
      by_contra hdifferent
      exact hnone ⟨left, right, hequal, hdifferent⟩
    let factor : C → D := fun coordinate =>
      q_D (Classical.choose (effective_C coordinate))
    refine ⟨factor, ?_⟩
    funext state
    unfold Function.comp
    simp only [factor]
    exact hfiber (Classical.choose_spec (effective_C (q_C state))).symm
  constructor
  · let answer_D : D → Bool := fun coordinate =>
      if coordinate = q_D x then false else true
    let question : X → Bool := answer_D ∘ q_D
    have hquestion : question x ≠ question y := by
      unfold question Function.comp
      simpa [answer_D, hdifferent, hdifferent.symm] using Bool.false_ne_true
    refine ⟨question, ?_, ?_⟩
    · refine ⟨answer_D, rfl, ?_⟩
      intro other hother
      funext coordinate
      obtain ⟨state, hstate⟩ := effective_D coordinate
      calc
        other coordinate = other (q_D state) := congrArg other hstate.symm
        _ = question state := by
          have hpoint := (congrFun hother state).symm
          unfold Function.comp at hpoint
          exact hpoint
        _ = answer_D (q_D state) := by
          rfl
        _ = answer_D coordinate := congrArg answer_D hstate
    · rintro ⟨answer_C, hanswer_C⟩
      apply hquestion
      calc
        question x = answer_C (q_C x) := by
          have hpoint := congrFun hanswer_C x
          unfold Function.comp at hpoint
          exact hpoint
        _ = answer_C (q_C y) := congrArg answer_C hsame
        _ = question y := by
          have hpoint := (congrFun hanswer_C y).symm
          unfold Function.comp at hpoint
          exact hpoint
  · obtain ⟨u₀, u₁, hactions⟩ := distinctActions
    let action_D : D → U := fun coordinate =>
      if coordinate = q_D x then u₀ else u₁
    let policy : X → U := action_D ∘ q_D
    have hpolicy : policy x ≠ policy y := by
      unfold policy Function.comp
      simpa [action_D, hdifferent, hdifferent.symm] using hactions
    refine ⟨policy, ?_, ?_⟩
    · refine ⟨action_D, rfl, ?_⟩
      intro other hother
      funext coordinate
      obtain ⟨state, hstate⟩ := effective_D coordinate
      calc
        other coordinate = other (q_D state) := congrArg other hstate.symm
        _ = policy state := by
          have hpoint := (congrFun hother state).symm
          unfold Function.comp at hpoint
          exact hpoint
        _ = action_D (q_D state) := by
          rfl
        _ = action_D coordinate := congrArg action_D hstate
    · rintro ⟨action_C, haction_C⟩
      apply hpolicy
      calc
        policy x = action_C (q_C x) := by
          have hpoint := congrFun haction_C x
          unfold Function.comp at hpoint
          exact hpoint
        _ = action_C (q_C y) := congrArg action_C hsame
        _ = policy y := by
          have hpoint := (congrFun haction_C y).symm
          unfold Function.comp at hpoint
          exact hpoint

/-- Constant and identity readouts witness satisfiability of effective strict
refinement. -/
example :
    ∃ (q_C : Bool → Unit) (q_D : Bool → Bool),
      Function.Surjective q_C ∧ Function.Surjective q_D ∧
        StrictRefinement q_C q_D := by
  refine ⟨fun _ => (), id, ?_, Function.surjective_id, ?_⟩
  · intro coordinate
    exact ⟨false, Subsingleton.elim _ _⟩
  · constructor
    · exact ⟨fun _ => (), rfl⟩
    · rintro ⟨factor, hfactor⟩
      apply Bool.false_ne_true
      calc
        false = factor () := by
          simpa only [Function.comp_apply, id_eq] using congrFun hfactor false
        _ = true := by
          simpa only [Function.comp_apply, id_eq] using (congrFun hfactor true).symm

#print axioms strict_refinement_capability

end D5.S3.ConceptDynamics.StrictRefinementCapability
