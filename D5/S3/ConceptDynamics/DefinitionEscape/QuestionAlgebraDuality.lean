/- GID: D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective concept refinement is exactly inclusion of answerable Boolean questions. -/

import D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion

/- Library-search audit trail (2026-08-23):
   * `AnswerableTargetMonotonicity.answerable_target_monotone` gives the forward
     monotonicity direction for arbitrary target codomains.
   * `StrictRefinementCapability.strict_refinement_capability` constructs a new
     Boolean question from effective strict refinement.
   * Repository search found no converse reconstructing refinement from all
     Boolean questions, no effective-range normalization interface, and no theorem
     removing unused-coordinate surjectivity assumptions from the operational test. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.StrictRefinementCapability
open D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion

/-- The effective coordinate type removes labels that are never attained. -/
def EffectiveCoordinate {X Coordinate : Type*}
    (readout : Concept X Coordinate) : Type _ :=
  Set.range readout

/-- Every readout factors through its attained-coordinate subtype. -/
def effectiveReadout {X Coordinate : Type*}
    (readout : Concept X Coordinate) :
    Concept X (EffectiveCoordinate readout) :=
  fun state => ⟨readout state, ⟨state, rfl⟩⟩

/-- Effective normalization is surjective by construction. -/
theorem effectiveReadout_surjective
    {X Coordinate : Type*} (readout : Concept X Coordinate) :
    Function.Surjective (effectiveReadout readout) := by
  rintro ⟨coordinate, state, hstate⟩
  refine ⟨state, ?_⟩
  apply Subtype.ext
  exact hstate

/-- Effective normalization preserves exactly the original readout fibers. -/
theorem effectiveReadout_eq_iff
    {X Coordinate : Type*} (readout : Concept X Coordinate) (x y : X) :
    effectiveReadout readout x = effectiveReadout readout y ↔
      readout x = readout y := by
  constructor
  · exact fun equality => congrArg Subtype.val equality
  · exact fun equality => Subtype.ext equality

/-- Between effective readouts, factorization is exactly fiber implication. -/
theorem effective_refines_iff_fiber
    {X Coarse Fine : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine) :
    Refines (effectiveReadout coarse) (effectiveReadout fine) ↔
      ∀ ⦃x y : X⦄, fine x = fine y → coarse x = coarse y := by
  classical
  constructor
  · rintro ⟨factor, factors⟩ x y fineEqual
    have normalizedFineEqual :
        effectiveReadout fine x = effectiveReadout fine y :=
      Subtype.ext fineEqual
    have normalizedCoarseEqual :
        effectiveReadout coarse x = effectiveReadout coarse y := by
      rw [factors]
      exact congrArg factor normalizedFineEqual
    exact congrArg Subtype.val normalizedCoarseEqual
  · intro fiberImplication
    let chooseState : EffectiveCoordinate fine → X :=
      fun coordinate => Classical.choose coordinate.property
    let factor : EffectiveCoordinate fine → EffectiveCoordinate coarse :=
      fun coordinate => effectiveReadout coarse (chooseState coordinate)
    refine ⟨factor, ?_⟩
    funext state
    change effectiveReadout coarse state = factor (effectiveReadout fine state)
    apply Subtype.ext
    change coarse state = coarse (chooseState (effectiveReadout fine state))
    apply fiberImplication
    exact (Classical.choose_spec (effectiveReadout fine state).property).symm

/-- Boolean questions answerable by a concept form its operational question algebra. -/
def AnswerableQuestions {X Coordinate : Type*}
    (readout : Concept X Coordinate) : Set (Concept X Bool) :=
  {question | Refines question readout}

/-- Constant questions are answerable through every concept. -/
theorem constant_question_answerable
    {X Coordinate : Type*} (readout : Concept X Coordinate) (value : Bool) :
    (fun _ : X => value) ∈ AnswerableQuestions readout := by
  exact ⟨fun _ => value, rfl⟩

/-- Answerable questions are closed under Boolean negation. -/
theorem answerable_not
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    {question : Concept X Bool} (answerable : question ∈ AnswerableQuestions readout) :
    (fun state => !(question state)) ∈ AnswerableQuestions readout := by
  rcases answerable with ⟨answer, factors⟩
  refine ⟨fun coordinate => !(answer coordinate), ?_⟩
  funext state
  rw [factors]
  rfl

/-- Answerable questions are closed under Boolean conjunction. -/
theorem answerable_and
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    {left right : Concept X Bool}
    (leftAnswerable : left ∈ AnswerableQuestions readout)
    (rightAnswerable : right ∈ AnswerableQuestions readout) :
    (fun state => left state && right state) ∈ AnswerableQuestions readout := by
  rcases leftAnswerable with ⟨leftAnswer, leftFactors⟩
  rcases rightAnswerable with ⟨rightAnswer, rightFactors⟩
  refine ⟨fun coordinate => leftAnswer coordinate && rightAnswer coordinate, ?_⟩
  funext state
  rw [leftFactors, rightFactors]
  rfl

/-- Answerable questions are closed under Boolean disjunction. -/
theorem answerable_or
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    {left right : Concept X Bool}
    (leftAnswerable : left ∈ AnswerableQuestions readout)
    (rightAnswerable : right ∈ AnswerableQuestions readout) :
    (fun state => left state || right state) ∈ AnswerableQuestions readout := by
  rcases leftAnswerable with ⟨leftAnswer, leftFactors⟩
  rcases rightAnswerable with ⟨rightAnswer, rightFactors⟩
  refine ⟨fun coordinate => leftAnswer coordinate || rightAnswer coordinate, ?_⟩
  funext state
  rw [leftFactors, rightFactors]
  rfl

/-- Refinement monotonically enlarges the operational question algebra. -/
theorem answerable_questions_mono
    {X Coarse Fine : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine)
    (refinement : Refines coarse fine) :
    AnswerableQuestions coarse ⊆ AnswerableQuestions fine := by
  intro question answerable
  rcases answerable with ⟨answer, questionFactors⟩
  rcases refinement with ⟨factor, refinementFactors⟩
  refine ⟨answer ∘ factor, ?_⟩
  funext state
  change question state = answer (factor (fine state))
  calc
    question state = answer (coarse state) := congrFun questionFactors state
    _ = answer (factor (fine state)) :=
      congrArg answer (congrFun refinementFactors state)

/-- For effective readouts, inclusion of all answerable Boolean questions is not
merely a consequence of refinement; it completely reconstructs refinement. -/
theorem effective_refinement_iff_question_inclusion
    {X Coarse Fine : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine) :
    Refines (effectiveReadout coarse) (effectiveReadout fine) ↔
      AnswerableQuestions (effectiveReadout coarse) ⊆
        AnswerableQuestions (effectiveReadout fine) := by
  classical
  constructor
  · exact answerable_questions_mono
      (effectiveReadout coarse) (effectiveReadout fine)
  · intro inclusion
    apply (effective_refines_iff_fiber coarse fine).2
    intro x y fineEqual
    by_contra coarseDifferent
    let question : Concept X Bool :=
      fun state => decide (coarse state = coarse x)
    have coarseAnswerable :
        question ∈ AnswerableQuestions (effectiveReadout coarse) := by
      refine ⟨fun coordinate => decide (coordinate.1 = coarse x), ?_⟩
      funext state
      rfl
    rcases inclusion coarseAnswerable with ⟨answer, answerFactors⟩
    have normalizedFineEqual :
        effectiveReadout fine x = effectiveReadout fine y :=
      Subtype.ext fineEqual
    have questionEqual : question x = question y := by
      rw [answerFactors]
      exact congrArg answer normalizedFineEqual
    have impossible : (true : Bool) = false := by
      simpa [question, coarseDifferent, Ne.symm coarseDifferent] using questionEqual
    exact Bool.noConfusion impossible

/-- Effective strict refinement is exactly strict growth of the Boolean question
algebra, witnessed by one newly answerable question. -/
theorem strict_effective_refinement_iff_new_question
    {X Coarse Fine : Type*}
    (coarse : Concept X Coarse) (fine : Concept X Fine) :
    StrictRefinement (effectiveReadout coarse) (effectiveReadout fine) ↔
      (AnswerableQuestions (effectiveReadout coarse) ⊆
          AnswerableQuestions (effectiveReadout fine)) ∧
        ∃ question : Concept X Bool,
          question ∈ AnswerableQuestions (effectiveReadout fine) ∧
          question ∉ AnswerableQuestions (effectiveReadout coarse) := by
  classical
  constructor
  · intro strict
    constructor
    · exact answerable_questions_mono
        (effectiveReadout coarse) (effectiveReadout fine) strict.1
    · rcases (strict_refinement_capability
        (U := Bool) (effectiveReadout coarse) (effectiveReadout fine)
        (effectiveReadout_surjective coarse)
        (effectiveReadout_surjective fine) strict
        ⟨false, true, Bool.false_ne_true⟩).1 with
        ⟨question, uniqueFineAnswer, noCoarseAnswer⟩
      rcases uniqueFineAnswer with ⟨answer, answerFactors, _⟩
      exact ⟨question, ⟨answer, answerFactors⟩, noCoarseAnswer⟩
  · rintro ⟨inclusion, ⟨question, fineAnswerable, notCoarseAnswerable⟩⟩
    have refinement :
        Refines (effectiveReadout coarse) (effectiveReadout fine) :=
      (effective_refinement_iff_question_inclusion coarse fine).2 inclusion
    refine ⟨refinement, ?_⟩
    intro reverseRefinement
    exact notCoarseAnswerable
      (answerable_questions_mono
        (effectiveReadout fine) (effectiveReadout coarse)
        reverseRefinement fineAnswerable)

/-- Target inadequacy is strict effective refinement by adjoining the target. -/
theorem target_inadequate_iff_effective_join_strict
    {X Latent Target : Type*} [Nonempty X]
    (latent : Concept X Latent) (target : Concept X Target) :
    (¬TargetAdequate latent target) ↔
      StrictRefinement (effectiveReadout latent)
        (effectiveReadout (conceptJoin latent target)) := by
  constructor
  · intro inadequate
    constructor
    · apply (effective_refines_iff_fiber latent (conceptJoin latent target)).2
      intro x y joinedEqual
      exact congrArg Prod.fst joinedEqual
    · intro reverseRefinement
      apply inadequate
      apply (target_adequate_iff_fiber_constant latent target).2
      intro x y latentEqual
      have joinedEqual :=
        (effective_refines_iff_fiber (conceptJoin latent target) latent).1
          reverseRefinement latentEqual
      exact congrArg Prod.snd joinedEqual
  · rintro ⟨_, noReverse⟩ adequate
    apply noReverse
    apply (effective_refines_iff_fiber (conceptJoin latent target) latent).2
    intro x y latentEqual
    apply Prod.ext latentEqual
    exact (target_adequate_iff_fiber_constant latent target).1
      adequate latentEqual

/-- Range normalization removes the earlier product-surjectivity assumption:
latent inadequacy automatically creates a Boolean question on attained joined
coordinates that is unavailable on attained latent coordinates. -/
theorem target_inadequate_iff_effective_new_question
    {X Latent Target : Type*} [Nonempty X]
    (latent : Concept X Latent) (target : Concept X Target) :
    (¬TargetAdequate latent target) ↔
      ∃ question : X → Bool,
        (∃! answer : EffectiveCoordinate (conceptJoin latent target) → Bool,
          question = answer ∘ effectiveReadout (conceptJoin latent target)) ∧
        ¬∃ answer : EffectiveCoordinate latent → Bool,
          question = answer ∘ effectiveReadout latent := by
  classical
  constructor
  · intro inadequate
    have strict :=
      (target_inadequate_iff_effective_join_strict latent target).1 inadequate
    exact (strict_refinement_capability
      (U := Bool)
      (effectiveReadout latent)
      (effectiveReadout (conceptJoin latent target))
      (effectiveReadout_surjective latent)
      (effectiveReadout_surjective (conceptJoin latent target))
      strict ⟨false, true, Bool.false_ne_true⟩).1
  · rintro ⟨question, uniqueFineAnswer, noCoarseAnswer⟩
    rcases uniqueFineAnswer with ⟨answer, answerFactors, _⟩
    have coarseRefinesFine :
        Refines (effectiveReadout latent)
          (effectiveReadout (conceptJoin latent target)) := by
      apply (effective_refines_iff_fiber latent (conceptJoin latent target)).2
      intro x y joinedEqual
      exact congrArg Prod.fst joinedEqual
    have strict :
        StrictRefinement (effectiveReadout latent)
          (effectiveReadout (conceptJoin latent target)) :=
      (strict_effective_refinement_iff_new_question
        latent (conceptJoin latent target)).2
        ⟨answerable_questions_mono
            (effectiveReadout latent)
            (effectiveReadout (conceptJoin latent target))
            coarseRefinesFine,
          ⟨question, ⟨answer, answerFactors⟩, noCoarseAnswer⟩⟩
    exact (target_inadequate_iff_effective_join_strict latent target).2 strict

example :
    AnswerableQuestions (effectiveReadout (id : Concept Bool Bool)) =
      Set.univ := by
  ext question
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨fun coordinate => question coordinate.1, by funext state; rfl⟩

#print axioms effective_refinement_iff_question_inclusion
#print axioms strict_effective_refinement_iff_new_question
#print axioms target_inadequate_iff_effective_new_question

end D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
