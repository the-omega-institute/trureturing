/- GID: D5/S3/ConceptDynamics/DefinitionEscape/MinimalTargetDistillation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact target distillation removes defects without over-separation. -/

import D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

/- Library-search audit trail (2026-08-23):
   * Canonical `defectRelation` supplies the under-resolution carrier and is
     reused rather than mirrored under another name.
   * `TargetClosureOperator` supplies the target join as a closure benchmark.
   * Repository search found no over-separation carrier and no theorem
     characterizing exact target distillation by equality of question algebras. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.MinimalTargetDistillation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

/-- Pairs preserved by the canonical target completion but separated by the
candidate completion. -/
def OverResidual
    {X Current Target Added : Type*}
    (current : Concept X Current) (target : Concept X Target)
    (added : Concept X Added) : Set (X × X) :=
  {pair |
    conceptJoin current target pair.1 = conceptJoin current target pair.2 ∧
    conceptJoin current added pair.1 ≠ conceptJoin current added pair.2}

/-- A candidate is exact when it induces precisely the canonical target-completion
fiber relation. -/
def ExactTargetDistillation
    {X Current Target Added : Type*}
    (current : Concept X Current) (target : Concept X Target)
    (added : Concept X Added) : Prop :=
  ∀ x y,
    conceptJoin current added x = conceptJoin current added y ↔
      conceptJoin current target x = conceptJoin current target y

/-- Exact distillation is equivalent to eliminating the canonical target defect
and eliminating target-irrelevant over-separation. -/
theorem exact_distillation_iff_defect_over_empty
    {X Current Target Added : Type*}
    (current : Concept X Current) (target : Concept X Target)
    (added : Concept X Added) :
    ExactTargetDistillation current target added ↔
      defectRelation (conceptJoin current added) target = ∅ ∧
        OverResidual current target added = ∅ := by
  constructor
  · intro exact
    constructor
    · ext pair
      constructor
      · rintro ⟨candidateEqual, targetDifferent⟩
        have targetCompletionEqual := (exact pair.1 pair.2).1 candidateEqual
        exact targetDifferent (congrArg Prod.snd targetCompletionEqual)
      · intro impossible
        exact impossible.elim
    · ext pair
      constructor
      · rintro ⟨targetCompletionEqual, candidateDifferent⟩
        exact candidateDifferent ((exact pair.1 pair.2).2 targetCompletionEqual)
      · intro impossible
        exact impossible.elim
  · rintro ⟨defectEmpty, overEmpty⟩ x y
    constructor
    · intro candidateEqual
      have currentEqual := congrArg Prod.fst candidateEqual
      have targetEqual : target x = target y := by
        by_contra targetDifferent
        have defect :
            (x, y) ∈ defectRelation (conceptJoin current added) target :=
          ⟨candidateEqual, targetDifferent⟩
        have impossible : (x, y) ∈ (∅ : Set (X × X)) := by
          rw [← defectEmpty]
          exact defect
        exact impossible.elim
      exact Prod.ext currentEqual targetEqual
    · intro targetCompletionEqual
      by_contra candidateDifferent
      have over : (x, y) ∈ OverResidual current target added :=
        ⟨targetCompletionEqual, candidateDifferent⟩
      have impossible : (x, y) ∈ (∅ : Set (X × X)) := by
        rw [← overEmpty]
        exact over
      exact impossible.elim

/-- Adjoining the target itself is the canonical exact benchmark. -/
theorem target_itself_exact_distillation
    {X Current Target : Type*}
    (current : Concept X Current) (target : Concept X Target) :
    ExactTargetDistillation current target target := by
  intro x y
  rfl

/-- Exact distillation is mutual refinement between effective candidate and target
completions. -/
theorem exact_distillation_iff_effective_birefines
    {X Current Target Added : Type*}
    (current : Concept X Current) (target : Concept X Target)
    (added : Concept X Added) :
    ExactTargetDistillation current target added ↔
      Refines (effectiveReadout (conceptJoin current added))
        (effectiveReadout (conceptJoin current target)) ∧
      Refines (effectiveReadout (conceptJoin current target))
        (effectiveReadout (conceptJoin current added)) := by
  constructor
  · intro exact
    constructor
    · apply (effective_refines_iff_fiber
        (conceptJoin current added) (conceptJoin current target)).2
      intro x y targetEqual
      exact (exact x y).2 targetEqual
    · apply (effective_refines_iff_fiber
        (conceptJoin current target) (conceptJoin current added)).2
      intro x y candidateEqual
      exact (exact x y).1 candidateEqual
  · rintro ⟨candidateFromTarget, targetFromCandidate⟩ x y
    constructor
    · exact (effective_refines_iff_fiber
        (conceptJoin current target) (conceptJoin current added)).1
          targetFromCandidate (x := x) (y := y)
    · exact (effective_refines_iff_fiber
        (conceptJoin current added) (conceptJoin current target)).1
          candidateFromTarget (x := x) (y := y)

/-- Exact target distillation has exactly the canonical target completion's
Boolean question algebra. -/
theorem exact_distillation_iff_question_algebra_eq
    {X Current Target Added : Type*}
    (current : Concept X Current) (target : Concept X Target)
    (added : Concept X Added) :
    ExactTargetDistillation current target added ↔
      AnswerableQuestions
          (effectiveReadout (conceptJoin current added)) =
        AnswerableQuestions
          (effectiveReadout (conceptJoin current target)) := by
  constructor
  · intro exact
    rcases (exact_distillation_iff_effective_birefines
      current target added).1 exact with ⟨candidateFromTarget, targetFromCandidate⟩
    apply Set.Subset.antisymm
    · exact answerable_questions_mono _ _ candidateFromTarget
    · exact answerable_questions_mono _ _ targetFromCandidate
  · intro questionAlgebraEqual
    apply (exact_distillation_iff_effective_birefines
      current target added).2
    constructor
    · apply (effective_refinement_iff_question_inclusion
        (conceptJoin current added) (conceptJoin current target)).2
      rw [questionAlgebraEqual]
    · apply (effective_refinement_iff_question_inclusion
        (conceptJoin current target) (conceptJoin current added)).2
      rw [questionAlgebraEqual]

#print axioms exact_distillation_iff_defect_over_empty
#print axioms exact_distillation_iff_question_algebra_eq

end D5.S3.ConceptDynamics.DefinitionEscape.MinimalTargetDistillation
