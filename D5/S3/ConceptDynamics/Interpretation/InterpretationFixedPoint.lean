/- GID: D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Interpretation fixed points are relative to context; context variation can change them, while objectivity carries an invariant-factor proof. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-21):
   * `rg "formal-concept|interpretation|fixed point|fixedPoints" D5/ -g
     '*.lean'` found the repository wrappers
     `RecursiveDefinition.is_recursive_definition_iff_fixed_point` and
     `KnasterTarski.knaster_tarski_extremal_fixed_points`.
   * `rg "IsFixedPt|fixedPoints" .lake/packages/mathlib/Mathlib/Order/FixedPoints.lean`
     found `Function.IsFixedPt`, `Function.fixedPoints`, and the
     `OrderHom.lfp`/`OrderHom.gfp` API used by those wrappers.
   * `rg "context.*fixed|fixed.*context|invariant.*fixed|common.*fixed" D5
     .lake/packages/mathlib/Mathlib -g '*.lean'` found no declaration combining
     conceptual equivalence, context-relative result stability, contextual
     nonuniqueness, and an invariant-factor obligation.
   * `rg "false_ne_true" .lake/packages/mathlib/Mathlib -g '*.lean'` confirmed
     the imported Boolean separation API; the finite witness directly applies
     `Bool.false_ne_true` rather than reproving Boolean distinctness.
   * The fixed-point hits concern literal equality under an endomorphism, so
     they are not exact matches for the source's conceptual-equivalence and
     interpretation-stability definition and are not re-proved here. The
     unavailable `loogle` and `leansearch` executables were not invoked. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint

/-- The parameters relative to which an interpretation is evaluated. -/
structure InterpretationContext
    (Text ReaderAdmission Background EvaluationGoal Rule : Type*) where
  text : Text
  readerAdmission : ReaderAdmission
  background : Background
  evaluationGoal : EvaluationGoal
  interpretationRule : Rule

/-- A stage is a relative interpretation fixed point when its next concept is
conceptually equivalent to the current one and both have the same interpreted
result in the fixed context. -/
def IsRelativeInterpretationFixedPoint
    {Text ReaderAdmission Background EvaluationGoal Rule Concept Meaning : Type*}
    (conceptuallyEquivalent : Concept -> Concept -> Prop)
    (interpret :
      InterpretationContext Text ReaderAdmission Background EvaluationGoal Rule ->
        Concept -> Meaning)
    (concepts : Nat -> Concept)
    (context :
      InterpretationContext Text ReaderAdmission Background EvaluationGoal Rule)
    (n : Nat) : Prop :=
  conceptuallyEquivalent (concepts (n + 1)) (concepts n) ∧
    interpret context (concepts (n + 1)) = interpret context (concepts n)

/-- Conceptual equivalence of adjacent stages together with stability of their
interpretation reaches the corresponding relative interpretation fixed point. -/
theorem conceptual_equivalence_and_stability_reach_fixed_point
    {Text ReaderAdmission Background EvaluationGoal Rule Concept Meaning : Type*}
    (conceptuallyEquivalent : Concept -> Concept -> Prop)
    (interpret :
      InterpretationContext Text ReaderAdmission Background EvaluationGoal Rule ->
        Concept -> Meaning)
    (concepts : Nat -> Concept)
    (context :
      InterpretationContext Text ReaderAdmission Background EvaluationGoal Rule)
    (n : Nat)
    (hConcept : conceptuallyEquivalent (concepts (n + 1)) (concepts n))
    (hStable :
      interpret context (concepts (n + 1)) = interpret context (concepts n)) :
    IsRelativeInterpretationFixedPoint
      conceptuallyEquivalent interpret concepts context n :=
  And.intro hConcept hStable

/-- A finite context family used to witness that contextual fixed meanings need
not be absolutely unique. -/
abbrev BinaryInterpretationContext :=
  InterpretationContext Unit Bool Bool Bool Unit

def baselineContext : BinaryInterpretationContext where
  text := ()
  readerAdmission := false
  background := false
  evaluationGoal := false
  interpretationRule := ()

def alternateContext : BinaryInterpretationContext where
  text := ()
  readerAdmission := true
  background := true
  evaluationGoal := true
  interpretationRule := ()

/-- In the finite witness, the selected fixed meaning records admission,
background, and evaluation goal. -/
def IsBinaryFixedMeaning
    (context : BinaryInterpretationContext)
    (meaning : Bool × Bool × Bool) : Prop :=
  meaning =
    (context.readerAdmission, context.background, context.evaluationGoal)

/-- With text and interpretation rule held fixed, changing reader admission,
background, and evaluation goal can select a different fixed meaning. -/
theorem context_parameters_can_select_distinct_fixed_points :
    baselineContext.text = alternateContext.text ∧
      baselineContext.interpretationRule = alternateContext.interpretationRule ∧
      baselineContext.readerAdmission ≠ alternateContext.readerAdmission ∧
      baselineContext.background ≠ alternateContext.background ∧
      baselineContext.evaluationGoal ≠ alternateContext.evaluationGoal ∧
      IsBinaryFixedMeaning baselineContext (false, false, false) ∧
      IsBinaryFixedMeaning alternateContext (true, true, true) ∧
      (false, false, false) ≠ (true, true, true) := by
  refine ⟨rfl, rfl, Bool.false_ne_true, Bool.false_ne_true,
    Bool.false_ne_true, rfl, rfl, ?_⟩
  intro equalMeanings
  exact Bool.false_ne_true (congrArg Prod.fst equalMeanings)

/-- An objective interpretation claim is proof-carrying: every contextual fixed
meaning must have the same value under the proposed invariant-factor map. -/
def ObjectiveInterpretationClaim
    {Context Meaning Factor : Type*}
    (isFixedMeaning : Context -> Meaning -> Prop)
    (factor : Meaning -> Factor) : Prop :=
  ∃ commonFactor, ∀ context meaning, isFixedMeaning context meaning ->
    factor meaning = commonFactor

/-- Every objective interpretation claim supplies an invariant common factor
across all of its contextual fixed meanings. -/
theorem objective_claim_requires_invariant_common_factor
    {Context Meaning Factor : Type*}
    (isFixedMeaning : Context -> Meaning -> Prop)
    (factor : Meaning -> Factor)
    (claim : ObjectiveInterpretationClaim isFixedMeaning factor) :
    ∃ commonFactor, ∀ context meaning,
      isFixedMeaning context meaning -> factor meaning = commonFactor :=
  claim

#print axioms conceptual_equivalence_and_stability_reach_fixed_point
#print axioms context_parameters_can_select_distinct_fixed_points
#print axioms objective_claim_requires_invariant_common_factor

end D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
