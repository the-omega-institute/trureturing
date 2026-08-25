/- GID: D5/S3/ConceptDynamics/Coding/ProductiveDiagonalEscapeCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ProductiveDiagonalEscapeCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A diagonal catalog escape is productive iff it creates a new question. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `escaped_of_fixedPointFree` proves that a fixed-point-free
     twisted diagonal lies outside every supplied catalog range.
   * Exact repository hit `diagonal_novelty_need_not_add_world_information` proves the
     negative direction when escaped semantics already factors through the current
     concept.
   * `QuestionAlgebraDuality` supplies effective-range normalization and the exact
     operational criterion. No raw product-surjectivity hypothesis remains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ProductiveDiagonalEscapeCriterion

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.StrictRefinementCapability
open D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

/-- A catalog escape is productive when it is absent from the old catalog and its
world semantics strictly refines the current concept. The definition keeps
representational novelty and semantic information growth as separate conjuncts. -/
def ProductiveCatalogEscape
    {Address Symbol World CurrentInfo ExpressionInfo : Type*}
    (catalog : Address → Address → Symbol)
    (current : Concept World CurrentInfo)
    (expressionSemantics : (Address → Symbol) → Concept World ExpressionInfo)
    (candidate : Address → Symbol) : Prop :=
  candidate ∉ Set.range catalog ∧
    StrictRefinement current
      (conceptJoin current (expressionSemantics candidate))

/-- Under a fixed-point-free twist, the canonical diagonal is a productive catalog
escape exactly when its world semantics is inadequate as a target of the current
concept. Diagonalization settles catalog novelty; target inadequacy settles semantic
growth. -/
theorem productive_diagonal_escape_iff_target_inadequate
    {Address Symbol World CurrentInfo ExpressionInfo : Type*}
    (twist : Symbol → Symbol) (catalog : Address → Address → Symbol)
    (current : Concept World CurrentInfo)
    (expressionSemantics : (Address → Symbol) → Concept World ExpressionInfo)
    (fixedPointFree : ∀ symbol, twist symbol ≠ symbol) :
    ProductiveCatalogEscape catalog current expressionSemantics
        (diagonal twist catalog) ↔
      ¬TargetAdequate current
        (expressionSemantics (diagonal twist catalog)) := by
  constructor
  · intro productive
    exact (latent_join_strict_iff_inadequate current
      (expressionSemantics (diagonal twist catalog))).mp productive.2
  · intro inadequate
    exact ⟨escaped_of_fixedPointFree twist fixedPointFree catalog,
      (latent_join_strict_iff_inadequate current
        (expressionSemantics (diagonal twist catalog))).mpr inadequate⟩

/-- Productive diagonal escape is strict growth of the effective Boolean question
algebra. The first conjunct is inclusion; the second supplies an explicit newly
answerable question. -/
theorem productive_diagonal_escape_iff_question_algebra_growth
    {Address Symbol World CurrentInfo ExpressionInfo : Type*} [Nonempty World]
    (twist : Symbol → Symbol) (catalog : Address → Address → Symbol)
    (current : Concept World CurrentInfo)
    (expressionSemantics : (Address → Symbol) → Concept World ExpressionInfo)
    (fixedPointFree : ∀ symbol, twist symbol ≠ symbol) :
    ProductiveCatalogEscape catalog current expressionSemantics
        (diagonal twist catalog) ↔
      (AnswerableQuestions (effectiveReadout current) ⊆
        AnswerableQuestions (effectiveReadout
          (conceptJoin current
            (expressionSemantics (diagonal twist catalog))))) ∧
      ∃ question : World → Bool,
        question ∈ AnswerableQuestions (effectiveReadout
          (conceptJoin current
            (expressionSemantics (diagonal twist catalog)))) ∧
        question ∉ AnswerableQuestions (effectiveReadout current) := by
  rw [productive_diagonal_escape_iff_target_inadequate
    twist catalog current expressionSemantics fixedPointFree]
  rw [target_inadequate_iff_effective_join_strict]
  exact strict_effective_refinement_iff_new_question
    current (conceptJoin current
      (expressionSemantics (diagonal twist catalog)))

/-- Main criterion. Effective-range normalization removes the earlier assumption
that every raw product coordinate is attained. A fixed-point-free diagonal is
productive exactly when it creates a Boolean question uniquely answerable on the
attained joined coordinates and unavailable on the attained current coordinates. -/
theorem productive_diagonal_escape_iff_new_question
    {Address Symbol World CurrentInfo ExpressionInfo : Type*} [Nonempty World]
    (twist : Symbol → Symbol) (catalog : Address → Address → Symbol)
    (current : Concept World CurrentInfo)
    (expressionSemantics : (Address → Symbol) → Concept World ExpressionInfo)
    (fixedPointFree : ∀ symbol, twist symbol ≠ symbol) :
    ProductiveCatalogEscape catalog current expressionSemantics
        (diagonal twist catalog) ↔
      ∃ question : World → Bool,
        (∃! answer : EffectiveCoordinate
            (conceptJoin current
              (expressionSemantics (diagonal twist catalog))) → Bool,
          question = answer ∘ effectiveReadout
            (conceptJoin current
              (expressionSemantics (diagonal twist catalog)))) ∧
        ¬∃ answer : EffectiveCoordinate current → Bool,
          question = answer ∘ effectiveReadout current := by
  exact (productive_diagonal_escape_iff_target_inadequate
    twist catalog current expressionSemantics fixedPointFree).trans
      (target_inadequate_iff_effective_new_question current
        (expressionSemantics (diagonal twist catalog)))

/-- Boolean negation, a one-row catalog, a constant current readout, and identity
world semantics give a concrete productive diagonal escape. -/
example :
    let twist : Bool → Bool := fun symbol => !symbol
    let catalog : Unit → Unit → Bool := fun _ _ => true
    let current : Concept Bool Unit := fun _ => ()
    let expressionSemantics : (Unit → Bool) → Concept Bool Bool := fun _ => id
    ProductiveCatalogEscape catalog current expressionSemantics
      (diagonal twist catalog) := by
  dsimp [ProductiveCatalogEscape]
  constructor
  · exact escaped_of_fixedPointFree (fun symbol : Bool => !symbol) (by decide)
      (fun _ : Unit => fun _ : Unit => true)
  · apply (latent_join_strict_iff_inadequate
      (fun _ : Bool => ()) (id : Concept Bool Bool)).mpr
    rintro ⟨decode, factors⟩
    apply Bool.false_ne_true
    calc
      false = decode () := by
        simpa only [Function.comp_apply, id_eq] using congrFun factors false
      _ = true := by
        simpa only [Function.comp_apply, id_eq] using
          (congrFun factors true).symm

#print axioms productive_diagonal_escape_iff_target_inadequate
#print axioms productive_diagonal_escape_iff_question_algebra_growth
#print axioms productive_diagonal_escape_iff_new_question

end D5.S3.ConceptDynamics.Coding.ProductiveDiagonalEscapeCriterion
