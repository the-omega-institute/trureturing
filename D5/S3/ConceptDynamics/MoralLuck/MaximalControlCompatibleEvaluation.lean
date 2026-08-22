/- GID: D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the maximal evaluation recoverable from a control concept. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.MoralLuck.MaximalControlCompatibleEvaluation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * The frozen family declarations `Concept` and `Refines` are exact hits for
     the source readouts and factorization order and are imported directly.
   * Repository searches found no common-coarsening quotient or its universal law.
   * Pinned Mathlib's `Setoid.sup_eq_eqvGen` identifies setoid supremum with the
     source's equivalence closure of a kernel union. `le_sup_left`, `le_sup_right`,
     `sup_le`, `Quotient.sound`, and `Quotient.lift` supply the universal proof. -/

/-- The least equivalence relation containing both evaluation equality and
control equality, represented by the supremum of their kernel setoids. -/
def fairKernel {X Evaluation Control : Type _}
    (evaluation : Concept X Evaluation) (control : Concept X Control) : Setoid X :=
  Setoid.ker evaluation ⊔ Setoid.ker control

private lemma fairKernel_eq_equivalenceClosure
    {X Evaluation Control : Type _}
    (evaluation : Concept X Evaluation) (control : Concept X Control) :
    fairKernel evaluation control = Relation.EqvGen.setoid
      (fun x y => evaluation x = evaluation y ∨ control x = control y) := by
  rw [fairKernel]
  exact Setoid.sup_eq_eqvGen _ _

/-- The fair evaluation is the quotient readout by the equivalence closure of
evaluation equality and control equality. -/
def fairEvaluation {X Evaluation Control : Type _}
    (evaluation : Concept X Evaluation) (control : Concept X Control) :
    Concept X (Quotient (fairKernel evaluation control)) :=
  fun x => Quotient.mk'' x

private noncomputable def evaluationToFair
    {X Evaluation Control : Type _} [Nonempty X]
    (evaluation : Concept X Evaluation) (control : Concept X Control)
    (value : Evaluation) : Quotient (fairKernel evaluation control) := by
  classical
  exact if h : ∃ x, evaluation x = value then
      Quotient.mk'' (Classical.choose h)
    else
      Quotient.mk'' (Classical.choice inferInstance)

private noncomputable def controlToFair
    {X Evaluation Control : Type _} [Nonempty X]
    (evaluation : Concept X Evaluation) (control : Concept X Control)
    (value : Control) : Quotient (fairKernel evaluation control) := by
  classical
  exact if h : ∃ x, control x = value then
      Quotient.mk'' (Classical.choose h)
    else
      Quotient.mk'' (Classical.choice inferInstance)

private lemma evaluationToFair_apply
    {X Evaluation Control : Type _} [Nonempty X]
    (evaluation : Concept X Evaluation) (control : Concept X Control) (x : X) :
    evaluationToFair evaluation control (evaluation x) =
      fairEvaluation evaluation control x := by
  rw [evaluationToFair, dif_pos ⟨x, rfl⟩]
  apply Quotient.sound
  apply (show Setoid.ker evaluation ≤ fairKernel evaluation control from le_sup_left)
  exact Classical.choose_spec
    (show ∃ y, evaluation y = evaluation x from ⟨x, rfl⟩)

private lemma controlToFair_apply
    {X Evaluation Control : Type _} [Nonempty X]
    (evaluation : Concept X Evaluation) (control : Concept X Control) (x : X) :
    controlToFair evaluation control (control x) =
      fairEvaluation evaluation control x := by
  rw [controlToFair, dif_pos ⟨x, rfl⟩]
  apply Quotient.sound
  apply (show Setoid.ker control ≤ fairKernel evaluation control from le_sup_right)
  exact Classical.choose_spec
    (show ∃ y, control y = control x from ⟨x, rfl⟩)

/--
The common-coarsening quotient refines both the full evaluation and the control
concept, and every concept refining both also refines this quotient.
-/
theorem maximal_control_compatible_evaluation
    {X Evaluation Control Candidate : Type _} [Nonempty X]
    (evaluation : Concept X Evaluation) (control : Concept X Control)
    (candidate : Concept X Candidate) :
    Refines (fairEvaluation evaluation control) evaluation ∧
      Refines (fairEvaluation evaluation control) control ∧
      (Refines candidate evaluation → Refines candidate control →
        Refines candidate (fairEvaluation evaluation control)) := by
  constructor
  · refine ⟨evaluationToFair evaluation control, ?_⟩
    funext x
    exact (evaluationToFair_apply evaluation control x).symm
  constructor
  · refine ⟨controlToFair evaluation control, ?_⟩
    funext x
    exact (controlToFair_apply evaluation control x).symm
  · rintro ⟨evaluationFactor, hEvaluation⟩ ⟨controlFactor, hControl⟩
    have hEvaluationKernel : Setoid.ker evaluation ≤ Setoid.ker candidate := by
      intro x y hxy
      change candidate x = candidate y
      rw [hEvaluation]
      exact congrArg evaluationFactor hxy
    have hControlKernel : Setoid.ker control ≤ Setoid.ker candidate := by
      intro x y hxy
      change candidate x = candidate y
      rw [hControl]
      exact congrArg controlFactor hxy
    have hFairKernel : fairKernel evaluation control ≤ Setoid.ker candidate :=
      sup_le hEvaluationKernel hControlKernel
    refine ⟨Quotient.lift candidate (fun x y hxy => hFairKernel hxy), ?_⟩
    funext x
    rfl

#print axioms maximal_control_compatible_evaluation

end D5.S3.ConceptDynamics.MoralLuck.MaximalControlCompatibleEvaluation
