/- GID: D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target recovery is exactly constancy on process fibers and absence of target defects. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-23):
   * Exact repository hit
     `D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion`
     packages whole-codomain factorization, fiber constancy, and emptiness of the
     same collision relation. It is applied directly below.
   * Exact family hits `Concept` and `defectRelation` are imported rather than
     redeclared; the latter constructs the source's target-sensitive loss set.
   * Exact pinned-Mathlib hit `Function.factorsThrough_iff` is applied by the
     imported criterion. Its whole-codomain converse requires a nonempty target;
     the public inhabited-state hypothesis supplies one through `target`.
   * `MoralLuckDescent.moral_luck_descent_iff` is a finite moral-evaluation
     specialization. `UniversalSufficiencyFactorization` factors a canonical
     image-valued target. Neither is the exact arbitrary recovery criterion here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- On an inhabited state space, a target can be recovered from a process
readout exactly when the process is constant on target values within each
fiber, equivalently when its target defect is empty. Failure of recovery is
therefore exactly the existence of two merged states with different targets. -/
theorem target_recovery_criterion
    {X ProcessState Target : Type*} [Nonempty X]
    (process : Concept X ProcessState) (target : Concept X Target) :
    ((∃ recover : ProcessState → Target, target = recover ∘ process) ↔
      ∀ ⦃x y : X⦄, process x = process y → target x = target y) ∧
    ((∀ ⦃x y : X⦄, process x = process y → target x = target y) ↔
      defectRelation process target = ∅) ∧
    (defectRelation process target = ∅ ↔
      ∃ recover : ProcessState → Target, target = recover ∘ process) ∧
    ((¬∃ recover : ProcessState → Target, target = recover ∘ process) ↔
      (defectRelation process target).Nonempty) := by
  let anchor : X := Classical.choice (inferInstance : Nonempty X)
  have criterion :=
    D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      anchor process target
  have fiberCriterion :
      (∀ ⦃x y : X⦄, process x = process y → target x = target y) ↔
        defectRelation process target = ∅ := by
    simpa only [defectRelation] using criterion.2.1
  have factorCriterion :
      (∃ recover : ProcessState → Target, target = recover ∘ process) ↔
        ∀ ⦃x y : X⦄, process x = process y → target x = target y := by
    constructor
    · exact criterion.1.mp
    · exact criterion.1.mpr
  have emptyCriterion :
      defectRelation process target = ∅ ↔
        ∃ recover : ProcessState → Target, target = recover ∘ process := by
    constructor
    · intro emptyDefect
      apply criterion.2.2.mp
      simpa only [defectRelation] using emptyDefect
    · intro recovery
      have emptyDefect := criterion.2.2.mpr recovery
      simpa only [defectRelation] using emptyDefect
  refine ⟨factorCriterion, fiberCriterion, emptyCriterion, ?_⟩
  exact (not_congr emptyCriterion).symm.trans
    Set.nonempty_iff_ne_empty.symm

/-- Identity readouts provide a recoverable instance of the public criterion. -/
example :
    ∃ recover : Bool → Bool,
      (id : Concept Bool Bool) = recover ∘ (id : Concept Bool Bool) := by
  exact (target_recovery_criterion (id : Concept Bool Bool)
    (id : Concept Bool Bool)).1.mpr (fun _ _ equality => equality)

/-- A constant process merges two states separated by the identity target, so
the target is not recoverable and the canonical defect is nonempty. -/
example :
    (¬∃ recover : Unit → Bool,
      (id : Concept Bool Bool) = recover ∘ (fun _ : Bool => ())) ∧
    (defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
  have defect :
      (defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  exact ⟨(target_recovery_criterion (fun _ : Bool => ())
    (id : Concept Bool Bool)).2.2.2.mpr defect, defect⟩

#print axioms target_recovery_criterion

end D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
