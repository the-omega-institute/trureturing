/- GID: D5/S3/ConceptDynamics/Experiment/OffPolicyResidualIdentifiability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/OffPolicyResidualIdentifiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavior-law fiber constancy is equivalent to an empty off-policy residual. -/

import D5.S3.ConceptDynamics.Experiment.ExperimentValueIsKernelReduction

/- Library-search audit trail (2026-08-25):
   * Repository searches for `OPRes`, off-policy residuals, behavior-law
     identifiability, and target-policy laws found no existing declaration.
   * Exact family hit `residualPairs` in
     `ExperimentValueIsKernelReduction.lean` already constructs pairs that
     agree under every allowed experiment and disagree under a target readout.
     `offPolicyResidual` specializes that canonical object to one Unit-indexed
     behavior-law interface instead of redeclaring the residual relation.
   * The existing `TargetIdentifiable` definition is residual nonexistence, so
     using it as the public identifiability clause would make this theorem a
     definitional tautology. The public left side below instead states the
     source semantics directly: the target law is constant on each behavior-
     law fiber.
   * Exact repository hit `answerability_criterion.2.1` proves fiber constancy
     iff the matching defect set is empty and is applied directly. Padding the
     model type with `Option` supplies its anchor without adding a nonempty-
     model hypothesis. Exact Mathlib hit `Set.eq_empty_iff_forall_notMem`
     transfers emptiness between padded and source residual sets. -/

namespace D5.S3.ConceptDynamics.Experiment.OffPolicyResidualIdentifiability

open D5.S3.ConceptDynamics.Experiment.ExperimentValueIsKernelReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

/-- Pairs of models with the same behavior law and different target-policy
laws, constructed as the residual of the Unit-indexed behavior interface. -/
def offPolicyResidual
    {Model : Type u} {BehaviorLaw : Type v} {TargetLaw : Type w}
    (behaviorLaw : Model -> BehaviorLaw) (targetLaw : Model -> TargetLaw) :
    Set (Model × Model) :=
  residualPairs (Set.univ : Set Unit) (fun _ => behaviorLaw) targetLaw

/-- A target-policy law is identified throughout a model class by the behavior
law exactly when no two models share the behavior law while disagreeing on the
target law. The model class may be empty. -/
theorem target_policy_identifiable_iff_off_policy_residual_empty
    {Model : Type u} {BehaviorLaw : Type v} {TargetLaw : Type w}
    (behaviorLaw : Model -> BehaviorLaw) (targetLaw : Model -> TargetLaw) :
    (forall first second : Model,
      behaviorLaw first = behaviorLaw second ->
        targetLaw first = targetLaw second) ↔
      offPolicyResidual behaviorLaw targetLaw = ∅ := by
  let paddedBehavior : Option Model -> Option BehaviorLaw := Option.map behaviorLaw
  let paddedTarget : Option Model -> Option TargetLaw := Option.map targetLaw
  have paddedCriterion :=
    (D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      (none : Option Model) paddedBehavior paddedTarget).2.1
  have policyIffPadded :
      (forall first second : Model,
        behaviorLaw first = behaviorLaw second ->
          targetLaw first = targetLaw second) ↔
      (forall first second : Option Model,
        paddedBehavior first = paddedBehavior second ->
          paddedTarget first = paddedTarget second) := by
    constructor
    · intro identified first second sameBehavior
      cases first with
      | none =>
          cases second <;> simp_all [paddedBehavior, paddedTarget]
      | some first =>
          cases second with
          | none => simp_all [paddedBehavior, paddedTarget]
          | some second =>
              simp only [paddedBehavior, paddedTarget, Option.map_some,
                Option.some.injEq] at sameBehavior ⊢
              exact identified first second sameBehavior
    · intro identified first second sameBehavior
      have sameTarget := identified (some first) (some second) (by
        simpa [paddedBehavior] using sameBehavior)
      simpa [paddedTarget] using sameTarget
  have residualIffPadded :
      offPolicyResidual behaviorLaw targetLaw = ∅ ↔
        {pair : Option Model × Option Model |
          paddedBehavior pair.1 = paddedBehavior pair.2 ∧
            paddedTarget pair.1 ≠ paddedTarget pair.2} = ∅ := by
    constructor
    · intro emptyResidual
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨first, second⟩ residual
      cases first with
      | none =>
          cases second <;> simp_all [paddedBehavior, paddedTarget]
      | some first =>
          cases second with
          | none => simp_all [paddedBehavior, paddedTarget]
          | some second =>
              have originalResidual :
                  (first, second) ∈ offPolicyResidual behaviorLaw targetLaw := by
                simpa [paddedBehavior, paddedTarget, offPolicyResidual,
                  residualPairs, ResidualPair] using residual
              rw [emptyResidual] at originalResidual
              exact originalResidual
    · intro emptyPadded
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨first, second⟩ residual
      have paddedResidual :
          (some first, some second) ∈
            {pair : Option Model × Option Model |
              paddedBehavior pair.1 = paddedBehavior pair.2 ∧
                paddedTarget pair.1 ≠ paddedTarget pair.2} := by
        simpa [paddedBehavior, paddedTarget, offPolicyResidual,
          residualPairs, ResidualPair] using residual
      rw [emptyPadded] at paddedResidual
      exact paddedResidual
  rw [policyIffPadded, residualIffPadded]
  exact paddedCriterion

#print axioms offPolicyResidual
#print axioms target_policy_identifiable_iff_off_policy_residual_empty

end D5.S3.ConceptDynamics.Experiment.OffPolicyResidualIdentifiability
