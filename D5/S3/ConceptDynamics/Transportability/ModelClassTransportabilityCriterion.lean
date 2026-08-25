/- GID: D5/S3/ConceptDynamics/Transportability/ModelClassTransportabilityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transportability/ModelClassTransportabilityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transportability is empty target residual and reverse kernel inclusion. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import D5.S3.ObserverMemory.Refinement.InterfaceKernelCriterion

/- Library-search audit trail (2026-08-25):
   * Exact family hit `defectRelation` is the canonical set of state pairs
     merged by a readout and separated by a target. It constructs the source's
     transport residual directly and is imported rather than redeclared.
   * Exact observer-family hit `interface_refinement_iff_kernel_inclusion`
     gives the unique realized-image computation criterion and reverse equality-
     kernel inclusion. It is applied directly below.
   * `target_recovery_criterion` contains adjacent whole-codomain recovery and
     empty-defect clauses but requires an inhabited model type and does not state
     the source's unique realized-image computation clause.
   * Pinned Mathlib exact hits `Set.eq_empty_iff_forall_notMem`, `Setoid.ker_def`,
     and `Set.rangeFactorization` support the residual/kernel bridge. No theorem
     packages both public equivalences on arbitrary carrier types. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transportability.ModelClassTransportabilityCriterion

open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ObserverMemory.Refinement.InterfaceKernelCriterion

/-- A target has one unique computation on the realized evidence image exactly
when no two models share all evidence while differing on the target. This is
equivalent to inclusion of the evidence equality kernel in the target kernel. -/
theorem model_class_transportability_criterion
    {Model Evidence Target : Type*}
    (evidence : Model → Evidence) (target : Model → Target) :
    ((∃! compute : Set.range evidence → Set.range target,
        ∀ model,
          compute (Set.rangeFactorization evidence model) =
            Set.rangeFactorization target model) ↔
      defectRelation evidence target = ∅) ∧
    (defectRelation evidence target = ∅ ↔
      Setoid.ker evidence ≤ Setoid.ker target) := by
  have calculationIffKernel :
      (∃! compute : Set.range evidence → Set.range target,
          ∀ model,
            compute (Set.rangeFactorization evidence model) =
              Set.rangeFactorization target model) ↔
        Setoid.ker evidence ≤ Setoid.ker target := by
    change
      (∃! compute : Set.range evidence → Set.range target,
          ∀ model,
            compute (Set.rangeFactorization evidence model) =
              Set.rangeFactorization target model) ↔
        ∀ first second,
          evidence first = evidence second → target first = target second
    exact interface_refinement_iff_kernel_inclusion target evidence
  have residualIffKernel :
      defectRelation evidence target = ∅ ↔
        Setoid.ker evidence ≤ Setoid.ker target := by
    constructor
    · intro residualEmpty first second sameEvidence
      by_contra differentTarget
      have residualPair :
          (first, second) ∈ defectRelation evidence target :=
        ⟨sameEvidence, differentTarget⟩
      rw [residualEmpty] at residualPair
      exact residualPair
    · intro kernelInclusion
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨first, second⟩ ⟨sameEvidence, differentTarget⟩
      exact differentTarget (kernelInclusion sameEvidence)
  exact ⟨calculationIffKernel.trans residualIffKernel.symm, residualIffKernel⟩

#print axioms model_class_transportability_criterion

end D5.S3.ConceptDynamics.Transportability.ModelClassTransportabilityCriterion
