/- GID: D5/S3/ConceptDynamics/Governance/InformationRefinementGovernance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/InformationRefinementGovernance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Information refinement expands answerability, policy capability, and sensitive leakage. -/

import D5.S3.ConceptDynamics.Answering.AnswerableTargetMonotonicity
import D5.S3.ConceptDynamics.Disclosure.SensitiveLeakageMonotonicity
import D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity

/- Library-search audit trail (2026-09-01):
   * Exact repository hits `answerable_target_monotone`,
     `policy_capability_monotone`, and `sensitive_leakage_monotone` prove the
     three source clauses separately. They are applied directly below rather
     than reproved or hidden behind duplicate family primitives.
   * The source's preceding summary clauses already have canonical deposits:
     `truthfulness_sufficiency_independence` separates literal truth from target
     sufficiency, while `equal_content_does_not_determine_admission` separates
     equal outcomes from provenance-sensitive status.
   * The only in-flight ConceptDynamics delta was
     `origin/lane/math/m433catchup`; its relevant declarations have the same
     component theorem names and contain no three-clause composition theorem.
   * Pinned Mathlib provides `Function.factorsThrough_iff` and
     `Set.range_comp_subset_range`, which underlie the imported component
     proofs. No pinned-library theorem states this domain-specific conjunction.
     The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.InformationRefinementGovernance

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Answering.AnswerableTargetMonotonicity
open D5.S3.ConceptDynamics.Disclosure.SensitiveLeakageMonotonicity
open D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity

/-- Refining an information interface simultaneously preserves every old
answerable target, every old implementable policy, and the sensitive component
of its joint readout. -/
theorem information_refinement_expands_answers_policies_and_leakage
    {X C D Y U S : Type*}
    (q_C : Concept X C) (q_D : Concept X D) (sensitive : Concept X S)
    (refinement : Refines q_C q_D) :
    AnswerableTargets (Y := Y) q_C ⊆ AnswerableTargets (Y := Y) q_D ∧
      policyCapability q_C U ⊆ policyCapability q_D U ∧
      Refines (conceptJoin q_C sensitive) (conceptJoin q_D sensitive) := by
  exact ⟨answerable_target_monotone q_C q_D refinement,
    policy_capability_monotone q_C q_D refinement,
    sensitive_leakage_monotone q_C q_D sensitive refinement⟩

/-- A constant Boolean interface refined by the identity interface is a
concrete positive instance. The coarse values agree at `false` and `true`,
while the refined values are numerically distinct. -/
example :
    let coarse : Concept Bool Unit := fun _ => ()
    let fine : Concept Bool Bool := id
    let sensitive : Concept Bool Bool := id
    coarse false = coarse true ∧
      fine false ≠ fine true ∧
      (AnswerableTargets (Y := Bool) coarse ⊆ AnswerableTargets (Y := Bool) fine ∧
        policyCapability coarse Bool ⊆ policyCapability fine Bool ∧
        Refines (conceptJoin coarse sensitive) (conceptJoin fine sensitive)) := by
  dsimp
  refine ⟨rfl, Bool.false_ne_true, ?_⟩
  apply information_refinement_expands_answers_policies_and_leakage
  exact ⟨fun _ => (), rfl⟩

/-- Reversing the same concrete interfaces breaks the refinement premise and
the policy-capability clause: the identity policy distinguishes `false` and
`true`, whereas every policy through the constant interface gives them the
same value. -/
example :
    let fine : Concept Bool Bool := id
    let coarse : Concept Bool Unit := fun _ => ()
    (¬Refines fine coarse) ∧
      ¬(AnswerableTargets (Y := Bool) fine ⊆ AnswerableTargets (Y := Bool) coarse ∧
        policyCapability fine Bool ⊆ policyCapability coarse Bool ∧
        Refines (conceptJoin fine fine) (conceptJoin coarse fine)) := by
  dsimp
  constructor
  · rintro ⟨factor, factorization⟩
    apply Bool.false_ne_true
    calc
      false = factor () := by
        simpa only [Function.comp_apply, id_eq] using congrFun factorization false
      _ = true := by
        simpa only [Function.comp_apply, id_eq] using
          (congrFun factorization true).symm
  · intro clauses
    have identityAvailable :
        (id : Bool → Bool) ∈ policyCapability (id : Concept Bool Bool) Bool :=
      ⟨id, rfl⟩
    obtain ⟨policy, policyFactors⟩ := clauses.2.1 identityAvailable
    have atFalse := congrFun policyFactors false
    have atTrue := congrFun policyFactors true
    simp only [Function.comp_apply, id_eq] at atFalse atTrue
    exact Bool.false_ne_true (atFalse.symm.trans atTrue)

#print axioms information_refinement_expands_answers_policies_and_leakage

end D5.S3.ConceptDynamics.Governance.InformationRefinementGovernance
