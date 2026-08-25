/- GID: D5/S3/ConceptDynamics/DefinitionEscape/MultiTargetBlindResidual
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/MultiTargetBlindResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A joint target's blind residual is the union of its components' residuals. -/

import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
import D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

/- Library-search audit trail (2026-08-24):
   * `MultiTargetMinimalSufficiency` supplies the canonical dependent
     `jointTarget`; it is reused rather than redefined.
   * `DefinitionKernelGalois` supplies the common language kernel, semantic
     closure, and full-language defect identity.
   * Repository search found no target-family union law for blind residuals and
     no exact equivalence between simultaneous full-language sufficiency and
     componentwise blind-residual emptiness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.MultiTargetBlindResidual

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/-- The target-family blind residual is the blind residual of the canonical
dependent joint target. -/
def FamilyBlindResidual
    {X Index Current InputOutput : Type*}
    {Target : Index → Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    Set (X × X) :=
  blindResidual Gamma current (jointTarget targets)

/-- A pair escapes the joint target exactly when it escapes at least one
component target. Consequently, the joint blind residual is the union of all
component blind residuals. -/
theorem familyBlindResidual_eq_iUnion
    {X Index Current InputOutput : Type*}
    {Target : Index → Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    FamilyBlindResidual Gamma current targets =
      ⋃ index, blindResidual Gamma current (targets index) := by
  classical
  ext pair
  constructor
  · rintro ⟨⟨currentEqual, jointDifferent⟩, pairInKernel⟩
    have componentDifferent :
        ∃ index, targets index pair.1 ≠ targets index pair.2 := by
      by_contra noComponent
      apply jointDifferent
      funext index
      by_contra different
      exact noComponent ⟨index, different⟩
    rcases componentDifferent with ⟨index, different⟩
    exact Set.mem_iUnion.2
      ⟨index, ⟨⟨currentEqual, different⟩, pairInKernel⟩⟩
  · intro pairInUnion
    rcases Set.mem_iUnion.1 pairInUnion with
      ⟨index, ⟨⟨currentEqual, componentDifferent⟩, pairInKernel⟩⟩
    refine ⟨⟨currentEqual, ?_⟩, pairInKernel⟩
    intro jointEqual
    exact componentDifferent (congrFun jointEqual index)

/-- The joint blind residual is empty exactly when every component blind
residual is empty. -/
theorem familyBlindResidual_empty_iff_components
    {X Index Current InputOutput : Type*}
    {Target : Index → Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    FamilyBlindResidual Gamma current targets = ∅ ↔
      ∀ index, blindResidual Gamma current (targets index) = ∅ := by
  rw [familyBlindResidual_eq_iUnion]
  constructor
  · intro unionEmpty index
    ext pair
    constructor
    · intro componentMember
      have unionMember :
          pair ∈ ⋃ index, blindResidual Gamma current (targets index) :=
        Set.mem_iUnion.2 ⟨index, componentMember⟩
      rw [unionEmpty] at unionMember
      exact unionMember
    · intro impossible
      exact impossible.elim
  · intro componentsEmpty
    ext pair
    constructor
    · intro unionMember
      rcases Set.mem_iUnion.1 unionMember with ⟨index, componentMember⟩
      rw [componentsEmpty index] at componentMember
      exact componentMember
    · intro impossible
      exact impossible.elim

/-- Full-language sufficiency for the dependent joint target is equivalent to
componentwise disappearance of all blind residuals. -/
theorem jointTarget_fullLanguage_sufficient_iff_components_blind_empty
    {X Index Current InputOutput : Type*}
    {Target : Index → Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    Refines (jointTarget targets)
        (languageExtension current
          (fun definition : Gamma => definition.1)) ↔
      ∀ index, blindResidual Gamma current (targets index) = ∅ := by
  have recoveryCriterion :=
    target_recovery_criterion
      (languageExtension current
        (fun definition : Gamma => definition.1))
      (jointTarget targets)
  calc
    Refines (jointTarget targets)
        (languageExtension current
          (fun definition : Gamma => definition.1)) ↔
        defectRelation
          (languageExtension current
            (fun definition : Gamma => definition.1))
          (jointTarget targets) = ∅ := by
      simpa only [Refines] using recoveryCriterion.2.2.1.symm
    _ ↔ FamilyBlindResidual Gamma current targets = ∅ := by
      rw [languageExtension_defect_eq_blindResidual]
      rfl
    _ ↔ ∀ index, blindResidual Gamma current (targets index) = ∅ :=
      familyBlindResidual_empty_iff_components Gamma current targets

/-- The full definition language decides every component target exactly when it
decides their canonical joint target. -/
theorem componentwise_fullLanguage_sufficient_iff_joint
    {X Index Current InputOutput : Type*}
    {Target : Index → Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    (∀ index,
      Refines (targets index)
        (languageExtension current
          (fun definition : Gamma => definition.1))) ↔
      Refines (jointTarget targets)
        (languageExtension current
          (fun definition : Gamma => definition.1)) := by
  simpa using
    (multi_target_minimal_sufficiency targets
      (languageExtension current
        (fun definition : Gamma => definition.1))).1

#print axioms familyBlindResidual_eq_iUnion
#print axioms familyBlindResidual_empty_iff_components
#print axioms jointTarget_fullLanguage_sufficient_iff_components_blind_empty

end D5.S3.ConceptDynamics.DefinitionEscape.MultiTargetBlindResidual
