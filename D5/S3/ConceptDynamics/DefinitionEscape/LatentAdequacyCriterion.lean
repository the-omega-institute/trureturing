/- GID: D5/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/LatentAdequacyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target adequacy binds canonical recovery to join strictness. -/

import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
import D5.S3.ConceptDynamics.StrictRefinementCapability

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `target_recovery_criterion` already proves target
     factorization, fiber constancy, canonical `defectRelation` emptiness, and
     the nonempty-defect failure witness; those clauses are reused directly.
   * Exact repository hit `strict_refinement_capability` supplies the operational
     consequence used downstream after effective-range normalization.
   * Repository search found no theorem identifying target-recovery failure with
     strictness of the canonical join, which is the new bridge retained here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.StrictRefinementCapability
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

/-- A latent readout is adequate for a target when the target can be decoded
from the latent coordinate. -/
def TargetAdequate {X Latent Target : Type*}
    (latent : Concept X Latent) (target : Concept X Target) : Prop :=
  Refines target latent

/-- Adequacy is the existing canonical recovery/fiber-constancy criterion. -/
theorem target_adequate_iff_fiber_constant
    {X Latent Target : Type*} [Nonempty X]
    (latent : Concept X Latent) (target : Concept X Target) :
    TargetAdequate latent target ↔
      ∀ ⦃x y : X⦄, latent x = latent y → target x = target y := by
  simpa only [TargetAdequate, Refines] using
    (target_recovery_criterion latent target).1

/-- Inadequacy is exactly nonemptiness of the repository's canonical target
`defectRelation`; no parallel residual carrier is introduced. -/
theorem target_inadequate_iff_defect_nonempty
    {X Latent Target : Type*} [Nonempty X]
    (latent : Concept X Latent) (target : Concept X Target) :
    (¬TargetAdequate latent target) ↔
      (defectRelation latent target).Nonempty := by
  simpa only [TargetAdequate, Refines] using
    (target_recovery_criterion latent target).2.2.2

/-- Adjoining the target is a strict latent refinement exactly when the latent
readout is target-inadequate. -/
theorem latent_join_strict_iff_inadequate
    {X Latent Target : Type*}
    (latent : Concept X Latent) (target : Concept X Target) :
    StrictRefinement latent (conceptJoin latent target) ↔
      ¬TargetAdequate latent target := by
  constructor
  · rintro ⟨_, noReverse⟩ adequate
    apply noReverse
    exact (concept_join_universal latent target latent).2.2
      ⟨id, rfl⟩ adequate
  · intro inadequate
    refine ⟨(concept_join_universal latent target latent).1, ?_⟩
    rintro ⟨factor, factors⟩
    apply inadequate
    refine ⟨Prod.snd ∘ factor, ?_⟩
    funext state
    have componentEquality := congrArg Prod.snd (congrFun factors state)
    change target state = (factor (latent state)).2
    exact componentEquality

example :
    (defectRelation (fun _ : Bool => ())
      (id : Concept Bool Bool)).Nonempty := by
  exact (target_inadequate_iff_defect_nonempty
    (fun _ : Bool => ()) (id : Concept Bool Bool)).mp (by
      rintro ⟨decode, factors⟩
      apply Bool.false_ne_true
      calc
        false = decode () := by
          simpa only [Function.comp_apply, id_eq] using congrFun factors false
        _ = true := by
          simpa only [Function.comp_apply, id_eq] using
            (congrFun factors true).symm)

#print axioms target_inadequate_iff_defect_nonempty
#print axioms latent_join_strict_iff_inadequate

end D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
