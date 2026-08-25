/- GID: D5/S3/ConceptDynamics/CanonicalImage/GlobalProfileCounterfactualTargetMinimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CanonicalImage/GlobalProfileCounterfactualTargetMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fiber-constant target families factor uniquely through the canonical profile image. -/

import D5.S3.ConceptDynamics.CanonicalImage.CounterfactualTargetMinimality
import D5.S3.ConceptDynamics.Sufficiency.GlobalProfileQuotientUniversality
import Mathlib.Data.Set.Image

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CanonicalImage.GlobalProfileCounterfactualTargetMinimality

open D5.S3.ConceptDynamics.CanonicalImage.CounterfactualTargetMinimality
open D5.S3.ConceptDynamics.Sufficiency.GlobalProfileQuotientUniversality

/- Library-search audit trail (2026-08-25):
   * The canonical `globalProfile` is imported from
     `GlobalProfileQuotientUniversality`; no local profile or readout wrapper is
     introduced.
   * The existing `CounterfactualImage` and `counterfactualProjection` carriers
     are reused from the legal canonical-image namespace.
   * Pinned Mathlib supplies `Set.rangeSplitting`, `Set.apply_rangeSplitting`,
     `Set.rangeFactorization`, and `Set.rangeFactorization_surjective`; no exact
     theorem for this dependent target-family statement was found.
 -/

/-- Every target in a family that is constant on the canonical global-profile
fibers has a unique factor through the realized counterfactual image. -/
theorem global_profile_target_family_factors
    {M J K : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) (Target : K → Type _)
    (targets : ∀ k, M → Target k)
    (constantOnFibers : ∀ k ⦃m n⦄,
      globalProfile queries m = globalProfile queries n → targets k m = targets k n) :
    ∀ k, ∃! factor : CounterfactualImage Value queries → Target k,
      targets k = factor ∘ counterfactualProjection Value queries := by
  intro k
  let profile : M → (∀ j, Set (Value j)) := globalProfile queries
  let factor : Set.range profile → Target k := fun imagePoint =>
    targets k (Set.rangeSplitting profile imagePoint)
  have factorizes : targets k = factor ∘ Set.rangeFactorization profile := by
    funext model
    change targets k model =
      targets k (Set.rangeSplitting profile (Set.rangeFactorization profile model))
    exact constantOnFibers k (Set.apply_rangeSplitting profile
      (Set.rangeFactorization profile model)).symm
  refine ⟨factor, ?_, ?_⟩
  · change targets k = factor ∘ Set.rangeFactorization profile
    exact factorizes
  · intro other otherFactorizes
    apply Set.rangeFactorization_surjective.injective_comp_right
    exact otherFactorizes.symm.trans factorizes

example :
    ∀ k : Unit, ∃! factor :
        CounterfactualImage (fun _ : Unit => Bool)
            (fun _ (_ : Bool) => ({true} : Set Bool)) → Bool,
      (fun _ : Bool => false) = factor ∘
        counterfactualProjection (fun _ : Unit => Bool)
          (fun _ (_ : Bool) => ({true} : Set Bool)) := by
  intro _k
  exact global_profile_target_family_factors
    (fun _ : Unit => Bool)
    (fun _ (_ : Bool) => ({true} : Set Bool))
    (fun _ : Unit => Bool)
    (fun _ (_ : Bool) => false)
    (by intro _ m n h; rfl) _k

#print axioms global_profile_target_family_factors

end D5.S3.ConceptDynamics.CanonicalImage.GlobalProfileCounterfactualTargetMinimality
