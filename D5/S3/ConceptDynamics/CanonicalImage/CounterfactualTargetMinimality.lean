/- GID: D5/S3/ConceptDynamics/CanonicalImage/CounterfactualTargetMinimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CanonicalImage/CounterfactualTargetMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fiber-constant targets factor uniquely through the canonical profile image. -/

import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
import Mathlib.Data.Set.Image

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CanonicalImage.CounterfactualTargetMinimality

open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- The query family is the source-semantic primitive: each query returns a set of
possible values, and the profile records all query answers simultaneously. -/
def queryProfile {M J : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) : M → ∀ j, Set (Value j) :=
  fun model j => queries j model

abbrev CounterfactualImage {M J : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) :=
  TargetImage (queryProfile Value queries)

def counterfactualProjection {M J : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) : M → CounterfactualImage Value queries :=
  Set.rangeFactorization (queryProfile Value queries)

noncomputable def targetFactorOnImage {M J K : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) (Target : K → Type _)
    (targets : ∀ k, M → Target k) (k : K) :
    CounterfactualImage Value queries → Target k :=
  fun imagePoint => targets k (Classical.choose imagePoint.property)

theorem targetFactorOnImage_apply {M J K : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) (Target : K → Type _)
    (targets : ∀ k, M → Target k) (k : K)
    (constantOnFibers : ∀ ⦃m n⦄,
      queryProfile Value queries m = queryProfile Value queries n -> targets k m = targets k n)
    (model : M) :
    targetFactorOnImage Value queries Target targets k
        (counterfactualProjection Value queries model) = targets k model := by
  apply constantOnFibers
  exact Classical.choose_spec (Set.mem_range.mpr ⟨model, rfl⟩)

/- Library-search audit trail (2026-08-25):
   * `rg -n -F 'queryProfile' D5 Golden/Frozen/accepted` found no exact source profile.
   * `rg -n -F 'TargetImage' D5` found the canonical target-image carrier in
     `UniversalSufficiencyFactorization`; it is imported rather than redeclared.
   * `rg -n -F 'Set.rangeFactorization' D5 .lake/packages/mathlib/Mathlib` found
     the canonical image map and its surjectivity theorem; both are applied below.
   * `universal_sufficiency_factorization` is an adjacent single-target fiber criterion,
     but its carrier is `TargetImage target`, not the source profile image, so it is
     not an exact cover of this atom and no wrapper duplicate is made. -/

/-- Every target in a family that is constant on the query-profile fibers has a
unique factor through the canonical image `CounterfactualImage Value queries`. -/
theorem target_family_factors_through_cf_image
    {M J K : Type _} (Value : J → Type _)
    (queries : ∀ j, M → Set (Value j)) (Target : K → Type _)
    (targets : ∀ k, M → Target k)
    (constantOnFibers : ∀ k ⦃m n⦄,
      queryProfile Value queries m = queryProfile Value queries n -> targets k m = targets k n) :
    ∀ k, ∃! factor : CounterfactualImage Value queries → Target k,
      targets k = factor ∘ counterfactualProjection Value queries := by
  intro k
  let factor : CounterfactualImage Value queries → Target k :=
    targetFactorOnImage Value queries Target targets k
  have factorizes : targets k = factor ∘ counterfactualProjection Value queries := by
    funext model
    exact (targetFactorOnImage_apply Value queries Target targets k (constantOnFibers k) model).symm
  refine ⟨factor, factorizes, ?_⟩
  intro other otherFactorizes
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
  exact target_family_factors_through_cf_image
    (fun _ : Unit => Bool)
    (fun _ (_ : Bool) => ({true} : Set Bool))
    (fun _ : Unit => Bool)
    (fun _ (_ : Bool) => false)
    (by intro _ m n h; rfl) _k

#print axioms target_family_factors_through_cf_image

end D5.S3.ConceptDynamics.CanonicalImage.CounterfactualTargetMinimality
