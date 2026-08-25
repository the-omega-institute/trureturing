/- GID: D5/S3/ConceptDynamics/RefinementFactorization/InterventionTargetFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/InterventionTargetFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Law kernels characterize unique target descent through the causal image. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Set.Image
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit `jointReadout` is the canonical dependent product
     readout and constructs the complete allowed-intervention law profile below.
   * `QueryFamilyIdentification` has adjacent kernel and quotient-factorization
     theorems, but its carrier is a simultaneous-kernel quotient rather than the
     source's canonical realized law image.
   * The adjacent current-tree theorem
     `realized_image_unique_factorization_iff_reverse_kernel` factors into the
     realized target image and puts all carriers in one universe. It is not
     applied because the source allows independent model, law, and target
     universes and requires the full target codomain.
   * Pinned Mathlib exact support hits `Set.rangeFactorization`,
     `Set.rangeSplitting`, `Set.apply_rangeSplitting`,
     `Set.rangeFactorization_surjective`, and
     `Function.Surjective.injective_comp_right` provide the causal-image map and
     uniqueness. No exact full-codomain realized-image theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.InterventionTargetFactorization

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- A target descends uniquely through the realized complete profile of all
allowed intervention laws exactly when equality of those profiles implies
equality of target values. The factor's domain is the canonical causal image,
not an independently defined quotient. -/
theorem intervention_target_factorization
    {Intervention : Type u} {Model : Type v} {Law : Intervention -> Type w}
    {Target : Type z}
    (interventionLaw : forall intervention, Model -> Law intervention)
    (target : Model -> Target) :
    (∃! factor : Set.range (jointReadout interventionLaw) -> Target,
        target =
          factor ∘ Set.rangeFactorization (jointReadout interventionLaw)) ↔
      Setoid.ker (jointReadout interventionLaw) <= Setoid.ker target := by
  let profile := jointReadout interventionLaw
  change
    (∃! factor : Set.range profile -> Target,
        target = factor ∘ Set.rangeFactorization profile) ↔
      Setoid.ker profile <= Setoid.ker target
  constructor
  · rintro ⟨factor, factorizes, _⟩ model₁ model₂ sameProfile
    calc
      target model₁ = factor (Set.rangeFactorization profile model₁) :=
        congrFun factorizes model₁
      _ = factor (Set.rangeFactorization profile model₂) :=
        congrArg factor
          ((Set.rangeFactorization_eq_rangeFactorization_iff model₁ model₂).2
            sameProfile)
      _ = target model₂ := (congrFun factorizes model₂).symm
  · intro kernelInclusion
    let factor : Set.range profile -> Target := fun value =>
      target (Set.rangeSplitting profile value)
    have factorizes :
        target = factor ∘ Set.rangeFactorization profile := by
      funext model
      change
        target model =
          target (Set.rangeSplitting profile (Set.rangeFactorization profile model))
      apply kernelInclusion
      exact
        (Set.apply_rangeSplitting profile (Set.rangeFactorization profile model)).symm
    refine ⟨factor, factorizes, ?_⟩
    intro other otherFactorizes
    apply Set.rangeFactorization_surjective.injective_comp_right
    exact otherFactorizes.symm.trans factorizes

#print axioms intervention_target_factorization

end D5.S3.ConceptDynamics.RefinementFactorization.InterventionTargetFactorization
