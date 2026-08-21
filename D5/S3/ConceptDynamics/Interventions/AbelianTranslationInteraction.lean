/- GID: D5/S3/ConceptDynamics/Interventions/AbelianTranslationInteraction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/AbelianTranslationInteraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent translations commute, so an observed order defect excludes that model. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Algebra.Group.Commute.Basic

/- Library-search audit trail (2026-08-21):
   * Repository searches for independent translations, additive interactions,
     commutation defects, and intervention commutation found no exact theorem.
   * The exact family hit `ConceptFiberDecomposition.Concept` is imported and used
     as the canonical target-readout type; no sibling observation type is declared.
   * Pinned Mathlib search found the exact translation mechanism
     `AddCommute.function_commute_add_right` in `Algebra/Group/Commute/Basic.lean`;
     it is applied directly below.
   * Pinned Mathlib and repository searches found no theorem packaging the full
     conjunction of translation commutation and target-defect exclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.AbelianTranslationInteraction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- Independent translations of an abelian group commute. Consequently, a
nonempty target-level order defect excludes every independent-translation model
for the same intervention family. -/
theorem abelian_translation_commutation_and_defect_exclusion
    {X U Target : Type*} [AddCommGroup X]
    (intervention : U → X → X) :
    (∀ displacement : U → X,
      (∀ u x, intervention u x = x + displacement u) →
      ∀ u v, intervention u ∘ intervention v =
        intervention v ∘ intervention u) ∧
    (∀ (target : Concept X Target) u v,
      ({x | target (intervention u (intervention v x)) ≠
        target (intervention v (intervention u x))} : Set X).Nonempty →
      ¬ ∃ displacement : U → X,
        ∀ w x, intervention w x = x + displacement w) := by
  have hcommutes :
      ∀ displacement : U → X,
        (∀ u x, intervention u x = x + displacement u) →
        ∀ u v, intervention u ∘ intervention v =
          intervention v ∘ intervention u := by
    intro displacement htranslation u v
    apply funext
    intro x
    simpa only [Function.comp_apply, htranslation] using
      (AddCommute.all (displacement u) (displacement v)).function_commute_add_right x
  refine ⟨hcommutes, ?_⟩
  intro target u v hdefect
  rintro ⟨displacement, htranslation⟩
  let x : X := Classical.choose hdefect
  have hx :
      target (intervention u (intervention v x)) ≠
        target (intervention v (intervention u x)) :=
    Classical.choose_spec hdefect
  have hstate := congrFun (hcommutes displacement htranslation u v) x
  exact hx (congrArg target hstate)

/-- The source hypothesis is inhabited by integer translations indexed by a
Boolean intervention choice. -/
example :
    ∃ (intervention : Bool → Int → Int) (displacement : Bool → Int),
      ∀ u x, intervention u x = x + displacement u := by
  refine ⟨(fun u x => x + if u then 1 else 0),
    (fun u => if u then 1 else 0), ?_⟩
  intro u x
  rfl

/-- The defect premise is also inhabited: negation after a unit shift differs
from a unit shift after negation at the integer state zero. -/
example :
    let intervention : Bool → Int → Int :=
      fun u x => if u then x + 1 else -x
    let target : Concept Int Int := id
    ({x | target (intervention false (intervention true x)) ≠
      target (intervention true (intervention false x))} : Set Int).Nonempty := by
  refine ⟨0, ?_⟩
  change (-1 : Int) ≠ 1
  intro h
  cases h

#print axioms abelian_translation_commutation_and_defect_exclusion

end D5.S3.ConceptDynamics.Interventions.AbelianTranslationInteraction
