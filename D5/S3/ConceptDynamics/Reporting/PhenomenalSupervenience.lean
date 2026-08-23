/- GID: D5/S3/ConceptDynamics/Reporting/PhenomenalSupervenience
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reporting/PhenomenalSupervenience
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint public refinement exactly excludes selected phenomenal zombie witnesses. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'supervenience_xor_zombie_witness' D5
     Golden/Frozen/accepted` returned no hit.
   * Reading `TruthfulReportBlocksInvertedSpectrum` found the same publicly equal,
     phenomenally unequal pair, but only factorization-to-agreement and premise-failure
     directions; it has no converse or selected-concept variability result.
   * Structural searches found `AnswerabilityCriterion.answerability_criterion` and
     `InductiveSufficiency.inductive_sufficiency_criterion`. The former supplies the
     general factorization/fiber criterion reused below. The latter factors through the
     realized image and neither theorem treats a public `conceptJoin` or compares two
     selected public concepts on one state space.
   * Pinned Mathlib's `Function.factorsThrough_iff` is the underlying general result,
     already reused by `answerability_criterion`; no lower-level proof is duplicated here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reporting.PhenomenalSupervenience

open D5.S0.Rewriting.Quotients.AnswerabilityCriterion
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A zombie witness is relative to selected phenomenal and public concepts: two states
share their public value but differ phenomenally. -/
def ZombieWitness {X Phenomenal Public : Type*}
    (phenomenal : Concept X Phenomenal) (publicReadout : Concept X Public) : Prop :=
  ∃ x y, publicReadout x = publicReadout y ∧ phenomenal x ≠ phenomenal y

/-- For an inhabited state space, a phenomenal concept factors through the joint public
concept exactly when there is no zombie witness. On `Bool`, changing only the selected
joint public concept makes such a witness first exist and then disappear. -/
theorem supervenience_xor_zombie_witness :
    (∀ {X Phenomenal PublicLeft PublicRight : Type*} [Nonempty X]
      (phenomenal : Concept X Phenomenal)
      (publicLeft : Concept X PublicLeft) (publicRight : Concept X PublicRight),
      Refines phenomenal (conceptJoin publicLeft publicRight) ↔
        ¬ZombieWitness phenomenal (conceptJoin publicLeft publicRight)) ∧
    ZombieWitness (id : Concept Bool Bool)
      (conceptJoin (fun _ : Bool => false) (fun _ : Bool => false)) ∧
    ¬ZombieWitness (id : Concept Bool Bool)
      (conceptJoin (id : Concept Bool Bool) (fun _ : Bool => false)) := by
  constructor
  · intro X Phenomenal PublicLeft PublicRight _ phenomenal publicLeft publicRight
    classical
    change
      (∃ factor : (PublicLeft × PublicRight) → Phenomenal,
        phenomenal = factor ∘ conceptJoin publicLeft publicRight) ↔
      ¬∃ x y,
        conceptJoin publicLeft publicRight x = conceptJoin publicLeft publicRight y ∧
          phenomenal x ≠ phenomenal y
    have factor_iff_fiber :=
      (answerability_criterion (Classical.arbitrary X)
        (conceptJoin publicLeft publicRight) phenomenal).1
    constructor
    · rintro hfactor ⟨x, y, samePublic, differentPhenomenal⟩
      exact differentPhenomenal (factor_iff_fiber.mp hfactor samePublic)
    · intro noWitness
      apply factor_iff_fiber.mpr
      intro x y samePublic
      by_contra differentPhenomenal
      exact noWitness ⟨x, y, samePublic, differentPhenomenal⟩
  · constructor
    · exact ⟨false, true, rfl, Bool.false_ne_true⟩
    · rintro ⟨x, y, samePublic, differentPhenomenal⟩
      exact differentPhenomenal (congrArg Prod.fst samePublic)

example :
    ZombieWitness (id : Concept Bool Bool)
      (conceptJoin (fun _ : Bool => false) (fun _ : Bool => false)) := by
  exact ⟨false, true, rfl, Bool.false_ne_true⟩

#print axioms supervenience_xor_zombie_witness

end D5.S3.ConceptDynamics.Reporting.PhenomenalSupervenience
