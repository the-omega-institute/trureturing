/- GID: D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A type-valued sheaf identifies global sections with the pairwise equalizer. -/

import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes

/- Library-search audit trail (2026-08-25):
   * Repository searches for sheaves, presieves, compatible sections,
     equalizers, and gluing found no D5 theorem on this carrier.
   * Pinned Mathlib supplies the exact constituent primitives:
     `PreZeroHypercover.toPreOneHypercover` uses pairwise pullbacks,
     `MulticospanIndex.sections` is their section equalizer, and
     `PreZeroHypercover.isLimit_toPreOneHypercover_type_iff` identifies the
     sheaf condition with bijectivity of the canonical restriction map.
   * No single library theorem states both the canonical equivalence with its
     computation rule and the atom's explicit unique-gluing clause. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.SheafPairwiseEqualizer

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

/-- For a cover with pairwise pullbacks, the equalizer type consists of one
section over every cover object whose two restrictions to each pairwise
pullback agree. The sheaf condition makes the canonical global restriction
map an equivalence, and every compatible family has a unique global glue. -/
theorem sheaf_sections_equiv_pairwise_equalizer
    {C : Type u} [Category.{v} C] {U : C}
    (E : PreZeroHypercover.{w} U) [E.HasPullbacks]
    (F : Cᵒᵖ ⥤ Type*) (hSheaf : E.presieve₀.IsSheafFor F) :
    ∃ equivalence : F.obj (op U) ≃
        (E.toPreOneHypercover.multicospanIndex F).sections,
      (∀ globalSection,
          equivalence globalSection =
            (E.toPreOneHypercover.multifork F).toSections globalSection) ∧
        ∀ compatibleSections :
            (E.toPreOneHypercover.multicospanIndex F).sections,
          ∃! globalSection : F.obj (op U),
            (E.toPreOneHypercover.multifork F).toSections globalSection =
              compatibleSections := by
  have limiting : Nonempty
      (IsLimit (E.toPreOneHypercover.multifork F)) :=
    (PreZeroHypercover.isLimit_toPreOneHypercover_type_iff E F).2 hSheaf
  have restrictionBijective : Function.Bijective
      (E.toPreOneHypercover.multifork F).toSections :=
    (Multifork.isLimit_types_iff
      (E.toPreOneHypercover.multifork F)).1 limiting
  refine ⟨Equiv.ofBijective _ restrictionBijective, fun _ => rfl, ?_⟩
  intro compatibleSections
  obtain ⟨globalSection, restricts⟩ := restrictionBijective.2 compatibleSections
  exact ⟨globalSection, restricts, fun candidate hCandidate =>
    restrictionBijective.1 (hCandidate.trans restricts.symm)⟩

#print axioms sheaf_sections_equiv_pairwise_equalizer

end D5.S3.ConceptDynamics.Gluing.SheafPairwiseEqualizer
