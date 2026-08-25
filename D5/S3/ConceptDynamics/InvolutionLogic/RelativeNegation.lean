/- GID: D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InvolutionLogic/RelativeNegation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a proposition inside the old ambient, negation grows by the admitted region. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib supplies set difference, complement, union, and disjointness.
   * Repository searches found no accepted theorem packaging the exact change-of-
     universe decomposition for relative negation.
   * The statements below are point-set identities and carry no biological or
     software-engineering interpretation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InvolutionLogic.RelativeNegation

/-- Negation of a proposition set relative to an explicitly named universe. -/
def relativeNegation {X : Type*} (ambient proposition : Set X) : Set X :=
  ambient \ proposition

/-- Enlarging the universe decomposes the new negation into the old negation
and the newly admitted region. -/
theorem relative_complement_expansion
    {X : Type*} {proposition oldUniverse newUniverse : Set X}
    (propositionInOld : proposition ⊆ oldUniverse)
    (oldInNew : oldUniverse ⊆ newUniverse) :
    relativeNegation newUniverse proposition =
      relativeNegation oldUniverse proposition ∪ (newUniverse \ oldUniverse) := by
  ext x
  change (x ∈ newUniverse ∧ x ∉ proposition) ↔
    (x ∈ oldUniverse ∧ x ∉ proposition) ∨
      (x ∈ newUniverse ∧ x ∉ oldUniverse)
  constructor
  · rintro ⟨xInNew, xOutsideProposition⟩
    by_cases xInOld : x ∈ oldUniverse
    · exact Or.inl ⟨xInOld, xOutsideProposition⟩
    · exact Or.inr ⟨xInNew, xInOld⟩
  · rintro (⟨xInOld, xOutsideProposition⟩ | ⟨xInNew, xOutsideOld⟩)
    · exact ⟨oldInNew xInOld, xOutsideProposition⟩
    · refine ⟨xInNew, ?_⟩
      intro xInProposition
      exact xOutsideOld (propositionInOld xInProposition)

/-- The old negative region and the newly admitted region are disjoint. -/
theorem relative_complement_parts_disjoint
    {X : Type*} {proposition oldUniverse newUniverse : Set X} :
    Disjoint (relativeNegation oldUniverse proposition)
      (newUniverse \ oldUniverse) := by
  refine Set.disjoint_left.2 ?_
  intro x xInOldNegative xInNewRegion
  exact xInNewRegion.2 xInOldNegative.1

/-- The part of the enlarged negation that was unavailable before is exactly
`newUniverse \ oldUniverse`. -/
theorem relative_complement_new_region
    {X : Type*} {proposition oldUniverse newUniverse : Set X}
    (propositionInOld : proposition ⊆ oldUniverse)
    (oldInNew : oldUniverse ⊆ newUniverse) :
    relativeNegation newUniverse proposition \
        relativeNegation oldUniverse proposition =
      newUniverse \ oldUniverse := by
  ext x
  change
    ((x ∈ newUniverse ∧ x ∉ proposition) ∧
        ¬(x ∈ oldUniverse ∧ x ∉ proposition)) ↔
      (x ∈ newUniverse ∧ x ∉ oldUniverse)
  constructor
  · rintro ⟨⟨xInNew, xOutsideProposition⟩, xOutsideOldNegative⟩
    refine ⟨xInNew, ?_⟩
    intro xInOld
    exact xOutsideOldNegative ⟨xInOld, xOutsideProposition⟩
  · rintro ⟨xInNew, xOutsideOld⟩
    have xOutsideProposition : x ∉ proposition := by
      intro xInProposition
      exact xOutsideOld (propositionInOld xInProposition)
    refine ⟨⟨xInNew, xOutsideProposition⟩, ?_⟩
    rintro ⟨xInOld, _⟩
    exact xOutsideOld xInOld

/-- Relative negation in the full universe is ordinary set complement. -/
theorem relativeNegation_univ
    {X : Type*} (proposition : Set X) :
    relativeNegation Set.univ proposition = propositionᶜ := by
  ext x
  simp [relativeNegation]

/-- Relative negation is monotone in the ambient universe. -/
theorem relativeNegation_mono_universe
    {X : Type*} {proposition oldUniverse newUniverse : Set X}
    (oldInNew : oldUniverse ⊆ newUniverse) :
    relativeNegation oldUniverse proposition ⊆
      relativeNegation newUniverse proposition := by
  rintro x ⟨xInOld, xOutsideProposition⟩
  exact ⟨oldInNew xInOld, xOutsideProposition⟩

#print axioms relative_complement_expansion
#print axioms relative_complement_new_region

end D5.S3.ConceptDynamics.InvolutionLogic.RelativeNegation
