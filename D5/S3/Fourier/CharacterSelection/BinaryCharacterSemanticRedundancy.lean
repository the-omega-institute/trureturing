/- GID: D5/S3/Fourier/CharacterSelection/BinaryCharacterSemanticRedundancy
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/BinaryCharacterSemanticRedundancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Character-span rank counts semantic bits while dependencies supply parity checks. -/

import D5.S3.Fourier.CharacterSelection.BinaryCharacterProfileRankCardinality
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/- Library-search audit trail (2026-08-26):
   * The current-tree binary-character carrier is `Module.Dual (ZMod 2)
     (ModN G 2)`, evaluated through `ModN.mkQ`; it is reused directly.
   * `binary_character_profile_rank_cardinality` is the exact image-cardinality
     input, but it does not state the relation-space dimension or the effect of
     adjoining a dependent character.
   * Body-shape searches for `Fintype.linearCombination`, relation kernels,
     dependent roles, parity checks, and Hamming distance found no D5 theorem
     covering all public clauses.
   * Pinned Mathlib hits `Fintype.range_linearCombination`,
     `LinearMap.finrank_range_add_finrank_ker`,
     `Module.finrank_fintype_fun_eq_card`, and
     `Fintype.linearCombination_apply` supply the relation-count proof and the
     explicit parity relation. No exact whole-theorem hit was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.BinaryCharacterSemanticRedundancy

open Module Set
open D5.S3.Fourier.CharacterSelection.BinaryCharacterProfileRankCardinality

/-- For a finite family of binary characters, the realized profile has exactly
`2^r` values, where `r` is the character-span rank, while the coefficient
relation space has dimension `m-r`. Adjoining a character already in the span
preserves the number of distinguishable profiles, adds exactly one independent
relation, and supplies a parity relation whose new-coordinate coefficient is
one. -/
theorem binary_character_semantic_redundancy
    {G : Type*} [AddCommGroup G] [Fintype G]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2))
    (dependent : Module.Dual (ZMod 2) (ModN G 2))
    (dependent_mem : dependent ∈
      Submodule.span (ZMod 2) (Set.range characters)) :
    let originalProfile : AddMonoidHom G (I -> ZMod 2) :=
      AddMonoidHom.pi fun i =>
        characters i |>.toAddMonoidHom.comp (ModN.mkQ 2)
    let extendedCharacters : Option I ->
        Module.Dual (ZMod 2) (ModN G 2) :=
      fun index => index.elim dependent characters
    let extendedProfile : AddMonoidHom G (Option I -> ZMod 2) :=
      AddMonoidHom.pi fun index =>
        extendedCharacters index |>.toAddMonoidHom.comp (ModN.mkQ 2)
    let roleSpace := Submodule.span (ZMod 2) (Set.range characters)
    let relations := LinearMap.ker
      (Fintype.linearCombination (ZMod 2) characters)
    let extendedRelations := LinearMap.ker
      (Fintype.linearCombination (ZMod 2) extendedCharacters)
    Fintype.card originalProfile.range =
        2 ^ Module.finrank (ZMod 2) roleSpace /\
      Module.finrank (ZMod 2) relations =
        Fintype.card I - Module.finrank (ZMod 2) roleSpace /\
      Fintype.card extendedProfile.range =
        Fintype.card originalProfile.range /\
      Module.finrank (ZMod 2) extendedRelations =
        Module.finrank (ZMod 2) relations + 1 /\
      ∃ check : Option I -> ZMod 2,
        check ∈ extendedRelations /\ check none = 1 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  dsimp only
  let originalProfile : AddMonoidHom G (I -> ZMod 2) :=
    AddMonoidHom.pi fun i =>
      characters i |>.toAddMonoidHom.comp (ModN.mkQ 2)
  let extendedCharacters : Option I ->
      Module.Dual (ZMod 2) (ModN G 2) :=
    fun index => index.elim dependent characters
  let extendedProfile : AddMonoidHom G (Option I -> ZMod 2) :=
    AddMonoidHom.pi fun index =>
      extendedCharacters index |>.toAddMonoidHom.comp (ModN.mkQ 2)
  let roleSpace := Submodule.span (ZMod 2) (Set.range characters)
  let relations := LinearMap.ker
    (Fintype.linearCombination (ZMod 2) characters)
  let extendedRelations := LinearMap.ker
    (Fintype.linearCombination (ZMod 2) extendedCharacters)
  have originalImage : Fintype.card originalProfile.range =
      2 ^ Module.finrank (ZMod 2) roleSpace := by
    exact (binary_character_profile_rank_cardinality characters).2.1
  have originalRange : LinearMap.range
      (Fintype.linearCombination (ZMod 2) characters) = roleSpace := by
    simpa only [roleSpace] using
      (Fintype.range_linearCombination (ZMod 2) characters)
  have originalRankNullity :
      Module.finrank (ZMod 2) roleSpace +
          Module.finrank (ZMod 2) relations = Fintype.card I := by
    have rankNullity := LinearMap.finrank_range_add_finrank_ker
      (Fintype.linearCombination (ZMod 2) characters)
    rw [originalRange, Module.finrank_fintype_fun_eq_card] at rankNullity
    simpa only [relations] using rankNullity
  have relationDimension : Module.finrank (ZMod 2) relations =
      Fintype.card I - Module.finrank (ZMod 2) roleSpace := by
    omega
  have extendedRangeSet : Set.range extendedCharacters =
      Set.insert dependent (Set.range characters) := by
    ext character
    constructor
    · rintro ⟨index, rfl⟩
      cases index with
      | none => exact Set.mem_insert dependent _
      | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
    · intro member
      rcases member with equal | inRange
      · exact ⟨none, equal.symm⟩
      · rcases inRange with ⟨i, rfl⟩
        exact ⟨some i, rfl⟩
  have extendedSpan : Submodule.span (ZMod 2)
      (Set.range extendedCharacters) = roleSpace := by
    rw [extendedRangeSet]
    exact Submodule.span_insert_eq_span dependent_mem
  have extendedImage : Fintype.card extendedProfile.range =
      2 ^ Module.finrank (ZMod 2) roleSpace := by
    have image :=
      (binary_character_profile_rank_cardinality extendedCharacters).2.1
    rwa [extendedSpan] at image
  have unchangedProfiles : Fintype.card extendedProfile.range =
      Fintype.card originalProfile.range := by
    rw [extendedImage, originalImage]
  have extendedRankNullity :
      Module.finrank (ZMod 2) roleSpace +
          Module.finrank (ZMod 2) extendedRelations = Fintype.card I + 1 := by
    have rankNullity := LinearMap.finrank_range_add_finrank_ker
      (Fintype.linearCombination (ZMod 2) extendedCharacters)
    rw [Fintype.range_linearCombination, extendedSpan,
      Module.finrank_fintype_fun_eq_card, Fintype.card_option] at rankNullity
    simpa only [extendedRelations] using rankNullity
  have extendedRelationDimension :
      Module.finrank (ZMod 2) extendedRelations =
        Module.finrank (ZMod 2) relations + 1 := by
    omega
  have dependentInRange : dependent ∈ LinearMap.range
      (Fintype.linearCombination (ZMod 2) characters) := by
    rwa [Fintype.range_linearCombination]
  obtain ⟨coefficients, coefficientEquation⟩ := dependentInRange
  let check : Option I -> ZMod 2 := fun
    | none => 1
    | some i => -coefficients i
  have checkRelation : check ∈ extendedRelations := by
    rw [LinearMap.mem_ker]
    rw [Fintype.linearCombination_apply, Fintype.sum_option]
    simp only [check, extendedCharacters, one_smul]
    change dependent + ∑ i, (-coefficients i) • characters i = 0
    simp_rw [neg_smul]
    rw [Finset.sum_neg_distrib]
    rw [← sub_eq_add_neg]
    rw [← Fintype.linearCombination_apply, coefficientEquation]
    exact sub_self dependent
  exact ⟨originalImage, relationDimension, unchangedProfiles,
    extendedRelationDimension, check, checkRelation, rfl⟩

example :
    (0 : Module.Dual (ZMod 2) (ModN (ZMod 2) 2)) ∈
      Submodule.span (ZMod 2)
        (Set.range (fun _ : Fin 1 =>
          (0 : Module.Dual (ZMod 2) (ModN (ZMod 2) 2)))) :=
  Submodule.zero_mem _

#print axioms binary_character_semantic_redundancy

end D5.S3.Fourier.CharacterSelection.BinaryCharacterSemanticRedundancy
