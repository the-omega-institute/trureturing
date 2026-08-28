/- GID: D5/S3/Fourier/CharacterSelection/BinaryCharacterProfileRankCardinality
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/BinaryCharacterProfileRankCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary-character span rank controls profile image and realized-fiber cardinalities. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.Fourier.BinaryCharacterBasisMinimality
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index

/- Library-search audit trail (2026-08-26):
   * The canonical D5 binary-character carrier is `Module.Dual (ZMod 2)
     (ModN G 2)`, evaluated on the original group through `ModN.mkQ`; it is
     reused without a sibling character or profile definition.
   * `binary_character_basis_minimality` and
     `binary_character_subfamily_sufficiency_tfae` are adjacent span and
     sufficiency results, but neither states image or fiber cardinalities.
   * Exact pinned-Mathlib hits `LinearMap.ker_pi`,
     `Subspace.finrank_add_finrank_dualCoannihilator_eq`,
     `LinearMap.finrank_range_add_finrank_ker`,
     `Module.card_eq_pow_finrank`, `AddSubgroup.index_ker`, and
     `AddMonoidHom.card_fiber_eq_of_mem_range` prove the three public clauses.
     No exact whole-theorem hit was found in D5 or pinned Mathlib. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.BinaryCharacterProfileRankCardinality

open Module Set

set_option maxHeartbeats 2000000 in
-- The annihilator rank and finite-cardinality reductions need extended elaboration time.
/-- For binary characters on a finite abelian group, the joint profile kernel
is the intersection of the character kernels, its realized image has size two
to the character-span rank, and every realized profile has the corresponding
uniform fiber cardinality. -/
theorem binary_character_profile_rank_cardinality
    {G : Type*} [AddCommGroup G] [Fintype G]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) :
    let profileHom : AddMonoidHom G (I -> ZMod 2) :=
      AddMonoidHom.pi fun i =>
        characters i |>.toAddMonoidHom.comp (ModN.mkQ 2)
    let H := Submodule.span (ZMod 2) (Set.range characters)
    let r := Module.finrank (ZMod 2) H
    profileHom.ker =
        iInf (fun i =>
          (characters i).toAddMonoidHom.comp (ModN.mkQ 2) |>.ker) /\
      Fintype.card profileHom.range = 2 ^ r /\
      forall b : profileHom.range,
        Fintype.card {g : G // profileHom g = b.1} =
          Fintype.card G / 2 ^ r := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  dsimp only
  let profileHom : AddMonoidHom G (I -> ZMod 2) :=
    AddMonoidHom.pi fun i =>
      characters i |>.toAddMonoidHom.comp (ModN.mkQ 2)
  let profileLinear : ModN G 2 →ₗ[ZMod 2] (I -> ZMod 2) :=
    LinearMap.pi characters
  let H := Submodule.span (ZMod 2) (Set.range characters)
  let r := Module.finrank (ZMod 2) H
  have kernelClause :
      profileHom.ker =
        iInf (fun i =>
          (characters i).toAddMonoidHom.comp (ModN.mkQ 2) |>.ker) := by
    ext g
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp,
      LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      AddSubgroup.mem_iInf]
    exact funext_iff
  have mkQSurjective : Function.Surjective (ModN.mkQ (G := G) 2) := by
    change Function.Surjective
      (LinearMap.range
        (LinearMap.lsmul ℤ G (↑(2 : Nat) : ℤ))).mkQ
    exact (LinearMap.range
      (LinearMap.lsmul ℤ G (↑(2 : Nat) : ℤ))).mkQ_surjective
  letI : Fintype (ModN G 2) := Fintype.ofFinite (ModN G 2)
  have rangeSetEquality :
      (profileHom.range : Set (I -> ZMod 2)) =
        (profileLinear.range : Set (I -> ZMod 2)) := by
    ext observed
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ModN.mkQ 2 g, rfl⟩
    · rintro ⟨quotientState, rfl⟩
      obtain ⟨g, rfl⟩ := mkQSurjective quotientState
      exact ⟨g, rfl⟩
  have linearKernel : profileLinear.ker = H.dualCoannihilator := by
    ext quotientState
    rw [LinearMap.mem_ker, Submodule.mem_dualCoannihilator]
    constructor
    · intro jointlyZero character characterInSpan
      have spanLe : H <= LinearMap.ker
          (Module.Dual.eval (ZMod 2) (ModN G 2) quotientState) := by
        change Submodule.span (ZMod 2) (Set.range characters) <= _
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply LinearMap.mem_ker.mpr
        have coordinateZero := congrFun jointlyZero i
        change characters i quotientState =
          (0 : I -> ZMod 2) i at coordinateZero
        change characters i quotientState = 0
        exact coordinateZero
      simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using
        spanLe characterInSpan
    · intro annihilated
      funext i
      exact annihilated (characters i)
        (Submodule.subset_span ⟨i, rfl⟩)
  have rangeFinrank :
      Module.finrank (ZMod 2) profileLinear.range = r := by
    have rankNullity :=
      LinearMap.finrank_range_add_finrank_ker profileLinear
    have annihilatorDimension :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq H
    rw [linearKernel] at rankNullity
    exact Nat.add_right_cancel
      (rankNullity.trans annihilatorDimension.symm)
  have linearRangeCard :
      Fintype.card profileLinear.range = 2 ^ r := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
      rangeFinrank]
  have imageClause : Fintype.card profileHom.range = 2 ^ r := by
    calc
      Fintype.card profileHom.range =
          Fintype.card profileLinear.range :=
        Fintype.card_congr (Equiv.setCongr rangeSetEquality)
      _ = 2 ^ r := linearRangeCard
  refine ⟨kernelClause, imageClause, ?_⟩
  intro b
  have fiberCard :
      Fintype.card {g : G // profileHom g = b.1} =
        Nat.card profileHom.ker := by
    rw [Fintype.card_subtype]
    have equalFiber :=
      AddMonoidHom.card_fiber_eq_of_mem_range profileHom
        b.property ⟨0, profileHom.map_zero⟩
    rw [equalFiber]
    rw [← Fintype.card_subtype]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      (Equiv.subtypeEquivProp (by ext g; simp))
  calc
    Fintype.card {g : G // profileHom g = b.1} =
        Nat.card profileHom.ker := fiberCard
    _ = Nat.card G / Nat.card profileHom.range := by
      rw [← profileHom.ker.card_mul_index, AddSubgroup.index_ker]
      exact (Nat.mul_div_cancel (Nat.card profileHom.ker)
        (Nat.card_pos (α := profileHom.range))).symm
    _ = Fintype.card G / 2 ^ r := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        imageClause]

#print axioms binary_character_profile_rank_cardinality

end D5.S3.Fourier.CharacterSelection.BinaryCharacterProfileRankCardinality
