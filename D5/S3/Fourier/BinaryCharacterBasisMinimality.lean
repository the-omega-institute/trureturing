/- GID: D5/S3/Fourier/BinaryCharacterBasisMinimality
   generality: G
   mirror-B: D5/B/S3/Fourier/BinaryCharacterBasisMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary-character bases are exactly minimum complete observation families. -/

import Mathlib
import D5.S3.ConceptDynamics.LinearSufficiency.BinaryRoleMinimumCardinality

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for binary characters, character-span rank, joint
     kernels, minimum sufficient observation families, and basis observations
     found no exact D5 declaration. The frozen
     `binary_role_minimum_cardinality` theorem covers the same-span minimum
     but not joint kernels or the arbitrary-basis clause, so it is imported
     and applied as the canonical family result.
   * Body-shape searches for intersections of character kernels and spans of
     additive homomorphisms found no existing D5 family primitive to reuse.
   * Pinned Mathlib exact hits `ModN`, `ModN.mkQ`, and `ModN.liftEquiv'`
     provide the canonical exponent-two quotient through which every binary
     character factors.
   * Pinned Mathlib exact hits `mem_span_of_iInf_ker_le_ker`,
     `finrank_range_le_card`, `Module.finBasis`, and
     `Module.finrank_eq_card_basis` supply the linear-algebraic proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Module Set
open D5.S3.ConceptDynamics.LinearSufficiency.BinaryRoleMinimumCardinality

namespace D5.S3.Fourier.BinaryCharacterBasisMinimality

set_option maxHeartbeats 2000000 in
-- The four span-to-kernel arguments need more elaboration time than the default.
/-- For binary characters on a finite abelian group, any family with the same
joint kernel has at least the character-span rank many members. A family of
exactly that rank is constructed, and every basis of the character span is a
minimum sufficient observation family. All characters are evaluated on the
original group through the canonical quotient by doubles. -/
theorem binary_character_basis_minimality
    {G : Type*} [AddCommGroup G] [Finite G]
    {originalIndex competitorIndex basisIndex : Type*}
    [Finite originalIndex] [Fintype competitorIndex] [Fintype basisIndex]
    (characters : originalIndex -> Module.Dual (ZMod 2) (ModN G 2))
    (competitor : competitorIndex -> Module.Dual (ZMod 2) (ModN G 2))
    (basis : Basis basisIndex (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range characters)))
    (sameJointKernel : forall g : G,
      (forall i, characters i (ModN.mkQ 2 g) = 0) <->
        forall j, competitor j (ModN.mkQ 2 g) = 0) :
    let E := Set.range characters
    let H := Submodule.span (ZMod 2) (Set.range characters)
    let r := Module.finrank (ZMod 2) H
    IsLeast
        {cardinality : Cardinal | exists chosen :
            Set (Module.Dual (ZMod 2) (ModN G 2)),
          chosen ⊆ E /\
            Submodule.span (ZMod 2) chosen = H /\
            Cardinal.mk chosen = cardinality}
        (Module.rank (ZMod 2) H) /\
      r <= Fintype.card competitorIndex /\
      (exists selected : Fin r -> Module.Dual (ZMod 2) (ModN G 2),
        (forall i, selected i ∈ Set.range characters) /\
          LinearIndependent (ZMod 2) selected /\
          Submodule.span (ZMod 2) (Set.range selected) = H /\
          forall g : G,
            (forall i, selected i (ModN.mkQ 2 g) = 0) <->
              forall i, characters i (ModN.mkQ 2 g) = 0) /\
      ((forall g : G,
          (forall j,
            (((basis j : Submodule.span (ZMod 2) (Set.range characters)) :
                Module.Dual (ZMod 2) (ModN G 2)) (ModN.mkQ 2 g)) = 0) <->
            forall i, characters i (ModN.mkQ 2 g) = 0) /\
        Fintype.card basisIndex <= Fintype.card competitorIndex) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  dsimp only
  let H : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ModN G 2)) :=
    Submodule.span (ZMod 2) (Set.range characters)
  have hH : H = Submodule.span (ZMod 2) (Set.range characters) := rfl
  have kernelSubspaceEq :
      (iInf fun i => LinearMap.ker (characters i)) =
        iInf fun j => LinearMap.ker (competitor j) := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro g
    constructor
    · intro hx
      have hchars : ∀ i, characters i (ModN.mkQ 2 g) = 0 := by
        intro i
        exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).1 hx i)
      have hcomp := (sameJointKernel g).mp hchars
      apply (Submodule.mem_iInf _).2
      intro j
      exact LinearMap.mem_ker.mpr (hcomp j)
    · intro hx
      have hcomp : ∀ j, competitor j (ModN.mkQ 2 g) = 0 := by
        intro j
        exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).1 hx j)
      have hchars := (sameJointKernel g).mpr hcomp
      apply (Submodule.mem_iInf _).2
      intro i
      exact LinearMap.mem_ker.mpr (hchars i)
  have competitorMem (j : competitorIndex) : competitor j ∈ H := by
    rw [hH]
    have hker :
        (iInf fun i => LinearMap.ker (characters i)) <=
          LinearMap.ker (competitor j) := by
      rw [kernelSubspaceEq]
      exact iInf_le _ j
    exact mem_span_of_iInf_ker_le_ker
      (𝕜 := ZMod 2) (E := ModN G 2)
      (L := characters) (K := competitor j) hker
  have characterMem (i : originalIndex) :
      characters i ∈ Submodule.span (ZMod 2) (Set.range competitor) := by
    have hker :
        (iInf fun j => LinearMap.ker (competitor j)) <=
          LinearMap.ker (characters i) := by
      rw [← kernelSubspaceEq]
      exact iInf_le _ i
    exact mem_span_of_iInf_ker_le_ker
      (𝕜 := ZMod 2) (E := ModN G 2)
      (L := competitor) (K := characters i) hker
  have competitorSpanEq :
      Submodule.span (ZMod 2) (Set.range competitor) = H := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact competitorMem j
    · rw [hH, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact characterMem i
  have rankLowerBound :
      Module.finrank (ZMod 2) H <= Fintype.card competitorIndex := by
    rw [← competitorSpanEq]
    exact finrank_range_le_card (R := ZMod 2) competitor
  letI : FiniteDimensional (ZMod 2) H := by
    rw [hH]
    exact FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range characters)
  obtain ⟨selected, selectedFromOriginal, selectedSpanEq, selectedIndependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq
      (ZMod 2) (Set.range characters)
  have selectedKernel : forall g : G,
      (forall i, selected i (ModN.mkQ 2 g) = 0) <->
        forall i, characters i (ModN.mkQ 2 g) = 0 := by
    intro g
    constructor
    · intro hselected i
      have spanLe :
          Submodule.span (ZMod 2) (Set.range selected) <=
            LinearMap.ker (Module.Dual.eval (ZMod 2) (ModN G 2)
              (ModN.mkQ 2 g)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        apply LinearMap.mem_ker.mpr
        simpa only [Module.Dual.eval_apply] using hselected j
      have hi : characters i ∈ Submodule.span (ZMod 2) (Set.range selected) := by
        rw [selectedSpanEq]
        exact Submodule.subset_span ⟨i, rfl⟩
      simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using spanLe hi
    · intro hcharacters j
      have spanLe :
          Submodule.span (ZMod 2) (Set.range characters) <=
            LinearMap.ker (Module.Dual.eval (ZMod 2) (ModN G 2)
              (ModN.mkQ 2 g)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply LinearMap.mem_ker.mpr
        simpa only [Module.Dual.eval_apply] using hcharacters i
      have hj : selected j ∈ Submodule.span (ZMod 2) (Set.range characters) := by
        exact Submodule.subset_span (selectedFromOriginal j)
      simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using spanLe hj
  let basisFamily : basisIndex -> Module.Dual (ZMod 2) (ModN G 2) :=
    fun j => (basis j : Module.Dual (ZMod 2) (ModN G 2))
  have basisSpanEq :
      Submodule.span (ZMod 2) (Set.range basisFamily) = H := by
    apply (Submodule.span_range_subtype_eq_top_iff H fun j => (basis j).property).mp
    simpa only [basisFamily] using basis.span_eq
  have basisKernel : forall g : G,
      (forall j, basisFamily j (ModN.mkQ 2 g) = 0) <->
        forall i, characters i (ModN.mkQ 2 g) = 0 := by
    intro g
    constructor
    · intro hbasis i
      have spanLe :
          Submodule.span (ZMod 2) (Set.range basisFamily) <=
            LinearMap.ker (Module.Dual.eval (ZMod 2) (ModN G 2)
              (ModN.mkQ 2 g)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        apply LinearMap.mem_ker.mpr
        simpa only [Module.Dual.eval_apply] using hbasis j
      have hi : characters i ∈ Submodule.span (ZMod 2) (Set.range basisFamily) := by
        rw [basisSpanEq, hH]
        exact Submodule.subset_span ⟨i, rfl⟩
      simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using spanLe hi
    · intro hcharacters j
      have spanLe :
          Submodule.span (ZMod 2) (Set.range characters) <=
            LinearMap.ker (Module.Dual.eval (ZMod 2) (ModN G 2)
              (ModN.mkQ 2 g)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply LinearMap.mem_ker.mpr
        simpa only [Module.Dual.eval_apply] using hcharacters i
      have hj : basisFamily j ∈ Submodule.span (ZMod 2) (Set.range characters) := by
        rw [← hH, ← basisSpanEq]
        exact Submodule.subset_span ⟨j, rfl⟩
      simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using spanLe hj
  have basisMinimum :
      Fintype.card basisIndex <= Fintype.card competitorIndex := by
    rw [← Module.finrank_eq_card_basis basis]
    exact rankLowerBound
  have originalMinimum :=
    binary_role_minimum_cardinality (Set.range characters)
  refine ⟨originalMinimum, rankLowerBound, ?_, ?_⟩
  · exact ⟨selected, selectedFromOriginal, selectedIndependent,
      selectedSpanEq, selectedKernel⟩
  · exact ⟨basisKernel, basisMinimum⟩

#print axioms binary_character_basis_minimality

end D5.S3.Fourier.BinaryCharacterBasisMinimality
