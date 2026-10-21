/- GID: D5/S3/FiniteGroups/FrobeniusCharacterDegrees
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrobeniusCharacterDegrees
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point-free conjugation gives the character-degree divisibility dichotomy. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: degree_dvd_or_index_dvd_of_fixedPointFree
Fixed-point-free conjugation forces a nontrivial constituent inertia group to equal the normal kernel; Clifford decomposition yields the dichotomy.
trivial_of_invariant_fixedPointFree | proof_shape: bind-only | escape_witness: none | consumer: inertia_eq_of_fixedPointFree
abelian_character_eq_iff | proof_shape: bind-only | escape_witness: none | consumer: inertia_eq_of_fixedPointFree
degree_square_le_card | proof_shape: bind-only | escape_witness: none | consumer: BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd
degree_dvd_quotient_card | proof_shape: bind-only | escape_witness: none | consumer: degree_dvd_or_index_dvd_of_fixedPointFree
inertia_eq_of_fixedPointFree | proof_shape: bind-only | escape_witness: none | consumer: degree_dvd_or_index_dvd_of_fixedPointFree
restriction_trivial_of_clifford_constituent_trivial | proof_shape: bind-only | escape_witness: none | consumer: degree_dvd_or_index_dvd_of_fixedPointFree
degree_dvd_or_index_dvd_of_fixedPointFree | proof_shape: content | escape_witness: degree_dvd_or_index_dvd_of_fixedPointFree | consumer: BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import D5.S3.FiniteGroups.ComplexCharacterAbelianProducts
import D5.S3.FiniteGroups.InducedCharacterFormula
import D5.S3.FiniteGroups.CharacterDegreeDivisibility
import D5.S3.FiniteGroups.CliffordConstituents
import D5.S3.FiniteGroups.CliffordDecomposition
import D5.S3.FiniteGroups.FiniteCharacterAlgebra

section ScratchSource_FixedPointFreeDual

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory

variable {A : Type*} [CommGroup A]

private theorem trivial_of_invariant_fixedPointFree [Finite A]
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k A V) (f : MulAut A)
    (hf : ∀ a : A, f a = a → a = 1)
    (hρ : ∀ a : A, ρ (f a) = ρ a) : Representation.IsTrivial ρ := by
  constructor
  intro a
  obtain ⟨b, rfl⟩ := MonoidHom.FixedPointFree.commutatorMap_surjective
    (φ := f) hf a
  simp only [MonoidHom.commutatorMap_apply, div_eq_mul_inv]
  rw [map_mul, ← hρ b, ← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem abelian_character_eq_iff {k : Type*} [Field k] [IsAlgClosed k]
    (X : FDRep k A) [Simple X] (a b : A) :
    X.character a = X.character b ↔ X.ρ a = X.ρ b := by
  letI : Representation.IsIrreducible X.ρ := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
  have hdim : Module.finrank k X = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative X.ρ
  obtain ⟨c, hc⟩ := D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.central_action_scalar X.ρ a (fun g => mul_comm a g)
  obtain ⟨d, hd⟩ := D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.central_action_scalar X.ρ b (fun g => mul_comm b g)
  constructor
  · intro h
    have hcd : c = d := by
      simpa [FDRep.character, Representation.character, hc, hd,
        map_smul, LinearMap.trace_id, hdim] using h
    rw [hc, hd, hcd]
  · intro h
    exact congrArg (LinearMap.trace k X) h

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_FixedPointFreeDual

section ScratchSource_CharacterFacts

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory
open scoped _root_.MonoidAlgebra

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389
- Dimension bound obtained directly from the upstream density theorem. -/
theorem degree_square_le_card (G : Type) [Group G] [Finite G]
    (X : FDRep ℂ G) [Simple X] :
    Module.finrank ℂ X ^ 2 ≤ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hρ : Representation.IsIrreducible X.ρ := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
  have hs : Function.Surjective (Representation.asAlgebraHom X.ρ) :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible X.ρ hρ
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (Representation.asAlgebraHom X.ρ).toLinearMap) hs
  have hcard : Module.finrank ℂ (MonoidAlgebra ℂ G) = Nat.card G := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ), Fintype.card_eq_nat_card]
  simpa [Module.finrank_linearMap, hcard, pow_two] using h

/-- A simple representation trivial on a normal subgroup has degree dividing the quotient order. -/
private theorem degree_dvd_quotient_card (G : Type) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (X : FDRep ℂ G) [Simple X]
    [Representation.IsTrivial (X.ρ.comp N.subtype)] :
    Module.finrank ℂ X ∣ Nat.card (G ⧸ N) := by
  have hcomp : (Representation.ofQuotient X.ρ N).comp (QuotientGroup.mk' N) = X.ρ := by
    ext g v
    rfl
  haveI : Representation.IsIrreducible ((Representation.ofQuotient X.ρ N).comp (QuotientGroup.mk' N)) := by
    rw [hcomp]
    exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
  haveI : Representation.IsIrreducible (Representation.ofQuotient X.ρ N) :=
    (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.isIrreducible_comp_surjective_iff (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (Representation.ofQuotient X.ρ N)).mp inferInstance
  exact _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card (Representation.ofQuotient X.ρ N)

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_CharacterFacts

section ScratchSource_CliffordPeak

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti D5.S3.FiniteGroups.CliffordConstituents.TauCeti D5.S3.FiniteGroups.CliffordDecomposition.TauCeti D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti
open scoped IsMulCommutative

variable {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
  [IsMulCommutative N]

private theorem inertia_eq_of_fixedPointFree
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (V : FDRep ℂ N) [Simple V] (hV : ¬ Representation.IsTrivial V.ρ) :
    (MulAction.stabilizer K (toSkeleton V)) = N := by
  apply le_antisymm
  · intro g hg
    by_contra hgN
    apply hV
    apply trivial_of_invariant_fixedPointFree V.ρ (MulAut.conjNormal g⁻¹)
    · exact hfix g⁻¹ (fun h => hgN (by simpa using N.inv_mem h))
    · intro n
      apply (abelian_character_eq_iff V _ _).mp
      convert char_conj_eq_of_mem_inertia hg n using 1
      congr 1
      apply Subtype.ext
      simp
  · exact le_inertia V

private theorem restriction_trivial_of_clifford_constituent_trivial
    (W : FDRep ℂ K) (V : FDRep ℂ N) [Finite (K ⧸ (MulAction.stabilizer K (toSkeleton V)))]
    (e : ℕ) (iso : ((Action.res (FGModuleCat ℂ) (N).subtype).obj W) ≅ (D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V e))
    (hdim : Module.finrank ℂ W = e * ((MulAction.stabilizer K (toSkeleton V))).index * Module.finrank ℂ V)
    [Representation.IsTrivial V.ρ] :
    Representation.IsTrivial (W.ρ.comp N.subtype) := by
  classical
  letI : Fintype (K ⧸ (MulAction.stabilizer K (toSkeleton V))) := Fintype.ofFinite _
  constructor
  intro n
  apply (_root_.D5.S3.FiniteGroups.InducedCharacterFormula.Representation.char_eq_finrank_iff (W.ρ.comp N.subtype)
    (isOfFinOrder_of_finite n)).mp
  have hc := congrFun (FDRep.char_iso iso) n
  rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.character_actionRes, _root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum,
    finsum_eq_sum_of_fintype] at hc
  have hv (q : K ⧸ (MulAction.stabilizer K (toSkeleton V))) :
      ((conjNormalFDRepFunctor (Quotient.out q)).obj V).character n = (Module.finrank ℂ V : ℂ) := by
    rw [char_conjNormalFDRep]
    change LinearMap.trace ℂ V (V.ρ _) = _
    rw [Representation.isTrivial_def, LinearMap.trace_id]
  simp_rw [hv] at hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hc
  change W.character (N.subtype n) = (Module.finrank ℂ W : ℂ)
  rw [hc, hdim]
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  push_cast
  ring

/-- The degree dichotomy supplied by fixed-point-free conjugation on an abelian kernel. -/
theorem degree_dvd_or_index_dvd_of_fixedPointFree
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (W : FDRep ℂ K) [Simple W] :
    Module.finrank ℂ W ∣ N.index ∨ N.index ∣ Module.finrank ℂ W := by
  obtain ⟨V, hV, hf, e, he, ⟨iso⟩, hdim⟩ := (D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank (N := N) W)
  letI := hV
  letI := hf
  by_cases ht : Representation.IsTrivial V.ρ
  · letI := ht
    letI := restriction_trivial_of_clifford_constituent_trivial N W V e iso hdim
    left
    simpa [Subgroup.index_eq_card] using degree_dvd_quotient_card K N W
  · right
    rw [inertia_eq_of_fixedPointFree N hfix V ht] at hdim
    exact ⟨e * Module.finrank ℂ V, by rw [hdim]; ring⟩

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_CliffordPeak
