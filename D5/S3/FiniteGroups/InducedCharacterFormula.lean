/- GID: D5/S3/FiniteGroups/InducedCharacterFormula
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/InducedCharacterFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite character theory: InducedCharacterFormula. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: Claude
Authors: The Tau Ceti contributors

This port uses repository namespaces and the pinned Mathlib API.

Replace these ports by direct imports when the repository’s pinned Mathlib supplies
equivalent declarations with the same hypotheses and conclusions.

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: TauCeti.ClassFunction.ind_ofFDRep
The induced representation character is computed from the coset permutation of its finite-dimensional model.
FDRep.clifford_restrict_finrank | proof_shape: content | escape_witness: D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.iSup_conjSubrep_eq_top | consumer: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree
Representation.char_eq_finrank_iff_of_pow_eq_one | proof_shape: bind-only | escape_witness: none | consumer: Representation.char_eq_finrank_iff
Representation.char_eq_finrank_iff | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial
TauCeti.stabilizer_quotientGroup_mk | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf
TauCeti.doubleCosetMk_eq_mk_iff_mem | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.doubleCosetMk_eq_mk_one_iff
TauCeti.doubleCoset_one_eq_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.doubleCosetMk_eq_mk_one_iff
TauCeti.doubleCosetMk_eq_mk_one_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.doubleCosetMk_eq_mk_one_iff_mem
TauCeti.doubleCosetMk_eq_mk_one_iff_mem | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff
QuotientGroup.mk_out_smul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mem_classFunction
TauCeti.indTerm | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.trace_ind_eq_sum_terms, TauCeti.character_indFDRep_sum_quotient, TauCeti.indClassFun, TauCeti.indClassFun_add, TauCeti.indClassFun_mem_classFunction, TauCeti.indClassFun_smul, TauCeti.indTerm_add, TauCeti.indTerm_apply, TauCeti.indTerm_conj, TauCeti.indTerm_eq_of_mk_eq_of_conj, TauCeti.indTerm_one, TauCeti.indTerm_smul, TauCeti.natCard_mul_indClassFun, TauCeti.natCard_mul_sum_indClassFun_mul, TauCeti.sum_indTerm_mul_eq_sum_subtype, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indTerm_mackeyClassFun
TauCeti.indTerm_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.trace_ind_eq_sum_terms, TauCeti.character_indFDRep_sum_quotient, TauCeti.natCard_mul_sum_indClassFun_mul, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indTerm_mackeyClassFun
TauCeti.indTerm_conj | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mem_classFunction, TauCeti.sum_indTerm_mul_eq_sum_subtype
TauCeti.indTerm_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.sum_indTerm_mul_eq_sum_subtype
TauCeti.indTerm_eq_of_mk_eq_of_conj | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indTerm_eq_of_mk_eq
TauCeti.indClassFun | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind, TauCeti.ClassFunction.ind_ofFDRep, TauCeti.characterPairing_ind, TauCeti.frobenius_reciprocity_classFunction, TauCeti.indClassFun_add, TauCeti.indClassFun_apply, TauCeti.indClassFun_mem_classFunction, TauCeti.indClassFun_ofFDRep_character, TauCeti.indClassFun_smul, TauCeti.natCard_mul_indClassFun, TauCeti.natCard_mul_sum_indClassFun_mul, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey
TauCeti.indClassFun_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_ofFDRep_character, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey
TauCeti.indTerm_add | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_add
TauCeti.indClassFun_add | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind
TauCeti.indTerm_smul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_smul
TauCeti.indClassFun_smul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind
TauCeti.indTerm_eq_of_mk_eq | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.character_indFDRep_sum_quotient, TauCeti.indClassFun_mem_classFunction, TauCeti.natCard_mul_indClassFun, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey
TauCeti.indClassFun_mem_classFunction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind
TauCeti.natCard_mul_indClassFun | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.natCard_mul_sum_indClassFun_mul
TauCeti.ClassFunction.ind | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind_apply, TauCeti.ClassFunction.ind_ofFDRep, TauCeti.characterPairing_ind, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
TauCeti.ClassFunction.ind_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind_ofFDRep, TauCeti.characterPairing_ind, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey
TauCeti.Rep.rightCosetFactor | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi, TauCeti.Rep.coindSubtypeEquivPi_apply, TauCeti.Rep.coindSubtypeEquivPi_ρ_apply, TauCeti.Rep.indSubtypeEquivPi_ρ_apply, TauCeti.Rep.rightCosetFactor_mul, TauCeti.Rep.rightCosetFactor_mul_out, TauCeti.Rep.rightCosetFactor_out, TauCeti.Rep.trace_ind_eq_sum_rightCosets, TauCeti.Rep.trace_ind_eq_sum_terms
TauCeti.Rep.rightCoset_mk_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi, TauCeti.Rep.coindSubtypeEquivPi_apply, TauCeti.Rep.rightCosetFactor_mul
TauCeti.Rep.rightCosetFactor_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi, TauCeti.Rep.coindSubtypeEquivPi_apply
TauCeti.Rep.rightCosetFactor_mul_out | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi, TauCeti.Rep.coindSubtypeEquivPi_apply, TauCeti.Rep.coindSubtypeEquivPi_ρ_apply, TauCeti.Rep.trace_ind_eq_sum_terms
TauCeti.Rep.rightCosetFactor_out | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi, TauCeti.Rep.coindSubtypeEquivPi_apply
TauCeti.Rep.coindSubtypeEquivPi | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi_apply, TauCeti.Rep.coindSubtypeEquivPi_ρ_apply, TauCeti.Rep.indSubtypeEquivPi, TauCeti.Rep.indSubtypeEquivPi_apply
TauCeti.Rep.coindSubtypeEquivPi_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.coindSubtypeEquivPi_ρ_apply
TauCeti.Rep.coindSubtypeEquivPi_ρ_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.indSubtypeEquivPi_ρ_apply
TauCeti.Rep.indSubtypeEquivPi | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.finiteDimensional_ind, TauCeti.Rep.finrank_ind, TauCeti.Rep.indSubtypeEquivPi_apply, TauCeti.Rep.indSubtypeEquivPi_ρ_apply, TauCeti.Rep.trace_ind_eq_sum_rightCosets
TauCeti.Rep.indSubtypeEquivPi_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.indSubtypeEquivPi_ρ_apply
TauCeti.Rep.indSubtypeEquivPi_ρ_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.trace_ind_eq_sum_rightCosets
TauCeti.Rep.finiteDimensional_ind | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indFDRep, TauCeti.indFDRepForgetEquiv
TauCeti.Rep.finrank_ind | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_indFDRep
TauCeti.indFDRep | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation, D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_finrank, D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_simple, TauCeti.ClassFunction.ind_ofFDRep, TauCeti.character_indFDRep_sum_quotient, TauCeti.finrank_indFDRep, TauCeti.indClassFun_ofFDRep_character, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_indFDRep_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff_doubleCoset, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff_of_normal, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_ofLinearCharacter_iff
TauCeti.indFDRepForgetEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.character_indFDRep_sum_quotient, TauCeti.finrank_indFDRep
TauCeti.finrank_indFDRep | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_finrank
TauCeti.sum_indTerm_mul_eq_sum_subtype | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.natCard_mul_sum_indClassFun_mul
TauCeti.natCard_mul_sum_indClassFun_mul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.frobenius_reciprocity_classFunction
TauCeti.frobenius_reciprocity_classFunction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_ind
TauCeti.characterPairing_ind | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey
TauCeti.doubleCosetMk_out_mk | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finite_doubleCosetQuotient
TauCeti.finite_doubleCosetQuotient | proof_shape: bind-only | escape_witness: none | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_indFDRep_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase, D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff_doubleCoset
TauCeti.Rep.quotientRightRelEquivQuotientLeftRel_mk | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.character_indFDRep_sum_quotient
TauCeti.Rep.character_mem_classFunction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.character_indFDRep_sum_quotient
TauCeti.Rep.trace_ind_eq_sum_rightCosets | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Rep.trace_ind_eq_sum_terms
TauCeti.Rep.trace_ind_eq_sum_terms | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.character_indFDRep_sum_quotient
TauCeti.character_indFDRep_sum_quotient | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_ofFDRep_character
TauCeti.indClassFun_ofFDRep_character | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ClassFunction.ind_ofFDRep
TauCeti.ClassFunction.ind_ofFDRep | proof_shape: content | escape_witness: TauCeti.ClassFunction.ind_ofFDRep | consumer: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
-/

import Mathlib.GroupTheory.DoubleCoset
import Mathlib.RepresentationTheory.FiniteIndex
import D5.S3.FiniteGroups.CharacterDegreeDivisibility
import D5.S3.FiniteGroups.CliffordDecomposition
import D5.S3.FiniteGroups.CliffordConstituents
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
namespace D5.S3.FiniteGroups.InducedCharacterFormula
namespace FDRep
end FDRep
namespace QuotientGroup
end QuotientGroup
namespace Representation
end Representation
namespace TauCeti
end TauCeti
namespace TauCeti.ClassFunction
end TauCeti.ClassFunction
namespace TauCeti.IndSmallModel
end TauCeti.IndSmallModel
namespace TauCeti.Rep
end TauCeti.Rep
section UpstreamSource6_0
open CategoryTheory
universe u v
namespace FDRep
open _root_.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep _root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti
variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.Normal]
theorem clifford_restrict_finrank [IsAlgClosed k] (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V)
      (hfinite : Finite (G ⧸ MulAction.stabilizer G (toSkeleton V))),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ Nonempty (((Action.res (FGModuleCat k) (N).subtype).obj W) ≅ (_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V) e) ∧
        Module.finrank k W =
          e * (MulAction.stabilizer G (toSkeleton V)).index * Module.finrank k V := by
  obtain ⟨V, hV, hfinite, e, he, ⟨iso⟩⟩ := (_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso (N := N) W)
  let _ : Finite (G ⧸ MulAction.stabilizer G (toSkeleton V)) := hfinite
  refine ⟨V, hV, hfinite, e, he, ⟨iso⟩, ?_⟩
  have h : Module.finrank k W = Module.finrank k ((_root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V) e) :=
    (isoToLinearEquiv iso).finrank_eq
  rw [finrank_cliffordSum, ← Subgroup.index_eq_card] at h
  rw [h]
  ring
end FDRep
end UpstreamSource6_0
section UpstreamSource6_1
open _root_.Module
universe u v w
namespace Representation
open _root_.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.Representation _root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation
section Monoid
variable {G : Type v} {V : Type w} [Monoid G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]
private theorem char_eq_finrank_iff_of_pow_eq_one (ρ : Representation ℂ G V) {g : G} {n : ℕ}
    (hn : n ≠ 0) (hg : g ^ n = 1) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.trace_eq_finrank_iff hn (by rw [← map_pow, hg, map_one])
theorem char_eq_finrank_iff (ρ : Representation ℂ G V) {g : G} (hg : IsOfFinOrder g) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  char_eq_finrank_iff_of_pow_eq_one ρ hg.orderOf_pos.ne' (pow_orderOf_eq_one g)
end Monoid
end Representation
end UpstreamSource6_1
section UpstreamSource6_3
open MulAction
open scoped Pointwise
attribute [simp] Subgroup.quotientEquivOfEq_mk
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
variable {G : Type*} [Group G]
@[simp]
theorem stabilizer_quotientGroup_mk (H : Subgroup G) (s : G) :
    stabilizer G ((s : G ⧸ H)) = MulAut.conj s • H := by
  have hs : ((s : G) : G ⧸ H) = s • ((1 : G) : G ⧸ H) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [hs, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_quotient]
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]
end TauCeti
end UpstreamSource6_3
section UpstreamSource6_5
open scoped Pointwise
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
variable {G : Type*} [Group G]
private theorem doubleCosetMk_eq_mk_iff_mem (H K : Subgroup G) (a s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K a ↔
      s ∈ DoubleCoset.doubleCoset a (H : Set G) (K : Set G) := by
  rw [eq_comm, DoubleCoset.eq, DoubleCoset.mem_doubleCoset]
  simp
private theorem doubleCoset_one_eq_mul (H K : Subgroup G) :
    DoubleCoset.doubleCoset (1 : G) (H : Set G) (K : Set G) = (H : Set G) * K := by
  simp [DoubleCoset.doubleCoset]
private theorem doubleCosetMk_eq_mk_one_iff (H K : Subgroup G) (s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K 1 ↔ s ∈ (H : Set G) * K := by
  rw [doubleCosetMk_eq_mk_iff_mem, doubleCoset_one_eq_mul]
@[simp]
theorem doubleCosetMk_eq_mk_one_iff_mem (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [doubleCosetMk_eq_mk_one_iff, coe_mul_coe, SetLike.mem_coe]
end TauCeti
end UpstreamSource6_5
section UpstreamSource6_6
namespace QuotientGroup
open _root_.QuotientGroup
variable {G : Type*} [Group G] {H : Subgroup G}
@[to_additive]
private theorem mk_out_smul (g : G) (q : G ⧸ H) : ((g • q).out : G ⧸ H) = (g * q.out : G) := by
  simp [← smul_eq_mul]
end QuotientGroup
end UpstreamSource6_6
section UpstreamSource6_7
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
universe u v
variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}
section AddCommMonoid
variable [AddCommMonoid k]
open scoped Classical in
noncomputable def indTerm (f : S → k) (g x : G) : k :=
  if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0
open scoped Classical in
theorem indTerm_apply (f : S → k) (g x : G) :
    indTerm f g x = if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 :=
  (rfl)
private theorem indTerm_conj (f : S → k) (g x c : G) :
    indTerm f (c * g * c⁻¹) x = indTerm f g (c⁻¹ * x) := by
  classical
  have h : x⁻¹ * (c * g * c⁻¹) * x = (c⁻¹ * x)⁻¹ * g * (c⁻¹ * x) := by group
  simp only [indTerm, h]
open scoped Classical in
private theorem indTerm_one (f : S → k) (g : G) :
    indTerm f g 1 = if h : g ∈ S then f ⟨g, h⟩ else 0 := by
  simp [indTerm]
private theorem indTerm_eq_of_mk_eq_of_conj {f : S → k}
    (hf : ∀ y s : S, f (s * y * s⁻¹) = f y) (g x y : G)
    (hxy : (QuotientGroup.mk x : G ⧸ S) = QuotientGroup.mk y) :
    indTerm f g x = indTerm f g y := by
  have hs : x⁻¹ * y ∈ S := QuotientGroup.eq.mp hxy
  let s : S := ⟨x⁻¹ * y, hs⟩
  have hy : x * (s : G) = y := mul_inv_cancel_left x y
  rw [← hy]
  classical
  by_cases hx : x⁻¹ * g * x ∈ S
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∈ S := by
      simpa [mul_assoc] using S.mul_mem (S.mul_mem (S.inv_mem s.2) hx) s.2
    rw [indTerm, dite_eq_left hx, indTerm, dite_eq_left hxs]
    have helem : (⟨(x * (s : G))⁻¹ * g * (x * s), hxs⟩ : S) =
        s⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [helem, hf ⟨x⁻¹ * g * x, hx⟩ s⁻¹]
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∉ S := by
      intro h
      exact hx (by simpa [mul_assoc] using S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2))
    rw [indTerm, dite_eq_right hx, indTerm, dite_eq_right hxs]
open scoped Classical in
noncomputable def indClassFun (S : Subgroup G) [S.FiniteIndex] (f : S → k) : G → k := fun g =>
  letI := Fintype.ofFinite (G ⧸ S)
  ∑ t : G ⧸ S, indTerm f g (Quotient.out t)
open scoped Classical in
theorem indClassFun_apply [S.FiniteIndex] (f : S → k) (g : G) :
    indClassFun S f g =
      letI := Fintype.ofFinite (G ⧸ S)
      ∑ t : G ⧸ S,
        if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ S then
          f ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩
        else 0 :=
  (rfl)
private theorem indTerm_add (f₁ f₂ : S → k) (g x : G) :
    indTerm (f₁ + f₂) g x = indTerm f₁ g x + indTerm f₂ g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]
@[simp]
private theorem indClassFun_add [S.FiniteIndex] (f₁ f₂ : S → k) :
    indClassFun S (f₁ + f₂) = indClassFun S f₁ + indClassFun S f₂ := by
  funext g
  simp [indClassFun, indTerm_add, Finset.sum_add_distrib]
end AddCommMonoid
section Semiring
variable [Semiring k]
private theorem indTerm_smul (c : k) (f : S → k) (g x : G) :
    indTerm (c • f) g x = c * indTerm f g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]
@[simp]
private theorem indClassFun_smul [S.FiniteIndex] (c : k) (f : S → k) :
    indClassFun S (c • f) = c • indClassFun S f := by
  funext g
  simp [indClassFun, indTerm_smul, Finset.mul_sum]
section ClassFun
variable {f : S → k}
theorem indTerm_eq_of_mk_eq (hf : f ∈ ClassFunction k S) (g x y : G)
    (hxy : (QuotientGroup.mk x : G ⧸ S) = QuotientGroup.mk y) :
    indTerm f g x = indTerm f g y :=
  indTerm_eq_of_mk_eq_of_conj (ClassFunction.mem_iff.mp hf) g x y hxy
private theorem indClassFun_mem_classFunction [S.FiniteIndex] (hf : f ∈ ClassFunction k S) :
    indClassFun S f ∈ ClassFunction k G := by
  refine ClassFunction.mem_iff.mpr fun g c => ?_
  let := Fintype.ofFinite (G ⧸ S)
  calc indClassFun S f (c * g * c⁻¹)
      = ∑ t : G ⧸ S, indTerm f g (c⁻¹ * Quotient.out t) := by
        simp only [indClassFun, indTerm_conj]
    _ = indClassFun S f g :=
        Fintype.sum_equiv (MulAction.toPerm c⁻¹) _ _ fun t =>
          indTerm_eq_of_mk_eq hf _ _ _ (_root_.D5.S3.FiniteGroups.InducedCharacterFormula.QuotientGroup.mk_out_smul _ t).symm
end ClassFun
open scoped Classical in
private theorem natCard_mul_indClassFun [Fintype G] {f : S → k} (hf : f ∈ ClassFunction k S) (g : G) :
    (Nat.card S : k) * indClassFun S f g =
      ∑ x : G, if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 := by
  let := Fintype.ofFinite (G ⧸ S)
  let e : G ≃ (G ⧸ S) × S := Subgroup.groupEquivQuotientProdSubgroup
  have hterm (q : G ⧸ S) (s : S) : indTerm f g (e.symm (q, s)) = indTerm f g q.out := by
    refine indTerm_eq_of_mk_eq hf _ _ _ ?_
    exact (congrArg Prod.fst (e.apply_symm_apply (q, s))).trans (Quotient.out_eq' q).symm
  calc (Nat.card S : k) * indClassFun S f g
      = ∑ q : G ⧸ S, ∑ _s : S, indTerm f g q.out := by
        simp [indClassFun, Finset.mul_sum]
    _ = ∑ q : G ⧸ S, ∑ s : S, indTerm f g (e.symm (q, s)) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ => (hterm q s).symm
    _ = ∑ x : G, indTerm f g x := by
        rw [← e.symm.sum_comp (fun x => indTerm f g x), Fintype.sum_prod_type]
    _ = _ := rfl
namespace ClassFunction
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction
noncomputable def ind (S : Subgroup G) [S.FiniteIndex] :
    ClassFunction k S →ₗ[k] ClassFunction k G where
  toFun f := ⟨indClassFun S f.1, indClassFun_mem_classFunction f.2⟩
  map_add' f₁ f₂ := Subtype.ext (indClassFun_add f₁.1 f₂.1)
  map_smul' c f := Subtype.ext (indClassFun_smul c f.1)
@[simp]
theorem ind_apply [S.FiniteIndex] (f : ClassFunction k S) (g : G) :
    (ind S f).1 g = indClassFun S f.1 g :=
  (rfl)
end ClassFunction
end Semiring
end TauCeti
end UpstreamSource6_7
section UpstreamSource6_9
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
open CategoryTheory
universe u v w
namespace Rep
variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}
section CosetModel
variable [CommRing k]
private noncomputable def rightCosetFactor (g : G) : S :=
  ⟨g * (Quotient.out (Quotient.mk'' g :
      Quotient (QuotientGroup.rightRel S)))⁻¹,
    QuotientGroup.rightRel_apply.mp
      (Quotient.eq''.mp (Quotient.out_eq' (Quotient.mk'' g)))⟩
@[simp]
private theorem rightCoset_mk_mul (s : S) (g : G) :
    Quotient.mk'' ((s : G) * g) =
      (Quotient.mk'' g : Quotient (QuotientGroup.rightRel S)) :=
  Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr (by simp))
@[simp]
private theorem rightCosetFactor_mul (s : S) (g : G) :
    rightCosetFactor (S := S) ((s : G) * g) = s * rightCosetFactor (S := S) g := by
  ext
  simp [rightCosetFactor, mul_assoc]
@[simp]
private theorem rightCosetFactor_mul_out (g : G) : (rightCosetFactor (S := S) g : G) *
        Quotient.out (Quotient.mk'' g :
          Quotient (QuotientGroup.rightRel S)) = g :=
  mul_eq_of_eq_mul_inv rfl
@[simp]
private theorem rightCosetFactor_out (q : Quotient (QuotientGroup.rightRel S)) :
    rightCosetFactor (S := S) q.out = 1 := by
  ext
  simp [rightCosetFactor]
private noncomputable def coindSubtypeEquivPi (A : Rep.{w} k S) :
    Rep.coind S.subtype A ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) where
  toFun f q := f.1 q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x :=
    ⟨fun g ↦ A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)),
      fun s g ↦ by
        change A.ρ (rightCosetFactor (S := S) ((s : G) * g))
          (x (Quotient.mk'' ((s : G) * g))) =
            A.ρ s (A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)))
        rw [rightCoset_mk_mul, rightCosetFactor_mul, ← Module.End.mul_apply, ← map_mul]⟩
  left_inv f := by
    ext g
    have h := f.2 (rightCosetFactor (S := S) g)
      (Quotient.out (Quotient.mk'' g :
        Quotient (QuotientGroup.rightRel S)))
    change f.1 ((rightCosetFactor (S := S) g : G) *
      Quotient.out (Quotient.mk'' g :
        Quotient (QuotientGroup.rightRel S))) =
        A.ρ (rightCosetFactor (S := S) g)
          (f.1 (Quotient.out (Quotient.mk'' g :
            Quotient (QuotientGroup.rightRel S)))) at h
    simpa only [rightCosetFactor_mul_out] using h.symm
  right_inv x := by
    funext q
    change A.ρ (rightCosetFactor (S := S) q.out) (x (Quotient.mk'' q.out)) = x q
    rw [rightCosetFactor_out]
    simp
@[simp]
private theorem coindSubtypeEquivPi_apply (A : Rep.{w} k S)
    (f : Rep.coind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    (dsimp% only (coindSubtypeEquivPi A f q)) = f.1 q.out := by
  rw [coindSubtypeEquivPi]
  rfl
private theorem coindSubtypeEquivPi_ρ_apply (A : Rep.{w} k S) (g : G)
    (f : Rep.coind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    coindSubtypeEquivPi A ((Rep.coind S.subtype A).ρ g f) q =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (coindSubtypeEquivPi A f (Quotient.mk'' (q.out * g))) := by
  have h := f.2 (rightCosetFactor (S := S) (q.out * g))
    (Quotient.out (Quotient.mk'' (q.out * g) :
      Quotient (QuotientGroup.rightRel S)))
  change f.1 ((rightCosetFactor (S := S) (q.out * g) : G) *
    Quotient.out (Quotient.mk'' (q.out * g) :
      Quotient (QuotientGroup.rightRel S))) =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (f.1 (Quotient.out (Quotient.mk'' (q.out * g) :
          Quotient (QuotientGroup.rightRel S)))) at h
  rw [coindSubtypeEquivPi_apply, coindSubtypeEquivPi_apply]
  change f.1 (q.out * g) = _
  simpa only [rightCosetFactor_mul_out] using h
private noncomputable def indSubtypeEquivPi [S.FiniteIndex] (A : Rep.{max w u} k S) :
    Rep.ind S.subtype A ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  exact
    ((forget₂ (Rep k G) (ModuleCat k)).mapIso
      (Rep.indCoindIso.{w, u, v} A)).toLinearEquiv.trans (coindSubtypeEquivPi A)
private theorem indSubtypeEquivPi_apply [S.FiniteIndex] (A : Rep.{max w u} k S)
    (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A x q =
      ((letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
        Rep.indCoindIso.{w, u, v} A).hom.hom x).1 q.out := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  rw [indSubtypeEquivPi]
  rfl
private theorem indSubtypeEquivPi_ρ_apply [S.FiniteIndex] (A : Rep.{max w u} k S) (g : G)
    (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A ((Rep.ind S.subtype A).ρ g x) q =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (indSubtypeEquivPi A x (Quotient.mk'' (q.out * g))) := by
  rw [indSubtypeEquivPi_apply, indSubtypeEquivPi_apply, Rep.hom_comm_apply]
  exact coindSubtypeEquivPi_ρ_apply A g _ q
end CosetModel
section Dimension
variable [Field k]
private noncomputable instance finiteDimensional_ind [S.FiniteIndex] (A : Rep.{max w u} k S)
    [FiniteDimensional k A] : FiniteDimensional k (Rep.ind S.subtype A) := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  let := S.fintypeQuotientOfFiniteIndex
  let : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  let : FiniteDimensional k
      (Quotient (QuotientGroup.rightRel S) → A) := inferInstance
  exact (indSubtypeEquivPi A).symm.finiteDimensional
private theorem finrank_ind [S.FiniteIndex] (A : Rep.{max w u} k S) [FiniteDimensional k A] :
    (dsimp% only (Module.finrank k (Rep.ind S.subtype A))) = S.index * Module.finrank k A := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  let := S.fintypeQuotientOfFiniteIndex
  let : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  rw [LinearEquiv.finrank_eq (indSubtypeEquivPi A), Module.finrank_pi_fintype]
  simp [QuotientGroup.card_quotient_rightRel, Subgroup.index_eq_card]
end Dimension
end Rep
noncomputable def indFDRep {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) : FDRep k G := by
  let A' := (forget₂ (FDRep k S) (Rep k S)).obj A
  let V := Rep.ind S.subtype A'
  letI : FiniteDimensional k V := Rep.finiteDimensional_ind.{u, v, 0} A'
  exact D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrink V.ρ
private noncomputable def indFDRepForgetEquiv {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) :
    ((forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A)).ρ.Equiv
      (Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)).ρ := by
  let A' := (forget₂ (FDRep k S) (Rep k S)).obj A
  let V := Rep.ind S.subtype A'
  letI : FiniteDimensional k V := Rep.finiteDimensional_ind.{u, v, 0} A'
  exact D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrinkEquiv V.ρ
@[simp]
theorem finrank_indFDRep {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) :
    Module.finrank k (indFDRep A) = S.index * Module.finrank k A := by
  rw [← _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.finrankForgetObject (indFDRep A),
    LinearEquiv.finrank_eq (indFDRepForgetEquiv A).toLinearEquiv,
    Rep.finrank_ind, _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.finrankForgetObject]
end TauCeti
end UpstreamSource6_9
section UpstreamSource7_0
open CategoryTheory
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
universe u v
section ClassFunctions
variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}
section Semiring
variable [Semiring k]
open scoped Classical in
private theorem sum_indTerm_mul_eq_sum_subtype [Fintype G] (f : S → k) {h : G → k}
    (hh : h ∈ ClassFunction k G) (x : G) :
    (∑ g : G, indTerm f g x * h g⁻¹) = ∑ s : S, f s * h ((s : G)⁻¹) := by
  have hinv (y : G) : (x * y * x⁻¹)⁻¹ = x * y⁻¹ * x⁻¹ := conj_inv
  calc (∑ g : G, indTerm f g x * h g⁻¹)
      = ∑ y : G, indTerm f (x * y * x⁻¹) x * h (x * y * x⁻¹)⁻¹ := by
        refine (Fintype.sum_equiv ((Equiv.mulRight x⁻¹).trans (Equiv.mulLeft x)) _ _ ?_).symm
        intro y
        simp [mul_assoc]
    _ = ∑ y : G, (if hy : y ∈ S then f ⟨y, hy⟩ else 0) * h y⁻¹ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [indTerm_conj, inv_mul_cancel, indTerm_one]
        congr 1
        rw [hinv y]
        exact ClassFunction.mem_iff.mp hh y⁻¹ x
    _ = ∑ y ∈ Finset.univ.filter (fun y : G => y ∈ S),
          (if hy : y ∈ S then f ⟨y, hy⟩ else 0) * h y⁻¹ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy => ?_).symm
        rw [Finset.mem_filter] at hy
        rw [dite_eq_right fun hy' => hy ⟨Finset.mem_univ y, hy'⟩, zero_mul]
    _ = ∑ s : S, (if hy : (s : G) ∈ S then f ⟨(s : G), hy⟩ else 0) * h (s : G)⁻¹ :=
        Finset.sum_subtype (p := fun y : G => y ∈ S) _ (by simp) _
    _ = ∑ s : S, f s * h ((s : G)⁻¹) :=
        Finset.sum_congr rfl fun s _ => by rw [dite_eq_left s.2]
open scoped Classical in
private theorem natCard_mul_sum_indClassFun_mul [Fintype G] {f : S → k}
    (hf : f ∈ ClassFunction k S) {h : G → k} (hh : h ∈ ClassFunction k G) :
    (Nat.card S : k) * ∑ g : G, indClassFun S f g * h g⁻¹
      = (Nat.card G : k) * ∑ s : S, f s * h ((s : G)⁻¹) :=
  calc (Nat.card S : k) * ∑ g : G, indClassFun S f g * h g⁻¹
      = ∑ g : G, ((Nat.card S : k) * indClassFun S f g) * h g⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => (mul_assoc _ _ _).symm
    _ = ∑ g : G, (∑ x : G, indTerm f g x) * h g⁻¹ := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [natCard_mul_indClassFun hf g]
        simp only [indTerm_apply]
    _ = ∑ x : G, ∑ g : G, indTerm f g x * h g⁻¹ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun g _ => by rw [Finset.sum_mul]
    _ = ∑ _x : G, ∑ s : S, f s * h ((s : G)⁻¹) :=
        Finset.sum_congr rfl fun x _ => sum_indTerm_mul_eq_sum_subtype f hh x
    _ = (Nat.card G : k) * ∑ s : S, f s * h ((s : G)⁻¹) := by
        simp [Nat.card_eq_fintype_card]
end Semiring
variable [Field k]
open scoped Classical in
private theorem frobenius_reciprocity_classFunction [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k S) (h : ClassFunction k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, indClassFun S f.1 g * h.1 g⁻¹ =
      (Nat.card S : k)⁻¹ * ∑ s : S, f.1 s * h.1 ((s : G)⁻¹) := by
  have hS : IsUnit (Nat.card S : k) := isUnit_natCard_subgroup S hG
  set X : k := ∑ s : S, f.1 s * h.1 ((s : G)⁻¹) with hX
  refine mul_left_cancel₀ hS.ne_zero ?_
  calc (Nat.card S : k) * ((Nat.card G : k)⁻¹ * ∑ g : G, indClassFun S f.1 g * h.1 g⁻¹)
      = (Nat.card G : k)⁻¹ * ((Nat.card S : k) * ∑ g : G, indClassFun S f.1 g * h.1 g⁻¹) := by
        ring
    _ = (Nat.card G : k)⁻¹ * ((Nat.card G : k) * X) := by
        rw [hX, natCard_mul_sum_indClassFun_mul f.2 h.2]
    _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hG.ne_zero, one_mul]
    _ = (Nat.card S : k) * ((Nat.card S : k)⁻¹ * X) := by
        rw [← mul_assoc, mul_inv_cancel₀ hS.ne_zero, one_mul]
open scoped Classical in
theorem characterPairing_ind [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k S) (h : ClassFunction k G) :
    ClassFunction.characterPairing (ClassFunction.ind S f) h =
      ClassFunction.characterPairing f (ClassFunction.comap S.subtype h) := by
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply]
  simpa only [ClassFunction.ind_apply, ClassFunction.comap_apply, Subgroup.coe_subtype,
    Subgroup.coe_inv] using frobenius_reciprocity_classFunction hG f h
end ClassFunctions
end TauCeti
end UpstreamSource7_0
section UpstreamSource7_1
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
variable {G : Type*} [Group G]
private theorem doubleCosetMk_out_mk (H K : Subgroup G) (g : G) :
    DoubleCoset.mk H K (Quotient.out (QuotientGroup.mk g : G ⧸ K)) = DoubleCoset.mk H K g := by
  have hmem : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g))
  rw [DoubleCoset.eq]
  exact ⟨1, H.one_mem, _, hmem, by simp⟩
instance finite_doubleCosetQuotient (H K : Subgroup G) [K.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_surjective (fun t : G ⧸ K => DoubleCoset.mk H K t.out) fun d =>
    ⟨QuotientGroup.mk d.out, (doubleCosetMk_out_mk H K d.out).trans (DoubleCoset.out_eq' d)⟩
end TauCeti
end UpstreamSource7_1
section UpstreamSource7_2
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
open CategoryTheory
universe u v
namespace Rep
variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
private theorem quotientRightRelEquivQuotientLeftRel_mk (S : Subgroup G) (x : G) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel S (Quotient.mk'' x) =
      QuotientGroup.mk x⁻¹ := by
  change @Quotient.map' G G (QuotientGroup.rightRel S) (QuotientGroup.leftRel S)
    (fun y => y⁻¹) (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply]
      exact fun h => (congrArg (· ∈ S) (by simp)).mp (S.inv_mem h))
      (@Quotient.mk'' G (QuotientGroup.rightRel S) x) =
      @Quotient.mk'' G (QuotientGroup.leftRel S) x⁻¹
  apply Quotient.map'_mk''
private theorem character_mem_classFunction {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k S V) : ρ.character ∈ ClassFunction k S :=
  ClassFunction.mem_iff.mpr ρ.char_conj
open scoped Classical in
private theorem trace_ind_eq_sum_rightCosets [S.FiniteIndex] [Fintype ((Quotient (QuotientGroup.rightRel S)))]
    (A : Rep.{u} k S) [FiniteDimensional k A] (g : G) :
    LinearMap.trace k (Rep.ind S.subtype A) ((Rep.ind S.subtype A).ρ g) =
      ∑ q : (Quotient (QuotientGroup.rightRel S)),
        if Quotient.mk'' (q.out * g) = q then
          LinearMap.trace k A (A.ρ (rightCosetFactor (S := S) (q.out * g)))
        else 0 := by
  let e := indSubtypeEquivPi A
  rw [← LinearMap.trace_conj' ((Rep.ind S.subtype A).ρ g) e]
  have hT (x : (Quotient (QuotientGroup.rightRel S)) → A) (q : (Quotient (QuotientGroup.rightRel S))) :
      e.conj ((Rep.ind S.subtype A).ρ g) x q =
        A.ρ (rightCosetFactor (S := S) (q.out * g))
          (x (Quotient.mk'' (q.out * g))) := by
    have he : indSubtypeEquivPi A (e.symm x) = x := by
      simpa only [e] using e.apply_symm_apply x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [indSubtypeEquivPi_ρ_apply]
    exact congrArg (A.ρ (rightCosetFactor (S := S) (q.out * g)))
      (congrFun he (Quotient.mk'' (q.out * g)))
  rw [_root_.D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq
    (T := e.conj ((Rep.ind S.subtype A).ρ g))
    (σ := fun q => Quotient.mk'' (q.out * g))
    (f := fun q => A.ρ (rightCosetFactor (S := S) (q.out * g))) hT]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Quotient.mk'' (q.out * g) = q <;> simp [hq]
open scoped Classical in
private theorem trace_ind_eq_sum_terms [S.FiniteIndex] [Fintype ((Quotient (QuotientGroup.rightRel S)))]
    (A : Rep.{u} k S) [FiniteDimensional k A] (g : G) :
    LinearMap.trace k (Rep.ind S.subtype A) ((Rep.ind S.subtype A).ρ g) =
      ∑ q : (Quotient (QuotientGroup.rightRel S)), indTerm A.ρ.character g q.out⁻¹ := by
  rw [trace_ind_eq_sum_rightCosets A g]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Quotient.mk'' (q.out * g) = q
  · have hmem : q.out * g * q.out⁻¹ ∈ S := by
      have hq' :
          Quotient.mk'' (q.out * g) = (Quotient.mk'' q.out : (Quotient (QuotientGroup.rightRel S))) :=
        hq.trans (Quotient.out_eq' q).symm
      have hinv : q.out * g⁻¹ * q.out⁻¹ ∈ S := by
        simpa [mul_assoc] using
          (QuotientGroup.rightRel_apply.mp (Quotient.exact' hq'))
      simpa [mul_assoc] using S.inv_mem hinv
    rw [ite_eq_left hq, indTerm_apply, dite_eq_left (by simpa [mul_assoc] using hmem)]
    have hfactor :
        rightCosetFactor (S := S) (q.out * g) =
          ⟨q.out * g * q.out⁻¹, hmem⟩ := by
      apply Subtype.ext
      have hout :
          Quotient.out (Quotient.mk'' (q.out * g) : (Quotient (QuotientGroup.rightRel S))) = q.out :=
        Quotient.out_inj.mpr hq
      calc
        (rightCosetFactor (S := S) (q.out * g) : G) =
            (rightCosetFactor (S := S) (q.out * g) : G) *
              Quotient.out (Quotient.mk'' (q.out * g) : (Quotient (QuotientGroup.rightRel S))) * q.out⁻¹ := by
                rw [hout]
                simp
        _ = q.out * g * q.out⁻¹ := by rw [rightCosetFactor_mul_out]
    rw [hfactor]
    simp only [Representation.character, inv_inv]
  · have hmem : q.out * g * q.out⁻¹ ∉ S := by
      intro h
      apply hq
      refine (Quotient.sound' ?_).trans (Quotient.out_eq' q)
      rw [QuotientGroup.rightRel_apply]
      simpa [mul_assoc] using S.inv_mem h
    rw [ite_eq_right hq, indTerm_apply, dite_eq_right (by simpa [mul_assoc] using hmem)]
end Rep
open scoped Classical in
private theorem character_indFDRep_sum_quotient {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) (g : G) :
    (indFDRep (k := k) (G := G) A).character g =
      letI := Fintype.ofFinite (G ⧸ S)
      ∑ t : G ⧸ S,
        if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ S then
          A.character ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩
        else 0 := by
  have hindCharacter :
    (indFDRep (k := k) (G := G) A).character g =
        (Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)).ρ.character g :=
    (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.characterForgetObject (indFDRep (k := k) (G := G) A) g).symm.trans (congrFun
      (Representation.char_iso (indFDRepForgetEquiv A)) g)
  let := Fintype.ofFinite (G ⧸ S)
  let A' : Rep.{u} k S := (forget₂ (FDRep k S) (Rep k S)).obj A
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  let : Fintype ((Quotient (QuotientGroup.rightRel S))) := QuotientGroup.fintypeQuotientRightRel
  have hforgetCharacter (s : S) : A'.ρ.character s = A.character s :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.characterForgetObject A s
  have hcharacter :
      (indFDRep (k := k) (G := G) A).character g =
        LinearMap.trace k (Rep.ind S.subtype A') ((Rep.ind S.subtype A').ρ g) := by
    rw [hindCharacter, Representation.character]
  rw [hcharacter, Rep.trace_ind_eq_sum_terms A' g]
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel S
  calc
    (∑ q : (Quotient (QuotientGroup.rightRel S)), indTerm A'.ρ.character g q.out⁻¹) =
        ∑ t : G ⧸ S, indTerm A'.ρ.character g t.out := by
      apply Fintype.sum_equiv e
      intro q
      refine indTerm_eq_of_mk_eq (Rep.character_mem_classFunction A'.ρ) _ _ _ ?_
      have heq : e q = QuotientGroup.mk q.out⁻¹ := by
        calc
          e q = e (Quotient.mk'' q.out) :=
            congrArg e (Quotient.out_eq' q).symm
          _ = QuotientGroup.mk q.out⁻¹ :=
            Rep.quotientRightRelEquivQuotientLeftRel_mk S q.out
      exact heq.symm.trans (Quotient.out_eq' (e q)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [indTerm_apply]
      by_cases hmem : t.out⁻¹ * g * t.out ∈ S
      · rw [dite_eq_left hmem, dite_eq_left hmem, hforgetCharacter]
      · rw [dite_eq_right hmem, dite_eq_right hmem]
section ClassFun
variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
@[simp]
private theorem indClassFun_ofFDRep_character [S.FiniteIndex] (A : FDRep k S) :
    indClassFun S A.character = (indFDRep (k := k) (G := G) A).character := by
  funext g
  rw [indClassFun_apply]
  exact (character_indFDRep_sum_quotient A g).symm
@[simp]
theorem ClassFunction.ind_ofFDRep [S.FiniteIndex] (A : FDRep k S) :
    ClassFunction.ind S ((ClassFunction.ofCharacter (FDRep.ρ A))) =
      (ClassFunction.ofCharacter (FDRep.ρ (indFDRep (k := k) (G := G) A))) := by
  have hcoe : (((ClassFunction.ofCharacter (FDRep.ρ A)) : ClassFunction k S) : S → k) = A.character :=
    rfl
  refine Subtype.ext (funext fun g => ?_)
  rw [ClassFunction.ind_apply, hcoe, indClassFun_ofFDRep_character, ClassFunction.ofCharacter_apply]
  rfl
end ClassFun
end TauCeti
end UpstreamSource7_2
end D5.S3.FiniteGroups.InducedCharacterFormula
