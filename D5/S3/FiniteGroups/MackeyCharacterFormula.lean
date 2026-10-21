/- GID: D5/S3/FiniteGroups/MackeyCharacterFormula
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/MackeyCharacterFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite character theory: MackeyCharacterFormula. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: The Tau Ceti contributors

This port uses repository namespaces and the pinned Mathlib API.

Replace these ports by direct imports when the repository’s pinned Mathlib supplies
equivalent declarations with the same hypotheses and conclusions.

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: TauCeti.simple_indFDRep_ofLinearCharacter_iff
The double-coset character pairing gives irreducibility exactly when the nontrivial conjugates of the linear character differ.
TauCeti.mackeySubgroup | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.MackeyDisjoint
TauCeti.mackeySubgroup_def | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeySubgroup_conj
TauCeti.mem_mackeySubgroup_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indTerm_mackeyClassFun
TauCeti.mackeySubgroup_le_right | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupOfCongr_apply
TauCeti.mackeySubgroup_le_conj | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeyToH_apply
TauCeti.mackeySubgroup_of_mem | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeySubgroup_subgroupOf_self_of_mem
TauCeti.mackeySubgroup_subgroupOf_self_of_mem | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeySubgroupSelfEquiv
TauCeti.mackeySubgroupSelfEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.coe_mackeySubgroupSelfEquiv_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.mackeySubgroup_of_normal | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupNormalEquiv_apply
TauCeti.mackeySubgroupNormalEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupNormalEquiv
TauCeti.coe_mackeySubgroupNormalEquiv_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupNormalEquiv
TauCeti.coe_mackeySubgroupNormalEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_hom_res_mackeyToH_of_normal
TauCeti.mackeySubgroup_conj | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeySubgroupCongr
TauCeti.mackeySubgroupCongr | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupCongr_apply
TauCeti.coe_mackeySubgroupCongr_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupOfCongr_apply
TauCeti.mackeySubgroupOfCongr | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.coe_mackeySubgroupOfCongr_apply
TauCeti.coe_mackeySubgroupOfCongr_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right
TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.card_orbit_eq_relIndex
TauCeti.card_orbit_eq_relIndex | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.instIsFiniteRelIndexMackeySubgroup
TauCeti.instIsFiniteRelIndexMackeySubgroup | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_ind_ind_mackey
TauCeti.mackeyCoset | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mackey
TauCeti.mackeyCoset_mk | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeyCoset_out
TauCeti.mackeyCoset_out | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mackey
TauCeti.mackeyQuotientEquiv | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mackey
TauCeti.mackeyQuotientEquiv_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mackey
TauCeti.mackeyToH | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.MackeyDisjoint
TauCeti.coe_mackeyToH_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.mackeyClassFun | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.mackeyClassFun_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.mackeyClassFun_mem_classFunction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeyClassFunction
TauCeti.mackeyClassFunction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_ind_ind_mackey
TauCeti.mackeyClassFunction_coe | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_mackeyClassFunction_of_mem
TauCeti.indTerm_mackeyClassFun | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.indClassFun_mackey
TauCeti.indClassFun_mackey | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.comap_subtype_ind_mackey
TauCeti.comap_subtype_ind_mackey | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_ind_ind_mackey
TauCeti.character_res_mackeyToH | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.ofFDRep_res_mackeyToH
TauCeti.characterPairing_ind_ind_mackey | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_ind_ind_mackey_erase
TauCeti.characterPairing_mackeyClassFunction_of_mem | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.characterPairing_ind_ind_mackey_erase
TauCeti.characterPairing_ind_ind_mackey_erase | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
TauCeti.ofFDRep_res_mackeyToH | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.natCast_finrank_hom_indFDRep_mackey_erase
TauCeti.natCast_finrank_hom_indFDRep_mackey_erase | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_hom_indFDRep_mackey_erase
TauCeti.finrank_hom_indFDRep_mackey_erase | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff_doubleCoset
TauCeti.finrank_hom_res_mackeyToH_of_normal | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal
TauCeti.res_ρ_comm_ρAut_hom | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right
TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeyDisjoint_mul_left_mul_right_iff
TauCeti.isZero_of_finrank_end_eq_zero | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff_doubleCoset
TauCeti.finrank_hom_eq_zero_of_isZero | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff_doubleCoset
TauCeti.MackeyDisjoint | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeyDisjoint_iff_finrank_eq_zero
TauCeti.mackeyDisjoint_iff_finrank_eq_zero | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal
TauCeti.mackeyDisjoint_mul_left_mul_right_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff
TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff_of_normal
TauCeti.simple_indFDRep_iff_doubleCoset | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff
TauCeti.simple_indFDRep_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_iff_of_normal
TauCeti.simple_indFDRep_iff_of_normal | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_ofLinearCharacter_iff
Representation.linearCharacterRepresentation | proof_shape: bind-only | escape_witness: none | consumer: FDRep.ofLinearCharacter
Representation.isIrreducible_linearCharacterRepresentation | proof_shape: bind-only | escape_witness: none | consumer: FDRep.simple_ofLinearCharacter
FDRep.ofLinearCharacter | proof_shape: bind-only | escape_witness: none | consumer: FDRep.finrank_ofLinearCharacter
FDRep.actionRes_obj_ofLinearCharacter | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.conjNormalFDRep_ofLinearCharacter
FDRep.finrank_ofLinearCharacter | proof_shape: bind-only | escape_witness: none | consumer: BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_finrank
FDRep.simple_ofLinearCharacter | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_ofLinearCharacter_iff
FDRep.nonempty_iso_ofLinearCharacter_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff
TauCeti.conjNormalFDRep_ofLinearCharacter | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff
TauCeti.nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.simple_indFDRep_ofLinearCharacter_iff
TauCeti.simple_indFDRep_ofLinearCharacter_iff | proof_shape: content | escape_witness: TauCeti.simple_indFDRep_ofLinearCharacter_iff | consumer: BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_simple
-/

import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.FiniteGroups.InducedCharacterFormula
import D5.S3.FiniteGroups.CliffordConstituents
import D5.S3.FiniteGroups.CliffordDecomposition
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
namespace D5.S3.FiniteGroups.MackeyCharacterFormula
namespace TauCeti
end TauCeti
section UpstreamSource8_1
open MulAction
open scoped Pointwise
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti
variable {G : Type*} [Group G]
private def mackeySubgroup (s : G) (H K : Subgroup G) : Subgroup G :=
  K ⊓ MulAut.conj s • H
variable {s : G} {H K : Subgroup G}
private theorem mackeySubgroup_def (s : G) (H K : Subgroup G) :
    mackeySubgroup s H K = K ⊓ MulAut.conj s • H :=
  (rfl)
@[simp]
private theorem mem_mackeySubgroup_iff {x : G} :
    x ∈ mackeySubgroup s H K ↔ x ∈ K ∧ s⁻¹ * x * s ∈ H := by
  simp [mackeySubgroup_def]
private theorem mackeySubgroup_le_right : mackeySubgroup s H K ≤ K :=
  inf_le_left
private theorem mackeySubgroup_le_conj : mackeySubgroup s H K ≤ MulAut.conj s • H :=
  inf_le_right
section Special
@[simp]
private theorem mackeySubgroup_of_mem (hs : s ∈ H) : mackeySubgroup s H K = K ⊓ H := by
  rw [mackeySubgroup_def, Subgroup.conj_smul_eq_self_of_mem hs]
private theorem mackeySubgroup_subgroupOf_self_of_mem (hs : s ∈ H) :
    (mackeySubgroup s H H).subgroupOf H = ⊤ := by
  rw [mackeySubgroup_of_mem hs, inf_idem, Subgroup.subgroupOf_self]
private noncomputable def mackeySubgroupSelfEquiv (hs : s ∈ H) :
    ((mackeySubgroup s H H).subgroupOf H) ≃* H :=
  (MulEquiv.subgroupCongr (mackeySubgroup_subgroupOf_self_of_mem hs)).trans Subgroup.topEquiv
@[simp]
private theorem coe_mackeySubgroupSelfEquiv_apply (hs : s ∈ H)
    (y : (mackeySubgroup s H H).subgroupOf H) :
    (mackeySubgroupSelfEquiv hs y : H) = (y : H) :=
  (rfl)
@[simp]
private theorem mackeySubgroup_of_normal [H.Normal] : mackeySubgroup s H K = K ⊓ H := by
  rw [mackeySubgroup_def, Subgroup.Normal.conj_smul_eq_self]
private noncomputable def mackeySubgroupNormalEquiv (s : G) [H.Normal] :
    ((mackeySubgroup s H H).subgroupOf H) ≃* H :=
  (MulEquiv.subgroupCongr (by
    rw [mackeySubgroup_of_normal, inf_idem, Subgroup.subgroupOf_self])).trans Subgroup.topEquiv
@[simp]
private theorem coe_mackeySubgroupNormalEquiv_apply (s : G) [H.Normal]
    (y : (mackeySubgroup s H H).subgroupOf H) :
    (mackeySubgroupNormalEquiv s y : H) = (y : H) := by
  simp [mackeySubgroupNormalEquiv]
@[simp]
private theorem coe_mackeySubgroupNormalEquiv (s : G) [H.Normal] :
    (mackeySubgroupNormalEquiv (H := H) s : ((mackeySubgroup s H H).subgroupOf H) →* H) =
      ((mackeySubgroup s H H).subgroupOf H).subtype := by
  ext y
  exact congrArg Subtype.val (coe_mackeySubgroupNormalEquiv_apply s y)
end Special
section Representative
private theorem mackeySubgroup_conj {k h : G} (hk : k ∈ K) (hh : h ∈ H) :
    mackeySubgroup (k * s * h) H K = MulAut.conj k • mackeySubgroup s H K := by
  rw [mackeySubgroup_def, mackeySubgroup_def, Subgroup.smul_inf,
    Subgroup.conj_smul_eq_self_of_mem hk, conj_mul_smul, conj_mul_smul,
    Subgroup.conj_smul_eq_self_of_mem hh]
private def mackeySubgroupCongr {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G) :
    mackeySubgroup s H K ≃* mackeySubgroup (k * s * h) H K :=
  (Subgroup.equivSMul (MulAut.conj k) (mackeySubgroup s H K)).trans
    (MulEquiv.subgroupCongr (mackeySubgroup_conj hk hh).symm)
@[simp]
private theorem coe_mackeySubgroupCongr_apply {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G)
    (x : mackeySubgroup s H K) :
    (mackeySubgroupCongr hk hh s x : G) = k * (x : G) * k⁻¹ := by
  simp [mackeySubgroupCongr]
private def mackeySubgroupOfCongr {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G) :
    (mackeySubgroup s H K).subgroupOf K ≃* (mackeySubgroup (k * s * h) H K).subgroupOf K :=
  ((Subgroup.subgroupOfEquivOfLe (mackeySubgroup_le_right (s := s) (H := H) (K := K))).trans
      (mackeySubgroupCongr hk hh s)).trans
    (Subgroup.subgroupOfEquivOfLe
      (mackeySubgroup_le_right (s := k * s * h) (H := H) (K := K))).symm
@[simp]
private theorem coe_mackeySubgroupOfCongr_apply {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G)
    (y : (mackeySubgroup s H K).subgroupOf K) :
    ((mackeySubgroupOfCongr hk hh s y : K) : G) = k * ((y : K) : G) * k⁻¹ := by
  simp [mackeySubgroupOfCongr]
end Representative
section Orbit
@[simp]
private theorem stabilizer_eq_mackeySubgroup_subgroupOf (s : G) (H K : Subgroup G) :
    stabilizer (↥K) ((s : G ⧸ H)) = (mackeySubgroup s H K).subgroupOf K := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff, mem_stabilizer_iff,
    Subgroup.smul_def, ← mem_stabilizer_iff,
    stabilizer_quotientGroup_mk, mem_conj_smul]
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
private theorem card_orbit_eq_relIndex (s : G) (H K : Subgroup G) :
    Nat.card (orbit K ((s : G ⧸ H))) = (mackeySubgroup s H K).relIndex K := by
  rw [Subgroup.relIndex, ← stabilizer_eq_mackeySubgroup_subgroupOf, Nat.card_coe_set_eq]
  exact (index_stabilizer K _).symm
private instance instIsFiniteRelIndexMackeySubgroup (s : G) (H K : Subgroup G) [H.FiniteIndex] :
    (mackeySubgroup s H K).IsFiniteRelIndex K where
  relIndex_ne_zero := by
    rw [← card_orbit_eq_relIndex]
    have : Finite (orbit K ((s : G ⧸ H))) := Subtype.finite
    exact Nat.card_ne_zero.2 ⟨⟨⟨_, mem_orbit_self _⟩⟩, this⟩
end Orbit
end TauCeti
end UpstreamSource8_1
section UpstreamSource8_2
open scoped Pointwise
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti
universe u
section Coset
variable {G : Type*} [Group G]
private def mackeyCoset (s : G) (H K : Subgroup G) :
    K ⧸ (mackeySubgroup s H K).subgroupOf K → G ⧸ H :=
  Quotient.map' (fun u : K => (u : G) * s) fun u v huv => by
    have hmem := (mem_mackeySubgroup_iff.mp
      (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp huv))).2
    have heq : ((u : G) * s)⁻¹ * ((v : G) * s) = s⁻¹ * ((u⁻¹ * v : K) : G) * s := by
      push_cast
      group
    rw [QuotientGroup.leftRel_apply, heq]
    exact hmem
@[simp]
private theorem mackeyCoset_mk (s : G) (H K : Subgroup G) (u : K) :
    mackeyCoset s H K (QuotientGroup.mk u) = QuotientGroup.mk ((u : G) * s) :=
  (rfl)
private theorem mackeyCoset_out (s : G) (H K : Subgroup G)
    (u : K ⧸ (mackeySubgroup s H K).subgroupOf K) :
    mackeyCoset s H K u = QuotientGroup.mk ((u.out : G) * s) := by
  rw [← mackeyCoset_mk s H K u.out, QuotientGroup.out_eq']
private noncomputable def mackeyQuotientEquiv (H K : Subgroup G) :
    (Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        K ⧸ (mackeySubgroup D.out H K).subgroupOf K) ≃ G ⧸ H :=
  Equiv.ofBijective (fun p => mackeyCoset p.1.out H K p.2) (by
    constructor
    · rintro ⟨D, u⟩ ⟨D', v⟩ hp
      simp only [mackeyCoset_out, QuotientGroup.eq] at hp
      have hD : D = D' := by
        have hmk := (DoubleCoset.eq (H := K) (K := H) (a := D.out) (b := D'.out)).mpr
          ⟨(v.out : G)⁻¹ * (u.out : G),
            K.mul_mem (K.inv_mem (SetLike.coe_mem v.out)) (SetLike.coe_mem u.out), _, hp, by
              group⟩
        rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at hmk
      subst hD
      have huv : u = v := by
        rw [← QuotientGroup.out_eq' u, ← QuotientGroup.out_eq' v, QuotientGroup.eq,
          Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff]
        refine ⟨?_, ?_⟩
        · exact SetLike.coe_mem _
        · have heq : (D.out)⁻¹ * ((u.out⁻¹ * v.out : K) : G) * D.out
              = ((u.out : G) * D.out)⁻¹ * ((v.out : G) * D.out) := by
            push_cast
            group
          rw [heq]
          exact hp
      rw [huv]
    · intro t
      obtain ⟨a, ha, b, hb, hab⟩ :=
        DoubleCoset.eq.mp (DoubleCoset.out_eq' (DoubleCoset.mk K H t.out))
      refine ⟨⟨DoubleCoset.mk K H t.out, QuotientGroup.mk ⟨a, ha⟩⟩, ?_⟩
      simp only [mackeyCoset_mk]
      conv_rhs => rw [← QuotientGroup.out_eq' t]
      rw [QuotientGroup.eq]
      have hrw : (a * (DoubleCoset.mk K H t.out).out)⁻¹ * t.out = b :=
        inv_mul_eq_of_eq_mul hab
      rw [hrw]
      exact hb)
@[simp]
private theorem mackeyQuotientEquiv_apply (H K : Subgroup G)
    (p : Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        K ⧸ (mackeySubgroup D.out H K).subgroupOf K) :
    mackeyQuotientEquiv H K p = mackeyCoset p.1.out H K p.2 :=
  (rfl)
variable (s : G) (H K : Subgroup G)
private def mackeyToH : ((mackeySubgroup s H K).subgroupOf K) →* H :=
  (((Subgroup.equivSMul (MulAut.conj s) H).symm).toMonoidHom.comp (Subgroup.inclusion (mackeySubgroup_le_conj (s := s) (H := H) (K := K)))).comp
    (Subgroup.subgroupOfEquivOfLe mackeySubgroup_le_right).toMonoidHom
@[simp]
private theorem coe_mackeyToH_apply (y : (mackeySubgroup s H K).subgroupOf K) :
    (mackeyToH s H K y : G) = s⁻¹ * ((y : K) : G) * s := by
  simp [mackeyToH]
end Coset
section ClassFun
variable {k : Type*} [Semiring k] {G : Type*} [Group G] {H K : Subgroup G}
private def mackeyClassFun (s : G) (H K : Subgroup G) (f : H → k) :
    ((mackeySubgroup s H K).subgroupOf K) → k :=
  f ∘ mackeyToH s H K
omit [Semiring k] in
@[simp]
private theorem mackeyClassFun_apply (s : G) (H K : Subgroup G) (f : H → k)
    (y : (mackeySubgroup s H K).subgroupOf K) :
    mackeyClassFun s H K f y = f (mackeyToH s H K y) :=
  (rfl)
private theorem mackeyClassFun_mem_classFunction (s : G) (H K : Subgroup G) {f : H → k}
    (hf : f ∈ ClassFunction k H) :
    mackeyClassFun s H K f ∈ ClassFunction k ((mackeySubgroup s H K).subgroupOf K) :=
  ClassFunction.mem_iff.mpr fun y c => by
    rw [mackeyClassFun_apply, mackeyClassFun_apply, map_mul, map_mul, map_inv]
    exact ClassFunction.mem_iff.mp hf _ _
private def mackeyClassFunction (s : G) (H K : Subgroup G) (f : ClassFunction k H) :
    ClassFunction k ((mackeySubgroup s H K).subgroupOf K) :=
  Subtype.map (mackeyClassFun s H K)
    (fun _ hf => mackeyClassFun_mem_classFunction s H K hf) f
@[simp]
private theorem mackeyClassFunction_coe (s : G) (H K : Subgroup G) (f : ClassFunction k H) :
    (mackeyClassFunction s H K f).1 = mackeyClassFun s H K f.1 :=
  (rfl)
private theorem indTerm_mackeyClassFun (s : G) (H K : Subgroup G) (f : H → k) (x u : K) :
    indTerm f (x : G) ((u : G) * s) = indTerm (mackeyClassFun s H K f) x u := by
  classical
  have hconj : ((u : G) * s)⁻¹ * (x : G) * ((u : G) * s)
      = s⁻¹ * ((u⁻¹ * x * u : K) : G) * s := by
    push_cast
    group
  have hiff : ((u : G) * s)⁻¹ * (x : G) * ((u : G) * s) ∈ H ↔
      u⁻¹ * x * u ∈ (mackeySubgroup s H K).subgroupOf K := by
    rw [hconj, Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff]
    exact ⟨fun h => ⟨SetLike.coe_mem _, h⟩, fun h => h.2⟩
  rw [indTerm_apply, indTerm_apply]
  by_cases hmem : ((u : G) * s)⁻¹ * (x : G) * ((u : G) * s) ∈ H
  · rw [dite_eq_left hmem, dite_eq_left (hiff.mp hmem), mackeyClassFun_apply]
    exact congrArg f (Subtype.ext (by rw [coe_mackeyToH_apply]; exact hconj))
  · rw [dite_eq_right hmem, dite_eq_right fun h => hmem (hiff.mpr h)]
private theorem indClassFun_mackey [H.FiniteIndex] {f : H → k} (hf : f ∈ ClassFunction k H) (x : K) :
    indClassFun H f (x : G) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
      ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        indClassFun ((mackeySubgroup D.out H K).subgroupOf K)
          (mackeyClassFun D.out H K f) x := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
  let := Fintype.ofFinite (G ⧸ H)
  let (D : DoubleCoset.Quotient (K : Set G) (H : Set G)) :
      Fintype (K ⧸ (mackeySubgroup D.out H K).subgroupOf K) := Fintype.ofFinite _
  calc indClassFun H f (x : G)
      = ∑ t : G ⧸ H, indTerm f (x : G) t.out := by
        rw [indClassFun_apply]
        exact Finset.sum_congr rfl fun t _ => (indTerm_apply _ _ _).symm
    _ = ∑ p : Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
            K ⧸ (mackeySubgroup D.out H K).subgroupOf K,
          indTerm f (x : G) (mackeyQuotientEquiv H K p).out :=
        (Equiv.sum_comp (mackeyQuotientEquiv H K) _).symm
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          ∑ u : K ⧸ (mackeySubgroup D.out H K).subgroupOf K,
            indTerm f (x : G) ((u.out : G) * D.out) := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun u _ => ?_
        refine indTerm_eq_of_mk_eq hf _ _ _ ?_
        rw [QuotientGroup.out_eq']
        exact (mackeyQuotientEquiv_apply H K ⟨D, u⟩).trans (mackeyCoset_out _ _ _ _)
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          ∑ u : K ⧸ (mackeySubgroup D.out H K).subgroupOf K,
            indTerm (mackeyClassFun D.out H K f) x u.out :=
        Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun u _ =>
          indTerm_mackeyClassFun _ _ _ _ _ _
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          indClassFun ((mackeySubgroup D.out H K).subgroupOf K)
            (mackeyClassFun D.out H K f) x :=
        Finset.sum_congr rfl fun D _ => by
          rw [indClassFun_apply]
          exact Finset.sum_congr rfl fun u _ => indTerm_apply _ _ _
private theorem comap_subtype_ind_mackey (K : Subgroup G) [H.FiniteIndex] (f : ClassFunction k H) :
    ClassFunction.comap K.subtype (ClassFunction.ind H f) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
      ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        ClassFunction.ind ((mackeySubgroup D.out H K).subgroupOf K)
          (mackeyClassFunction D.out H K f) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
  refine Subtype.ext (funext fun x => ?_)
  rw [ClassFunction.comap_apply, ClassFunction.ind_apply, Subgroup.coe_subtype]
  simp only [Submodule.coe_sum, Finset.sum_apply, ClassFunction.ind_apply,
    mackeyClassFunction_coe]
  exact indClassFun_mackey f.2 x
end ClassFun
section Character
variable {k G : Type u} [Field k] [Group G] {H K : Subgroup G}
@[simp]
private theorem character_res_mackeyToH (s : G) (A : FDRep k H) :
    FDRep.character ((Action.res (FGModuleCat k) (mackeyToH s H K)).obj A) =
      mackeyClassFun s H K A.character := by
  funext y
  rw [mackeyClassFun_apply, FDRep.character, FDRep.character]
  congr 1
end Character
end TauCeti
end UpstreamSource8_2
end D5.S3.FiniteGroups.MackeyCharacterFormula

namespace D5.S3.FiniteGroups.MackeyCharacterFormula
namespace FDRep
end FDRep
namespace Representation
end Representation
namespace TauCeti
end TauCeti
section UpstreamSource8_3
open scoped Pointwise
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti
universe u v
section ClassFunctions
variable {k : Type u} {G : Type v} [Field k] [Group G] {H K : Subgroup G}
open scoped Classical in
private theorem characterPairing_ind_ind_mackey [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k H) (h : ClassFunction k K) :
    ClassFunction.characterPairing (ClassFunction.ind H f) (ClassFunction.ind K h) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
      ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        ClassFunction.characterPairing (mackeyClassFunction D.out K H h)
          (ClassFunction.comap ((mackeySubgroup D.out K H).subgroupOf H).subtype f) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  have hH : IsUnit (Nat.card H : k) := isUnit_natCard_subgroup H hG
  calc ClassFunction.characterPairing (ClassFunction.ind H f) (ClassFunction.ind K h)
      = ClassFunction.characterPairing f
          (ClassFunction.comap H.subtype (ClassFunction.ind K h)) :=
        characterPairing_ind hG f (ClassFunction.ind K h)
    _ = ClassFunction.characterPairing f
          (∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
            ClassFunction.ind ((mackeySubgroup D.out K H).subgroupOf H)
              (mackeyClassFunction D.out K H h)) := by
        rw [comap_subtype_ind_mackey]
    _ = ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
          ClassFunction.characterPairing f
            (ClassFunction.ind ((mackeySubgroup D.out K H).subgroupOf H)
              (mackeyClassFunction D.out K H h)) :=
        map_sum (ClassFunction.characterPairing f) _ _
    _ = ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
          ClassFunction.characterPairing (mackeyClassFunction D.out K H h)
            (ClassFunction.comap ((mackeySubgroup D.out K H).subgroupOf H).subtype f) :=
        Finset.sum_congr rfl fun D _ => by
          rw [ClassFunction.characterPairing_symm]
          exact characterPairing_ind hH _ f
end ClassFunctions
section IdentityCoset
variable {k : Type u} {G : Type v} [Field k] [Group G] {H : Subgroup G}
open scoped Classical in
private theorem characterPairing_mackeyClassFunction_of_mem [Fintype H] {s : G} (hs : s ∈ H)
    (f : ClassFunction k H) :
    ClassFunction.characterPairing (mackeyClassFunction s H H f)
        (ClassFunction.comap ((mackeySubgroup s H H).subgroupOf H).subtype f) =
      ClassFunction.characterPairing f f := by
  have hcard : Nat.card ((mackeySubgroup s H H).subgroupOf H) = Nat.card H :=
    Nat.card_congr (mackeySubgroupSelfEquiv hs).toEquiv
  have hterm (y : (mackeySubgroup s H H).subgroupOf H) :
      f.1 (mackeyToH s H H y) = f.1 (mackeySubgroupSelfEquiv hs y) := by
    have hconj : (⟨s, hs⟩ : H)⁻¹ * (mackeySubgroupSelfEquiv hs y) * (⟨s, hs⟩ : H)⁻¹⁻¹
        = mackeyToH s H H y :=
      Subtype.ext (by simp [coe_mackeyToH_apply])
    rw [← hconj]
    exact ClassFunction.mem_iff.mp f.2 _ _
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply, hcard]
  congr 1
  refine Fintype.sum_equiv (mackeySubgroupSelfEquiv hs).toEquiv _ _ fun y => ?_
  have hinv : ((mackeySubgroup s H H).subgroupOf H).subtype y⁻¹
      = (mackeySubgroupSelfEquiv hs y)⁻¹ := by simp
  rw [mackeyClassFunction_coe, mackeyClassFun_apply, hterm y, ClassFunction.comap_apply, hinv]
  rfl
open scoped Classical in
private theorem characterPairing_ind_ind_mackey_erase [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k H) :
    ClassFunction.characterPairing (ClassFunction.ind H f) (ClassFunction.ind H f) =
      ClassFunction.characterPairing f f +
        letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
        ∑ D ∈ Finset.univ.erase (DoubleCoset.mk H H 1),
          ClassFunction.characterPairing (mackeyClassFunction D.out H H f)
            (ClassFunction.comap ((mackeySubgroup D.out H H).subgroupOf H).subtype f) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  rw [characterPairing_ind_ind_mackey hG f f,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (DoubleCoset.mk H H 1)),
    characterPairing_mackeyClassFunction_of_mem
      ((doubleCosetMk_eq_mk_one_iff_mem H _).mp (DoubleCoset.out_eq' _)) f]
end IdentityCoset
section Representations
variable {k G : Type u} [Field k] [Group G] {H K : Subgroup G}
@[simp]
private theorem ofFDRep_res_mackeyToH (s : G) (H K : Subgroup G) (A : FDRep k H) :
    (ClassFunction.ofCharacter (FDRep.ρ ((Action.res (FGModuleCat k) (mackeyToH s H K)).obj A))) =
      mackeyClassFunction s H K ((ClassFunction.ofCharacter (FDRep.ρ A))) :=
  Subtype.ext <| funext fun y => by
    change FDRep.character ((Action.res (FGModuleCat k) (mackeyToH s H K)).obj A) y =
      A.character (mackeyToH s H K y)
    exact congrFun (character_res_mackeyToH s A) y
open scoped Classical in
private theorem natCast_finrank_hom_indFDRep_mackey_erase [Finite G] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k H) :
    (Module.finrank k (indFDRep A ⟶ indFDRep A) : k) =
      (Module.finrank k (A ⟶ A) : k) +
        letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
        ∑ D ∈ Finset.univ.erase (DoubleCoset.mk H H 1),
          (Module.finrank k (((Action.res (FGModuleCat k) (((mackeySubgroup D.out H H).subgroupOf H)).subtype).obj A) ⟶
            (Action.res (FGModuleCat k) (mackeyToH D.out H H)).obj A) : k) := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  let : Invertible (Nat.card G : k) := hG.invertible
  have hH : IsUnit (Nat.card H : k) := isUnit_natCard_subgroup H hG
  let : Invertible (Nat.card H : k) := hH.invertible
  rw [← ClassFunction.characterPairing_ofFDRep_eq_finrank, ← ClassFunction.ind_ofFDRep,
    characterPairing_ind_ind_mackey_erase hG]
  congr 1
  · exact ClassFunction.characterPairing_ofFDRep_eq_finrank A A
  · refine Finset.sum_congr rfl fun D _ => ?_
    let : Invertible (Nat.card ((mackeySubgroup D.out H H).subgroupOf H) : k) :=
      (isUnit_natCard_subgroup _ hH).invertible
    rw [← ofFDRep_res_mackeyToH, ClassFunction.comap_subtype_ofFDRep,
      ClassFunction.characterPairing_ofFDRep_eq_finrank]
open scoped Classical in
private theorem finrank_hom_indFDRep_mackey_erase [Finite G] [CharZero k] (A : FDRep k H) :
    Module.finrank k (indFDRep A ⟶ indFDRep A) =
      Module.finrank k (A ⟶ A) +
        letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
        ∑ D ∈ Finset.univ.erase (DoubleCoset.mk H H 1),
          Module.finrank k (((Action.res (FGModuleCat k) (((mackeySubgroup D.out H H).subgroupOf H)).subtype).obj A) ⟶
            (Action.res (FGModuleCat k) (mackeyToH D.out H H)).obj A) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  have hG : IsUnit (Nat.card G : k) :=
    isUnit_of_invertible (Nat.card G : k)
  exact_mod_cast natCast_finrank_hom_indFDRep_mackey_erase hG A
private theorem finrank_hom_res_mackeyToH_of_normal [H.Normal] (A : FDRep k H) (s : G) :
    Module.finrank k (((Action.res (FGModuleCat k) (((mackeySubgroup s H H).subgroupOf H)).subtype).obj A) ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) =
      Module.finrank k (A ⟶ (conjNormalFDRepFunctor s).obj A) := by
  let e := mackeySubgroupNormalEquiv (H := H) s
  have he_apply (y : (mackeySubgroup s H H).subgroupOf H) : e y = (y : H) :=
    coe_mackeySubgroupNormalEquiv_apply s y
  have hsubtype : ((mackeySubgroup s H H).subgroupOf H).subtype = e.toMonoidHom :=
    ((MulEquiv.toMonoidHom_eq_coe e).trans (coe_mackeySubgroupNormalEquiv s)).symm
  have hconj : mackeyToH s H H =
      (MulAut.conjNormal s⁻¹ : MulAut H).toMonoidHom.comp e.toMonoidHom := by
    ext y
    simp only [coe_mackeyToH_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply]
    rw [he_apply]
    simp
  have hsource : ((Action.res (FGModuleCat k) (((mackeySubgroup s H H).subgroupOf H)).subtype).obj A) =
      (Action.res (FGModuleCat k) e.toMonoidHom).obj A := by
    exact congrArg (fun φ => (Action.res (FGModuleCat k) φ).obj A) hsubtype
  have htarget : (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A =
      (Action.res (FGModuleCat k) e.toMonoidHom).obj ((conjNormalFDRepFunctor s).obj A) := by
    rw [hconj, conjNormalFDRepFunctor]
    exact CategoryTheory.Functor.congr_obj (actionRes_comp _ _) A
  rw [hsource, htarget]
  exact finrank_hom_res_mulEquiv e A ((conjNormalFDRepFunctor s).obj A)
open CategoryTheory in
private theorem res_ρ_comm_ρAut_hom {L M N : Type u} [Group L] [Monoid M] [Monoid N]
    (A : FDRep k L) (g : L) (φ : M →* N) (σ : N →* L) (σ' : M →* L)
    (hg : ∀ y : M, g * σ (φ y) = σ' y * g) (y : M) :
    (Action.ρ ((Action.res (FGModuleCat k) φ).obj ((Action.res (FGModuleCat k) σ).obj A)) y).asHom ≫
        (Action.ρAut A g).asIso.hom =
      (Action.ρAut A g).asIso.hom ≫ (Action.ρ ((Action.res (FGModuleCat k) σ').obj A) y).asHom := by
  change (Action.ρ A (σ (φ y))).asHom ≫ (Action.ρ A g).asHom =
    (Action.ρ A g).asHom ≫ (Action.ρ A (σ' y)).asHom
  rw [← End.mul_asHom, ← End.mul_asHom, ← map_mul, ← map_mul, hg]
open CategoryTheory in
private theorem finrank_hom_res_mackeyToH_mul_left_mul_right (A : FDRep k H) (B : FDRep k K) {h₁ h₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G) :
    Module.finrank k (((Action.res (FGModuleCat k) (((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H)).subtype).obj A) ⟶
        (Action.res (FGModuleCat k) (mackeyToH (h₁ * s * h₂) K H)).obj B) =
      Module.finrank k (((Action.res (FGModuleCat k) (((mackeySubgroup s K H).subgroupOf H)).subtype).obj A) ⟶
        (Action.res (FGModuleCat k) (mackeyToH s K H)).obj B) := by
  let α : (Action.res (FGModuleCat k) ((mackeySubgroupOfCongr hh₁ hh₂ s) : _ →* _)).obj
        (((Action.res (FGModuleCat k) (((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H)).subtype).obj A)) ≅
      ((Action.res (FGModuleCat k) (((mackeySubgroup s K H).subgroupOf H)).subtype).obj A) :=
    Action.mkIso (Action.ρAut A (⟨h₁, hh₁⟩ : H)⁻¹).asIso <|
      res_ρ_comm_ρAut_hom A (⟨h₁, hh₁⟩ : H)⁻¹ _ _ _ fun y => Subtype.ext (by
        simp only [MonoidHom.coe_ofClass, Subgroup.coe_subtype, coe_mackeySubgroupOfCongr_apply,
          Subgroup.coe_mul, Subgroup.coe_inv]
        group)
  let β : (Action.res (FGModuleCat k) ((mackeySubgroupOfCongr hh₁ hh₂ s) : _ →* _)).obj
        ((Action.res (FGModuleCat k) (mackeyToH (h₁ * s * h₂) K H)).obj B) ≅
      (Action.res (FGModuleCat k) (mackeyToH s K H)).obj B :=
    Action.mkIso (Action.ρAut B ⟨h₂, hh₂⟩).asIso <|
      res_ρ_comm_ρAut_hom B ⟨h₂, hh₂⟩ _ _ _ fun y => Subtype.ext (by
        simp only [MonoidHom.coe_ofClass, coe_mackeyToH_apply, coe_mackeySubgroupOfCongr_apply,
          Subgroup.coe_mul]
        group)
  rw [← finrank_hom_res_mulEquiv (mackeySubgroupOfCongr hh₁ hh₂ s)]
  exact (Linear.homCongr k α β).finrank_eq
end Representations
end TauCeti
end UpstreamSource8_3
section UpstreamSource8_4
open scoped Pointwise
open CategoryTheory Limits
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti
universe u
section ZeroObject
variable {k : Type u} [Field k]
private theorem isZero_of_finrank_end_eq_zero {S : Type u} [Monoid S] (A : FDRep k S)
    (h : Module.finrank k (A ⟶ A) = 0) : IsZero A :=
  have : Subsingleton (A ⟶ A) := Module.finrank_zero_iff.mp h
  (IsZero.iff_id_eq_zero A).mpr (Subsingleton.elim _ _)
private theorem finrank_hom_eq_zero_of_isZero {S : Type u} [Monoid S] {X Y : FDRep k S}
    (h : IsZero Y) :
    Module.finrank k (X ⟶ Y) = 0 :=
  have : Subsingleton (X ⟶ Y) :=
    ⟨fun f g => by rw [h.eq_zero_of_tgt f, h.eq_zero_of_tgt g]⟩
  Module.finrank_zero_of_subsingleton
end ZeroObject
section Disjoint
variable {k G : Type u} [Field k] [Group G] {H : Subgroup G}
private def MackeyDisjoint (A : FDRep k H) (s : G) : Prop :=
  Subsingleton (((Action.res (FGModuleCat k) (((mackeySubgroup s H H).subgroupOf H)).subtype).obj A) ⟶
    (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A)
private theorem mackeyDisjoint_iff_finrank_eq_zero (A : FDRep k H) (s : G) :
    MackeyDisjoint A s ↔
      Module.finrank k (((Action.res (FGModuleCat k) (((mackeySubgroup s H H).subgroupOf H)).subtype).obj A) ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) = 0 :=
  Module.finrank_zero_iff.symm
private theorem mackeyDisjoint_mul_left_mul_right_iff (A : FDRep k H) {h₁ h₂ : G} (hh₁ : h₁ ∈ H)
    (hh₂ : h₂ ∈ H) (s : G) : MackeyDisjoint A (h₁ * s * h₂) ↔ MackeyDisjoint A s := by
  rw [mackeyDisjoint_iff_finrank_eq_zero, mackeyDisjoint_iff_finrank_eq_zero,
    finrank_hom_res_mackeyToH_mul_left_mul_right A A hh₁ hh₂ s]
end Disjoint
section NormalDisjoint
variable {k G : Type u} [Field k] [Group G] {H : Subgroup G} [H.Normal]
private theorem mackeyDisjoint_iff_isEmpty_iso_of_normal (A : FDRep k H) [Simple A] (s : G) :
    MackeyDisjoint A s ↔ IsEmpty ((conjNormalFDRepFunctor s).obj A ≅ A) := by
  have hsimple : Simple ((conjNormalFDRepFunctor s).obj A) := by
    rw [← conjNormalFDRepEquiv_functor]
    exact CategoryTheory.simple_obj _ A
  let _ := hsimple
  rw [mackeyDisjoint_iff_finrank_eq_zero, finrank_hom_res_mackeyToH_of_normal]
  constructor
  · intro h
    have hsubsingleton : Subsingleton (A ⟶ (conjNormalFDRepFunctor s).obj A) :=
      Module.finrank_zero_iff.mp h
    exact ⟨fun e ↦ (CategoryTheory.isIso_iff_nonzero e.symm.hom).mp inferInstance
      (hsubsingleton.elim e.symm.hom 0)⟩
  · intro h
    exact CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
      fun e ↦ h.false e.symm
end NormalDisjoint
section Criterion
variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {H : Subgroup G}
private theorem simple_indFDRep_iff_doubleCoset (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G), D ≠ DoubleCoset.mk H H 1 →
        MackeyDisjoint A D.out := by
  classical
  simp only [mackeyDisjoint_iff_finrank_eq_zero]
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  have : NeZero (Nat.card G : k) := NeZero.charZero
  have : NeZero (Nat.card H : k) := NeZero.charZero
  rw [FDRep.simple_iff_end_is_rank_one, FDRep.simple_iff_end_is_rank_one,
    finrank_hom_indFDRep_mackey_erase A]
  constructor
  · intro h
    have hA : Module.finrank k (A ⟶ A) ≠ 0 := by
      intro h0
      rw [h0, Finset.sum_eq_zero fun D _ =>
        finrank_hom_eq_zero_of_isZero ((Action.res (FGModuleCat k) _).map_isZero
          (isZero_of_finrank_end_eq_zero A h0))] at h
      exact absurd h (by norm_num)
    obtain ⟨h1, h2⟩ := (Nat.add_eq_one_iff.mp h).resolve_left fun hc => hA hc.1
    exact ⟨h1, fun D hD => Finset.sum_eq_zero_iff.mp h2 D (Finset.mem_erase.mpr ⟨hD, by simp⟩)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, Finset.sum_eq_zero fun D hD => h2 D (Finset.mem_erase.mp hD).1, add_zero]
private theorem simple_indFDRep_iff (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧ ∀ s ∉ H, MackeyDisjoint A s := by
  rw [simple_indFDRep_iff_doubleCoset]
  refine and_congr_right fun _ => ⟨fun h s hs => ?_, fun h D hD => ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ :=
      DoubleCoset.eq.mp (DoubleCoset.out_eq' (DoubleCoset.mk H H s))
    exact hab ▸ (mackeyDisjoint_mul_left_mul_right_iff A ha hb _).mpr
      (h _ fun hc => hs ((doubleCosetMk_eq_mk_one_iff_mem H s).mp hc))
  · exact h D.out fun hmem =>
      hD ((DoubleCoset.out_eq' D).symm.trans
        ((doubleCosetMk_eq_mk_one_iff_mem H D.out).mpr hmem))
private theorem simple_indFDRep_iff_of_normal [H.Normal] (A : FDRep k H) :
    Simple (indFDRep A) ↔
      Simple A ∧ ∀ s ∉ H, IsEmpty ((conjNormalFDRepFunctor s).obj A ≅ A) := by
  rw [simple_indFDRep_iff]
  refine and_congr_right fun hA ↦ ?_
  let _ := hA
  exact forall_congr' fun s ↦ forall_congr' fun _ ↦
    mackeyDisjoint_iff_isEmpty_iso_of_normal A s
end Criterion
end TauCeti
end UpstreamSource8_4
section UpstreamSource8_5
open CategoryTheory
universe u v
namespace Representation
open _root_.Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation _root_.D5.S3.FiniteGroups.CliffordConstituents.Representation _root_.D5.S3.FiniteGroups.CliffordDecomposition.Representation _root_.D5.S3.FiniteGroups.InducedCharacterFormula.Representation
variable {k : Type u} {G : Type v}
private def linearCharacterRepresentation [CommSemiring k] [Monoid G] (χ : G →* kˣ) : Representation k G k :=
  (Algebra.lsmul k k k).toMonoidHom.comp ((Units.coeHom k).comp χ)
private instance isIrreducible_linearCharacterRepresentation [Field k] [Monoid G] (χ : G →* kˣ) :
    (linearCharacterRepresentation (k := k) χ).IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)
end Representation
namespace FDRep
open _root_.FDRep
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep _root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep _root_.D5.S3.FiniteGroups.InducedCharacterFormula.FDRep
variable {k : Type u} {G : Type v}
noncomputable def ofLinearCharacter [CommRing k] [Monoid G] (χ : G →* kˣ) : FDRep k G :=
  FDRep.of (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.Representation.linearCharacterRepresentation χ)
@[simp]
private theorem actionRes_obj_ofLinearCharacter [CommRing k] [Monoid G] {S : Type*} [Monoid S]
    (f : S →* G) (χ : G →* kˣ) :
    (Action.res (FGModuleCat k) f).obj (ofLinearCharacter χ) = ofLinearCharacter (χ.comp f) :=
  (rfl)
@[simp]
theorem finrank_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    Module.finrank k (ofLinearCharacter (k := k) χ) = 1 :=
  Module.finrank_self k
private instance simple_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    Simple (ofLinearCharacter (k := k) χ) :=
  have : Representation.IsIrreducible (ofLinearCharacter (k := k) χ).ρ :=
    _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.Representation.isIrreducible_linearCharacterRepresentation χ
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible _
@[simp]
private theorem nonempty_iso_ofLinearCharacter_iff [CommRing k] [Monoid G] (χ ψ : G →* kˣ) :
    Nonempty (ofLinearCharacter (k := k) χ ≅ ofLinearCharacter ψ) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => MonoidHom.ext fun g => Units.ext ?_, fun h => ⟨h ▸ Iso.refl _⟩⟩
  obtain ⟨f, hf⟩ : ∃ f : k ≃ₗ[k] k, ∀ x : k, f ((χ g : k) * x) = (ψ g : k) * f x := by
    refine ⟨isoToLinearEquiv e, fun x => ?_⟩
    have h := DFunLike.congr_fun (FDRep.Iso.conj_ρ e g) (isoToLinearEquiv e x)
    have hx := congrArg (fun y => isoToLinearEquiv e ((ofLinearCharacter (k := k) χ).ρ g y))
      ((isoToLinearEquiv e).symm_apply_apply x)
    exact (h.trans hx).symm
  have hlin : ∀ c : k, f c = c * f 1 := fun c => by
    conv_lhs => rw [← mul_one c, ← smul_eq_mul]
    rw [map_smul, smul_eq_mul]
  have hkey : (χ g : k) * f 1 = (ψ g : k) * f 1 := by
    have h := hf 1
    rwa [mul_one, hlin] at h
  exact f.injective (by rw [hlin (χ g : k), hlin (ψ g : k)]; exact hkey)
end FDRep
end UpstreamSource8_5
section UpstreamSource9_0
open CategoryTheory
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti _root_.D5.S3.FiniteGroups.CliffordDecomposition.TauCeti _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti
universe u
section Conjugation
variable {k G : Type u} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
@[simp]
private theorem conjNormalFDRep_ofLinearCharacter (g : G) (χ : N →* kˣ) :
    (conjNormalFDRepFunctor g).obj (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter χ) =
      _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter (χ.comp (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom) :=
  _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.actionRes_obj_ofLinearCharacter _ _
private theorem nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff (g : G) (χ : N →* kˣ) :
    Nonempty ((conjNormalFDRepFunctor g).obj (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter (k := k) χ) ≅ _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter χ) ↔
      ∀ x : N, χ (MulAut.conjNormal g⁻¹ x) = χ x := by
  rw [conjNormalFDRep_ofLinearCharacter, _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.nonempty_iso_ofLinearCharacter_iff]
  exact DFunLike.ext_iff
end Conjugation
section Criterion
variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal] [Finite G] [IsAlgClosed k]
  [CharZero k]
theorem simple_indFDRep_ofLinearCharacter_iff (χ : N →* kˣ) :
    Simple (indFDRep (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter (k := k) χ)) ↔
      ∀ s ∉ N, ∃ x : N, χ (MulAut.conjNormal s x) ≠ χ x := by
  rw [simple_indFDRep_iff_of_normal]
  simp only [not_nonempty_iff.symm, nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff, not_forall,
    and_iff_right (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.simple_ofLinearCharacter χ)]
  exact ⟨fun h s hs => by simpa using h s⁻¹ (fun hc => hs (by simpa using inv_mem hc)),
    fun h s hs => by simpa using h s⁻¹ (fun hc => hs (by simpa using inv_mem hc))⟩
end Criterion
end TauCeti
end UpstreamSource9_0
end D5.S3.FiniteGroups.MackeyCharacterFormula
