/- GID: D5/S3/FiniteGroups/CharacterDegreeDivisibility
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CharacterDegreeDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite character theory: CharacterDegreeDivisibility. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: The Tau Ceti contributors

This port uses repository namespaces and the pinned Mathlib API.

Replace these ports by direct imports when the repository’s pinned Mathlib supplies
equivalent declarations with the same hypotheses and conclusions.

admission_basis: escape-witness
Direct frozen dependencies: none.
Module escape_witness: TauCeti.Representation.finrank_dvd_card
Class-sum integrality and the central-character trace decomposition force the irreducible degree to divide the group order.
TauCeti.centerToEnd | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.centralCharacter
TauCeti.centralCharacter | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_dvd_card
TauCeti.smul_eq_centralCharacter_smul | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.asAlgebraHom_center_apply
TauCeti.isIntegral_classSumCenter | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.isIntegral_centralCharacter_classSumCenter
TauCeti.Representation.asAlgebraHom_classSum | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.trace_asAlgebraHom_classSum
TauCeti.Representation.trace_asAlgebraHom_classSum | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one
TauCeti.Representation.asAlgebraHom_center_apply | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.asAlgebraHom_center
TauCeti.Representation.asAlgebraHom_center | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.trace_asAlgebraHom_center
TauCeti.Representation.trace_asAlgebraHom_center | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one
TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card
TauCeti.Representation.isIntegral_centralCharacter_classSumCenter | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_dvd_card
TauCeti.End.pow_eq_one_of_isRoot_charpoly | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.isIntegral_trace_of_pow_eq_one_of_splits
TauCeti.End.isIntegral_trace_of_pow_eq_one_of_splits | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.isIntegral_trace_of_pow_eq_one
TauCeti.End.isIntegral_trace_of_pow_eq_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.isIntegral_char
TauCeti.End.isSemisimple_of_pow_eq_one | proof_shape: bind-only | escape_witness: none | consumer: Module.End.exists_eq_smul_of_norm_trace_eq_finrank
TauCeti.End.mapsTo_pow_eigenspace | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.trace_pow_eq_sum_eigenvalue_pow
TauCeti.End.trace_restrict_eigenspace | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.trace_pow_eq_sum_eigenvalue_pow
TauCeti.End.pow_eq_one_of_hasEigenvalue | proof_shape: bind-only | escape_witness: none | consumer: Module.End.exists_eq_smul_of_norm_trace_eq_finrank
TauCeti.End.isInternal_eigenspace_of_pow_eq_one | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.trace_pow_eq_sum_eigenvalue_pow
TauCeti.End.trace_pow_eq_sum_eigenvalue_pow | proof_shape: bind-only | escape_witness: none | consumer: Module.End.exists_eq_smul_of_norm_trace_eq_finrank
Module.End.exists_eq_smul_of_norm_trace_eq_finrank | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.eq_one_of_trace_eq_finrank
TauCeti.End.eq_one_of_trace_eq_finrank | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.End.trace_eq_finrank_iff
TauCeti.End.trace_eq_finrank_iff | proof_shape: bind-only | escape_witness: none | consumer: InducedCharacterFormula.Representation.char_eq_finrank_iff_of_pow_eq_one
TauCeti.Representation.isIntegral_char | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_dvd_card
TauCeti.dvd_of_isIntegral_of_natCast_mul_eq | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_dvd_card
TauCeti.Representation.character_mul_character_inv_mem_classFunction | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card
TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card | proof_shape: bind-only | escape_witness: none | consumer: TauCeti.Representation.finrank_dvd_card
TauCeti.Representation.finrank_dvd_card | proof_shape: content | escape_witness: TauCeti.Representation.finrank_dvd_card | consumer: FrobeniusCharacterDegrees.degree_dvd_quotient_card
-/

import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
namespace D5.S3.FiniteGroups.CharacterDegreeDivisibility
namespace Module.End
end Module.End
namespace TauCeti
end TauCeti
namespace TauCeti.End
end TauCeti.End
namespace TauCeti.Representation
end TauCeti.Representation
section UpstreamSource2_2
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
universe u v w
section CenterToEnd
variable (k : Type u) [CommSemiring k] (A : Type v) [Semiring A] [Algebra k A]
variable (M : Type w) [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
private def centerToEnd : Subalgebra.center k A →ₐ[k] Module.End A M where
  toFun z := Module.End.smulLeft (M := M) (z : A)
    (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp z.2))
  map_one' := by ext m; simp
  map_mul' z w := by ext m; simp [smul_smul, Subalgebra.mem_center_iff.mp w.2 (z : A)]
  map_zero' := by ext m; simp
  map_add' z w := by ext m; simp [add_smul]
  commutes' r := by ext m; simp [algebraMap_smul]
end CenterToEnd
section CentralCharacter
variable (k : Type u) [Field k] [IsAlgClosed k] (A : Type v) [Ring A] [Algebra k A]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable [IsSimpleModule A M] [FiniteDimensional k M]
private noncomputable def centralCharacter : Subalgebra.center k A →ₐ[k] k :=
  (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := M)).toAlgHom.comp (centerToEnd k A M)
@[simp]
private theorem smul_eq_centralCharacter_smul (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centralCharacter k A M z • m :=
  (endAlgEquivSelfOfIsSimpleModule_smul (k := k) (centerToEnd k A M z) m).symm
variable {k A M}
end CentralCharacter
end TauCeti
end UpstreamSource2_2
section UpstreamSource2_3
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]



private theorem isIntegral_classSumCenter (k : Type*) [CommRing k] (C : ConjClasses G) :
    IsIntegral ℤ (classSumCenter (k := k) C) := by
  have hZ : IsIntegral ℤ (classSum ℤ C) := Algebra.IsIntegral.isIntegral _

  have hmap : MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ k) (classSum ℤ C) = classSum k C := by
    simp [classSum_eq_sum, map_sum, MonoidAlgebra.of_apply]
  have hk : IsIntegral ℤ (classSum k C) :=
    hmap ▸ hZ.map (MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ k))
  refine (isIntegral_algHom_iff
    ((Subalgebra.center k (MonoidAlgebra k G)).val.restrictScalars ℤ) Subtype.val_injective).mp ?_
  simpa using hk
end TauCeti
end UpstreamSource2_3
section UpstreamSource2_4
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
universe u v w
variable {k : Type u} {G : Type v} {V : Type w} [Group G] [Fintype G] [DecidableEq G]
section
variable [CommSemiring k] [AddCommMonoid V] [Module k V] (ρ : Representation k G V)
private theorem asAlgebraHom_classSum (C : ConjClasses G) :
    ρ.asAlgebraHom (classSum k C) = ∑ x : C.carrier, ρ (x : G) := by
  rw [classSum_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun x _ => ρ.asAlgebraHom_of x
end
variable [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
private theorem trace_asAlgebraHom_classSum {C : ConjClasses G} {g : G} (hg : ConjClasses.mk g = C) :
    LinearMap.trace k V (ρ.asAlgebraHom (classSum k C)) = Nat.card C.carrier * ρ.character g := by
  rw [asAlgebraHom_classSum, map_sum]
  have hconst : ∀ x : C.carrier, LinearMap.trace k V (ρ (x : G)) = ρ.character g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp (hg.trans (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm))
    exact ρ.char_conj g c
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
end Representation
end TauCeti
end UpstreamSource2_4
section UpstreamSource2_5
open _root_.Module (finrank)
open scoped _root_.MonoidAlgebra
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
universe u v w
variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] (ρ : Representation k G V)
variable [IsAlgClosed k] [FiniteDimensional k V] [ρ.IsIrreducible]
private theorem asAlgebraHom_center_apply (z : Subalgebra.center k k[G]) (v : V) :
    ρ.asAlgebraHom (z : k[G]) v = (_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) z • v := by
  have h : (z : k[G]) • ρ.asModuleEquiv.symm v =
      (_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) z • ρ.asModuleEquiv.symm v :=
    _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.smul_eq_centralCharacter_smul k k[G] ρ.asModule z _
  have h' := congrArg ρ.asModuleEquiv h
  rwa [_root_.Representation.asModuleEquiv_map_smul, map_smul,
    LinearEquiv.apply_symm_apply] at h'
@[simp]
private theorem asAlgebraHom_center (z : Subalgebra.center k k[G]) :
    ρ.asAlgebraHom (z : k[G]) = (_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) z • LinearMap.id :=
  LinearMap.ext fun v => asAlgebraHom_center_apply ρ z v
private theorem trace_asAlgebraHom_center (z : Subalgebra.center k k[G]) :
    LinearMap.trace k V (ρ.asAlgebraHom (z : k[G])) = (_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) z * finrank k V := by
  rw [asAlgebraHom_center, map_smul, LinearMap.trace_id, smul_eq_mul]
section Finite
variable [Fintype G] [DecidableEq G]
private theorem centralCharacter_classSumCenter_mul_character_one {C : ConjClasses G} {g : G}
    (hg : ConjClasses.mk g = C) :
    (_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) (classSumCenter C) * ρ.character 1 =
      Nat.card C.carrier * ρ.character g := by
  rw [ρ.char_one, ← trace_asAlgebraHom_center ρ (classSumCenter C), classSumCenter_coe,
    trace_asAlgebraHom_classSum ρ hg]
private theorem isIntegral_centralCharacter_classSumCenter (C : ConjClasses G) :
    IsIntegral ℤ ((_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) (classSumCenter C)) :=
  (isIntegral_classSumCenter k C).map (((_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule)).restrictScalars ℤ)
end Finite
end Representation
end TauCeti
end UpstreamSource2_5
section UpstreamSource2_6
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
open _root_.Module _root_.Polynomial
universe u w
variable {k : Type u} {V : Type w} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
namespace End
private theorem pow_eq_one_of_isRoot_charpoly {f : End k V} {n : ℕ} (hf : f ^ n = 1) {μ : k}
    (hμ : f.charpoly.IsRoot μ) : μ ^ n = 1 := by
  have hspec : μ ∈ spectrum k f := (End.mem_spectrum_iff_isRoot_charpoly f μ).2 hμ
  rcases subsingleton_or_nontrivial (End k V) with _ | _
  · exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hspec)
  · have hpow := spectrum.pow_mem_pow f n hspec
    rw [hf, spectrum.one_eq] at hpow
    simpa using hpow
private theorem isIntegral_trace_of_pow_eq_one_of_splits {f : End k V} {n : ℕ} (hn : n ≠ 0)
    (hf : f ^ n = 1) (hsplits : f.charpoly.Splits) : IsIntegral ℤ (LinearMap.trace k V f) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits]
  refine IsIntegral.multiset_sum fun μ hμ => IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
  rw [pow_eq_one_of_isRoot_charpoly hf (isRoot_of_mem_roots hμ)]
  exact isIntegral_one
private theorem isIntegral_trace_of_pow_eq_one {f : End k V} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace k V f) := by
  have hbase : f.baseChange (AlgebraicClosure k) ^ n = 1 := by
    rw [← LinearMap.baseChange_pow, hf, LinearMap.baseChange_one]
  have hint := isIntegral_trace_of_pow_eq_one_of_splits (k := AlgebraicClosure k) hn hbase
    (IsAlgClosed.splits _)
  rw [LinearMap.trace_baseChange] at hint
  exact hint.tower_bot (algebraMap k (AlgebraicClosure k)).injective
omit [FiniteDimensional k V] in
private theorem isSemisimple_of_pow_eq_one {f : End k V} {n : ℕ} (hn : (n : k) ≠ 0) (hf : f ^ n = 1) :
    f.IsSemisimple := by
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ n - 1) ?_ ?_
  · simpa using (Polynomial.separable_X_pow_sub_C (1 : k) hn one_ne_zero).squarefree
  · simp [hf]
section Eigenspace
variable {f : End k V} {n : ℕ}
omit [FiniteDimensional k V] in
private theorem mapsTo_pow_eigenspace (f : End k V) (μ : k) (m : ℕ) :
    Set.MapsTo (f ^ m) (f.eigenspace μ) (f.eigenspace μ) := fun x hx => by
  have hx' : (f ^ m) x = μ ^ m • x := by
    simpa using End.aeval_apply_of_mem_apply_eq_smul (p := X ^ m) (End.mem_eigenspace_iff.1 hx)
  rw [SetLike.mem_coe, hx']
  exact Submodule.smul_mem _ _ hx
private theorem trace_restrict_eigenspace (f : End k V) (μ : k) (m : ℕ) :
    LinearMap.trace k _ ((f ^ m).restrict (mapsTo_pow_eigenspace f μ m)) =
      (finrank k (f.eigenspace μ) : k) * μ ^ m := by
  have hrestrict : (f ^ m).restrict (mapsTo_pow_eigenspace f μ m) = μ ^ m • LinearMap.id := by
    ext x
    refine (LinearMap.coe_restrict_apply _ x).trans ?_
    simpa using End.aeval_apply_of_mem_apply_eq_smul (p := X ^ m) (End.mem_eigenspace_iff.1 x.2)
  rw [hrestrict, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
private theorem pow_eq_one_of_hasEigenvalue (hf : f ^ n = 1) {μ : k} (hμ : f.HasEigenvalue μ) :
    μ ^ n = 1 :=
  pow_eq_one_of_isRoot_charpoly hf
    ((End.mem_spectrum_iff_isRoot_charpoly f μ).1 (End.hasEigenvalue_iff_mem_spectrum.1 hμ))
variable [IsAlgClosed k]
open scoped Classical in
private theorem isInternal_eigenspace_of_pow_eq_one (hn : (n : k) ≠ 0) (hf : f ^ n = 1) :
    DirectSum.IsInternal f.eigenspace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep
    (isSemisimple_of_pow_eq_one hn hf).iSup_eigenspace_eq_top
private theorem trace_pow_eq_sum_eigenvalue_pow (hn : (n : k) ≠ 0) (hf : f ^ n = 1) (m : ℕ) :
    LinearMap.trace k V (f ^ m) =
      ∑ μ ∈ (End.finite_hasEigenvalue f).toFinset, (finrank k (f.eigenspace μ) : k) * μ ^ m := by
  classical
  rw [LinearMap.trace_eq_sum_trace_restrict' (isInternal_eigenspace_of_pow_eq_one hn hf)
    (End.finite_hasEigenvalue f) (mapsTo_pow_eigenspace f · m)]
  exact Finset.sum_congr rfl fun μ _ => trace_restrict_eigenspace f μ m
end Eigenspace
section Complex
variable {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
private theorem _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.Module.End.exists_eq_smul_of_norm_trace_eq_finrank {f : End ℂ V} {n : ℕ}
    (hn : n ≠ 0) (hf : f ^ n = 1)
    (h : ‖LinearMap.trace ℂ V f‖ = (finrank ℂ V : ℝ)) : ∃ μ : ℂ, μ ^ n = 1 ∧ f = μ • 1 := by
  classical
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rcases Nat.eq_zero_or_pos (finrank ℂ V) with hV | hV
  · have : Subsingleton V := Module.finrank_zero_iff.1 hV
    exact ⟨1, one_pow n, LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  set E := (End.finite_hasEigenvalue f).toFinset with hE
  have hdim : ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℂ) = (finrank ℂ V : ℂ) := by
    simpa using (trace_pow_eq_sum_eigenvalue_pow hn' hf 0).symm
  have htrace : ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℂ) * μ = LinearMap.trace ℂ V f := by
    simpa using (trace_pow_eq_sum_eigenvalue_pow hn' hf 1).symm
  have hNne : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hV.ne'
  set μ₀ : ℂ := LinearMap.trace ℂ V f / (finrank ℂ V : ℂ) with hμ₀def
  have htμ₀ : LinearMap.trace ℂ V f = μ₀ * (finrank ℂ V : ℂ) := by
    rw [hμ₀def, div_mul_cancel₀ _ hNne]
  have hnormμ₀ : ‖μ₀‖ = 1 := by
    rw [hμ₀def, norm_div, h, Complex.norm_natCast]
    exact div_self (Nat.cast_ne_zero.2 hV.ne')
  have hμ₀ne : μ₀ ≠ 0 := norm_ne_zero_iff.mp (hnormμ₀ ▸ one_ne_zero)
  have hconj : (starRingEnd ℂ) μ₀ * μ₀ = 1 := by
    rw [← Complex.inv_eq_conj hnormμ₀]
    exact inv_mul_cancel₀ hμ₀ne
  have hkey : ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℂ) * ((starRingEnd ℂ) μ₀ * μ)
      = (finrank ℂ V : ℂ) := by
    calc ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℂ) * ((starRingEnd ℂ) μ₀ * μ)
        = (starRingEnd ℂ) μ₀ * ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℂ) * μ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = (starRingEnd ℂ) μ₀ * (μ₀ * (finrank ℂ V : ℂ)) := by rw [htrace, htμ₀]
      _ = (finrank ℂ V : ℂ) := by rw [← mul_assoc, hconj, one_mul]
  have hzero : ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℂ) * (1 - (starRingEnd ℂ) μ₀ * μ) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hdim, hkey, sub_self]
  have hreal : ∑ μ ∈ E, (finrank ℂ (f.eigenspace μ) : ℝ) * (1 - ((starRingEnd ℂ) μ₀ * μ).re)
      = 0 := by
    have := congrArg Complex.re hzero
    simpa [Complex.re_sum, Complex.mul_re] using this
  have hnormE : ∀ μ ∈ E, ‖(starRingEnd ℂ) μ₀ * μ‖ = 1 := by
    intro μ hμ
    have hpow : μ ^ n = 1 :=
      pow_eq_one_of_hasEigenvalue hf ((End.finite_hasEigenvalue f).mem_toFinset.1 hμ)
    rw [norm_mul, Complex.norm_conj, hnormμ₀, Complex.norm_eq_one_of_pow_eq_one hpow hn, one_mul]
  have hnonneg : ∀ μ ∈ E,
      0 ≤ (finrank ℂ (f.eigenspace μ) : ℝ) * (1 - ((starRingEnd ℂ) μ₀ * μ).re) := by
    intro μ hμ
    have := (Complex.re_le_norm ((starRingEnd ℂ) μ₀ * μ)).trans_eq (hnormE μ hμ)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hall : ∀ μ ∈ E, μ = μ₀ := by
    intro μ hμ
    have hev : f.HasEigenvalue μ := (End.finite_hasEigenvalue f).mem_toFinset.1 hμ
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hreal μ hμ
    have hdpos : (finrank ℂ (f.eigenspace μ) : ℝ) ≠ 0 := by
      have : f.eigenspace μ ≠ ⊥ := hev
      simpa [Submodule.finrank_eq_zero] using this
    have hre : ((starRingEnd ℂ) μ₀ * μ).re = 1 := by
      rcases mul_eq_zero.1 hz with h' | h'
      · exact absurd h' hdpos
      · linarith
    have him : ((starRingEnd ℂ) μ₀ * μ).im = 0 :=
      Complex.abs_re_eq_norm.mp (by rw [hre, hnormE μ hμ, abs_one])
    have h1 : (starRingEnd ℂ) μ₀ * μ = 1 :=
      Complex.ext (by simpa using hre) (by simpa using him)
    calc μ = ((starRingEnd ℂ) μ₀ * μ₀) * μ := by rw [hconj, one_mul]
      _ = μ₀ * ((starRingEnd ℂ) μ₀ * μ) := by ring
      _ = μ₀ := by rw [h1, mul_one]
  have hEne : E.Nonempty := by
    rcases Finset.eq_empty_or_nonempty E with hEmp | hne
    · rw [hEmp, Finset.sum_empty] at hdim
      exact absurd hdim.symm hNne
    · exact hne
  obtain ⟨ν, hν⟩ := hEne
  have hμ₀E : μ₀ ∈ E := by rw [← hall ν hν]; exact hν
  refine ⟨μ₀,
    pow_eq_one_of_hasEigenvalue hf ((End.finite_hasEigenvalue f).mem_toFinset.1 hμ₀E), ?_⟩
  have hss : (f - μ₀ • (1 : End ℂ V)).IsSemisimple := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (End.isSemisimple_sub_algebraMap_iff (μ := μ₀)).2 (isSemisimple_of_pow_eq_one hn' hf)
  refine sub_eq_zero.1 (hss.eq_zero_iff_forall_eigenvalue.2 fun μ hμ => ?_)
  have hid : (f - μ₀ • (1 : End ℂ V)) = f - μ₀ • LinearMap.id := by rw [End.one_eq_id]
  rw [hid, End.hasEigenvalue_sub_iff] at hμ
  have := hall (μ + μ₀) ((End.finite_hasEigenvalue f).mem_toFinset.2 hμ)
  linear_combination this
private theorem eq_one_of_trace_eq_finrank {f : End ℂ V} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1)
    (h : LinearMap.trace ℂ V f = (finrank ℂ V : ℂ)) : f = 1 := by
  obtain ⟨μ, -, rfl⟩ :=
    _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.Module.End.exists_eq_smul_of_norm_trace_eq_finrank hn hf (by rw [h, Complex.norm_natCast])
  rcases Nat.eq_zero_or_pos (finrank ℂ V) with hV | hV
  · have : Subsingleton V := Module.finrank_zero_iff.1 hV
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  · rw [map_smul, LinearMap.trace_one, smul_eq_mul] at h
    rw [mul_right_cancel₀ (Nat.cast_ne_zero.2 hV.ne') (h.trans (one_mul _).symm), one_smul]
theorem trace_eq_finrank_iff {f : End ℂ V} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1) :
    LinearMap.trace ℂ V f = (finrank ℂ V : ℂ) ↔ f = 1 :=
  ⟨eq_one_of_trace_eq_finrank hn hf, fun h => by rw [h, LinearMap.trace_one]⟩
end Complex
end End
end TauCeti
end UpstreamSource2_6
section UpstreamSource2_7
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
open _root_.Module _root_.Polynomial
universe u v w
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
section Field
variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]
private theorem isIntegral_char (ρ : Representation k G V) {g : G} {n : ℕ}
    (hn : n ≠ 0) (hg : g ^ n = 1) : IsIntegral ℤ (ρ.character g) := by
  have hf : ρ g ^ n = 1 := by rw [← map_pow, hg, map_one]
  exact End.isIntegral_trace_of_pow_eq_one hn hf
end Field
end Representation
end TauCeti
end UpstreamSource2_7
section UpstreamSource2_8
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
private theorem dvd_of_isIntegral_of_natCast_mul_eq {k : Type*} [Field k] [CharZero k] {m n : ℕ}
    {z : k} (hz : IsIntegral ℤ z) (h : (n : k) * z = m) (hn : n ≠ 0) : n ∣ m := by
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz' : algebraMap ℚ k ((m : ℚ) / (n : ℚ)) = z := by
    rw [map_div₀, map_natCast, map_natCast, eq_comm, eq_div_iff hnk, mul_comm]
    exact h
  have hq : IsIntegral ℤ ((m : ℚ) / (n : ℚ)) :=
    isIntegral_algebraMap_iff.mp (hz' ▸ hz)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  have hyq : (y : ℚ) * (n : ℚ) = (m : ℚ) := by
    rw [← eq_intCast (algebraMap ℤ ℚ) y, hy, div_mul_cancel₀]
    exact Nat.cast_ne_zero.mpr hn
  refine Int.natCast_dvd_natCast.mp ⟨y, ?_⟩
  exact_mod_cast (by linarith : (m : ℚ) = (n : ℚ) * (y : ℚ))
end TauCeti
end UpstreamSource2_8
section UpstreamSource2_9
namespace TauCeti
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
open _root_.Module (finrank)
open scoped _root_.MonoidAlgebra
namespace Representation
open _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
section Divisibility
private theorem character_mul_character_inv_mem_classFunction (ρ : Representation k G V) :
    (fun g : G => ρ.character g * ρ.character g⁻¹) ∈ ClassFunction k G := by
  refine ClassFunction.mem_iff.mpr fun g h => ?_
  have hinv : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := conj_inv
  rw [hinv, ρ.char_conj, ρ.char_conj]
variable [Fintype G] [DecidableEq G] [IsAlgClosed k] [FiniteDimensional k V]
  (ρ : Representation k G V) [ρ.IsIrreducible]
private theorem finrank_mul_sum_centralCharacter_eq_card [Invertible (Nat.card G : k)] :
    (finrank k V : k) * ∑ C : ConjClasses G, (_root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter k k[G] ρ.asModule) (classSumCenter C) *
        ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual) C = Nat.card G := by
  classical
  have hself : Nonempty (_root_.Representation.Equiv ρ ρ) := ⟨.refl ρ⟩
  have horth : ∑ g : G, ρ.character g * ρ.character g⁻¹ = Nat.card G := by
    have h := _root_.Representation.char_orthonormal ρ ρ
    rw [ite_eq_left hself,
      inv_mul_eq_iff_eq_mul₀ (Invertible.ne_zero (a := (Nat.card G : k)))] at h
    simpa using h
  rw [Finset.mul_sum, ← horth,
    ClassFunction.sum_eq_sum_conjClasses
      (⟨_, character_mul_character_inv_mem_classFunction ρ⟩ : ClassFunction k G)]
  refine Finset.sum_congr rfl fun C _ => ?_
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  have hω := centralCharacter_classSumCenter_mul_character_one ρ (rfl : ConjClasses.mk g = _)
  rw [ρ.char_one] at hω
  have hdual : ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual)
      (ConjClasses.mk g) = ρ.character g⁻¹ := by
    rw [ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply, ρ.char_dual]
  rw [hdual, ClassFunction.toConjClasses_mk, ← mul_assoc, mul_comm (finrank k V : k), hω,
    mul_assoc]
end Divisibility
section Dvd
variable [Finite G] [IsAlgClosed k] [CharZero k] [FiniteDimensional k V]
  (ρ : Representation k G V) [ρ.IsIrreducible]
include ρ in
theorem finrank_dvd_card : finrank k V ∣ Nat.card G := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hcard : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  have : Nontrivial V := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  refine dvd_of_isIntegral_of_natCast_mul_eq (k := k) ?_
    (finrank_mul_sum_centralCharacter_eq_card ρ) Module.finrank_pos.ne'
  refine IsIntegral.sum _ fun C _ => IsIntegral.mul
    (isIntegral_centralCharacter_classSumCenter ρ C) ?_
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply]
  exact isIntegral_char ρ.dual (isOfFinOrder_of_finite g).orderOf_pos.ne' (pow_orderOf_eq_one g)
end Dvd
end Representation
end TauCeti
end UpstreamSource2_9
end D5.S3.FiniteGroups.CharacterDegreeDivisibility
