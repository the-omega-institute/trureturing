/- GID: D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtComplexIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar extension preserves Specht intertwiner dimension and gives complex simplicity. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations/comments, repository namespaces, existing D5 suppliers,
and definitionally equivalent normalization at private supplier boundaries.
License, immutable locators, consumers and retirement rule:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
SOURCE ONLY: no elaboration, axiom report, validated Reg, freeze or full HSW result.
These are necessary supplier proofs, not an independent novelty/admission claim.
utility: none: unbounded structural representation theory, no finite computation.
-/
import D5.S3.Combinatorics.Partitions.SpechtAbsoluteIrreducibility
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
open scoped BigOperators

noncomputable section
open TensorProduct
namespace LinearMap
theorem isBaseChange_baseChangeHom (R A M N : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommMonoid N] [Module R N] :
    IsBaseChange A (baseChangeHom R A M N) := by
  convert! (TensorProduct.isBaseChange R M A).linearMapLeftRight
    (TensorProduct.isBaseChange R N A) using 1
  ext f m
  exact (IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R M A)
    ((TensorProduct.mk R A N) 1) f m).symm

end LinearMap
namespace Representation
section BaseChange
variable {R A G V : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Monoid G] [AddCommMonoid V] [Module R V]
@[simp]
theorem _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange_apply (ρ : _root_.Representation R G V) (g : G) :
    _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange A ρ g = (ρ g).baseChange A :=
  by
    rw [_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange, MonoidHom.comp_apply]
    rfl

end BaseChange
end Representation
namespace TauCeti
section Intertwiner
variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] {G : Type*} [Monoid G] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
private def intertwiningDefect (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    (V →ₗ[K] W) →ₗ[K] (G → (V →ₗ[K] W)) :=
  LinearMap.pi fun g => LinearMap.llcomp K V W W (σ g) - LinearMap.lcomp K W (ρ g)

private theorem intertwiningDefect_apply (ρ : _root_.Representation K G V)
    (σ : _root_.Representation K G W) (f : V →ₗ[K] W) (g : G) :
    intertwiningDefect ρ σ f g = σ g ∘ₗ f - f ∘ₗ ρ g :=
  rfl

private theorem mem_ker_intertwiningDefect {ρ : _root_.Representation K G V}
    {σ : _root_.Representation K G W} {f : V →ₗ[K] W} :
    f ∈ LinearMap.ker (intertwiningDefect ρ σ) ↔ ∀ g, f ∘ₗ ρ g = σ g ∘ₗ f := by
  rw [LinearMap.mem_ker, funext_iff]
  refine forall_congr' fun g => ?_
  rw [intertwiningDefect_apply, Pi.zero_apply, sub_eq_zero, eq_comm]

private def intertwiningMapEquivKerDefect (ρ : _root_.Representation K G V)
    (σ : _root_.Representation K G W) :
    _root_.Representation.IntertwiningMap ρ σ ≃ₗ[K] LinearMap.ker (intertwiningDefect ρ σ) where
  toFun f := ⟨f.toLinearMap, mem_ker_intertwiningDefect.mpr f.isIntertwining'⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.1, mem_ker_intertwiningDefect.mp f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem intertwiningDefect_baseChange (ρ : _root_.Representation K G V)
    (σ : _root_.Representation K G W) (f : V →ₗ[K] W) (g : G) :
    intertwiningDefect (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L ρ)
        (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L σ) (f.baseChange L) g
      = (intertwiningDefect ρ σ f g).baseChange L := by
  rw [intertwiningDefect_apply, intertwiningDefect_apply, LinearMap.baseChange_sub,
    LinearMap.baseChange_comp, LinearMap.baseChange_comp, _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange_apply,
    _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange_apply]

variable [Module.Free K V] [Module.Finite K V]
private theorem intertwiningDefect_homBaseChangeEquiv [Fintype G] [DecidableEq G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W)
    (x : L ⊗[K] (V →ₗ[K] W)) :
    intertwiningDefect (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L ρ)
        (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L σ)
        ((LinearMap.isBaseChange_baseChangeHom K L V W).equiv x)
      = ((TensorProduct.piRight K L L _).trans
          (LinearEquiv.piCongrRight fun _ ↦ (LinearMap.isBaseChange_baseChangeHom K L V W).equiv))
          (TensorProduct.AlgebraTensorModule.lTensor L L (intertwiningDefect ρ σ) x) := by
  induction x with
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
    funext g


    simp only [IsBaseChange.equiv_tmul, LinearMap.baseChangeHom_apply, _root_.map_smul,
      Pi.smul_apply, intertwiningDefect_baseChange,
      TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight_apply, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]

private theorem comap_ker_intertwiningDefect_baseChange [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Submodule.comap ((LinearMap.isBaseChange_baseChangeHom K L V W).equiv :
        L ⊗[K] (V →ₗ[K] W) →ₗ[L] _)
        (LinearMap.ker (intertwiningDefect (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L ρ)
          (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L σ)))
      = LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L
          (intertwiningDefect ρ σ)) := by
  classical
  let _ := Fintype.ofFinite G
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, LinearEquiv.coe_coe,
    intertwiningDefect_homBaseChangeEquiv]
  exact ((TensorProduct.piRight K L L (fun _ : G ↦ V →ₗ[K] W)).trans
    (LinearEquiv.piCongrRight fun _ : G ↦
      (LinearMap.isBaseChange_baseChangeHom K L V W).equiv)).map_eq_zero_iff

noncomputable def _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.intertwiningMapBaseChangeEquiv
    [Module.Flat K L] [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    L ⊗[K] _root_.Representation.IntertwiningMap ρ σ ≃ₗ[L]
      _root_.Representation.IntertwiningMap (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L ρ)
        (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L σ) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (intertwiningMapEquivKerDefect ρ σ)).trans <|
    (LinearMap.tensorKerEquiv L L (intertwiningDefect ρ σ)).trans <|
      (LinearEquiv.ofEq _ _ (comap_ker_intertwiningDefect_baseChange ρ σ).symm).trans <|
        (LinearEquiv.ofSubmodule' (LinearMap.isBaseChange_baseChangeHom K L V W).equiv _).trans
          (intertwiningMapEquivKerDefect (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L ρ)
            (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L σ)).symm

end Intertwiner
section IntertwinerDimension
variable {K L G V W : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Monoid G] [Finite G] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
theorem _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.finrank_intertwiningMap_baseChange
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Module.finrank L (_root_.Representation.IntertwiningMap
        (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L ρ) (_root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Representation.baseChange L σ))
      = Module.finrank K (_root_.Representation.IntertwiningMap ρ σ) := by
  rw [← (Representation.intertwiningMapBaseChangeEquiv ρ σ).finrank_eq, Module.finrank_baseChange]

end IntertwinerDimension
open CategoryTheory Module
variable {n : ℕ}
private noncomputable instance : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
theorem spechtModuleℂ_def (μ : n.Partition) :
    spechtModuleℂ μ = FDRep.of (Representation.baseChange ℂ (spechtModule μ).ρ) := (rfl)

private theorem finrank_intertwiningMap_spechtModuleℂ (μ ν : n.Partition) :
    finrank ℂ (Representation.IntertwiningMap (spechtModuleℂ μ).ρ (spechtModuleℂ ν).ρ)
      = finrank ℚ (Representation.IntertwiningMap (spechtModule μ).ρ (spechtModule ν).ρ) := by
  rw [spechtModuleℂ_def, spechtModuleℂ_def, FDRep.of_ρ', FDRep.of_ρ']
  exact Representation.finrank_intertwiningMap_baseChange _ _

private theorem sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card
    (μ ν : n.Partition) :
    ∑ σ : Equiv.Perm (Fin n),
        (spechtModuleℂ μ).character σ * (spechtModuleℂ ν).character σ⁻¹
      = (finrank ℚ (Representation.IntertwiningMap (spechtModule ν).ρ (spechtModule μ).ρ) : ℂ) *
        (Nat.card (Equiv.Perm (Fin n)) : ℂ) := by
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (spechtModuleℂ ν).ρ (spechtModuleℂ μ).ρ
  rw [finrank_intertwiningMap_spechtModuleℂ] at h
  have hN : ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp at h
  rw [mul_comm]
  exact h

instance instSimpleSpechtModuleℂ (μ : n.Partition) : Simple (spechtModuleℂ μ) := by
  have hend : finrank ℚ
      (Representation.IntertwiningMap (spechtModule μ).ρ (spechtModule μ).ρ) = 1 := by
    rw [(spechtModuleIntertwiningEndAlgEquiv μ).toLinearEquiv.finrank_eq]
    exact Module.finrank_self ℚ
  rw [FDRep.simple_iff_char_is_norm_one,
    sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card, hend]
  simp

end TauCeti

end

end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
