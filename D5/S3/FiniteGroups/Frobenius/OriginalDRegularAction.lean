/- GID: D5/S3/FiniteGroups/Frobenius/OriginalDRegularAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/OriginalDRegularAction
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Original division-ring normal-basis coordinates consumed by Frobenius. -/

/-
The descent supplier is the attributed project port of Qiuzhen-CFSG/CFSG,
revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7,
Theory/Representation/FiniteFieldSemilinearDisplacement/Descent.lean,
Apache-2.0. Normal bases and tensor-basis equivalences are from pinned Mathlib.
-/

import D5.S3.Factorization.Galois.GaloisVectorDescent
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Module
open scoped TensorProduct

namespace FrobeniusOriginalD.RegularAction

universe uK uF uD uU

variable {K : Type uK} {F : Type uF} {D : Type uD} {U : Type uU}
  [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
  [DivisionRing D] [AddCommGroup U] [Module D U]

variable (a : F →+* Module.End D U) (τ : Gal(F/K) →* Module.End D U)

/-- Original-D invariants. Mathlib's `Representation.invariants` requires a
commutative scalar ring, so it is deliberately NOT instantiated at D. -/
def fixed : Submodule D U where
  carrier := {u | ∀ g : Gal(F/K), τ g u = u}
  zero_mem' g := (τ g).map_zero
  add_mem' hu hv g := by rw [map_add, hu g, hv g]
  smul_mem' d u hu g := by rw [map_smul, hu g]

/-- The actual field operators give the F-module structure on U. -/
abbrev fieldModule : Module F U := Module.compHom U a

/-- A monoid map to endomorphisms of a group acts by invertible operators;
no extra invertibility assumption on its values is required. -/
abbrev groupAction : DistribMulAction Gal(F/K) U where
  smul g u := τ g u
  one_smul u := by change τ 1 u = u; rw [map_one]; rfl
  mul_smul g h u := by
    change τ (g * h) u = τ g (τ h u)
    rw [map_mul]; rfl
  smul_zero g := (τ g).map_zero
  smul_add g u v := (τ g).map_add u v

variable (cov : ∀ (g : Gal(F/K)) (x : F), τ g * a x = a (g x) * τ g)

include cov in
/-- True covariance supplies semilinearity, rather than assuming descent data. -/
theorem semilinear :
    letI : Module F U := fieldModule a
    letI : DistribMulAction Gal(F/K) U := groupAction τ
    SMulDistribClass Gal(F/K) F U := by
  letI : Module F U := fieldModule a
  letI : DistribMulAction Gal(F/K) U := groupAction τ
  exact ⟨fun g x u => LinearMap.congr_fun (cov g x) u⟩

/-- The forward normal-basis map. Its D-linearity comes directly from `a`.
Neither D-commutativity nor any D-algebra structure on F is used. -/
def normalMap : (Gal(F/K) → fixed τ) →ₗ[D] U where
  toFun f := ∑ g : Gal(F/K), a (IsGalois.normalBasis K F g) (f g : U)
  map_add' f q := by simp [Finset.sum_add_distrib]
  map_smul' d f := by simp [Finset.smul_sum]

local notation "GD" => D5.S3.Factorization.Galois.GaloisVectorDescent.fixedSubmodule

include cov in
/-- Bijectivity composes descent and the tensor-basis equivalence. -/
theorem normalMap_bijective : Function.Bijective (normalMap a τ) := by
  classical
  letI : Module F U := fieldModule a
  letI : Module K U := Module.restrictScalars K F U
  letI : IsScalarTower K F U := IsScalarTower.restrictScalars K F U
  letI : DistribMulAction Gal(F/K) U := groupAction τ
  letI : SMulDistribClass Gal(F/K) F U := semilinear a τ cov
  let S₀ : Submodule K U := GD Gal(F/K) K F U
  let b := IsGalois.normalBasis K F
  let e : (Gal(F/K) → S₀) ≃ₗ[K] U :=
    (Finsupp.linearEquivFunOnFinite K S₀ Gal(F/K)).symm ≪≫ₗ
      (TensorProduct.equivFinsuppOfBasisLeft b).symm ≪≫ₗ
      (D5.S3.Factorization.Galois.GaloisVectorDescent.descentEquiv
        Gal(F/K) K F U).restrictScalars K
  have he (f : Gal(F/K) → fixed τ) : e f = normalMap a τ f := by
    change S₀.subtype.liftBaseChange F
        ((TensorProduct.equivFinsuppOfBasisLeft b).symm
          ((Finsupp.linearEquivFunOnFinite K
            S₀ Gal(F/K)).symm f)) = normalMap a τ f
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
      Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simp only [map_sum, LinearMap.liftBaseChange_tmul]
    rfl
  constructor
  · intro f q h
    apply e.injective
    rw [he, he]
    exact h
  · intro u
    obtain ⟨f, hf⟩ := e.surjective u
    exact ⟨f, (he f).symm.trans hf⟩

include cov in
theorem normalMap_regular (h : Gal(F/K)) (f : Gal(F/K) → fixed τ) :
    normalMap a τ (fun g => f (h⁻¹ * g)) = τ h (normalMap a τ f) := by
  classical
  have hb (g : Gal(F/K)) :
      h (IsGalois.normalBasis K F g) = IsGalois.normalBasis K F (h * g) := by
    rw [IsGalois.normalBasis_apply (h * g), IsGalois.normalBasis_apply g]
    rfl
  have ht (g : Gal(F/K)) :
      τ h (a (IsGalois.normalBasis K F g) (f g : U)) =
        a (IsGalois.normalBasis K F (h * g)) (f g : U) := by
    have hc := LinearMap.congr_fun (cov h (IsGalois.normalBasis K F g)) (f g : U)
    change τ h (a (IsGalois.normalBasis K F g) (f g : U)) =
      a (h (IsGalois.normalBasis K F g)) (τ h (f g : U)) at hc
    rw [hb, (f g).property h] at hc
    exact hc
  change (∑ g : Gal(F/K), a (IsGalois.normalBasis K F g) (f (h⁻¹ * g) : U)) =
    τ h (∑ g : Gal(F/K), a (IsGalois.normalBasis K F g) (f g : U))
  rw [map_sum]
  simp_rw [ht]
  symm
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp)

/-- U has the actual left regular action over the ORIGINAL division ring D. -/
def regularEquiv : U ≃ₗ[D] (Gal(F/K) → fixed τ) :=
  (LinearEquiv.ofBijective (normalMap a τ) (normalMap_bijective a τ cov)).symm

theorem normalMap_regularEquiv (u : U) :
    normalMap a τ (regularEquiv a τ cov u) = u :=
  (LinearEquiv.ofBijective (normalMap a τ)
    (normalMap_bijective a τ cov)).apply_symm_apply u

/-- Pointwise equivariance, with the inverse on the LEFT of the index. -/
theorem regularEquiv_apply_action (h : Gal(F/K)) (u : U) (g : Gal(F/K)) :
    regularEquiv a τ cov (τ h u) g = regularEquiv a τ cov u (h⁻¹ * g) := by
  have he : regularEquiv a τ cov (τ h u) =
      fun g => regularEquiv a τ cov u (h⁻¹ * g) := by
    apply (normalMap_bijective a τ cov).injective
    rw [normalMap_regularEquiv, normalMap_regular a τ cov,
      normalMap_regularEquiv]
  exact congrFun he g

end FrobeniusOriginalD.RegularAction
