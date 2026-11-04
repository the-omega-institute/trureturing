/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Natural SL3 realizations identify tangent derivations. -/

/-
admission_basis: escape-witness
tangent_lie_equivalence: proof_shape: content;
  escape_witness: realizationDerivative_surjective (surjective reconstruction from naturality).
Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.derivations
  statement_id: sha256:be4fe9f79c6928168f52615918c3bc4bf02851f8ab2d6da4883e1aa2bacfaff4
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22191.
The tangent Lie equivalence reconstructs every derivation using dual numbers and
recovers brackets by a commutator over iterated dual numbers.
utility none: unbounded tensor and tangent constructions; no finite algorithm.
-/

import Mathlib.LinearAlgebra.Matrix.DualNumber

import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
import Mathlib.Algebra.Lie.Classical
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge

open TensorProduct
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The full automorphism group of a bilinear multiplication; no unit or associativity is imposed. -/
def automorphisms {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (μ : V →ₗ[R] V →ₗ[R] V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {g | ∀ x y, g (μ x y) = μ (g x) (g y)}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro g h hg hh x y
    change g (h (μ x y)) = μ (g (h x)) (g (h y))
    rw [hh, hg]
  inv_mem' := by
    intro g hg x y
    apply g.injective
    simpa using (hg (g.symm x) (g.symm y)).symm

/-- Affine coordinates on GL_d: matrix entries and the inverse determinant. -/
def glCoordinates {d : ℕ} {R : Type} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin d) R) : (Fin d × Fin d) ⊕ Unit → R
  | Sum.inl ij => (g : Matrix (Fin d) (Fin d) R) ij.1 ij.2
  | Sum.inr _ => ((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ)

/-- A closed matrix group, specified directly on commutative coefficient algebras.
The equations define a closed subgroup of GL_d. Over characteristic zero this is a linear
algebraic group as well as an affine group scheme. No general group-scheme API is assumed. -/
structure LinearAlgebraicGroup (k : Type) [Field k] where
  degree : ℕ
  equations : Set (MvPolynomial ((Fin degree × Fin degree) ⊕ Unit) k)
  points : (R : Type) → [CommRing R] → [Algebra k R] →
    Subgroup (Matrix.GeneralLinearGroup (Fin degree) R)
  zero_locus : ∀ (R : Type) [CommRing R] [Algebra k R]
    (g : Matrix.GeneralLinearGroup (Fin degree) R),
    g ∈ points R ↔ ∀ p ∈ equations,
      MvPolynomial.eval₂ (algebraMap k R) (glCoordinates g) p = 0
  mapMem : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) (g : Matrix.GeneralLinearGroup (Fin degree) R),
    g ∈ points R → Matrix.GeneralLinearGroup.map f.toRingHom g ∈ points S

/-- Isomorphism of the full group-valued functors, including naturality for every k-algebra map.
The image automorphisms commute with scalar extension, not merely with field-valued points. -/
structure Realizes {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (G : LinearAlgebraicGroup k) (μ : V →ₗ[k] V →ₗ[k] V) where
  equiv : (R : Type) → [CommRing R] → [Algebra k R] → G.points R ≃* (automorphisms (LinearMap.BilinMap.baseChange R μ))
  naturality : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) (g : G.points R) (x : R ⊗[k] V),
    (TensorProduct.map f.toLinearMap LinearMap.id) ((equiv R g).val x) =
      (equiv S ⟨Matrix.GeneralLinearGroup.map f.toRingHom g.val,
        G.mapMem R S f g.val g.property⟩).val ((TensorProduct.map f.toLinearMap LinearMap.id) x)


end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices

private noncomputable def squareZeroUnit {R A : Type} [CommRing R] [Ring A] [Algebra R A]
    (X : A) (u : R) (hu : u*u=0) : Aˣ := by
  have hn : IsNilpotent (u • X) := ⟨2, by
    simp only [pow_two, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hu, zero_smul]⟩
  let h := hn.isUnit_one_add
  exact h.unit.copy (1 + u • X) h.unit_spec.symm (1 - u • X)
    ((Units.mul_eq_one_iff_inv_eq).mp (by
      rw [h.unit_spec]
      simp only [mul_sub, add_mul, one_mul, mul_one, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_add, smul_sub, smul_smul, hu, zero_smul]
      abel)).symm

private theorem squareZeroUnit_commutator {R A : Type} [CommRing R] [Ring A] [Algebra R A]
    (X Y : A) (u v : R) (hu : u*u=0) (hv : v*v=0) :
    squareZeroUnit X u hu * squareZeroUnit Y v hv *
      (squareZeroUnit X u hu)⁻¹ * (squareZeroUnit Y v hv)⁻¹ =
    squareZeroUnit (X*Y-Y*X) (u*v)
      (by rw [mul_mul_mul_comm,hu,zero_mul]) := by
  apply Units.ext
  change ((1+u • X)*(1+v • Y)*(1-u • X)*(1-v • Y) : A) =
    1+(u*v) • (X*Y-Y*X)
  have hvu : (v*u)*v=0 := by rw [mul_right_comm,hv,zero_mul]
  have huuv : u*(u*v)=0 := by rw [← mul_assoc,hu,zero_mul]
  have hvuv : v*(u*v)=0 := by simpa only [mul_assoc] using hvu
  simp only [mul_sub, sub_mul, mul_add, add_mul, one_mul, mul_one,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add, smul_sub, smul_smul,
    hu,hv,hvu,huuv,hvuv,zero_smul,zero_mul,mul_zero,sub_zero,add_zero,zero_add,
    smul_sub]
  rw [mul_comm v u]
  simp only [huuv,hvuv,mul_zero,zero_smul,add_zero]
  abel

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal
open TensorProduct
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

private theorem derivation_baseChange (μ : V →ₗ[k] V →ₗ[k] V) (D : derivations μ)
    (R : Type) [CommRing R] [Algebra k R] (x y : R ⊗[k] V) :
    D.val.baseChange R ((LinearMap.BilinMap.baseChange R μ) x y) =
      (LinearMap.BilinMap.baseChange R μ) (D.val.baseChange R x) y +
        (LinearMap.BilinMap.baseChange R μ) x (D.val.baseChange R y) := by
  induction x using TensorProduct.induction_on
  case zero => simp
  case tmul a v =>
    induction y using TensorProduct.induction_on
    case zero => simp
    case tmul b w =>
      simp only [LinearMap.BilinMap.baseChange_tmul, LinearMap.baseChange_tmul]
      have hD : D.val (μ v w) = μ (D.val v) w + μ v (D.val w) := D.property v w
      rw [hD, TensorProduct.tmul_add]
    case add y z hy hz => simp only [map_add, hy, hz]; abel
  case add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz]
    abel

private noncomputable def squareZeroEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (D : Module.End R M) (u : R) (hu : u * u = 0) : M ≃ₗ[R] M :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv R M (DualMatrices.squareZeroUnit D u hu)

private theorem squareZeroEquiv_preserves (μ : V →ₗ[k] V →ₗ[k] V) (D : derivations μ)
    (R : Type) [CommRing R] [Algebra k R] (u : R) (hu : u * u = 0)
    (x y : R ⊗[k] V) :
    squareZeroEquiv (D.val.baseChange R) u hu ((LinearMap.BilinMap.baseChange R μ) x y) =
      (LinearMap.BilinMap.baseChange R μ) (squareZeroEquiv (D.val.baseChange R) u hu x)
        (squareZeroEquiv (D.val.baseChange R) u hu y) := by
  change (LinearMap.BilinMap.baseChange R μ) x y + u • D.val.baseChange R ((LinearMap.BilinMap.baseChange R μ) x y) =
    (LinearMap.BilinMap.baseChange R μ) (x + u • D.val.baseChange R x) (y + u • D.val.baseChange R y)
  rw [derivation_baseChange μ D R]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    LinearMap.map_smul₂, smul_add, smul_smul, hu, zero_smul]
  abel

private noncomputable def infinitesimalAut (μ : V →ₗ[k] V →ₗ[k] V) (D : derivations μ)
    (R : Type) [CommRing R] [Algebra k R] (u : R) (hu : u * u = 0) : (automorphisms (LinearMap.BilinMap.baseChange R μ)) :=
  ⟨squareZeroEquiv (D.val.baseChange R) u hu, squareZeroEquiv_preserves μ D R u hu⟩

private theorem infinitesimalAut_tmul (μ : V →ₗ[k] V →ₗ[k] V) (D : derivations μ)
    (R : Type) [CommRing R] [Algebra k R] (u : R) (hu : u * u = 0) (a : R) (v : V) :
    (infinitesimalAut μ D R u hu).val (a ⊗ₜ[k] v) =
      a ⊗ₜ[k] v + (u * a) ⊗ₜ[k] D.val v := by
  simp [infinitesimalAut, squareZeroEquiv, DualMatrices.squareZeroUnit, LinearMap.baseChange_tmul, smul_tmul']

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal


namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal
open TensorProduct TrivSqZeroExt
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

private def coeffTensor {R : Type} [CommRing R] [Algebra k R] (c : R →ₗ[k] k) :
    R ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp (TensorProduct.map c (LinearMap.id : V →ₗ[k] V))

private theorem coeffTensor_tmul {R : Type} [CommRing R] [Algebra k R]
    (c : R →ₗ[k] k) (a : R) (v : V) : coeffTensor c (a ⊗ₜ[k] v) = c a • v := by
  rfl

private theorem firstTensor_tmul (a : DualNumber k) (v : V) :
    (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) (a ⊗ₜ[k] v) = a.fst • v := by
  exact coeffTensor_tmul _ a v

private theorem secondTensor_tmul (a : DualNumber k) (v : V) :
    (coeffTensor (TrivSqZeroExt.sndHom k k)) (a ⊗ₜ[k] v) = a.snd • v := by
  exact coeffTensor_tmul _ a v

private theorem dual_tensor_decomposition (x : DualNumber k ⊗[k] V) :
    x = 1 ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) x + DualNumber.eps ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.sndHom k k)) x := by
  induction x using TensorProduct.induction_on
  case zero => simp
  case tmul a v =>
    rw [firstTensor_tmul, secondTensor_tmul, ← TensorProduct.smul_tmul,
      ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_one,
        DualNumber.fst_eps, smul_eq_mul, mul_one, mul_zero, add_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one,
        DualNumber.snd_eps, smul_eq_mul, mul_one, mul_zero, zero_add]
  case add x y hx hy =>
    calc x+y = (1 ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) x + DualNumber.eps ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.sndHom k k)) x) +
        (1 ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) y + DualNumber.eps ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.sndHom k k)) y) := congrArg₂ (·+·) hx hy
         _ = _ := by simp only [map_add, TensorProduct.tmul_add]; abel

private def tangentEnd (α : (DualNumber k ⊗[k] V) ≃ₗ[DualNumber k] (DualNumber k ⊗[k] V)) :
    Module.End k V := by
  letI : IsScalarTower k (DualNumber k) (DualNumber k) :=
    IsScalarTower.of_algebraMap_smul fun a b => (Algebra.smul_def a b).symm
  letI : IsScalarTower k (DualNumber k) (DualNumber k ⊗[k] V) := TensorProduct.isScalarTower_left
  exact (coeffTensor (TrivSqZeroExt.sndHom k k)).comp ((α.toLinearMap.restrictScalars k).comp ((TensorProduct.mk k (DualNumber k) V) 1))

private theorem tangentEnd_expansion
    (α : (DualNumber k ⊗[k] V) ≃ₗ[DualNumber k] (DualNumber k ⊗[k] V))
    (hα : ∀ v : V, (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) (α (1 ⊗ₜ[k] v)) = v) (v : V) :
    α (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] v + DualNumber.eps ⊗ₜ[k] tangentEnd α v := by
  change α (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] v +
    DualNumber.eps ⊗ₜ[k] (coeffTensor (TrivSqZeroExt.sndHom k k)) (α (1 ⊗ₜ[k] v))
  simpa only [hα] using dual_tensor_decomposition (α (1 ⊗ₜ[k] v))

private theorem tangentEnd_is_derivation (μ : V →ₗ[k] V →ₗ[k] V) (α : (automorphisms (LinearMap.BilinMap.baseChange (DualNumber k) μ)))
    (hα : ∀ v : V, (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) (α.val (1 ⊗ₜ[k] v)) = v) :
    tangentEnd α.val ∈ derivations μ := by
  intro v w
  have h := α.property (1 ⊗ₜ[k] v) (1 ⊗ₜ[k] w)
  rw [LinearMap.BilinMap.baseChange_tmul, one_mul,
    tangentEnd_expansion α.val hα v, tangentEnd_expansion α.val hα w,
    tangentEnd_expansion α.val hα (μ v w)] at h
  apply_fun (coeffTensor (TrivSqZeroExt.sndHom k k)) at h
  simpa only [map_add, LinearMap.add_apply, LinearMap.BilinMap.baseChange_tmul,
    secondTensor_tmul, one_mul, mul_one, DualNumber.eps_mul_eps,
    TrivSqZeroExt.snd_one, DualNumber.snd_eps, TensorProduct.zero_tmul,
    zero_smul, one_smul, map_zero, add_zero, zero_add, add_comm] using h

private def tangentDerivation (μ : V →ₗ[k] V →ₗ[k] V) (α : (automorphisms (LinearMap.BilinMap.baseChange (DualNumber k) μ)))
    (hα : ∀ v : V, (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) (α.val (1 ⊗ₜ[k] v)) = v) : derivations μ :=
  ⟨tangentEnd α.val, tangentEnd_is_derivation μ α hα⟩

private theorem infinitesimalAut_reconstruction (μ : V →ₗ[k] V →ₗ[k] V)
    (α : (automorphisms (LinearMap.BilinMap.baseChange (DualNumber k) μ)))
    (hα : ∀ v : V, (coeffTensor (TrivSqZeroExt.fstHom k k k).toLinearMap) (α.val (1 ⊗ₜ[k] v)) = v) :
    infinitesimalAut μ (tangentDerivation μ α hα) (DualNumber k) DualNumber.eps
      DualNumber.eps_mul_eps = α := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  have h : a ⊗ₜ[k] v = a • (1 ⊗ₜ[k] v) := TensorProduct.tmul_eq_smul_one_tmul a v
  simp only [h, map_smul]
  congr 1
  change (infinitesimalAut μ (tangentDerivation μ α hα) (DualNumber k)
    DualNumber.eps DualNumber.eps_mul_eps).val (1 ⊗ₜ[k] v) = α.val (1 ⊗ₜ[k] v)
  rw [infinitesimalAut_tmul, mul_one]
  exact (tangentEnd_expansion α.val hα v).symm

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal


namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem squareZeroEquiv_commutator {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (A B : Module.End R M) (u v : R) (hu : u * u = 0) (hv : v * v = 0) :
    squareZeroEquiv A u hu * squareZeroEquiv B v hv *
      (squareZeroEquiv A u hu)⁻¹ * (squareZeroEquiv B v hv)⁻¹ =
        squareZeroEquiv (A * B - B * A) (u * v)
          (by rw [mul_mul_mul_comm,hu,zero_mul])  := by
  simpa only [squareZeroEquiv, map_mul, map_inv] using
    congrArg (LinearMap.GeneralLinearGroup.generalLinearEquiv R M)
      (DualMatrices.squareZeroUnit_commutator A B u v hu hv)

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal


namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal
open TensorProduct TrivSqZeroExt
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

private theorem infinitesimalAut_derivative (μ : V →ₗ[k] V →ₗ[k] V) (D : derivations μ) :
    tangentEnd (infinitesimalAut μ D (DualNumber k) DualNumber.eps
      DualNumber.eps_mul_eps).val = D.val := by
  ext v
  change (coeffTensor (TrivSqZeroExt.sndHom k k)) ((infinitesimalAut μ D (DualNumber k) DualNumber.eps
    DualNumber.eps_mul_eps).val (1 ⊗ₜ[k] v)) = D.val v
  rw [infinitesimalAut_tmul, mul_one, map_add, secondTensor_tmul, secondTensor_tmul]
  simp

private theorem infinitesimalAut_injective (μ : V →ₗ[k] V →ₗ[k] V) :
    Function.Injective (fun D : derivations μ => infinitesimalAut μ D (DualNumber k)
      DualNumber.eps DualNumber.eps_mul_eps) := by
  intro D E h
  apply Subtype.ext
  have hh := congrArg (fun α : (automorphisms (LinearMap.BilinMap.baseChange (DualNumber k) μ)) => tangentEnd α.val) h
  simpa only [infinitesimalAut_derivative] using hh

private theorem infinitesimalAut_add (μ : V →ₗ[k] V →ₗ[k] V) (D E : derivations μ)
    (R : Type) [CommRing R] [Algebra k R] (u : R) (hu : u*u=0) :
    infinitesimalAut μ (D+E) R u hu = infinitesimalAut μ D R u hu * infinitesimalAut μ E R u hu := by
  apply Subtype.ext
  ext x
  change x + u • (D.val+E.val).baseChange R x =
    (x + u • E.val.baseChange R x) + u • D.val.baseChange R (x + u • E.val.baseChange R x)
  rw [LinearMap.baseChange_add]
  simp only [LinearMap.add_apply, map_add, map_smul, smul_add, smul_smul, hu, zero_smul]
  abel

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge
open Matrix

private noncomputable def slEquation (n : ℕ) : MvPolynomial ((Fin n × Fin n) ⊕ Unit) ℂ :=
  Matrix.det (fun i j => MvPolynomial.X (Sum.inl (i,j))) - 1

private theorem eval_slEquation (n : ℕ) (R : Type) [CommRing R] [Algebra ℂ R]
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    MvPolynomial.eval₂ (algebraMap ℂ R) (glCoordinates g) (slEquation n) =
      Matrix.det (g : Matrix (Fin n) (Fin n) R) - 1 := by
  let e := MvPolynomial.eval₂Hom (algebraMap ℂ R) (glCoordinates g)
  have h : e (Matrix.det (fun i j : Fin n => MvPolynomial.X (Sum.inl (i,j)))) =
      Matrix.det (g : Matrix (Fin n) (Fin n) R) := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [e, glCoordinates]
  change e (slEquation n) = Matrix.det (g : Matrix (Fin n) (Fin n) R) - 1
  simpa only [slEquation, map_sub, map_one] using congrArg (fun r => r - 1) h

noncomputable def slGroup (n : ℕ) : LinearAlgebraicGroup ℂ where
  degree := n
  equations := {slEquation n}
  points R := (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) R →* Rˣ).ker
  zero_locus := by
    intro R _ _ g
    simp only [Set.mem_singleton_iff, forall_eq, eval_slEquation]
    rw [MonoidHom.mem_ker, Units.ext_iff]
    exact sub_eq_zero.symm
  mapMem := by
    intro R S _ _ _ _ f g hg
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) = 1
    rw [Matrix.GeneralLinearGroup.map_det]
    change Matrix.GeneralLinearGroup.det g = 1 at hg
    rw [hg, map_one]

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge


set_option autoImplicit false
set_option maxHeartbeats 200000
namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices
open Matrix TrivSqZeroExt
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

private def tangentGL (X : Matrix n n k) : Matrix.GeneralLinearGroup n (DualNumber k) := by
  let x : DualNumber (Matrix n n k) := ⟨1, X⟩
  letI : Invertible x.fst := invertibleOne
  letI : Invertible x := TrivSqZeroExt.invertibleOfInvertibleFst x
  exact Units.map (Matrix.dualNumberEquiv (R := k)).symm.toRingHom.toMonoidHom
    (unitOfInvertible x)

private theorem tangentGL_add (X Y : Matrix n n k) :
    tangentGL (X + Y) = tangentGL X * tangentGL Y := by
  apply Units.ext
  apply (Matrix.dualNumberEquiv (R := k)).injective
  simp only [Units.val_mul]
  rw [map_mul]
  apply TrivSqZeroExt.ext
  · change (1 : Matrix n n k) = 1 * 1
    simp
  · change X + Y = (1 : Matrix n n k) * Y + X * 1
    simp only [one_mul,mul_one,add_comm]

private theorem tangentGL_injective : Function.Injective (tangentGL (k := k) (n := n)) := by
  intro X Y h
  ext i j
  exact congrArg (fun g : Matrix.GeneralLinearGroup n (DualNumber k) =>
    (g.val i j).snd) h


private theorem tangentGL_surj_kernel (g : Matrix.GeneralLinearGroup n (DualNumber k))
    (hg : Matrix.GeneralLinearGroup.map (TrivSqZeroExt.fstHom k k k).toRingHom g = 1) :
    tangentGL (fun i j => (g.val i j).snd) = g := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · exact (congrArg (fun h : Matrix.GeneralLinearGroup n k => h.val i j) hg).symm
  · rfl

private theorem tangentGL_scale (a : k) (X : Matrix n n k) :
    Matrix.GeneralLinearGroup.map
      (TrivSqZeroExt.map (a • (LinearMap.id : k →ₗ[k] k))).toRingHom (tangentGL X) =
        tangentGL (a • X) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (TrivSqZeroExt.map (a • (LinearMap.id : k →ₗ[k] k)))
    (⟨(1 : Matrix n n k) i j, X i j⟩ : DualNumber k) =
      (⟨(1 : Matrix n n k) i j, a • X i j⟩ : DualNumber k)
  apply TrivSqZeroExt.ext <;> simp

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices

set_option backward.isDefEq.respectTransparency.types true

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices
open Matrix TrivSqZeroExt
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

private theorem tangentGL_matrix (X : Matrix n n k) :
    (tangentGL X).val = (1 : Matrix n n (DualNumber k)) + (DualNumber.eps : DualNumber k) • X.map (algebraMap k (DualNumber k)) := by
  apply Matrix.ext
  intro i j
  change (⟨(1 : Matrix n n k) i j, X i j⟩ : DualNumber k) =
    (1 : Matrix n n (DualNumber k)) i j +
      DualNumber.eps * (algebraMap k (DualNumber k)) (X i j)
  by_cases h : i = j
  · subst j
    simp only [Matrix.one_apply_eq]
    apply TrivSqZeroExt.ext
    · change (1 : k) = 1 + 0 * X i i
      ring
    · change X i i = 0 + (0*0 + 1*X i i)
      ring
  · simp only [Matrix.one_apply_ne h]
    apply TrivSqZeroExt.ext
    · change (0 : k) = 0 + 0 * X i j
      ring
    · change X i j = 0 + (0*0 + 1*X i j)
      ring

private theorem tangentGL_det (X : Matrix n n k) :
    Matrix.det (tangentGL X).val = (⟨1,Matrix.trace X⟩ : DualNumber k) := by
  rw [tangentGL_matrix, Matrix.det_one_add_smul, DualNumber.eps_pow_two, mul_zero, add_zero]
  rw [← AddMonoidHom.map_trace (algebraMap k (DualNumber k)) X]
  apply TrivSqZeroExt.ext
  · change (1 : k) + Matrix.trace X * 0 = 1
    ring
  · change (0 : k) + (Matrix.trace X * 1 + 0 * 0) = Matrix.trace X
    ring

private theorem tangentGL_det_one_iff (X : Matrix n n k) :
    Matrix.GeneralLinearGroup.det (R := DualNumber k) (n := n) (tangentGL X) = 1 ↔ Matrix.trace X = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun u : (DualNumber k)ˣ => u.val.snd) h
    change (Matrix.det (tangentGL X).val).snd = 0 at hh
    rw [tangentGL_det] at hh
    exact hh
  · intro h
    apply Units.ext
    change Matrix.det (tangentGL X).val = (1 : DualNumber k)
    rw [tangentGL_det,h]
    rfl

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices


namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices
open Matrix TrivSqZeroExt
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

private theorem tangentGL_map {R : Type} [CommRing R] [Algebra k R]
    (X : Matrix n n k) (u : R) (hu : u*u=0) :
    Matrix.GeneralLinearGroup.map ((DualNumber.lift ⟨(Algebra.ofId k _, u), hu, fun _ => Commute.all _ _⟩)).toRingHom (tangentGL X) =
      squareZeroUnit (X.map (algebraMap k R)) u hu := by
  apply Units.ext
  change Matrix.map (tangentGL X).val ((DualNumber.lift ⟨(Algebra.ofId k _, u), hu, fun _ => Commute.all _ _⟩)) =
    (1 : Matrix n n R) + u • X.map (algebraMap k R)
  rw [tangentGL_matrix]
  apply Matrix.ext
  intro i j
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, DualNumber.lift_apply_eps,
    Matrix.one_apply, Matrix.map_apply]

private theorem tangentGL_commutator {R : Type} [CommRing R] [Algebra k R]
    (X Y : Matrix n n k) (u v : R) (hu : u*u=0) (hv : v*v=0) :
    Matrix.GeneralLinearGroup.map ((DualNumber.lift ⟨(Algebra.ofId k _, u), hu, fun _ => Commute.all _ _⟩)).toRingHom (tangentGL X) *
      Matrix.GeneralLinearGroup.map ((DualNumber.lift ⟨(Algebra.ofId k _, v), hv, fun _ => Commute.all _ _⟩)).toRingHom (tangentGL Y) *
      (Matrix.GeneralLinearGroup.map ((DualNumber.lift ⟨(Algebra.ofId k _, u), hu, fun _ => Commute.all _ _⟩)).toRingHom (tangentGL X))⁻¹ *
      (Matrix.GeneralLinearGroup.map ((DualNumber.lift ⟨(Algebra.ofId k _, v), hv, fun _ => Commute.all _ _⟩)).toRingHom (tangentGL Y))⁻¹ =
      Matrix.GeneralLinearGroup.map ((DualNumber.lift ⟨(Algebra.ofId k _, (u*v)), (by rw [mul_mul_mul_comm,hu,zero_mul]), fun _ => Commute.all _ _⟩)).toRingHom (tangentGL (X*Y-Y*X)) := by
  rw [tangentGL_map X u hu, tangentGL_map Y v hv,
    tangentGL_map (X * Y - Y * X) (u * v) (by rw [mul_mul_mul_comm, hu, zero_mul])]
  rw [squareZeroUnit_commutator]
  congr 1
  simp only [← RingHom.mapMatrix_apply, map_sub, map_mul]

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.DualMatrices

set_option backward.isDefEq.respectTransparency.types true

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge
open TensorProduct TrivSqZeroExt LieAlgebra
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def pointsMap (G : LinearAlgebraicGroup ℂ) {R S : Type}
    [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S] (f : R →ₐ[ℂ] S) :
    G.points R →* G.points S :=
  ((Matrix.GeneralLinearGroup.map f.toRingHom).domRestrict (G.points R)).codRestrict
    (G.points S) (fun g => G.mapMem R S f g.val g.property)

private noncomputable def slTangent (X : SpecialLinear.sl (Fin 3) ℂ) : (slGroup 3).points (DualNumber ℂ) :=
  ⟨DualMatrices.tangentGL X.val, by
    change Matrix.GeneralLinearGroup.det (R := DualNumber ℂ) (n := Fin 3) (DualMatrices.tangentGL X.val) = 1
    exact (DualMatrices.tangentGL_det_one_iff X.val).2 X.property⟩

private theorem slTangent_reduce (X : SpecialLinear.sl (Fin 3) ℂ) :
    pointsMap (slGroup 3) (TrivSqZeroExt.fstHom ℂ ℂ ℂ) (slTangent X) = 1 := by
  exact OneMemClass.coe_eq_one.mp rfl

private theorem slTangent_add (X Y : SpecialLinear.sl (Fin 3) ℂ) :
    slTangent (X+Y) = slTangent X * slTangent Y := by
  apply Subtype.ext
  exact DualMatrices.tangentGL_add X.val Y.val

private theorem slTangent_scale (a : ℂ) (X : SpecialLinear.sl (Fin 3) ℂ) :
    pointsMap (slGroup 3) (TrivSqZeroExt.map (a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))) (slTangent X) =
      slTangent (a • X) := by
  apply Subtype.ext
  exact DualMatrices.tangentGL_scale a X.val

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem realizer_tangent_kernel (μ : V →ₗ[ℂ] V →ₗ[ℂ] V) (e : Realizes (slGroup 3) μ)
    (X : SpecialLinear.sl (Fin 3) ℂ) (v : V) :
    (Infinitesimal.coeffTensor (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toLinearMap) ((e.equiv (DualNumber ℂ) (slTangent X)).val (1 ⊗ₜ[ℂ] v)) = v := by
  let f := TrivSqZeroExt.fstHom ℂ ℂ ℂ
  have hn := e.naturality (DualNumber ℂ) ℂ f (slTangent X) (1 ⊗ₜ[ℂ] v)
  change (TensorProduct.map f.toLinearMap LinearMap.id) ((e.equiv (DualNumber ℂ) (slTangent X)).val (1 ⊗ₜ[ℂ] v)) =
    (e.equiv ℂ (pointsMap (slGroup 3) f (slTangent X))).val ((TensorProduct.map f.toLinearMap LinearMap.id) (1 ⊗ₜ[ℂ] v)) at hn
  rw [slTangent_reduce, map_one] at hn
  have hh := congrArg (TensorProduct.lid ℂ V) hn
  simpa [ Infinitesimal.coeffTensor,  f] using hh

private noncomputable def realizationDerivative (μ : V →ₗ[ℂ] V →ₗ[ℂ] V) (e : Realizes (slGroup 3) μ)
    (X : SpecialLinear.sl (Fin 3) ℂ) : derivations μ :=
  Infinitesimal.tangentDerivation μ (e.equiv (DualNumber ℂ) (slTangent X))
    (realizer_tangent_kernel μ e X)

private theorem realizationDerivative_expansion (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) (X : SpecialLinear.sl (Fin 3) ℂ) (v : V) :
    (e.equiv (DualNumber ℂ) (slTangent X)).val (1 ⊗ₜ[ℂ] v) =
      1 ⊗ₜ[ℂ] v + DualNumber.eps ⊗ₜ[ℂ] (realizationDerivative μ e X).val v := by
  exact Infinitesimal.tangentEnd_expansion _ (realizer_tangent_kernel μ e X) v

private theorem realizationDerivative_extension (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) (X : SpecialLinear.sl (Fin 3) ℂ)
    {R : Type} [CommRing R] [Algebra ℂ R] (f : DualNumber ℂ →ₐ[ℂ] R) :
    e.equiv R (pointsMap (slGroup 3) f (slTangent X)) =
      Infinitesimal.infinitesimalAut μ (realizationDerivative μ e X) R (f DualNumber.eps)
        (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  have hn := e.naturality (DualNumber ℂ) R f (slTangent X) (1 ⊗ₜ[ℂ] v)
  change (TensorProduct.map f.toLinearMap LinearMap.id) ((e.equiv (DualNumber ℂ) (slTangent X)).val (1 ⊗ₜ[ℂ] v)) =
    (e.equiv R (pointsMap (slGroup 3) f (slTangent X))).val
      ((TensorProduct.map f.toLinearMap LinearMap.id) (1 ⊗ₜ[ℂ] v)) at hn
  rw [realizationDerivative_expansion] at hn
  simp only [ map_add, TensorProduct.map_tmul, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, map_one] at hn
  have ha : a ⊗ₜ[ℂ] v = a • (1 ⊗ₜ[ℂ] v) := TensorProduct.tmul_eq_smul_one_tmul a v
  simp only [ha, map_smul]
  congr 1
  change (e.equiv R (pointsMap (slGroup 3) f (slTangent X))).val (1 ⊗ₜ[ℂ] v) =
    (Infinitesimal.infinitesimalAut μ (realizationDerivative μ e X) R
      (f DualNumber.eps) (by rw [← map_mul,DualNumber.eps_mul_eps,map_zero])).val (1 ⊗ₜ[ℂ] v)
  rw [Infinitesimal.infinitesimalAut_tmul,mul_one]
  exact hn.symm

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge


namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge
open TensorProduct TrivSqZeroExt LieAlgebra
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem derivative_reconstruction (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) (X : SpecialLinear.sl (Fin 3) ℂ) :
    Infinitesimal.infinitesimalAut μ (realizationDerivative μ e X) (DualNumber ℂ)
      DualNumber.eps DualNumber.eps_mul_eps = e.equiv (DualNumber ℂ) (slTangent X) := by
  exact Infinitesimal.infinitesimalAut_reconstruction μ _ (realizer_tangent_kernel μ e X)

private theorem realizationDerivative_add (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) (X Y : SpecialLinear.sl (Fin 3) ℂ) :
    realizationDerivative μ e (X+Y) = realizationDerivative μ e X + realizationDerivative μ e Y := by
  apply Infinitesimal.infinitesimalAut_injective μ
  dsimp only
  rw [Infinitesimal.infinitesimalAut_add, derivative_reconstruction,
    derivative_reconstruction, derivative_reconstruction, slTangent_add, map_mul]

private theorem realizationDerivative_smul (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) (a : ℂ) (X : SpecialLinear.sl (Fin 3) ℂ) :
    realizationDerivative μ e (a • X) = a • realizationDerivative μ e X := by
  apply Subtype.ext
  ext v
  change (realizationDerivative μ e (a • X)).val v = a • (realizationDerivative μ e X).val v
  let f := TrivSqZeroExt.map (a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  have hn := e.naturality (DualNumber ℂ) (DualNumber ℂ) f (slTangent X) (1 ⊗ₜ[ℂ] v)
  change (TensorProduct.map f.toLinearMap LinearMap.id) ((e.equiv (DualNumber ℂ) (slTangent X)).val (1 ⊗ₜ[ℂ] v)) =
    (e.equiv (DualNumber ℂ) (pointsMap (slGroup 3) f (slTangent X))).val
      ((TensorProduct.map f.toLinearMap LinearMap.id) (1 ⊗ₜ[ℂ] v)) at hn
  rw [slTangent_scale] at hn
  simp only [TensorProduct.map_tmul,AlgHom.toLinearMap_apply,
    LinearMap.id_apply,map_one] at hn
  rw [realizationDerivative_expansion,realizationDerivative_expansion] at hn
  have hh := congrArg (Infinitesimal.coeffTensor (TrivSqZeroExt.sndHom ℂ ℂ)) hn
  simpa only [map_add,TensorProduct.map_tmul,AlgHom.toLinearMap_apply,
    LinearMap.id_apply,map_one,Infinitesimal.secondTensor_tmul,
    TrivSqZeroExt.snd_one,DualNumber.snd_eps,zero_smul,one_smul,zero_add,
    f,TrivSqZeroExt.snd_map,LinearMap.smul_apply,smul_eq_mul,mul_one] using hh.symm

private noncomputable def derivativeLinear (μ : V →ₗ[ℂ] V →ₗ[ℂ] V) (e : Realizes (slGroup 3) μ) :
    SpecialLinear.sl (Fin 3) ℂ →ₗ[ℂ] derivations μ where
  toFun := realizationDerivative μ e
  map_add' := realizationDerivative_add μ e
  map_smul' := realizationDerivative_smul μ e

private theorem realizationDerivative_injective (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) : Function.Injective (realizationDerivative μ e) := by
  intro X Y h
  have hg : slTangent X = slTangent Y := by
    apply (e.equiv (DualNumber ℂ)).injective
    rw [← derivative_reconstruction, ← derivative_reconstruction, h]
  apply Subtype.ext
  apply DualMatrices.tangentGL_injective
  exact congrArg Subtype.val hg

private theorem realizationDerivative_surjective (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) : Function.Surjective (realizationDerivative μ e) := by
  intro D
  let α := Infinitesimal.infinitesimalAut μ D (DualNumber ℂ) DualNumber.eps DualNumber.eps_mul_eps
  let g := (e.equiv (DualNumber ℂ)).symm α
  have hg : pointsMap (slGroup 3) (TrivSqZeroExt.fstHom ℂ ℂ ℂ) g = 1 := by
    apply (e.equiv ℂ).injective
    rw [map_one]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    have hn := e.naturality (DualNumber ℂ) ℂ (TrivSqZeroExt.fstHom ℂ ℂ ℂ) g (1 ⊗ₜ[ℂ] v)
    change (TensorProduct.map (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toLinearMap LinearMap.id) ((e.equiv (DualNumber ℂ) g).val (1 ⊗ₜ[ℂ] v)) =
      (e.equiv ℂ (pointsMap (slGroup 3) (TrivSqZeroExt.fstHom ℂ ℂ ℂ) g)).val
        ((TensorProduct.map (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toLinearMap LinearMap.id) (1 ⊗ₜ[ℂ] v)) at hn
    have he : e.equiv (DualNumber ℂ) g = α := (e.equiv (DualNumber ℂ)).apply_symm_apply α
    rw [he] at hn
    simp only [α, Infinitesimal.infinitesimalAut_tmul, mul_one,  map_add,
      TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      map_one, TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps,
      TensorProduct.zero_tmul, add_zero] at hn
    have ha : a ⊗ₜ[ℂ] v = a • (1 ⊗ₜ[ℂ] v) := TensorProduct.tmul_eq_smul_one_tmul a v
    simp only [ha, map_smul]
    exact congrArg (fun x => a • x) hn.symm
  have hg' : Matrix.GeneralLinearGroup.map (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom g.val = 1 :=
    congrArg Subtype.val hg
  let X : Matrix (Fin 3) (Fin 3) ℂ := fun i j => (g.val.val i j).snd
  have hX : DualMatrices.tangentGL X = g.val := DualMatrices.tangentGL_surj_kernel g.val hg'
  have htrace : Matrix.trace X = 0 := by
    exact (DualMatrices.tangentGL_det_one_iff X).1 (by rw [hX]; exact g.property)
  let Z : SpecialLinear.sl (Fin 3) ℂ := ⟨X,htrace⟩
  have hZ : slTangent Z = g := Subtype.ext hX
  refine ⟨Z,?_⟩
  apply Infinitesimal.infinitesimalAut_injective μ
  dsimp only
  rw [derivative_reconstruction, hZ]
  exact (e.equiv (DualNumber ℂ)).apply_symm_apply α

private noncomputable def derivativeEquiv (μ : V →ₗ[ℂ] V →ₗ[ℂ] V) (e : Realizes (slGroup 3) μ) :
    SpecialLinear.sl (Fin 3) ℂ ≃ₗ[ℂ] derivations μ :=
  LinearEquiv.ofBijective (derivativeLinear μ e)
    ⟨realizationDerivative_injective μ e, realizationDerivative_surjective μ e⟩

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge


namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal
open TensorProduct TrivSqZeroExt
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

private theorem infinitesimalAut_commutator (μ : V →ₗ[k] V →ₗ[k] V)
    (D E : derivations μ) (R : Type) [CommRing R] [Algebra k R]
    (u v : R) (hu : u*u=0) (hv : v*v=0) :
    infinitesimalAut μ D R u hu * infinitesimalAut μ E R v hv *
      (infinitesimalAut μ D R u hu)⁻¹ * (infinitesimalAut μ E R v hv)⁻¹ =
    infinitesimalAut μ ⁅D,E⁆ R (u*v)
      (by rw [mul_mul_mul_comm,hu,zero_mul]) := by
  apply Subtype.ext
  change squareZeroEquiv (D.val.baseChange R) u hu * squareZeroEquiv (E.val.baseChange R) v hv *
    (squareZeroEquiv (D.val.baseChange R) u hu)⁻¹ *
    (squareZeroEquiv (E.val.baseChange R) v hv)⁻¹ =
    squareZeroEquiv ((⁅D,E⁆ : derivations μ).val.baseChange R) (u*v)
      (by rw [mul_mul_mul_comm,hu,zero_mul])
  rw [squareZeroEquiv_commutator]
  congr 1
  change D.val.baseChange R * E.val.baseChange R - E.val.baseChange R * D.val.baseChange R =
    (D.val*E.val-E.val*D.val).baseChange R
  simp only [LinearMap.baseChange_sub,LinearMap.baseChange_mul]

private theorem innerEps_sq : ((TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) : DualNumber (DualNumber k))) * TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) = 0 := by
  change (TrivSqZeroExt.inlHom (DualNumber k) (DualNumber k)) (DualNumber.eps : DualNumber k) *
    (TrivSqZeroExt.inlHom (DualNumber k) (DualNumber k)) (DualNumber.eps : DualNumber k) = 0
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
private theorem mixedEps_sq :
    (((TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) : DualNumber (DualNumber k)) * (DualNumber.eps : DualNumber (DualNumber k))) : DualNumber (DualNumber k)) *
      (((TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) : DualNumber (DualNumber k)) * (DualNumber.eps : DualNumber (DualNumber k))) : DualNumber (DualNumber k)) = 0 := by
  have h := mul_mul_mul_comm ((TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) : DualNumber (DualNumber k))) ((DualNumber.eps : DualNumber (DualNumber k)))
    ((TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) : DualNumber (DualNumber k))) ((DualNumber.eps : DualNumber (DualNumber k)))
  rw [innerEps_sq (k := k),zero_mul] at h
  exact h

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem mixedAut_injective (μ : V →ₗ[k] V →ₗ[k] V) :
    Function.Injective (fun D : derivations μ => infinitesimalAut μ D (DualNumber (DualNumber k))
      (TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) * (DualNumber.eps : DualNumber (DualNumber k))) mixedEps_sq) := by
  intro D E h
  apply Subtype.ext
  ext v
  have hh := congrArg (fun α : (automorphisms (LinearMap.BilinMap.baseChange (DualNumber (DualNumber k)) μ)) =>
    coeffTensor (R := DualNumber (DualNumber k)) ((LinearMap.snd k k k).comp (LinearMap.snd k (DualNumber k) (DualNumber k))) (α.val (1 ⊗ₜ[k] v))) h
  simp only [infinitesimalAut_tmul, mul_one, map_add, coeffTensor_tmul] at hh
  change (1 : DualNumber (DualNumber k)).snd.snd • v +
      (TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) *
        (DualNumber.eps : DualNumber (DualNumber k))).snd.snd • D.val v =
    (1 : DualNumber (DualNumber k)).snd.snd • v +
      (TrivSqZeroExt.inl (DualNumber.eps : DualNumber k) *
        (DualNumber.eps : DualNumber (DualNumber k))).snd.snd • E.val v at hh
  simpa only [TrivSqZeroExt.snd_one, DualNumber.snd_mul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps,
    DualNumber.snd_eps, mul_one, zero_mul, add_zero,
    TrivSqZeroExt.snd_zero, zero_smul, one_smul, zero_add] using hh
end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge.Infinitesimal

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge
open TensorProduct TrivSqZeroExt LieAlgebra
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem slTangent_commutator {R : Type} [CommRing R] [Algebra ℂ R]
    (X Y : SpecialLinear.sl (Fin 3) ℂ) (u v : R) (hu : u*u=0) (hv : v*v=0) :
    pointsMap (slGroup 3) ((DualNumber.lift ⟨(Algebra.ofId ℂ _, u), hu, fun _ => Commute.all _ _⟩)) (slTangent X) *
      pointsMap (slGroup 3) ((DualNumber.lift ⟨(Algebra.ofId ℂ _, v), hv, fun _ => Commute.all _ _⟩)) (slTangent Y) *
      (pointsMap (slGroup 3) ((DualNumber.lift ⟨(Algebra.ofId ℂ _, u), hu, fun _ => Commute.all _ _⟩)) (slTangent X))⁻¹ *
      (pointsMap (slGroup 3) ((DualNumber.lift ⟨(Algebra.ofId ℂ _, v), hv, fun _ => Commute.all _ _⟩)) (slTangent Y))⁻¹ =
      pointsMap (slGroup 3) ((DualNumber.lift ⟨(Algebra.ofId ℂ _, (u*v)), (by rw [mul_mul_mul_comm,hu,zero_mul]), fun _ => Commute.all _ _⟩)) (slTangent ⁅X,Y⁆) := by
  apply Subtype.ext
  exact DualMatrices.tangentGL_commutator X.val Y.val u v hu hv

private theorem realizationDerivative_lie (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) (X Y : SpecialLinear.sl (Fin 3) ℂ) :
    realizationDerivative μ e ⁅X,Y⁆ = ⁅realizationDerivative μ e X,realizationDerivative μ e Y⁆ := by
  apply Infinitesimal.mixedAut_injective μ
  dsimp only
  let u := (TrivSqZeroExt.inl (DualNumber.eps : DualNumber ℂ) : DualNumber (DualNumber ℂ))
  let v := (DualNumber.eps : DualNumber (DualNumber ℂ))
  have h := congrArg (e.equiv (DualNumber (DualNumber ℂ)))
    (slTangent_commutator X Y u v Infinitesimal.innerEps_sq DualNumber.eps_mul_eps)
  simp only [map_mul,map_inv,realizationDerivative_extension,DualNumber.lift_apply_eps] at h
  rw [Infinitesimal.infinitesimalAut_commutator] at h
  exact h.symm

private noncomputable def derivativeLieEquiv (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) : SpecialLinear.sl (Fin 3) ℂ ≃ₗ⁅ℂ⁆ derivations μ :=
  { derivativeEquiv μ e with map_lie' := by intro X Y; exact realizationDerivative_lie μ e X Y }

/-- A full natural realization of SL₃ induces an isomorphism of tangent Lie algebras. -/
theorem tangent_lie_equivalence (μ : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (e : Realizes (slGroup 3) μ) :
    Nonempty (SpecialLinear.sl (Fin 3) ℂ ≃ₗ⁅ℂ⁆ derivations μ) :=
  ⟨derivativeLieEquiv μ e⟩

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismTangentBridge
