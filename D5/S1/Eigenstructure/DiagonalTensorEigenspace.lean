/- GID: D5/S1/Eigenstructure/DiagonalTensorEigenspace
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/DiagonalTensorEigenspace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis, mathlib/module/Mathlib.LinearAlgebra.Finsupp.Supported]
   utility: none
   digest: A diagonal tensor endomorphism has its full eigenspace parametrized by supported ground-valued coefficients. -/

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S1.Eigenstructure.DiagonalTensorEigenspace

open scoped TensorProduct
noncomputable section

variable {K I M T Q : Type*} [Field K]
variable [AddCommGroup M] [Module K M] [AddCommGroup T] [Module K T]

/-- Tensor coefficients in the given algebraic basis, supplied by Mathlib. -/
def coeffEquiv (b : Module.Basis I K M) : M ⊗[K] T ≃ₗ[K] (I →₀ T) := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft b

/-- The tensor operator acts diagonally on every vector's
    vector-valued coefficients, including nonhomogeneous vectors. -/
theorem coeff_action (b : Module.Basis I K M) (A : Module.End K M)
    (a : I → K) (hA : ∀ i, A (b i) = a i • b i)
    (v : M ⊗[K] T) (i : I) :
    coeffEquiv b (TensorProduct.map A (LinearMap.id : Module.End K T) v) i =
      a i • coeffEquiv b v i := by
  classical
  have hc : (b.coord i).comp A = a i • b.coord i := by
    apply b.ext
    intro j
    change b.repr (A (b j)) i = a i * b.repr (b j) i
    rw [hA, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, b.repr_self]
    by_cases h : j = i
    · subst j
      rfl
    · simp [Finsupp.single_apply, h]
  have hci (m : M) : b.repr (A m) i = a i * b.repr m i :=
    LinearMap.congr_fun hc m
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul m t =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, coeffEquiv,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rw [hci, mul_smul]
  | add v w hv hw =>
      simp only [map_add, Finsupp.add_apply, hv, hw, smul_add]

/-- Coefficient separation identifies the full eigenspace, not just
    a span of known eigenvectors. The ground module may even be zero. -/
theorem eigen_iff_supported (b : Module.Basis I K M) (A : Module.End K M)
    (a : I → K) (hA : ∀ i, A (b i) = a i • b i)
    (mu : K) (v : M ⊗[K] T) :
    TensorProduct.map A (LinearMap.id : Module.End K T) v = mu • v ↔
      coeffEquiv b v ∈ Finsupp.supported T K {i : I | a i = mu} := by
  classical
  constructor
  · intro hv
    rw [Finsupp.mem_supported']
    intro i hi
    have h := congrArg (fun w : M ⊗[K] T => coeffEquiv b w i) hv
    rw [coeff_action b A a hA] at h
    simp only [map_smul, Finsupp.smul_apply] at h
    have hz : (a i - mu) • coeffEquiv b v i = 0 := by
      rw [sub_smul, h, sub_self]
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hi)
  · intro hv
    apply (coeffEquiv b).injective
    ext i
    rw [coeff_action b A a hA]
    simp only [map_smul, Finsupp.smul_apply]
    by_cases hi : a i = mu
    · rw [hi]
    · have hz := (Finsupp.mem_supported' K (coeffEquiv b v)).mp hv i hi
      rw [hz, smul_zero, smul_zero]

/-- An injectively labelled diagonal tensor eigenspace is
    exactly one ground-module copy for each element of the degree fiber. -/
def gradedEigenspaceEquiv (b : Module.Basis I K M) (A : Module.End K M)
    (degree : I → Q) (value : Q → K) (hinj : Function.Injective value)
    (hA : ∀ i, A (b i) = value (degree i) • b i) (q : Q) :
    Module.End.eigenspace (TensorProduct.map A (LinearMap.id : Module.End K T)) (value q) ≃ₗ[K]
      ({i : I // degree i = q} →₀ T) := by
  classical
  let s : Set I := {i : I | degree i = q}
  have heq :
      Module.End.eigenspace (TensorProduct.map A (LinearMap.id : Module.End K T)) (value q) =
        (Finsupp.supported T K s).comap (coeffEquiv b).toLinearMap := by
    ext v
    rw [Module.End.mem_eigenspace_iff]
    change TensorProduct.map A (LinearMap.id : Module.End K T) v = value q • v ↔
      coeffEquiv b v ∈ Finsupp.supported T K s
    have hs : {i : I | value (degree i) = value q} = s := by
      ext i
      constructor
      · intro hi
        exact hinj hi
      · intro hi
        exact congrArg value hi
    rw [← hs]
    exact eigen_iff_supported b A (fun i => value (degree i)) hA (value q) v
  exact (LinearEquiv.ofEq _ _ heq).trans
    ((LinearEquiv.ofSubmodule' (coeffEquiv b) (Finsupp.supported T K s)).trans
      (Finsupp.supportedEquivFinsupp s))


end
end D5.S1.Eigenstructure.DiagonalTensorEigenspace
