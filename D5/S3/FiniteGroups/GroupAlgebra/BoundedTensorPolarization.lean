/- GID: D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis]
   utility: none
   digest: Bounded polynomial tensor multiplication, difference injection and polarization. -/

import D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Bounded polynomial tensor multiplication, difference injection and polarization.
These constructions are helpers on the route to the corrected relative-stable criterion.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization

open Polynomial
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

/-- Primal polynomials of degree at most n. -/
abbrev Trunc (R : Type u) [CommRing R] (n : ℕ) := Polynomial.degreeLT R (n + 1)

def tensorBasis (n m : ℕ) :
    Module.Basis (Fin (n + 1) × Fin (m + 1)) R (Trunc R n ⊗[R] Trunc R m) :=
  (Polynomial.degreeLT.basis R (n + 1)).tensorProduct
    (Polynomial.degreeLT.basis R (m + 1))

/-- Actual diagonal/multiplication map, given on every tensor monomial. -/
def multiplication (n m : ℕ) : Trunc R n ⊗[R] Trunc R m →ₗ[R] Trunc R (n + m) :=
  (tensorBasis (R := R) n m).constr R fun ij =>
    Polynomial.degreeLT.basis R (n + m + 1)
      ⟨(ij.1 : ℕ) + (ij.2 : ℕ), by have := ij.1.is_lt; have := ij.2.is_lt; omega⟩

@[simp] theorem multiplication_basis (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    multiplication (R := R) n m
      (Polynomial.degreeLT.basis R (n + 1) i ⊗ₜ[R]
        Polynomial.degreeLT.basis R (m + 1) j) =
      Polynomial.degreeLT.basis R (n + m + 1)
        ⟨(i : ℕ) + (j : ℕ), by have := i.is_lt; have := j.is_lt; omega⟩ := by
  simpa only [multiplication, tensorBasis, Module.Basis.tensorProduct_apply] using
    ((tensorBasis (R := R) n m).constr_basis R
      (fun ij => Polynomial.degreeLT.basis R (n + m + 1)
        ⟨(ij.1 : ℕ) + (ij.2 : ℕ), by have := ij.1.is_lt; have := ij.2.is_lt; omega⟩)
      (i, j))

/-- Ambient realization with z₁ corresponding to the FIRST tensor factor. -/
def tensorPolynomial (n m : ℕ) : Trunc R n ⊗[R] Trunc R m →ₗ[R] Bi R :=
  (tensorBasis (R := R) n m).constr R fun ij =>
    z₁ ^ (ij.1 : ℕ) * z₂ ^ (ij.2 : ℕ)

@[simp] theorem tensorPolynomial_basis (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    tensorPolynomial (R := R) n m
      (Polynomial.degreeLT.basis R (n + 1) i ⊗ₜ[R]
        Polynomial.degreeLT.basis R (m + 1) j) =
      z₁ ^ (i : ℕ) * z₂ ^ (j : ℕ) := by
  simpa only [tensorPolynomial, tensorBasis, Module.Basis.tensorProduct_apply] using
    ((tensorBasis (R := R) n m).constr_basis R
      (fun ij => z₁ ^ (ij.1 : ℕ) * z₂ ^ (ij.2 : ℕ)) (i, j))

/-- The bounded map really agrees with ambient diagonal substitution. -/
theorem diagonal_tensorPolynomial (n m : ℕ) :
    (diagonalLinear (R := R)).comp (tensorPolynomial n m) =
      (Polynomial.degreeLT R (n + m + 1)).subtype.comp (multiplication n m) := by
  apply (tensorBasis (R := R) n m).ext
  intro ij
  rcases ij with ⟨i, j⟩
  simp only [tensorBasis, Module.Basis.tensorProduct_apply, LinearMap.comp_apply,
    tensorPolynomial_basis, multiplication_basis, Submodule.subtype_apply,
    Polynomial.degreeLT.basis_val]
  change diagonal (z₁ ^ (i : ℕ) * z₂ ^ (j : ℕ)) = (X : R[X]) ^ ((i : ℕ) + (j : ℕ))
  rw [map_mul, map_pow, map_pow, diagonal_z₁, diagonal_z₂, pow_add]

/-- Choose the left exponent as min(k,n); the right exponent then fits in m. -/
def leftIndex (n m : ℕ) (k : Fin (n + m + 1)) : Fin (n + 1) :=
  ⟨min (k : ℕ) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def rightIndex (n m : ℕ) (k : Fin (n + m + 1)) : Fin (m + 1) :=
  ⟨(k : ℕ) - min (k : ℕ) n, by
    have hk := k.is_lt
    by_cases hkn : (k : ℕ) ≤ n
    · rw [Nat.min_eq_left hkn]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega⟩

/-- A linear lift used only for surjectivity. It has no claimed group symmetry. -/
def monomialLift (n m : ℕ) : Trunc R (n + m) →ₗ[R] Trunc R n ⊗[R] Trunc R m :=
  (Polynomial.degreeLT.basis R (n + m + 1)).constr R fun k =>
    Polynomial.degreeLT.basis R (n + 1) (leftIndex n m k) ⊗ₜ[R]
      Polynomial.degreeLT.basis R (m + 1) (rightIndex n m k)

theorem multiplication_monomialLift (n m : ℕ) :
    (multiplication (R := R) n m).comp (monomialLift n m) = LinearMap.id := by
  apply (Polynomial.degreeLT.basis R (n + m + 1)).ext
  intro k
  simp only [LinearMap.comp_apply, monomialLift, Module.Basis.constr_basis,
    multiplication_basis, LinearMap.id_apply]
  congr 1
  apply Fin.ext
  exact Nat.add_sub_of_le (Nat.min_le_left (k : ℕ) n)

theorem multiplication_surjective (n m : ℕ) :
    Function.Surjective (multiplication (R := R) n m) := by
  intro f
  refine ⟨monomialLift n m f, ?_⟩
  exact LinearMap.congr_fun (multiplication_monomialLift (R := R) n m) f

/-- Successor indexing avoids the n-1,m-1 boundary cases: this is d for the
original bounds n+1,m+1. Its source has dimension (n+1)(m+1). -/
def differenceTensor (n m : ℕ) :
    Trunc R n ⊗[R] Trunc R m →ₗ[R] Trunc R (n + 1) ⊗[R] Trunc R (m + 1) :=
  (tensorBasis (R := R) n m).constr R fun ij =>
    (Polynomial.degreeLT.basis R (n + 2) ij.1.succ ⊗ₜ[R]
      Polynomial.degreeLT.basis R (m + 2) ij.2.castSucc) -
    (Polynomial.degreeLT.basis R (n + 2) ij.1.castSucc ⊗ₜ[R]
      Polynomial.degreeLT.basis R (m + 2) ij.2.succ)

/-- Actual simultaneous translation on the bounded tensor factors. -/
def tensorTranslate (a : R) (n m : ℕ) :
    Trunc R n ⊗[R] Trunc R m →ₗ[R] Trunc R n ⊗[R] Trunc R m :=
  TensorProduct.map
    (Polynomial.taylorLinearEquiv a (n + 1)).toLinearMap
    (Polynomial.taylorLinearEquiv a (m + 1)).toLinearMap

/-- The two nested coefficient extractions used to recover a tensor coordinate. -/
def nestedCoeff (i j : ℕ) : Bi R →ₗ[R] R :=
  (Polynomial.lcoeff R j).comp ((Polynomial.lcoeff (R[X]) i).restrictScalars R)

theorem tensorPolynomial_injective (n m : ℕ) :
    Function.Injective (tensorPolynomial (R := R) n m) := by
  intro F G hFG
  apply (tensorBasis (R := R) n m).ext_elem_iff.mpr
  intro ij
  rcases ij with ⟨i, j⟩
  have hcoord :
      (Finsupp.lapply (i, j) :
          ((Fin (n + 1) × Fin (m + 1)) →₀ R) →ₗ[R] R).comp
          (tensorBasis (R := R) n m).repr.toLinearMap =
        (nestedCoeff (R := R) (i : ℕ) (j : ℕ)).comp
          (tensorPolynomial (R := R) n m) := by
    apply (tensorBasis (R := R) n m).ext
    intro kl
    rcases kl with ⟨k, l⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      tensorBasis, Module.Basis.tensorProduct_apply, tensorPolynomial_basis]
    by_cases hik : i = k
    · by_cases hjl : j = l
      · subst k
        subst l
        simp [nestedCoeff, z₁, z₂, Polynomial.coeff_mul_C,
          Polynomial.coeff_X_pow, ← Polynomial.C_pow, -map_pow]
      · have hnat : (j : ℕ) ≠ (l : ℕ) := by
          intro h
          exact hjl (Fin.ext h)
        simp [nestedCoeff, z₁, z₂, Polynomial.coeff_mul_C,
          Polynomial.coeff_X_pow, ← Polynomial.C_pow, -map_pow, hnat, hik, hjl]
    · have hnat : (i : ℕ) ≠ (k : ℕ) := by
        intro h
        exact hik (Fin.ext h)
      simp [nestedCoeff, z₁, z₂, Polynomial.coeff_mul_C,
        Polynomial.coeff_X_pow, ← Polynomial.C_pow, -map_pow, hnat, hik]
  have hcoordF := LinearMap.congr_fun hcoord F
  have hcoordG := LinearMap.congr_fun hcoord G
  calc
    (tensorBasis (R := R) n m).repr F (i, j) =
        nestedCoeff (R := R) (i : ℕ) (j : ℕ)
          (tensorPolynomial (R := R) n m F) := hcoordF
    _ = nestedCoeff (R := R) (i : ℕ) (j : ℕ)
          (tensorPolynomial (R := R) n m G) := by rw [hFG]
    _ = (tensorBasis (R := R) n m).repr G (i, j) := hcoordG.symm

theorem tensorPolynomial_difference (n m : ℕ)
    (F : Trunc R n ⊗[R] Trunc R m) :
    tensorPolynomial (R := R) (n + 1) (m + 1) (differenceTensor n m F) =
      difference * tensorPolynomial (R := R) n m F := by
  have hmap :
      (tensorPolynomial (R := R) (n + 1) (m + 1)).comp
          (differenceTensor n m) =
        (LinearMap.mulLeft R difference).comp
          (tensorPolynomial (R := R) n m) := by
    apply (tensorBasis (R := R) n m).ext
    intro ij
    rcases ij with ⟨i, j⟩
    rw [LinearMap.comp_apply, differenceTensor, Module.Basis.constr_basis]
    simp only [map_sub, tensorBasis, Module.Basis.tensorProduct_apply,
      tensorPolynomial_basis, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    change z₁ ^ ((i : ℕ) + 1) * z₂ ^ (j : ℕ) -
        z₁ ^ (i : ℕ) * z₂ ^ ((j : ℕ) + 1) =
      difference * (z₁ ^ (i : ℕ) * z₂ ^ (j : ℕ))
    rw [pow_succ, pow_succ]
    dsimp [difference]
    ring
  exact LinearMap.congr_fun hmap F

theorem differenceTensor_injective (n m : ℕ) :
    Function.Injective (differenceTensor (R := R) n m) := by
  intro F G hFG
  apply tensorPolynomial_injective (R := R) n m
  apply difference_mul_injective (R := R)
  simpa only [tensorPolynomial_difference (R := R) n m] using
    congrArg (tensorPolynomial (R := R) (n + 1) (m + 1)) hFG

theorem multiplication_differenceTensor (n m : ℕ) :
    (multiplication (R := R) (n + 1) (m + 1)).comp (differenceTensor n m) = 0 := by
  apply LinearMap.ext
  intro F
  apply Submodule.injective_subtype
  have hdiag :=
    LinearMap.congr_fun (diagonal_tensorPolynomial (R := R) (n + 1) (m + 1))
      (differenceTensor (R := R) n m F)
  change ((multiplication (R := R) (n + 1) (m + 1))
    (differenceTensor n m F) : R[X]) = 0
  change diagonal (tensorPolynomial (n + 1) (m + 1) (differenceTensor n m F)) =
    ((multiplication (R := R) (n + 1) (m + 1)) (differenceTensor n m F) : R[X]) at hdiag
  rw [← hdiag, tensorPolynomial_difference (R := R) n m]
  change diagonal (difference * tensorPolynomial (R := R) n m F) = 0
  rw [map_mul]
  simp [difference]

theorem differenceTensor_range {K : Type u} [Field K] (n m : ℕ) :
    LinearMap.range (differenceTensor (R := K) n m) =
      LinearMap.ker (multiplication (R := K) (n + 1) (m + 1)) := by
  letI : Module.Finite K
      (Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) :=
    Module.Finite.of_basis (tensorBasis (R := K) (n + 1) (m + 1))
  letI : Module.Finite K (Trunc K n ⊗[K] Trunc K m) :=
    Module.Finite.of_basis (tensorBasis (R := K) n m)
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro y ⟨F, rfl⟩
    change multiplication (R := K) (n + 1) (m + 1)
        (differenceTensor (R := K) n m F) = 0
    exact LinearMap.congr_fun
      (multiplication_differenceTensor (R := K) n m) F
  · have hdegree (q : ℕ) : Module.finrank K (Trunc K q) = q + 1 := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K (q + 1))]
      simp
    have hsource :
        Module.finrank K (Trunc K n ⊗[K] Trunc K m) = (n + 1) * (m + 1) := by
      rw [Module.finrank_tensorProduct, hdegree, hdegree]
    have hker :
        Module.finrank K
            (LinearMap.ker (multiplication (R := K) (n + 1) (m + 1))) =
          (n + 1) * (m + 1) := by
      have hnull :=
        (multiplication (R := K) (n + 1) (m + 1)).finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr
          (multiplication_surjective (R := K) (n + 1) (m + 1)),
        finrank_top] at hnull
      simp only [hdegree, Module.finrank_tensorProduct] at hnull
      ring_nf at hnull ⊢
      omega
    rw [LinearMap.finrank_range_of_inj
      (differenceTensor_injective (R := K) n m), hsource, hker]

/-- The first factor uses the outer variable; the second uses the inner one. -/
theorem tensorPolynomial_tmul (n m : ℕ) (f : Trunc R n) (g : Trunc R m) :
    tensorPolynomial n m (f ⊗ₜ[R] g) = (f.val.map C) * C g.val := by
  let L : Trunc R n →ₗ[R] Bi R :=
    (Polynomial.mapAlgHom (Polynomial.CAlgHom (R := R) (A := R))).toLinearMap.comp
      (Polynomial.degreeLT R (n + 1)).subtype
  let Q : Trunc R m →ₗ[R] Bi R :=
    (Polynomial.CAlgHom (R := R) (A := R[X])).toLinearMap.comp
      (Polynomial.degreeLT R (m + 1)).subtype
  have h : tensorPolynomial (R := R) n m =
      (LinearMap.mul' R (Bi R)).comp (TensorProduct.map L Q) := by
    apply (tensorBasis (R := R) n m).ext
    rintro ⟨i, j⟩
    simp [tensorBasis, tensorPolynomial_basis, L, Q, z₁, z₂]
  rw [h]
  simp [L, Q]
  rfl

/-- Bounded tensor translation realizes actual simultaneous polynomial substitution. -/
theorem tensorPolynomial_translate (a : R) (n m : ℕ)
    (F : Trunc R n ⊗[R] Trunc R m) :
    tensorPolynomial n m (tensorTranslate a n m F) =
      translate a (tensorPolynomial n m F) := by
  have h : (tensorPolynomial (R := R) n m).comp (tensorTranslate a n m) =
      (translateLinear a).comp (tensorPolynomial n m) := by
    apply (tensorBasis (R := R) n m).ext
    rintro ⟨i, j⟩
    simp only [LinearMap.comp_apply, tensorBasis, Module.Basis.tensorProduct_apply,
      tensorTranslate, TensorProduct.map_tmul, LinearEquiv.coe_coe, tensorPolynomial_tmul]
    change ((Polynomial.taylor a _).map C) * C (Polynomial.taylor a _) =
      translate a ((_ : R[X]).map C * C (_ : R[X]))
    rw [map_mul, translate_map_C, translate_C]
    rfl
  exact LinearMap.congr_fun h F

theorem tensorTranslate_differenceTensor (a : R) (n m : ℕ) :
    (tensorTranslate a (n + 1) (m + 1)).comp (differenceTensor (R := R) n m) =
      (differenceTensor n m).comp (tensorTranslate a n m) := by
  apply LinearMap.ext
  intro F
  apply tensorPolynomial_injective (R := R) (n + 1) (m + 1)
  simp only [LinearMap.comp_apply, tensorPolynomial_translate,
    tensorPolynomial_difference, translate_difference_mul]

/-- Every term carries both rectangular inequalities in its tensor indices. -/
def boundedPolarMonomial (n m : ℕ) (k : Fin (n + m + 1)) :
    Trunc R n ⊗[R] Trunc R m :=
  ∑ i : Fin (k.val + 1),
    if h : i.val ≤ n ∧ k.val - i.val ≤ m then
      (((n + m - k.val).choose (n - i.val) : R) * (k.val.choose i.val : R)) •
        (Polynomial.degreeLT.basis R (n + 1) ⟨i.val, by omega⟩ ⊗ₜ[R]
          Polynomial.degreeLT.basis R (m + 1) ⟨k.val - i.val, by omega⟩)
    else 0

theorem tensorPolynomial_boundedPolarMonomial (n m : ℕ) (k : Fin (n + m + 1)) :
    tensorPolynomial n m (boundedPolarMonomial (R := R) n m k) =
      polarMonomial (n + m) n k.val := by
  rw [boundedPolarMonomial, map_sum, polarMonomial,
    polarCoeff_box n m k.val (Nat.le_of_lt_succ k.is_lt), ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with h
  · rw [map_smul, tensorPolynomial_basis]
    simp only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, map_mul, ← Polynomial.C_eq_natCast]
    ring
  · exact map_zero _

theorem polarMonomial_in_tensor_range (n m k : ℕ) (hk : k ≤ n + m) :
    polarMonomial (R := R) (n + m) n k ∈ LinearMap.range (tensorPolynomial n m) :=
  ⟨boundedPolarMonomial n m ⟨k, by omega⟩,
    tensorPolynomial_boundedPolarMonomial n m ⟨k, by omega⟩⟩

/-- Denominator-free polarization into the actual bounded tensor factors. -/
def boundedPolarization (n m : ℕ) :
    Trunc R (n + m) →ₗ[R] Trunc R n ⊗[R] Trunc R m :=
  (Polynomial.degreeLT.basis R (n + m + 1)).constr R (boundedPolarMonomial n m)

theorem tensorPolynomial_boundedPolarization (n m : ℕ) :
    (tensorPolynomial (R := R) n m).comp (boundedPolarization n m) =
      polarization (n + m) n := by
  apply (Polynomial.degreeLT.basis R (n + m + 1)).ext
  intro k
  simp only [LinearMap.comp_apply, boundedPolarization, Module.Basis.constr_basis,
    polarization_basis, tensorPolynomial_boundedPolarMonomial]

theorem multiplication_boundedPolarization (n m : ℕ) :
    (multiplication (R := R) n m).comp (boundedPolarization n m) =
      ((n + m).choose n : R) • LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  have h := LinearMap.congr_fun (diagonal_polarization (R := R) (n + m) n) f
  have hr := LinearMap.congr_fun (tensorPolynomial_boundedPolarization (R := R) n m) f
  have hd := LinearMap.congr_fun (diagonal_tensorPolynomial (R := R) n m)
    (boundedPolarization n m f)
  change diagonal (tensorPolynomial n m (boundedPolarization n m f)) =
    ((multiplication n m (boundedPolarization n m f)) : R[X]) at hd
  change ((multiplication n m (boundedPolarization n m f)) : R[X]) =
    ((n + m).choose n : R) • f.val
  rw [← hd]
  change tensorPolynomial n m (boundedPolarization n m f) = _ at hr
  rw [hr]
  exact h

theorem boundedPolarization_translate (a : R) (n m : ℕ) :
    (tensorTranslate a n m).comp (boundedPolarization (R := R) n m) =
      (boundedPolarization n m).comp
        (Polynomial.taylorLinearEquiv a (n + m + 1)).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply tensorPolynomial_injective (R := R) n m
  simp only [LinearMap.comp_apply]
  rw [tensorPolynomial_translate]
  have hr := tensorPolynomial_boundedPolarization (R := R) n m
  change translate a (((tensorPolynomial n m).comp (boundedPolarization n m)) f) =
    ((tensorPolynomial n m).comp (boundedPolarization n m))
      ((Polynomial.taylorLinearEquiv a (n + m + 1)) f)
  rw [hr]
  exact LinearMap.congr_fun (polarization_translate a (n + m) n) f

/-- Invert only a scalar proved nonzero to obtain an actual equivariant section. -/
theorem equivariant_section {K : Type u} [Field K] (n m : ℕ)
    (hbinom : ((n + m).choose n : K) ≠ 0) :
    ∃ σ : Trunc K (n + m) →ₗ[K] Trunc K n ⊗[K] Trunc K m,
      (multiplication n m).comp σ = LinearMap.id ∧
        ∀ a : K, (tensorTranslate a n m).comp σ =
          σ.comp (Polynomial.taylorLinearEquiv a (n + m + 1)).toLinearMap := by
  refine ⟨((n + m).choose n : K)⁻¹ • boundedPolarization n m, ?_, ?_⟩
  · rw [LinearMap.comp_smul, multiplication_boundedPolarization, smul_smul,
      inv_mul_cancel₀ hbinom, one_smul]
  · intro a
    rw [LinearMap.comp_smul, LinearMap.smul_comp, boundedPolarization_translate]

section Dualization

variable {K : Type u} [Field K]

/-- The polynomial basis gives a concrete finite-dimensional dual model for each
bounded factor.  This is the coordinate bridge used before identifying the
dual model with the external `V_d` action. -/
def truncBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) K (Trunc K n) :=
  Polynomial.degreeLT.basis K (n + 1)

noncomputable def truncToDualEquiv (n : ℕ) :
    Trunc K n ≃ₗ[K] Module.Dual K (Trunc K n) :=
  (truncBasis (K := K) n).toDualEquiv

@[simp] theorem truncToDualEquiv_apply (n : ℕ) (f : Trunc K n) :
    truncToDualEquiv (K := K) n f =
      (truncBasis (K := K) n).toDual f := by
  rfl

/-- A section of multiplication dualizes to a retraction.  The order of the
dual maps is the essential contravariant step and is proved by the kernel API,
not by an informal finite-dimensional dimension count. -/
theorem dual_section_retraction {n m : ℕ}
    (σ : Trunc K (n + m) →ₗ[K] Trunc K n ⊗[K] Trunc K m)
    (hσ : (multiplication (R := K) n m).comp σ = LinearMap.id) :
    σ.dualMap.comp (multiplication (R := K) n m).dualMap = LinearMap.id := by
  rw [LinearMap.dualMap_comp_dualMap, hσ, LinearMap.dualMap_id]

/-- The finite dual of a tensor factor is canonically the tensor of the two
finite duals.  The local basis instances are explicit so this theorem records
exactly the finite-projective hypotheses used by `dualDistribEquiv`. -/
noncomputable def tensorDualEquiv (n m : ℕ) :
    Module.Dual K (Trunc K n) ⊗[K] Module.Dual K (Trunc K m) ≃ₗ[K]
      Module.Dual K (Trunc K n ⊗[K] Trunc K m) := by
  letI : Module.Finite K (Trunc K n) :=
    Module.Finite.of_basis (truncBasis (K := K) n)
  letI : Module.Finite K (Trunc K m) :=
    Module.Finite.of_basis (truncBasis (K := K) m)
  letI : Module.Projective K (Trunc K n) :=
    Module.Projective.of_basis (truncBasis (K := K) n)
  letI : Module.Projective K (Trunc K m) :=
    Module.Projective.of_basis (truncBasis (K := K) m)
  exact TensorProduct.dualDistribEquiv K (Trunc K n) (Trunc K m)

@[simp] theorem tensorDualEquiv_tmul_apply (n m : ℕ)
    (f : Module.Dual K (Trunc K n)) (g : Module.Dual K (Trunc K m))
    (x : Trunc K n) (y : Trunc K m) :
    tensorDualEquiv (K := K) n m (f ⊗ₜ[K] g) (x ⊗ₜ[K] y) = g y * f x := by
  letI : Module.Finite K (Trunc K n) :=
    Module.Finite.of_basis (truncBasis (K := K) n)
  letI : Module.Finite K (Trunc K m) :=
    Module.Finite.of_basis (truncBasis (K := K) m)
  letI : Module.Projective K (Trunc K n) :=
    Module.Projective.of_basis (truncBasis (K := K) n)
  letI : Module.Projective K (Trunc K m) :=
    Module.Projective.of_basis (truncBasis (K := K) m)
  simp [tensorDualEquiv]

/-- Transport the dualized multiplication map through the tensor-dual
equivalence, so its codomain is the product of the two factor duals. -/
noncomputable def dualMultiplicationTensor (n m : ℕ) :
    Module.Dual K (Trunc K (n + m)) →ₗ[K]
      Module.Dual K (Trunc K n) ⊗[K] Module.Dual K (Trunc K m) := by
  letI : Module.Finite K (Trunc K n) :=
    Module.Finite.of_basis (truncBasis (K := K) n)
  letI : Module.Finite K (Trunc K m) :=
    Module.Finite.of_basis (truncBasis (K := K) m)
  letI : Module.Projective K (Trunc K n) :=
    Module.Projective.of_basis (truncBasis (K := K) n)
  letI : Module.Projective K (Trunc K m) :=
    Module.Projective.of_basis (truncBasis (K := K) m)
  exact (tensorDualEquiv (K := K) n m).symm.toLinearMap.comp
    (multiplication (R := K) n m).dualMap

/-- The dualized section is transported to the tensor of the two factor duals. -/
noncomputable def dualSectionTensor
    {n m : ℕ} (σ : Trunc K (n + m) →ₗ[K] Trunc K n ⊗[K] Trunc K m) :
    Module.Dual K (Trunc K n) ⊗[K] Module.Dual K (Trunc K m) →ₗ[K]
      Module.Dual K (Trunc K (n + m)) := by
  letI : Module.Finite K (Trunc K n) :=
    Module.Finite.of_basis (truncBasis (K := K) n)
  letI : Module.Finite K (Trunc K m) :=
    Module.Finite.of_basis (truncBasis (K := K) m)
  letI : Module.Projective K (Trunc K n) :=
    Module.Projective.of_basis (truncBasis (K := K) n)
  letI : Module.Projective K (Trunc K m) :=
    Module.Projective.of_basis (truncBasis (K := K) m)
  exact σ.dualMap.comp (tensorDualEquiv (K := K) n m).toLinearMap

theorem dualSectionTensor_retraction {n m : ℕ}
    (σ : Trunc K (n + m) →ₗ[K] Trunc K n ⊗[K] Trunc K m)
    (hσ : (multiplication (R := K) n m).comp σ = LinearMap.id) :
    (dualSectionTensor (K := K) σ).comp
        (dualMultiplicationTensor (K := K) n m) = LinearMap.id := by
  letI : Module.Finite K (Trunc K n) :=
    Module.Finite.of_basis (truncBasis (K := K) n)
  letI : Module.Finite K (Trunc K m) :=
    Module.Finite.of_basis (truncBasis (K := K) m)
  letI : Module.Projective K (Trunc K n) :=
    Module.Projective.of_basis (truncBasis (K := K) n)
  letI : Module.Projective K (Trunc K m) :=
    Module.Projective.of_basis (truncBasis (K := K) m)
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, dualSectionTensor, dualMultiplicationTensor]
  change σ.dualMap
      ((tensorDualEquiv (K := K) n m)
        ((tensorDualEquiv (K := K) n m).symm
          ((multiplication (R := K) n m).dualMap φ))) x = φ x
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun ψ : Module.Dual K (Trunc K (n + m)) => ψ x)
    (LinearMap.congr_fun (dual_section_retraction (K := K) σ hσ) φ)

end Dualization

section OriginalModelBridge

variable {K : Type u} [Field K]

/-- The bounded dual model is definitionally the original `V_(n+1)` dual
module.  This equation also fixes the contragredient sign: the action at
`Multiplicative.ofAdd a` is the transpose of primal translation by `-a`. -/
theorem original_dualAction_as_dualMap (n : ℕ) (a : K) :
    ElmerKadrTensorCounterexample.dualAction K (n + 1)
        (Multiplicative.ofAdd a) =
      (Polynomial.taylorLinearEquiv (-a) (n + 1)).toLinearMap.dualMap := by
  simp only [ElmerKadrTensorCounterexample.dualAction,
    Representation.dual_apply, ElmerKadrTensorCounterexample.primalAction,
    ofAdd_neg, toAdd_ofAdd]
  change Module.Dual.transpose
      ((Polynomial.taylorLinearEquiv
        (Multiplicative.toAdd ((Multiplicative.ofAdd a)⁻¹)) (n + 1)).toLinearMap) =
    (Polynomial.taylorLinearEquiv (-a) (n + 1)).toLinearMap.dualMap
  rw [← ofAdd_neg a, toAdd_ofAdd]
  rfl

end OriginalModelBridge

/-
The continuation to the corrected external criterion remains unfinished:
identify finite-dimensional duals with the original V_d models, transport this
exact sequence and section to those actions, prove the quotient tensor is
M-relative-projective under the original divisibility assumptions, and connect
the binomial condition to Lucas/no-carry arithmetic and the converse obstruction.
No relative-stable equivalence or full carry criterion is asserted here.
-/

end D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
