/- GID: D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis]
   utility: none
   digest: Bounded polynomial tensor multiplication, difference injection and polarization. -/

import D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
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
    by_cases hik : i = k
    · by_cases hjl : j = l
      · subst k
        subst l
        simp [nestedCoeff, z₁, z₂, Polynomial.coeff_mul_C,
          Polynomial.coeff_X_pow, ← Polynomial.C_pow]
      · have hnat : (j : ℕ) ≠ (l : ℕ) := by
          intro h
          exact hjl (Fin.ext h)
        simp [nestedCoeff, z₁, z₂, Polynomial.coeff_mul_C,
          Polynomial.coeff_X_pow, ← Polynomial.C_pow, hnat]
    · have hnat : (i : ℕ) ≠ (k : ℕ) := by
        intro h
        exact hik (Fin.ext h)
      simp [nestedCoeff, z₁, z₂, Polynomial.coeff_mul_C,
        Polynomial.coeff_X_pow, ← Polynomial.C_pow, hnat]
  have hcoordF := LinearMap.congr_fun hcoord F
  have hcoordG := LinearMap.congr_fun hcoord G
  calc
    (tensorBasis (R := R) n m).repr F (i, j) =
        nestedCoeff (R := R) (i : ℕ) (j : ℕ)
          (tensorPolynomial (R := R) n m F) := hcoordF.symm
    _ = nestedCoeff (R := R) (i : ℕ) (j : ℕ)
          (tensorPolynomial (R := R) n m G) := by rw [hFG]
    _ = (tensorBasis (R := R) n m).repr G (i, j) := hcoordG

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
    simp only [LinearMap.comp_apply, differenceTensor, Module.Basis.constr_basis,
      map_sub, tensorPolynomial_basis, LinearMap.mulLeft_apply]
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

/-
EXACT UNFINISHED TYPES AND ROUTE (not accepted declarations).

1. Rectangular degree bounds for coefficient extraction. This is the essential
   missing codomain obligation, not supplied by the ambient scalar identity.
   A nonzero coefficient with z₁ exponent i and z₂ exponent j has i+j=k,
   i≤n, j≤m, since its auxiliary s,t exponents are n,m. Use the two binomial
   expansions, or a proved multigrading coefficient-support lemma. Existing
   Mathlib.Algebra.Polynomial.Homogenize offers homogenizeLM,
   isHomogeneous_homogenize, coeff_homogenize, and homogenize_mul for an
   alternative homogeneous implementation; no bridge from those APIs to
   this nested-polynomial coefficient construction is asserted here.

   theorem polarMonomial_in_tensor_range (n m k : ℕ) (hk : k ≤ n+m) :
       polarMonomial (R := R) (n+m) n k ∈
         LinearMap.range (tensorPolynomial n m)

2. Equivariance of the bounded difference map remains an exact separate target:
   theorem tensorTranslate_differenceTensor (a : R) (n m : ℕ) :
       (tensorTranslate a (n + 1) (m + 1)).comp (differenceTensor n m) =
         (differenceTensor n m).comp (tensorTranslate a n m)

3. This is the EXACT desired denominator-free bounded equivariant map. Do not
   replace it by the arbitrary monomialLift above: that map is not equivariant.
   The existence must be constructed from polarization, the range theorem,
   and tensorPolynomial_injective; the translation equation follows from
   translate_polarMonomial and the degreeLT Taylor coefficients.

   theorem bounded_polarization (n m : ℕ) :
       ∃ Δ : Trunc R (n+m) →ₗ[R] Trunc R n ⊗[R] Trunc R m,
         (tensorPolynomial n m).comp Δ = polarization (n+m) n ∧
         (multiplication n m).comp Δ =
           ((n+m).choose n : R) • LinearMap.id ∧
         ∀ a : R,
           (tensorTranslate a n m).comp Δ =
             Δ.comp (Polynomial.taylorLinearEquiv a (n+m+1)).toLinearMap

   Over a field with ((n+m).choose n : R) ≠ 0, multiplying this Δ by the
   inverse scalar then gives an ACTUAL equivariant section. Combining that
   with differenceTensor_range gives the primal direct sum; finite-dimensional
   dualization gives V_(n+m+1) and complement V_n tensor V_m for n,m>0.
   No assertion of that split, dual module identification, relative projectivity,
   Lucas/no-carry equivalence, or corrected stable theorem is made in this draft.
-/

end D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
