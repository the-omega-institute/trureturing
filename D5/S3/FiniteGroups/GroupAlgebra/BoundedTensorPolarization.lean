/- GID: D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis]
   utility: none
   digest: Bounded polynomial tensor multiplication, difference injection and polarization. -/


import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Denominator-free polarization, bounded tensor exactness and equivariant sections.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization

open Polynomial Finset
open scoped TensorProduct

universe u v

section CoefficientPolarization

variable {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]

/-- Set t=1 only in the homogeneous auxiliary variables; x,y remain independent. -/
def generating (N k : ℕ) (x y : A) : A[X] :=
  (X + 1) ^ (N - k) * (X * C x + C y) ^ k

/-- The denominator-free polarization coefficient at s^n. The intended domain
has k≤N; without that hypothesis this still defines an expression but is not
asserted to be the degree-N homogeneous construction. -/
def polarCoeff (N n k : ℕ) (x y : A) : A :=
  (generating N k x y).coeff n

/-- Naturality will be consumed both by diagonal restriction and by translation. -/
theorem generating_map (f : A →+* B) (N k : ℕ) (x y : A) :
    (generating N k x y).map f = generating N k (f x) (f y) := by
  simp [generating, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add]

theorem polarCoeff_natural (f : A →+* B) (N n k : ℕ) (x y : A) :
    f (polarCoeff N n k x y) = polarCoeff N n k (f x) (f y) := by
  unfold polarCoeff
  rw [← Polynomial.coeff_map, generating_map]

/-- The scalar arises from coefficient extraction of (s+1)^N. This proof uses
k≤N explicitly: truncated natural subtraction cannot silently remove it. -/
theorem polarCoeff_diagonal (N n k : ℕ) (hk : k ≤ N) (x : A) :
    polarCoeff N n k x x = (N.choose n : A) * x ^ k := by
  have hlin : (X : A[X]) * C x + C x = (X + 1) * C x := by ring
  unfold polarCoeff generating
  rw [hlin, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk,
    ← Polynomial.C_pow, Polynomial.coeff_mul_C,
    Polynomial.coeff_X_add_one_pow]

/-- Translation identity BEFORE extraction. This is a polynomial identity over
any commutative semiring, so it needs no finite-field cardinality hypothesis.
Its live algebraic step combines (N-k)+(k-j)=N-j for j≤k≤N. -/
theorem generating_add (N k : ℕ) (hk : k ≤ N) (x y c : A) :
    generating N k (x + c) (y + c) =
      ∑ j ∈ range (k + 1),
        C ((k.choose j : A) * c ^ (k - j)) * generating N j x y := by
  let S : A[X] := X + 1
  let L : A[X] := X * C x + C y
  have hlin : (X : A[X]) * C (x + c) + C (y + c) = L + C c * S := by
    dsimp [L, S]
    rw [map_add, map_add]
    ring
  change S ^ (N - k) * ((X : A[X]) * C (x + c) + C (y + c)) ^ k = _
  rw [hlin, add_pow L (C c * S) k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hexp : N - k + (k - j) = N - j := by omega
  change S ^ (N - k) * (L ^ j * (C c * S) ^ (k - j) * (k.choose j : A[X])) =
    C ((k.choose j : A) * c ^ (k - j)) * (S ^ (N - j) * L ^ j)
  rw [mul_pow, ← Polynomial.C_pow]
  calc
    S ^ (N - k) * (L ^ j * (C (c ^ (k - j)) * S ^ (k - j)) *
        (k.choose j : A[X])) =
      C ((k.choose j : A) * c ^ (k - j)) *
        (S ^ (N - k) * S ^ (k - j)) * L ^ j := by
          rw [map_mul, Polynomial.C_eq_natCast]
          ring
    _ = C ((k.choose j : A) * c ^ (k - j)) *
        (S ^ (N - j) * L ^ j) := by
          rw [← pow_add, hexp]
          ring

/-- The actual coefficient translation law includes all lower degrees. In
particular, polarization is not being asserted to commute merely with an
infinitesimal generator. -/
theorem polarCoeff_add (N n k : ℕ) (hk : k ≤ N) (x y c : A) :
    polarCoeff N n k (x + c) (y + c) =
      ∑ j ∈ range (k + 1),
        ((k.choose j : A) * c ^ (k - j)) * polarCoeff N n j x y := by
  unfold polarCoeff
  rw [generating_add N k hk]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

/-- Expanding the auxiliary variable keeps the condition i≤n explicit. -/
theorem polarCoeff_sum (N n k : ℕ) (x y : A) :
    polarCoeff N n k x y = ∑ i ∈ range (k + 1),
      if i ≤ n then
        ((N - k).choose (n - i) : A) * (k.choose i : A) * x ^ i * y ^ (k - i)
      else 0 := by
  unfold polarCoeff generating
  rw [add_pow (X * C x) (C y) k, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have ht : (X + 1) ^ (N - k) *
        ((X * C x) ^ i * C y ^ (k - i) * (k.choose i : A[X])) =
      ((X + 1) ^ (N - k) * X ^ i) *
        C ((k.choose i : A) * x ^ i * y ^ (k - i)) := by
    simp only [mul_pow, ← Polynomial.C_pow, map_mul, Polynomial.C_eq_natCast]
    ring
  rw [ht, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow']
  split_ifs <;> simp [Polynomial.coeff_X_add_one_pow, mul_assoc]

/-- Out-of-box terms vanish before truncated subtraction can create fake terms. -/
theorem polarCoeff_box (n m k : ℕ) (hk : k ≤ n + m) (x y : A) :
    polarCoeff (n + m) n k x y = ∑ i ∈ range (k + 1),
      if i ≤ n ∧ k - i ≤ m then
        ((n + m - k).choose (n - i) : A) * (k.choose i : A) * x ^ i * y ^ (k - i)
      else 0 := by
  rw [polarCoeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  by_cases hin : i ≤ n
  · by_cases hjm : k - i ≤ m
    · simp [hin, hjm]
    · have hz : (n + m - k).choose (n - i) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp [hin, hjm, hz]
  · simp [hin]

end CoefficientPolarization

section AmbientKernel

variable {R : Type u} [CommRing R]

abbrev Bi (R : Type u) [CommRing R] := Polynomial (Polynomial R)

/-- Outer polynomial variable. -/
def z₁ : Bi R := X

/-- Inner polynomial variable. -/
def z₂ : Bi R := C X

/-- Scalars in the two-variable polynomial ring. -/
def scalar (a : R) : Bi R := C (C a)

/-- Actual diagonal substitution, not a map on values at finitely many points. -/
def diagonal : Bi R →+* R[X] := Polynomial.evalRingHom X

@[simp] theorem diagonal_z₁ : diagonal (z₁ : Bi R) = (X : R[X]) := by
  simp [diagonal, z₁]

@[simp] theorem diagonal_z₂ : diagonal (z₂ : Bi R) = (X : R[X]) := by
  simp [diagonal, z₂]

/-- The chosen sign agrees with the supplied dual quotient checker. -/
def difference : Bi R := z₁ - z₂

/-- Simultaneously substitute z₁+a and z₂+a. The coefficient hom translates
z₂; the outer substitution translates z₁. -/
def translate (a : R) : Bi R →+* Bi R :=
  Polynomial.eval₂RingHom
    (Polynomial.C.comp (Polynomial.taylorAlgHom a).toRingHom)
    (z₁ + scalar a)

@[simp] theorem translate_z₁ (a : R) :
    translate a (z₁ : Bi R) = z₁ + scalar a := by
  simp [translate, z₁, Polynomial.coe_eval₂RingHom]

@[simp] theorem translate_z₂ (a : R) :
    translate a (z₂ : Bi R) = z₂ + scalar a := by
  simp [translate, z₂, scalar, Polynomial.coe_eval₂RingHom]

@[simp] theorem translate_scalar (a b : R) :
    translate a (scalar b) = scalar b := by
  simp [translate, scalar, Polynomial.coe_eval₂RingHom]

@[simp] theorem translate_difference (a : R) :
    translate a (difference : Bi R) = difference := by
  simp only [difference, map_sub, translate_z₁, translate_z₂]
  ring

/-- Difference multiplication is injective even over rings with zero divisors:
the OUTER polynomial X-C(X) is monic. No domain assumption is smuggled in. -/
theorem difference_mul_injective :
    Function.Injective (fun F : Bi R => difference * F) := by
  change IsLeftRegular ((X : Bi R) - C (X : R[X]))
  exact (Polynomial.monic_X_sub_C (X : R[X])).isRegular.left

/-- Translation equivariance of the ambient kernel injection. -/
theorem translate_difference_mul (a : R) (F : Bi R) :
    translate a (difference * F) = difference * translate a F := by
  rw [map_mul, translate_difference]

/-- Diagonal restriction intertwines actual polynomial translations. -/
theorem diagonal_translate (a : R) (F : Bi R) :
    diagonal (translate a F) = Polynomial.taylor a (diagonal F) := by
  have hh : (diagonal (R := R)).comp (translate a) =
      (Polynomial.taylorAlgHom a).toRingHom.comp (diagonal (R := R)) := by
    ext <;> simp [diagonal, translate, z₁, scalar, Polynomial.coe_eval₂RingHom]
  exact congrArg (fun f : Bi R →+* R[X] => f F) hh

/-- Simultaneous substitution also preserves the original R-module structure. -/
def translateLinear (a : R) : Bi R →ₗ[R] Bi R where
  toFun := translate a
  map_add' := (translate a).map_add
  map_smul' r F := by
    simp only [Algebra.smul_def, map_mul]
    change translate a (scalar r) * translate a F = scalar r * translate a F
    rw [translate_scalar]

theorem translate_map_C (a : R) (f : R[X]) :
    translate a (f.map C) = (Polynomial.taylor a f).map C := by
  have h : (translate a).comp (Polynomial.mapRingHom (C : R →+* R[X])) =
      (Polynomial.mapRingHom (C : R →+* R[X])).comp
        (Polynomial.taylorAlgHom a).toRingHom := by
    ext <;> simp [translate, z₁, scalar, Polynomial.coe_eval₂RingHom]
  exact congrArg (fun g : R[X] →+* Bi R => g f) h

theorem translate_C (a : R) (f : R[X]) :
    translate a (C f) = C (Polynomial.taylor a f) := by
  simp [translate, Polynomial.coe_eval₂RingHom]

end AmbientKernel

section PolynomialPolarization

variable {R : Type u} [CommRing R]

/-- N=n+m and output coefficient n are kept separate for simpler reuse. -/
def polarMonomial (N n k : ℕ) : Bi R :=
  polarCoeff N n k z₁ z₂

/-- Diagonal restriction after denominator-free polarization, with no
characteristic restriction. -/
theorem diagonal_polarMonomial (N n k : ℕ) (hk : k ≤ N) :
    diagonal (polarMonomial (R := R) N n k) =
      C (N.choose n : R) * (X : R[X]) ^ k := by
  rw [polarMonomial, polarCoeff_natural, diagonal_z₁, diagonal_z₂,
    polarCoeff_diagonal N n k hk, Polynomial.C_eq_natCast]

/-- Actual simultaneous-translation law for each polarized monomial. Since
scalar a is fixed by translate, these are precisely the binomial coefficients
of (z+a)^k, with the SAME translation parameter in the two factors. -/
theorem translate_polarMonomial (a : R) (N n k : ℕ) (hk : k ≤ N) :
    translate a (polarMonomial (R := R) N n k) =
      ∑ j ∈ range (k + 1),
        ((k.choose j : Bi R) * scalar a ^ (k - j)) *
          polarMonomial N n j := by
  rw [polarMonomial, polarCoeff_natural, translate_z₁, translate_z₂,
    polarCoeff_add N n k hk]
  rfl

/-- Extend by the existing degreeLT monomial basis. This targets the ambient
polynomial ring until the finite box bound is proved; see the companion file. -/
def polarization (N n : ℕ) : Polynomial.degreeLT R (N + 1) →ₗ[R] Bi R :=
  (Polynomial.degreeLT.basis R (N + 1)).constr R fun i => polarMonomial N n i

@[simp] theorem polarization_basis (N n : ℕ) (i : Fin (N + 1)) :
    polarization (R := R) N n (Polynomial.degreeLT.basis R (N + 1) i) =
      polarMonomial N n i := by
  simp [polarization]

/-- Diagonal restriction as an R-linear map. -/
def diagonalLinear : Bi R →ₗ[R] R[X] where
  toFun := diagonal
  map_add' := (diagonal (R := R)).map_add
  map_smul' r F := by
    change (r • F).eval (X : R[X]) = r • F.eval (X : R[X])
    exact Polynomial.eval_smul r F X

/-- mu Delta = choose(N,n) id, expressed in the ambient polynomial ring so
that no unproved finite-box membership is hidden in a codomain coercion. -/
theorem diagonal_polarization (N n : ℕ) :
    (diagonalLinear (R := R)).comp (polarization N n) =
      (N.choose n : R) • (Polynomial.degreeLT R (N + 1)).subtype := by
  apply (Polynomial.degreeLT.basis R (N + 1)).ext
  intro i
  simp only [LinearMap.comp_apply, polarization_basis, LinearMap.smul_apply,
    Submodule.subtype_apply, Polynomial.degreeLT.basis_val]
  change diagonal (polarMonomial (R := R) N n i) =
    (N.choose n : R) • (X : R[X]) ^ (i : ℕ)
  rw [diagonal_polarMonomial N n i (Nat.le_of_lt_succ i.is_lt), Polynomial.smul_eq_C_mul]

/-- Equivariance for every translation parameter, including all lower terms. -/
theorem polarization_translate (a : R) (N n : ℕ) :
    (translateLinear a).comp (polarization (R := R) N n) =
      (polarization N n).comp (Polynomial.taylorLinearEquiv a (N + 1)).toLinearMap := by
  apply (Polynomial.degreeLT.basis R (N + 1)).ext
  intro k
  have hcoeff (j : Fin (N + 1)) :
      (Polynomial.degreeLT.basis R (N + 1)).equivFun
        ((Polynomial.taylorLinearEquiv a (N + 1)).toLinearMap
          (Polynomial.degreeLT.basis R (N + 1) k)) j =
        a ^ (k.val - j.val) * (k.val.choose j.val : R) := by
    change (Polynomial.taylor a
      (Polynomial.degreeLT.basis R (N + 1) k : R[X])).coeff j.val = _
    rw [Polynomial.degreeLT.basis_val, Polynomial.taylor_X_pow, Polynomial.coeff_X_add_C_pow]
  simp only [LinearMap.comp_apply, polarization_basis]
  change translate a (polarMonomial (R := R) N n k.val) = _
  rw [translate_polarMonomial a N n k.val (Nat.le_of_lt_succ k.is_lt)]
  conv_rhs => rw [polarization, Module.Basis.constr_apply_fintype]
  simp only [hcoeff]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (a ^ (k.val - j) * (k.val.choose j : R)) • polarMonomial (R := R) N n j) (N + 1)]
  calc
    _ = ∑ j ∈ range (k.val + 1),
        (a ^ (k.val - j) * (k.val.choose j : R)) • polarMonomial N n j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
        map_mul, map_pow, scalar, RingHom.id_apply]
      simp only [Polynomial.C_eq_natCast]
      ring
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ
        (Nat.le_of_lt_succ k.is_lt)))
      intro j hj hjk
      have hkj : k.val < j := by
        simp only [Finset.mem_range, not_lt] at hjk
        omega
      simp [Nat.choose_eq_zero_of_lt hkj]

end PolynomialPolarization

end D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization

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

end D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
open Polynomial
open scoped TensorProduct DirectSum

universe uK uG

section DualMaps

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {A B : Type uK} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  {ρ : Representation K G A} {τ : Representation K G B}

/-- Transpose reverses an actual intertwiner; the inverse group element is
the one in the definition of the contragredient representation. -/
def dualIntertwiner (f : ρ.IntertwiningMap τ) :
    τ.dual.IntertwiningMap ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' c := by
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro x
    change l (τ c⁻¹ (f x)) = l (f (ρ c⁻¹ x))
    rw [f.isIntertwining]

/-- The canonical finite-dimensional dual tensor identification is equivariant
for the actual contragredient actions. Its evaluation uses Mathlib's order
`g y * f x`; no matrix model or basis change defines the action. -/
def dualTensorEquiv [Module.Finite K A] [Module.Finite K B]
    [Module.Projective K A] [Module.Projective K B]
    (ρ : Representation K G A) (τ : Representation K G B) :
    (ρ.dual.tprod τ.dual).Equiv (ρ.tprod τ).dual :=
  Representation.Equiv.mk (TensorProduct.dualDistribEquiv K A B) fun c => by
    apply TensorProduct.ext'
    intro f g
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.dualDistribEquiv K A B
        (ρ.dual c f ⊗ₜ[K] τ.dual c g) (x ⊗ₜ[K] y) =
      TensorProduct.dualDistribEquiv K A B (f ⊗ₜ[K] g)
        (ρ c⁻¹ x ⊗ₜ[K] τ c⁻¹ y)
    simp only [TensorProduct.dualDistribEquiv_tmul_tmul,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]

end DualMaps

section ExactSplitting

variable {K : Type uK} [Field K]

/-- Multiplication intertwines actual translations, by the already proved
diagonal realization of the bounded polynomial tensor map. -/
theorem multiplication_translate (a : K) (n m : ℕ) :
    (multiplication (R := K) n m).comp (tensorTranslate a n m) =
      (Polynomial.taylorLinearEquiv a (n + m + 1)).toLinearMap.comp
        (multiplication n m) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  have hd (z : Trunc K n ⊗[K] Trunc K m) :
      diagonal (tensorPolynomial n m z) = (multiplication n m z : K[X]) :=
    LinearMap.congr_fun (diagonal_tensorPolynomial (R := K) n m) z
  change (multiplication n m (tensorTranslate a n m F) : K[X]) =
    Polynomial.taylor a (multiplication n m F : K[X])
  calc
    _ = diagonal (tensorPolynomial n m (tensorTranslate a n m F)) := (hd _).symm
    _ = Polynomial.taylor a (multiplication n m F : K[X]) := by
      rw [tensorPolynomial_translate, diagonal_translate, hd]

def multiplicationIntertwiner (n m : ℕ) :
    ((primalAction K (n + 1)).tprod (primalAction K (m + 1))).IntertwiningMap
      (primalAction K (n + m + 1)) where
  toLinearMap := multiplication n m
  isIntertwining' c := multiplication_translate (Multiplicative.toAdd c) n m

def differenceIntertwiner (n m : ℕ) :
    ((primalAction K (n + 1)).tprod (primalAction K (m + 1))).IntertwiningMap
      ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))) where
  toLinearMap := differenceTensor n m
  isIntertwining' c :=
    (tensorTranslate_differenceTensor (Multiplicative.toAdd c) n m).symm

/-- The residual lands in range(d), by exactness and μσ = id. -/
def kernelResidual (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id) :
    (Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) →ₗ[K]
      LinearMap.range (differenceTensor (R := K) n m) :=
  (LinearMap.id - σ.comp (multiplication (n + 1) (m + 1))).codRestrict _ fun F => by
    rw [differenceTensor_range]
    change multiplication (n + 1) (m + 1)
      (F - σ (multiplication (n + 1) (m + 1) F)) = 0
    have hs := LinearMap.congr_fun hσ (multiplication (n + 1) (m + 1) F)
    change multiplication (n + 1) (m + 1)
      (σ (multiplication (n + 1) (m + 1) F)) = multiplication (n + 1) (m + 1) F at hs
    rw [map_sub, hs, sub_self]

/-- h is obtained from the inverse of d onto its PROVED range, applied to
id - σμ. No equivariant-complement choice is made. -/
def kernelRetraction (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id) :
    (Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) →ₗ[K]
      (Trunc K n ⊗[K] Trunc K m) :=
  (LinearEquiv.ofInjective (differenceTensor n m)
    (differenceTensor_injective n m)).symm.toLinearMap.comp (kernelResidual n m σ hσ)

theorem difference_kernelRetraction (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id)
    (F : Trunc K (n + 1) ⊗[K] Trunc K (m + 1)) :
    differenceTensor n m (kernelRetraction n m σ hσ F) =
      F - σ (multiplication (n + 1) (m + 1) F) := by
  exact LinearEquiv.ofInjective_symm_apply (differenceTensor (R := K) n m)
    (h := differenceTensor_injective n m) (kernelResidual n m σ hσ F)

/-- Injectivity of the actual d forces h to intertwine translations. -/
def kernelRetractionIntertwiner (n m : ℕ)
    (σ : (primalAction K ((n + 1) + (m + 1) + 1)).IntertwiningMap
      ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ.toLinearMap = LinearMap.id) :
    ((primalAction K ((n + 1) + 1)).tprod (primalAction K ((m + 1) + 1))).IntertwiningMap
      ((primalAction K (n + 1)).tprod (primalAction K (m + 1))) where
  toLinearMap := kernelRetraction n m σ.toLinearMap hσ
  isIntertwining' c := by
    apply LinearMap.ext
    intro F
    apply differenceTensor_injective (R := K) n m
    change differenceTensor n m (kernelRetraction n m σ.toLinearMap hσ
        (((primalAction K ((n + 1) + 1)).tprod
          (primalAction K ((m + 1) + 1))) c F)) =
      differenceIntertwiner n m
        (((primalAction K (n + 1)).tprod (primalAction K (m + 1))) c
          (kernelRetraction n m σ.toLinearMap hσ F))
    rw [difference_kernelRetraction, (differenceIntertwiner n m).isIntertwining]
    change _ = (((primalAction K ((n + 1) + 1)).tprod
      (primalAction K ((m + 1) + 1))) c)
        (differenceTensor n m (kernelRetraction n m σ.toLinearMap hσ F))
    rw [difference_kernelRetraction, map_sub]
    change _ - σ (multiplicationIntertwiner (n + 1) (m + 1)
      (((primalAction K ((n + 1) + 1)).tprod
        (primalAction K ((m + 1) + 1))) c F)) = _
    rw [(multiplicationIntertwiner (n + 1) (m + 1)).isIntertwining, σ.isIntertwining]
    simp [multiplicationIntertwiner]
    congr 1

end ExactSplitting

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion
