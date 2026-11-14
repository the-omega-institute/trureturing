/- GID: D5/S3/FiniteGroups/GroupAlgebra/PolynomialKernelPolarization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PolynomialKernelPolarization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis]
   utility: none
   digest: Denominator-free coefficient polarization and the ambient diagonal kernel. -/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

/-!
Denominator-free coefficient polarization and the ambient diagonal kernel.
These constructions are helpers on the route to the corrected relative-stable criterion.
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

@[simp] theorem diagonal_scalar (a : R) : diagonal (scalar a) = C a := by
  simp [diagonal, scalar]

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

/-- Ambient ideal-theoretic kernel. Finite rectangular bounds are a separate
obligation below; this theorem alone does not identify a bounded tensor kernel. -/
theorem diagonal_eq_zero_iff (F : Bi R) :
    diagonal F = 0 ↔ ∃ H : Bi R, F = difference * H := by
  change F.eval (X : R[X]) = 0 ↔ _
  constructor
  · intro hF
    have hd : (X : Bi R) - C (X : R[X]) ∣ F :=
      Polynomial.dvd_iff_isRoot.mpr hF
    obtain ⟨H, hH⟩ := hd
    exact ⟨H, hH⟩
  · rintro ⟨H, rfl⟩
    simp [difference, z₁, z₂]

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

end PolynomialPolarization

end D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
