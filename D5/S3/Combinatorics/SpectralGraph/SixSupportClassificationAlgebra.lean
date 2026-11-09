/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportClassificationAlgebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportClassificationAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The received exact quintic and endpoint tests act on actual ideal graphs. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial
import D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-! The symbolic coefficients below are the characteristic quotient from the
Nikandish outreach three-prime manuscript, not an independent spectral model.
The supplied MatrixPolynomialComplete02 determinant proof is reused intact. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

open Matrix Polynomial
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- Exact monic quintic, written using the three elementary symmetric parameters. -/
def quintic {R : Type*} [CommRing R] (a b c : R) : Polynomial R :=
  let s := a+b+c
  let t := a*b+a*c+b*c
  let u := a*b*c
  X^5 - C (3*s+t)*X^4 + C (3*s^2+2*s*t+s*u+t)*X^3
    - C (s^3+s^2*t+s^2*u+2*s*t+t^2+u^2+u)*X^2
    + C (s^2*t+s*t^2+s*t*u+2*s*u+t*u-3*u^2)*X
    - C (s^2*u+s*t*u)

/-- Scalar evaluation of the same quintic, over any coefficient ring. -/
def h {R : Type*} [CommRing R] (a b c x : R) : R := (quintic a b c).eval x

/-- Integer-friendly Horner evaluation of the identical quintic. -/
def value {R : Type*} [CommRing R] (a b c x : R) : R :=
  let s := a+b+c
  let t := a*b+a*c+b*c
  let u := a*b*c
  (((((x-(3*s+t))*x+(3*s^2+2*s*t+s*u+t))*x-
    (s^3+s^2*t+s^2*u+2*s*t+t^2+u^2+u))*x+
    (s^2*t+s*t^2+s*t*u+2*s*u+t*u-3*u^2))*x-(s^2*u+s*t*u))

/-- Horner evaluation changes neither the statement nor the characteristic model. -/
theorem h_eq_value {R : Type*} [CommRing R] (a b c x : R) : h a b c x = value a b c x := by
  simp [h, quintic, value]
  ring

/-- Reuse the supplied six-cell determinant at its complete parameter domain. -/
theorem determinant (a b c x : ℝ) :
    (Matrix.scalar (Fin 6) x - quotient a b c).det = x * h a b c x := by
  change (Matrix.scalar (Fin 6) x - quotientOver a b c).det = _
  rw [determinant_formula]
  simp only [h, quintic, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  dsimp [d₁, d₂, d₃]
  ring

/-- This is exactly the supplied quotient's reduced characteristic polynomial. -/
theorem quintic_eq_reduced (a b c : ℝ) :
    quintic a b c = reducedCharpoly a b c := by
  have heq : (X : Polynomial ℝ) * quintic a b c = (quotientOver a b c).charpoly := by
    apply Polynomial.funext
    intro x
    rw [Polynomial.eval_mul, Polynomial.eval_X, Matrix.eval_charpoly]
    change x * h a b c x = (Matrix.scalar (Fin 6) x - quotient a b c).det
    exact (determinant a b c x).symm
  rw [charpoly_zero_factor] at heq
  exact mul_left_cancel₀ (Polynomial.X_ne_zero : (X : Polynomial ℝ) ≠ 0) heq

/-- Root-to-eigenvector conversion on the literal six-cell operator. -/
theorem eigenpair_of_root (a b c e : ℝ) (he : h a b c e = 0) :
    ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient a b c *ᵥ z = e • z := by
  have hd : (Matrix.scalar (Fin 6) e - quotient a b c).det = 0 := by
    rw [determinant, he, mul_zero]
  obtain ⟨z, hz, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨z, hz, ?_⟩
  have hs : (Matrix.scalar (Fin 6) e) *ᵥ z = e • z := by
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  rw [Matrix.sub_mulVec, hs] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- Every nonzero real eigenvalue of the literal quotient is a root of the
same reduced characteristic polynomial. -/
theorem root_of_eigenpair (a b c e : ℝ) (he0 : e ≠ 0)
    (z : Fin 6 → ℝ) (hz : z ≠ 0) (he : quotient a b c *ᵥ z = e • z) :
    h a b c e = 0 := by
  have hd : (Matrix.scalar (Fin 6) e - quotient a b c).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨z, hz, ?_⟩
    have hs : (Matrix.scalar (Fin 6) e) *ᵥ z = e • z := by
      ext i
      simp [Matrix.scalar, Matrix.mulVec_diagonal]
    rw [Matrix.sub_mulVec, hs, he, sub_self]
  rw [determinant] at hd
  exact (mul_eq_zero.mp hd).resolve_left he0

/-- Every nonzero root of the exact quintic is consumed by the actual ideal graph. -/
theorem actual_of_root (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (he0 : e ≠ 0) (he : h (a : ℝ) (b : ℝ) (c : ℝ) e = 0) :
    HasActualEigenvalue (modulus p (exponents a b c))
      (((((a+1)*(b+1)*(c+1))-2 : ℕ) : ℝ)-e) := by
  obtain ⟨z, hz, heigen⟩ := eigenpair_of_root a b c e he
  exact actual_eigenvalue p hp hinj a b c ha hb hc e he0 z hz heigen

/-- Actual integral spectrum forces each nonzero quotient root to be an integer. -/
theorem root_integral_of_actual_integral (p : Fin 3 → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hint : ActualLaplacianIntegral (modulus p (exponents a b c)))
    (e : ℝ) (he0 : e ≠ 0) (he : h (a : ℝ) (b : ℝ) (c : ℝ) e = 0) :
    ∃ z : ℤ, e = z := by
  obtain ⟨z, hz⟩ := hint _ (actual_of_root p hp hinj a b c ha hb hc e he0 he)
  refine ⟨(((a+1)*(b+1)*(c+1)-2 : ℕ) : ℤ)-z, ?_⟩
  push_cast
  linarith

/-- A positive root in an open integer unit interval disproves integrality
of the actual graph; the nonzero graph eigenvector is supplied above. -/
theorem nonintegral_of_unit_root (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (he0 : e ≠ 0) (he : h (a : ℝ) (b : ℝ) (c : ℝ) e = 0)
    (q : ℤ) (hl : (q : ℝ) < e) (hu : e < (q : ℝ)+1) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  intro hint
  obtain ⟨z, rfl⟩ := root_integral_of_actual_integral p hp hinj a b c ha hb hc hint e he0 he
  have hzl : q < z := by exact_mod_cast hl
  have hzu : z < q+1 := by exact_mod_cast hu
  omega

/-- Integrality of the actual graph forces one of the two exact low-root endpoints.
No endpoint is excluded merely by the open interval (0,3). -/
theorem endpoint_one_or_two (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hint : ActualLaplacianIntegral (modulus p (exponents a b c))) :
    h (a : ℝ) (b : ℝ) (c : ℝ) 1 = 0 ∨
      h (a : ℝ) (b : ℝ) (c : ℝ) 2 = 0 := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  obtain ⟨e, he0, he3, z, hz, heigen⟩ := positive_real_low_eigenvalue a b c
    (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hbc)
  have hdet : (Matrix.scalar (Fin 6) e - quotient a b c).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨z, hz, ?_⟩
    have hs : (Matrix.scalar (Fin 6) e) *ᵥ z = e • z := by
      ext i
      simp [Matrix.scalar, Matrix.mulVec_diagonal]
    rw [Matrix.sub_mulVec, hs, heigen, sub_self]
  have hroot : h (a : ℝ) (b : ℝ) (c : ℝ) e = 0 := by
    rw [determinant] at hdet
    exact (mul_eq_zero.mp hdet).resolve_left he0.ne'
  obtain ⟨n, hn⟩ := root_integral_of_actual_integral p hp hinj a b c ha hb hc
    hint e he0.ne' hroot
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by simpa [hn] using he0)
  have hn3 : n < 3 := by exact_mod_cast (show (n : ℝ) < 3 by simpa [hn] using he3)
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  · left; simpa [hn] using hroot
  · right; simpa [hn] using hroot

#print axioms determinant
#print axioms quintic_eq_reduced
#print axioms actual_of_root
#print axioms nonintegral_of_unit_root
#print axioms endpoint_one_or_two

end D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
