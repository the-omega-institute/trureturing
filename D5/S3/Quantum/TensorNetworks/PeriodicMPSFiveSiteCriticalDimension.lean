/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalDimension
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalDimension
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.KrullDimension.Polynomial]
   utility: none
   digest: The two certified critical minors cut out a locus of complex codimension at least two. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Relative primality makes the second minor a nonzero divisor modulo the first. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDimension

open PeriodicMPSFiveSiteCriticalDivisors
open scoped nonZeroDivisors

private theorem two_equations_dim {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (p q : R) (hp : p ≠ 0) (h : IsRelPrime p q) :
    ringKrullDim (R ⧸ Ideal.span {p, q}) + 2 ≤ ringKrullDim R := by
  let I : Ideal R := Ideal.span {p}
  let J : Ideal R := Ideal.span {p, q}
  have hIJ : I ≤ J := Ideal.span_mono (by simp)
  have hq : Ideal.Quotient.mk I q ∈ (R ⧸ I)⁰ := by
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_right
      (Ideal.mem_span_singleton.mp ha))
  have hz : Ideal.Quotient.factor hIJ (Ideal.Quotient.mk I q) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have h₁ : ringKrullDim (R ⧸ I) + 1 ≤ ringKrullDim R :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_iff_ne_zero.mpr hp)
  have h₂ : ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ I) :=
    ringKrullDim_succ_le_of_surjective _ (Ideal.Quotient.factor_surjective hIJ) hq hz
  calc
    _ = (ringKrullDim (R ⧸ J) + 1) + 1 := by rw [add_assoc, one_add_one_eq_two]
    _ ≤ ringKrullDim (R ⧸ I) + 1 := add_le_add_left h₂ 1
    _ ≤ _ := h₁

/-- The quotient by the two critical equations has Krull dimension at most
eight, expressed as a codimension bound in the ten-variable cone. -/
theorem critical_minor_codimension {K : Type*} [Field K] [CharZero K] :
    ringKrullDim (MvPolynomial (Fin 10) K ⧸
      Ideal.span {minorOver (K := K) 0, minorOver (K := K) 1}) + 2 ≤ 10 := by
  have h := two_equations_dim (minorOver (K := K) 0) (minorOver (K := K) 1)
    first_minor_ne_zero relatively_prime_minors
  simpa using h

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDimension
